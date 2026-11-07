(* The check that the code to be translated uses only what the translation
   supports.  It runs on the IR handed to the translation and looks at the
   functions [Scope.reachable] returns; anything outside the list makes the
   answer UNKNOWN, with the first offending construct as the reason.

   It checks kinds: which instructions, types, attributes, metadata,
   constants and intrinsics may occur.  The conditions on the shape of a
   construct that is admitted (a lifetime marker's operands, a memset's
   length, a GEP's indices, ...) belong to the rule that translates it, which
   makes the answer UNKNOWN in the same way when they fail. *)

let unknown = Scope.unknown

(* Attributes with no effect on the meaning the translation gives a function
   or call: optimisation and code-generation hints, and the promises that the
   translation itself checks or assumes ([noundef], the extension of a narrow
   integer at a call boundary).  [alwaysinline] is listed for the T2 route's
   inlining, which this frontend does not do. *)
let function_attrs_ok =
  Ir.attribute_kinds
    [ "noinline"; "optnone"; "nounwind"; "uwtable"; "alwaysinline"; "cold" ]

let value_attrs_ok = Ir.attribute_kinds [ "noundef"; "signext"; "zeroext" ]

(* A pointer that passes a struct by value or receives a struct result:
   its type attribute and the promises clang puts beside it, which hold of
   a copy or a result slot. *)
let struct_param_attrs_ok =
  Ir.attribute_kinds
    [ "byval"; "sret"; "align"; "noalias"; "dead_on_unwind"; "writable"; "nonnull";
      "dereferenceable"; "nocapture"; "readonly"; "writeonly"; "noundef" ]

let param_attrs_ok fn i = if Ir.struct_param fn i <> None then struct_param_attrs_ok else value_attrs_ok

(* A modelled external may also be declared [noreturn]; its meaning is given
   by the translation, and [abort], [exit] and [__assert_fail] are.  It may
   be [nocallback] too, which clang derives from glibc's [__leaf__] on
   [abort] and [exit] in <stdlib.h>: the promise that the call does not
   re-enter the module, which a modelled external never does. *)
let modelled_attrs = [ "noreturn"; "nocallback" ]

let modelled_function_attrs_ok =
  Ir.attribute_kinds modelled_attrs @ function_attrs_ok

(* The promises glibc's [__attribute__((const))] and [pure] declarations
   make clang put on a function and its calls: that the call returns, frees
   and synchronises with nothing, and accesses no memory, or only what
   [memory(...)] allows.  The meaning the translation gives a model that
   returns and reads or writes none of the program's variables keeps every
   one of them, so accepting them there drops no undefined behaviour.  A
   model that does not return ([Program_end], [Reach_error]) or that changes
   the program's state is refused them. *)
let returning_model_attrs = Ir.attribute_kinds [ "willreturn"; "memory"; "nofree"; "nosync" ]

let returns_touching_no_memory (modelled : Scope.modelled) =
  match modelled with
  | Nondet | Output | Rand | Time | No_effect | Descriptor | Status | Byte_swap _ | Inet_addr | Imaxabs -> true
  | Reach_error | Program_end | Assume | Cut | Uninit_marker | Region_arbitrary _ | Wrap _ | Free -> false

let check_attrs ~what ~where ~allowed attrs =
  Array.iter
    (fun attr ->
      let kind = Ir.attr_kind_code attr in
      if kind >= 0 && not (List.mem kind allowed) then
        where
          (Printf.sprintf "%s has the attribute %s" what (Ir.attribute_name kind)))
    attrs

let check_function_attrs ~fn_attrs ~fail fn =
  let ty = Ir.global_value_type fn in
  check_attrs ~what:"the function" ~where:fail ~allowed:fn_attrs
    (Ir.function_attrs fn Function);
  check_attrs ~what:"its result" ~where:fail ~allowed:value_attrs_ok
    (Ir.function_attrs fn Return);
  Array.iteri
    (fun i _ ->
      check_attrs
        ~what:(Printf.sprintf "parameter %d" (i + 1))
        ~where:fail ~allowed:(param_attrs_ok fn i)
        (Ir.function_attrs fn (Param i)))
    (Ir.param_types ty)

let check_call_site_attrs ?callee ?(modelled = false) ?(extra = []) call =
  let fail reason = unknown call "%s" reason in
  check_attrs ~what:"the call" ~where:fail
    ~allowed:(Ir.attribute_kinds ((if modelled then modelled_attrs else [ "noreturn" ]) @ [ "nounwind"; "cold" ]) @ extra)
    (Ir.call_site_attrs call Function);
  check_attrs ~what:"the call's result" ~where:fail ~allowed:value_attrs_ok
    (Ir.call_site_attrs call Return);
  for i = 0 to Llvm.num_arg_operands call - 1 do
    check_attrs
      ~what:(Printf.sprintf "argument %d" (i + 1))
      ~where:fail
      ~allowed:(match callee with Some fn -> param_attrs_ok fn i | None -> value_attrs_ok)
      (Ir.call_site_attrs call (Param i))
  done

(* Metadata that states something about a value or a loop the translation
   would otherwise not know, and that is UB when false.  Ignoring it would
   drop that UB, so it is rejected until its meaning is part of the
   translation.  Every other kind (debug locations, loop locations, hints)
   is accepted. *)
let assuming_metadata =
  [ "range"; "nonnull"; "noundef"; "align"; "dereferenceable";
    "dereferenceable_or_null"; "tbaa"; "tbaa.struct"; "alias.scope";
    "noalias"; "invariant.load"; "invariant.group"; "llvm.access.group";
    "llvm.mem.parallel_loop_access" ]

let loop_must_progress loop =
  Array.exists
    (fun property ->
      match Ir.get_mdnode_operands property with
      | [||] -> false
      | ops -> Llvm.get_mdstring ops.(0) = Some "llvm.loop.mustprogress")
    (Ir.get_mdnode_operands loop)

let check_metadata ctx instr =
  if Llvm.has_metadata instr then (
    List.iter
      (fun name ->
        if Llvm.metadata instr (Llvm.mdkind_id ctx name) <> None then
          unknown instr "!%s metadata" name)
      assuming_metadata;
    match Llvm.metadata instr (Llvm.mdkind_id ctx "llvm.loop") with
    | Some loop when loop_must_progress loop ->
        unknown instr
          "llvm.loop.mustprogress (the loop may be assumed to terminate)"
    | _ -> ())

(* The intrinsics the translation gives a meaning, by the prefix of their
   overloaded names (llvm.memcpy.p0.p0.i64, llvm.abs.i32, ...). *)
let intrinsic_prefixes =
  [ "llvm.dbg."; "llvm.lifetime.start."; "llvm.lifetime.end.";
    "llvm.memset.p"; "llvm.memcpy.p"; "llvm.memmove.p"; "llvm.abs.i";
    "llvm.sadd.with.overflow."; "llvm.uadd.with.overflow.";
    "llvm.ssub.with.overflow."; "llvm.usub.with.overflow.";
    "llvm.smul.with.overflow."; "llvm.umul.with.overflow."; "llvm.ctpop.";
    "llvm.ctlz."; "llvm.cttz."; "llvm.bswap."; "llvm.stacksave";
    "llvm.stackrestore"; "llvm.assume"; "llvm.trap"; "llvm.ubsantrap";
    "llvm.experimental.noalias.scope.decl" ]

let intrinsic_ok name =
  List.exists (fun prefix -> String.starts_with ~prefix name) intrinsic_prefixes

let is_debug_intrinsic fn =
  String.starts_with ~prefix:"llvm.dbg." (Llvm.value_name fn)

let is_overflow_intrinsic fn =
  let name = Llvm.value_name fn in
  List.exists
    (fun op -> String.starts_with ~prefix:("llvm." ^ op ^ ".with.overflow.") name)
    [ "sadd"; "uadd"; "ssub"; "usub"; "smul"; "umul" ]

(* A global variable reached from translated code must be defined here, hold
   a value of a memory type, and be initialised without [undef]. *)
let rec initializer_ok c =
  match Llvm.classify_value c with
  (* padding (unions, packed layouts) is undef; read as arbitrary values *)
  | UndefValue -> true
  | ConstantInt | ConstantAggregateZero | ConstantDataArray | NullValue
  | PoisonValue ->
      true
  | ConstantArray | ConstantStruct ->
      let ok = ref true in
      for i = 0 to Llvm.num_operands c - 1 do
        if not (initializer_ok (Llvm.operand c i)) then ok := false
      done;
      !ok
  | _ -> false

let check_global instr g =
  let name = Llvm.value_name g in
  if Llvm.is_declaration g then
    unknown instr "the global variable %s is declared but not defined" name;
  if Llvm.is_thread_local g then
    unknown instr "the global variable %s is thread-local" name;
  if not (Ir.is_memory_type (Ir.global_value_type g)) then
    unknown instr "the global variable %s has the type %s" name
      (Llvm.string_of_lltype (Ir.global_value_type g));
  match Llvm.global_initializer g with
  | Some init when not (initializer_ok init) ->
      unknown instr "the initialiser of %s is not a plain constant" name
  | _ -> ()

(* An operand that is not an instruction: what constants may appear. *)
let rec check_operand instr v =
  match Llvm.classify_value v with
  | Instruction _ | BasicBlock | MDNode | MDString | ConstantInt | PoisonValue
  (* an undef operand is a fresh arbitrary value at each use *)
  | UndefValue ->
      ()
  | Argument ->
      if not (Ir.is_integer (Llvm.type_of v)) then
        unknown instr "a parameter of type %s"
          (Llvm.string_of_lltype (Llvm.type_of v))
  | NullValue | ConstantPointerNull -> unknown instr "a null pointer"
  | GlobalVariable -> check_global instr v
  | Function ->
      unknown instr "the function %s used as a value" (Llvm.value_name v)
  | GlobalAlias -> unknown instr "a use of the alias %s" (Llvm.value_name v)
  | GlobalIFunc -> unknown instr "a use of the ifunc %s" (Llvm.value_name v)
  | InlineAsm -> unknown instr "inline assembly"
  | BlockAddress -> unknown instr "a block address"
  | ConstantFP -> unknown instr "a floating-point constant"
  | ConstantVector | ConstantDataVector -> unknown instr "a vector constant"
  | ConstantArray | ConstantStruct | ConstantDataArray | ConstantAggregateZero
    ->
      unknown instr "an aggregate value"
  | ConstantExpr -> (
      match Llvm.constexpr_opcode v with
      | GetElementPtr | Add | Sub | Mul | Xor | Trunc ->
          for i = 0 to Llvm.num_operands v - 1 do
            check_operand instr (Llvm.operand v i)
          done
      | op -> unknown instr "a constant %s expression" (Ir.opcode_name op))

(* The base of an address: an object the translation tracks (a local or
   global variable), possibly through getelementptr. *)
let rec check_address instr p =
  match Llvm.classify_value p with
  | Instruction Alloca -> ()
  | Argument when Ir.struct_param_of_arg p <> None -> ()
  | GlobalVariable -> check_global instr p
  | Instruction GetElementPtr -> check_address instr (Llvm.operand p 0)
  | ConstantExpr when Llvm.constexpr_opcode p = GetElementPtr ->
      check_address instr (Llvm.operand p 0)
  | _ -> unknown instr "an access through a pointer whose target is not tracked"

let check_memory_type instr what ty =
  if not (Ir.is_memory_type ty) then
    unknown instr "%s of type %s" what (Llvm.string_of_lltype ty)

let check_result_type instr =
  let ty = Llvm.type_of instr in
  match Llvm.classify_type ty with
  | Integer | Void -> ()
  | Pointer -> (
      match Llvm.instr_opcode instr with
      | Alloca | GetElementPtr -> ()
      | Call
        when String.starts_with ~prefix:"llvm.stacksave"
               (Llvm.value_name (Ir.callee instr)) ->
          ()
      | _ -> unknown instr "a pointer value")
  | Struct
    when Llvm.instr_opcode instr = Call
         && is_overflow_intrinsic (Ir.callee instr) ->
      ()
  (* a struct returned in registers, and the load and store clang copies it
     with (a struct value is the tuple of its elements) *)
  | Struct
    when Ir.is_memory_type ty
         && (Llvm.instr_opcode instr = Load
            || Llvm.instr_opcode instr = InsertValue
            || Llvm.instr_opcode instr = ExtractValue
            || (Llvm.instr_opcode instr = Call
               && match Scope.classify_callee instr with Defined _ -> true | _ -> false)) ->
      ()
  | _ -> unknown instr "a value of type %s" (Llvm.string_of_lltype ty)

(* The text of a constant string a pointer designates: a constant global
   holding an [i8] array, or a getelementptr to its start. *)
let constant_string v =
  let rec base v =
    match Llvm.classify_value v with
    | GlobalVariable -> Some v
    | ConstantExpr when Llvm.constexpr_opcode v = GetElementPtr ->
        let zero i = Llvm.int64_of_const (Llvm.operand v i) = Some 0L in
        if List.for_all zero (List.init (Llvm.num_operands v - 1) (fun i -> i + 1)) then base (Llvm.operand v 0) else None
    | _ -> None
  in
  match base v with
  | Some g when Llvm.is_global_constant g -> Option.bind (Llvm.global_initializer g) Llvm.string_of_const
  | _ -> None

(* Whether a printf format has a %n conversion: after a [%], the flags,
   width, precision and length characters are skipped and the conversion
   character read; [%%] is a literal [%]. *)
let writes_memory text =
  let n = String.length text in
  let rec scan i =
    if i >= n then false
    else if text.[i] <> '%' then scan (i + 1)
    else
      let rec conv j =
        if j >= n then false
        else
          match text.[j] with
          | '-' | '+' | ' ' | '#' | '0' .. '9' | '.' | '*' | 'h' | 'l' | 'j' | 'z' | 't' | 'L' | '\'' -> conv (j + 1)
          | 'n' -> true
          | _ -> scan (j + 1)
      in
      conv (i + 1)
  in
  scan 0

let check_call instr =
  (match Ir.tail_call_kind instr with
  | Must_tail -> unknown instr "a musttail call"
  | No_marker | Tail | No_tail -> ());
  match Scope.classify_callee instr with
  | Intrinsic fn ->
      let name = Llvm.value_name fn in
      if not (intrinsic_ok name) then unknown instr "the intrinsic %s" name;
      (* A debug intrinsic's operands are metadata; the others' attributes
         (alignment of a memcpy's pointers, ...) promise nothing the
         translation could break, since it has no addresses. *)
      if not (is_debug_intrinsic fn) then
        for i = 0 to Llvm.num_arg_operands instr - 1 do
          let arg = Llvm.operand instr i in
          if not (Ir.is_pointer (Llvm.type_of arg)) then check_operand instr arg
        done
  | Modelled (modelled, fn) ->
      let extra = if returns_touching_no_memory modelled then returning_model_attrs else [] in
      check_call_site_attrs ~modelled:true ~extra instr;
      check_function_attrs ~fn_attrs:(modelled_function_attrs_ok @ extra)
        ~fail:(fun reason -> unknown instr "%s: %s" (Llvm.value_name fn) reason)
        fn;
      for i = 0 to Llvm.num_arg_operands instr - 1 do
        let arg = Llvm.operand instr i in
        (* [__assert_fail] takes the assertion text, the file and the
           function name as pointers to strings, [free] the block to
           release, [time] and [accept] the null pointer (checked by
           [Scope.check_modelled]), and [inet_addr] a constant string read
           at translation time; nothing reads them from the program's
           memory. *)
        if modelled = Scope.Output && Ir.is_pointer (Llvm.type_of arg) then
          match constant_string arg with
          | None -> unknown instr "%s: a pointer argument that is not a constant string" (Llvm.value_name fn)
          | Some text when i = 0 && writes_memory text ->
              unknown instr "%s: a format with %%n, which writes memory" (Llvm.value_name fn)
          | Some _ -> ()
        else if
          not
            (List.mem modelled [ Scope.Program_end; Scope.Free; Scope.Time; Scope.Descriptor; Scope.Inet_addr ]
            && Ir.is_pointer (Llvm.type_of arg))
        then check_operand instr arg
      done
  | Defined fn ->
      check_call_site_attrs ~callee:fn instr;
      for i = 0 to Llvm.num_arg_operands instr - 1 do
        let arg = Llvm.operand instr i in
        if Ir.is_pointer (Llvm.type_of arg) && Ir.struct_param fn i = None then
          unknown instr "a pointer passed to %s" (Llvm.value_name fn);
        check_operand instr arg
      done

let frees_only instr =
  let rec all_frees = function
    | None -> true
    | Some use ->
        let user = Llvm.user use in
        Llvm.classify_value user = Instruction Call
        && (match Scope.classify_callee user with Modelled (Scope.Free, _) -> true | _ -> false)
        && all_frees (Llvm.use_succ use)
  in
  all_frees (Llvm.use_begin instr)

let check_instr ctx instr =
  let op = Llvm.instr_opcode instr in
  let operands () =
    for i = 0 to Llvm.num_operands instr - 1 do
      check_operand instr (Llvm.operand instr i)
    done
  in
  check_metadata ctx instr;
  match op with
  | Ret | Br | Switch | Unreachable | Add | Sub | Mul | UDiv | SDiv | URem
  | SRem | Shl | LShr | AShr | And | Or | Xor | Trunc | ZExt | SExt | Select
  | PHI | Freeze | InsertValue ->
      check_result_type instr;
      operands ();
      (* Returning, selecting or merging a pointer is rejected through the
         result type, except for [ret], whose result type is void. *)
      if op = Ret && Llvm.num_operands instr = 1 then
        if Ir.is_pointer (Llvm.type_of (Llvm.operand instr 0)) then
          unknown instr "a pointer returned"
  | ICmp ->
      if not (Ir.is_integer (Llvm.type_of (Llvm.operand instr 0))) then
        unknown instr "a comparison of pointers";
      operands ()
  | Alloca ->
      check_memory_type instr "a local variable" (Ir.allocated_type instr);
      check_operand instr (Llvm.operand instr 0)
  (* A volatile access is read as an ordinary one: the program is
     single-threaded and nothing outside it writes its memory. *)
  | Load ->
      if Ir.is_atomic instr then unknown instr "an atomic load";
      check_result_type instr;
      check_address instr (Llvm.operand instr 0)
  | Store ->
      if Ir.is_atomic instr then unknown instr "an atomic store";
      let stored = Llvm.operand instr 0 in
      if not (Ir.is_integer (Llvm.type_of stored) || (Llvm.classify_type (Llvm.type_of stored) = Struct && Ir.is_memory_type (Llvm.type_of stored))) then
        unknown instr "a store of a value of type %s"
          (Llvm.string_of_lltype (Llvm.type_of stored));
      check_operand instr stored;
      check_address instr (Llvm.operand instr 1)
  | GetElementPtr ->
      check_memory_type instr "an access into a value"
        (Ir.gep_source_element_type instr);
      check_address instr (Llvm.operand instr 0);
      for i = 1 to Llvm.num_operands instr - 1 do
        check_operand instr (Llvm.operand instr i)
      done
  | Call ->
      check_result_type instr;
      check_call instr
  (* Ptr2Arr passes a block to [free] as its index, which clang converts to
     a pointer; nothing else may use the pointer, and the call reads nothing
     through it. *)
  | IntToPtr when frees_only instr -> operands ()
  | ExtractValue -> (
      let aggregate = Llvm.operand instr 0 in
      match Llvm.classify_value aggregate with
      | Instruction Call when is_overflow_intrinsic (Ir.callee aggregate) -> (
          match Ir.indices instr with
          | [| 0 |] | [| 1 |] -> ()
          | _ -> unknown instr "an extractvalue with other indices")
      | Instruction (Call | Load | InsertValue | ExtractValue) when Ir.is_memory_type (Llvm.type_of aggregate) ->
          check_result_type instr
      | _ -> unknown instr "an extractvalue from an aggregate value")
  | op -> unknown instr "the instruction %s" (Ir.opcode_name op)

let check_function ctx fn =
  let fail reason =
    Outcome.stop
      (Unknown (Printf.sprintf "%s: %s" (Llvm.value_name fn) reason))
  in
  let ty = Ir.global_value_type fn in
  if Llvm.is_var_arg ty then fail "a function with variable arguments";
  (match Llvm.classify_type (Llvm.return_type ty) with
  | Integer | Void -> ()
  | Struct when Ir.is_memory_type (Llvm.return_type ty) -> ()
  | _ ->
      fail
        (Printf.sprintf "returns %s"
           (Llvm.string_of_lltype (Llvm.return_type ty))));
  (* [main]'s parameters are unused (Scope.main_function), whatever their
     types. *)
  if Llvm.value_name fn <> "main" then
  Array.iteri
    (fun i param ->
      if not (Ir.is_integer param || Ir.struct_param fn i <> None) then
        fail
          (Printf.sprintf "parameter %d has the type %s" (i + 1)
             (Llvm.string_of_lltype param)))
    (Ir.param_types ty);
  (* a defined function may be noreturn (the new Ptr2Arr's __p2a_stop, which
     calls _Exit): a return from it is UB, which the translation writes *)
  check_function_attrs ~fn_attrs:(Ir.attribute_kinds [ "noreturn" ] @ function_attrs_ok) ~fail fn;
  Llvm.iter_blocks (Llvm.iter_instrs (check_instr ctx)) fn

let check llmodule =
  let ctx = Llvm.module_context llmodule in
  List.iter (check_function ctx) (Scope.reachable llmodule)
