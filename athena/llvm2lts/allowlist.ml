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
   integer at a call boundary).  [alwaysinline] is the one llvm2lts adds
   before inlining. *)
let function_attrs_ok =
  Ir.attribute_kinds
    [ "noinline"; "optnone"; "nounwind"; "uwtable"; "alwaysinline"; "cold" ]

let value_attrs_ok = Ir.attribute_kinds [ "noundef"; "signext"; "zeroext" ]

(* A modelled external may also be declared [noreturn]; its meaning is given
   by the translation, and [abort], [exit] and [__assert_fail] are.  It may
   also be [nocallback] (clang's reading of glibc's [__leaf__], which
   preprocessed tasks carry on [__assert_fail], [abort] and [exit]): the
   promise that the callee never calls back into the module holds of every
   modelled external, whose meaning calls nothing of the program, so
   accepting it drops no undefined behaviour. *)
let modelled_function_attrs_ok =
  Ir.attribute_kinds [ "noreturn"; "nocallback" ] @ function_attrs_ok

(* The promises glibc's [__attribute__((const))] and [pure] declarations
   (htons, imaxabs, ...) make clang put on a function and its calls: that
   the call returns, frees and synchronises with nothing, and accesses no
   memory, or only what [memory(...)] allows.  The meaning the translation
   gives these externals keeps every one of them: it returns, and reads or
   writes none of the program's variables ([inet_addr]'s constant string is
   read at translation time).  So accepting them drops no undefined
   behaviour.  [Program_end] and [Reach_error] do not return, so a
   [willreturn] there would be false, and is refused. *)
let returning_model_attrs = Ir.attribute_kinds [ "willreturn"; "memory"; "nofree"; "nosync" ]

let returns_touching_no_memory (modelled : Scope.modelled) =
  match modelled with
  | Nondet | Output | Rand | Time | No_effect | Descriptor | Status | Byte_swap _
  | Inet_addr | Imaxabs ->
      true
  | Reach_error | Program_end | Assume | Cut | Uninit_marker | Region_arbitrary _
  | Wrap _ ->
      false

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
        ~where:fail ~allowed:value_attrs_ok
        (Ir.function_attrs fn (Param i)))
    (Ir.param_types ty)

(* The function attributes a call site may carry: those of a call to a
   defined function, and with [~modelled] also [nocallback], for the reason
   given at [modelled_function_attrs_ok].  A defined function's body is
   translated, so a call back from it would be translated as an ordinary call
   and the promise's undefined behaviour dropped.  [~extra] adds the kinds a
   particular model keeps ([returning_model_attrs]). *)
let check_call_site_attrs ?(modelled = false) ?(extra = []) call =
  let fail reason = unknown call "%s" reason in
  check_attrs ~what:"the call" ~where:fail
    ~allowed:
      (Ir.attribute_kinds
         ([ "noreturn"; "nounwind"; "cold" ] @ if modelled then [ "nocallback" ] else [])
      @ extra)
    (Ir.call_site_attrs call Function);
  check_attrs ~what:"the call's result" ~where:fail ~allowed:value_attrs_ok
    (Ir.call_site_attrs call Return);
  for i = 0 to Llvm.num_arg_operands call - 1 do
    check_attrs
      ~what:(Printf.sprintf "argument %d" (i + 1))
      ~where:fail ~allowed:value_attrs_ok
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
    "llvm.stackrestore"; "llvm.experimental.noalias.scope.decl" ]

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
  | UndefValue -> false
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
    ->
      ()
  | Argument ->
      if not (Ir.is_integer (Llvm.type_of v)) then
        unknown instr "a parameter of type %s"
          (Llvm.string_of_lltype (Llvm.type_of v))
  | UndefValue -> unknown instr "an undef operand"
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
  | _ -> unknown instr "a value of type %s" (Llvm.string_of_lltype ty)

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
      let extra =
        if returns_touching_no_memory modelled then returning_model_attrs else []
      in
      check_call_site_attrs ~modelled:true ~extra instr;
      check_function_attrs ~fn_attrs:(extra @ modelled_function_attrs_ok)
        ~fail:(fun reason -> unknown instr "%s: %s" (Llvm.value_name fn) reason)
        fn;
      for i = 0 to Llvm.num_arg_operands instr - 1 do
        let arg = Llvm.operand instr i in
        (* [__assert_fail] takes the assertion text, the file and the
           function name as pointers to strings, [printf] and [puts] a
           format or a text, [time] and [accept] the null pointer (checked
           by [Scope.check_modelled]), and [inet_addr] a constant string,
           which [Scope.inet_addr_value] reads at translation time; the
           translation reads none of them from the program's memory. *)
        let reads_no_pointer =
          match modelled with
          | Scope.Program_end | Scope.Output | Scope.Time | Scope.Descriptor
          | Scope.Inet_addr ->
              true
          | _ -> false
        in
        if not (reads_no_pointer && Ir.is_pointer (Llvm.type_of arg))
        then check_operand instr arg
      done
  | Defined fn ->
      check_call_site_attrs instr;
      for i = 0 to Llvm.num_arg_operands instr - 1 do
        let arg = Llvm.operand instr i in
        if Ir.is_pointer (Llvm.type_of arg) then
          unknown instr "a pointer passed to %s" (Llvm.value_name fn);
        check_operand instr arg
      done

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
  | PHI ->
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
      if not (Ir.is_integer (Llvm.type_of stored)) then
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
  | ExtractValue -> (
      let aggregate = Llvm.operand instr 0 in
      match Llvm.classify_value aggregate with
      | Instruction Call when is_overflow_intrinsic (Ir.callee aggregate) -> (
          match Ir.indices instr with
          | [| 0 |] | [| 1 |] -> ()
          | _ -> unknown instr "an extractvalue with other indices")
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
  | _ ->
      fail
        (Printf.sprintf "returns %s"
           (Llvm.string_of_lltype (Llvm.return_type ty))));
  (* [main]'s parameters are unused (Scope.main_function), whatever their
     types. *)
  if Llvm.value_name fn <> "main" then
  Array.iteri
    (fun i param ->
      if not (Ir.is_integer param) then
        fail
          (Printf.sprintf "parameter %d has the type %s" (i + 1)
             (Llvm.string_of_lltype param)))
    (Ir.param_types ty);
  check_function_attrs ~fn_attrs:function_attrs_ok ~fail fn;
  Llvm.iter_blocks (Llvm.iter_instrs (check_instr ctx)) fn

let check llmodule =
  let ctx = Llvm.module_context llmodule in
  List.iter (check_function ctx) (Scope.reachable llmodule)
