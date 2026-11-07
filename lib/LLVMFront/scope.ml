(* The part of a module that is translated: the functions reachable from
   [main] through direct calls.  Code that is not reached is ignored whether
   or not it is supported.

   A call is direct when its callee operand is a function.  Calls to the
   modelled externals (the SV-COMP task functions, [abort], [exit], ...) end
   the walk: their meaning is given by the translation, and a body the module
   may have for one of them (tasks define [reach_error]; the new Ptr2Arr
   defines [__p2a_arbitrary_<array>], [__p2a_wrap_kN] and
   [__ptr2arr_assume]) is not followed.  The exceptions are a
   [__VERIFIER_nondet_T], a [__VERIFIER_assume], a [free], a modelled
   library function ([rand], [htons], ...) and a renamed input error event
   the module defines: the program's own definition gives their meaning (tasks define a
   string generator under the nondet prefix and an assume that exits), so
   they are followed and translated as any defined function. *)

type modelled =
  | Nondet  (** [__VERIFIER_nondet_T] for an integer [T]: a fresh value. *)
  | Reach_error
      (** the error event of unreach-call: [reach_error], and
          [__VERIFIER_error], its name in older SV-COMP tasks *)
  | Program_end
      (** [abort], [exit], [_Exit], [__assert_fail], and the input's error
          event the new Ptr2Arr renames, declared only *)
  | Assume  (** [__VERIFIER_assume] *)
  | Uninit_marker  (** the frontend's own marker for an uninitialised value *)
  | Output
      (** [printf], [puts], [putchar]: no effect on the program's state, an
          arbitrary [int] result *)
  | Region_arbitrary of string
      (** [__p2a_arbitrary_<global>] from the new Ptr2Arr: the global named
          after the prefix gets arbitrary contents where it is called *)
  | Wrap of bool * int
      (** [__p2a_wrap_sN] (signed) or [__p2a_wrap_uN] from the new Ptr2Arr's
          --wrap-integers, and [__p2a_wrapnn_uN], its --integers=auto name
          for an unsigned one whose argument it has shown non-negative: the
          identity at the N-bit type in C, which the new Ptr2Arr puts around
          an expression whose C value wraps around.  Its definition is the
          identity, so it is read by its name: the reduction into the type's
          range where integers are unbounded *)
  | Cut
      (** [__ptr2arr_assume] from the new Ptr2Arr's --assume-safety: an
          execution whose argument is 0 ends there (its definition calls
          [exit(0)]) *)
  | Rand
      (** [rand]: a fresh value in [0, RAND_MAX], glibc's 2^31 - 1 (the
          values a sequence of calls returns are not related: the seed,
          set by [srand] from the time, is unknown to the verifier) *)
  | Time
      (** [time] with a null argument: a fresh value of its type (the time
          is unknown); with any other argument it would write through it,
          and is refused *)
  | No_effect  (** [srand]: no effect on the program's state *)
  | Descriptor
      (** [socket], and [accept] with null address arguments: a fresh value
          >= -1 read as signed.  POSIX returns -1 on failure and otherwise
          the lowest descriptor not open, which depends on the environment,
          so every non-negative value is allowed (an over-approximation);
          [accept] is read as returning, although it may wait for a
          connection forever *)
  | Status
      (** [listen], [close]: a fresh value that is 0 or -1, the only
          results POSIX gives them *)
  | Byte_swap of int
      (** [htons]/[ntohs] (16) and [htonl]/[ntohl] (32): the argument's
          bytes reversed, read as unsigned, which is the conversion between
          host order on x86 (little-endian) and network order (big-endian) *)
  | Inet_addr
      (** [inet_addr] applied to a constant string holding a decimal dotted
          quad a.b.c.d: the constant a + b 2^8 + c 2^16 + d 2^24, the
          network-order address read as a little-endian word *)
  | Imaxabs
      (** [imaxabs]: as [llvm.abs.i64] with poison at the minimum, whose
          absolute value C leaves undefined *)
  | Free
      (** [free], declared only, of a pointer or an index: no effect on the state the translation
          keeps (Ptr2Arr has turned the heap into arrays, and freeing does
          not change their contents).  The UB of freeing a block twice, or
          one not allocated, is not seen: such an execution goes on as if
          the call did nothing *)

type callee =
  | Defined of Llvm.llvalue
  | Modelled of modelled * Llvm.llvalue
  | Intrinsic of Llvm.llvalue

let uninit_marker_prefix = "__llvmfront_uninit_"

let nondet_prefix = "__VERIFIER_nondet_"
let region_arbitrary_prefix = "__p2a_arbitrary_"
let wrap_prefix = "__p2a_wrap_"

let wrap_nonneg_prefix = "__p2a_wrapnn_u"

let suffix ~prefix name =
  let k = String.length prefix in
  String.sub name k (String.length name - k)

(* [__p2a_wrap_] followed by [u] or [s] and a positive width in decimal, or
   [__p2a_wrapnn_u] and a width: the name --integers=auto gives a reduction
   whose argument it has shown non-negative, read as [__p2a_wrap_uN]. *)
let wrap_of_name name =
  let rest =
    if String.starts_with ~prefix:wrap_nonneg_prefix name then "u" ^ suffix ~prefix:wrap_nonneg_prefix name
    else suffix ~prefix:wrap_prefix name
  in
  let n = String.length rest in
  if n < 2 then None
  else
    let digits = String.sub rest 1 (n - 1) in
    match (rest.[0], int_of_string_opt digits) with
    | ('u' | 's'), Some w when w > 0 && String.for_all (fun c -> c >= '0' && c <= '9') digits ->
        Some (Wrap (rest.[0] = 's', w))
    | _ -> None

(* The new Ptr2Arr's name for the input's own error event, which it renames
   where reach_error() is its violation marker: __p2a_input_reach_error or
   __p2a_input___VERIFIER_error, possibly followed by _N to avoid a name the
   input uses.  Declared only, a call of it ends the execution: it is the
   input's error event, which the property at hand does not report. *)
let is_input_error_event name =
  List.exists
    (fun base ->
      name = base
      || String.starts_with ~prefix:(base ^ "_") name
         &&
         let rest = suffix ~prefix:(base ^ "_") name in
         rest <> "" && String.for_all (fun c -> c >= '0' && c <= '9') rest)
    [ "__p2a_input_reach_error"; "__p2a_input___VERIFIER_error" ]

(* Whether the C type a [__VERIFIER_nondet_T] is named after is signed; [None]
   when [T] names no integer type ([String], [float], a pointer type). *)
let nondet_signedness name =
  match suffix ~prefix:nondet_prefix name with
  | "char" | "schar" | "short" | "int" | "long" | "longlong" | "s8" | "s16"
  | "s32" | "s64" ->
      Some true
  | "uchar" | "ushort" | "uint" | "unsigned" | "ulong" | "ulonglong" | "u8"
  | "u16" | "u32" | "u64" | "size_t" | "bool" | "_Bool" ->
      Some false
  | _ -> None

(* The width of the C type a [__VERIFIER_nondet_T] is named after, [long],
   [ulong] and [size_t] being as wide as a pointer; [None] when [T] names no
   integer type. *)
let nondet_bits ~pointer_bits name =
  match suffix ~prefix:nondet_prefix name with
  | "bool" | "_Bool" -> Some 1
  | "char" | "schar" | "uchar" | "s8" | "u8" -> Some 8
  | "short" | "ushort" | "s16" | "u16" -> Some 16
  | "int" | "uint" | "unsigned" | "s32" | "u32" -> Some 32
  | "longlong" | "ulonglong" | "s64" | "u64" -> Some 64
  | "long" | "ulong" | "size_t" -> Some pointer_bits
  | _ -> None

let modelled_of_name name =
  if String.starts_with ~prefix:nondet_prefix name then Some Nondet
  else if String.starts_with ~prefix:uninit_marker_prefix name then
    Some Uninit_marker
  else if String.starts_with ~prefix:region_arbitrary_prefix name then
    Some (Region_arbitrary (suffix ~prefix:region_arbitrary_prefix name))
  else if String.starts_with ~prefix:wrap_prefix name || String.starts_with ~prefix:wrap_nonneg_prefix name
  then wrap_of_name name
  else
    match name with
    | "reach_error" | "__VERIFIER_error" -> Some Reach_error
    | "abort" | "exit" | "_Exit" | "__assert_fail" -> Some Program_end
    | _ when is_input_error_event name -> Some Program_end
    | "free" -> Some Free
    | "__VERIFIER_assume" -> Some Assume
    | "__ptr2arr_assume" -> Some Cut
    | "printf" | "puts" | "putchar" -> Some Output
    | "rand" -> Some Rand
    | "time" -> Some Time
    | "srand" -> Some No_effect
    | "socket" | "accept" -> Some Descriptor
    | "listen" | "close" -> Some Status
    | "htons" | "ntohs" -> Some (Byte_swap 16)
    | "htonl" | "ntohl" -> Some (Byte_swap 32)
    | "inet_addr" -> Some Inet_addr
    | "imaxabs" -> Some Imaxabs
    | _ -> None

(* Where an instruction is, for a message: its function and, when it has a
   debug location, its C line. *)
let location instr =
  let fn = Llvm.value_name (Llvm.block_parent (Llvm.instr_parent instr)) in
  match Ir.debug_line instr with
  | 0 -> fn
  | line -> Printf.sprintf "%s, line %d" fn line

let unknown instr fmt =
  Printf.ksprintf
    (fun reason ->
      Outcome.stop (Unknown (Printf.sprintf "%s: %s" (location instr) reason)))
    fmt

(* A call may be written with a type that differs from its callee's only in
   the varargs flag: clang 19 on x86-64 calls a function defined without a
   prototype, such as `void reach_error() {...}`, through a varargs type.
   Such a call passes the same arguments as a direct call would (C17
   6.5.2.2p6, and the x86-64 calling convention passes them alike). *)
let compatible_call_type call fn =
  let call_ty = Ir.called_function_type call in
  let fn_ty = Ir.global_value_type fn in
  call_ty = fn_ty
  || Llvm.return_type call_ty = Llvm.return_type fn_ty
     && Ir.param_types call_ty = Ir.param_types fn_ty

(* The null pointer as a modelled external receives it: the constant null
   pointer, or the index 0 a Ptr2Arr makes of it. *)
let is_null_argument arg =
  Llvm.is_null arg
  ||
  match Llvm.classify_value arg with
  | ConstantInt -> Llvm.int64_of_const arg = Some 0L
  | _ -> false

(* The global variable a pointer operand points to the start of: the global
   itself, or a getelementptr of it whose indices are all 0. *)
let rec pointed_global v =
  match Llvm.classify_value v with
  | GlobalVariable -> Some v
  | ConstantExpr when Llvm.constexpr_opcode v = GetElementPtr ->
      let zero i =
        let o = Llvm.operand v i in
        Llvm.classify_value o = ConstantInt && Llvm.int64_of_const o = Some 0L
      in
      let rec all_zero i = i >= Llvm.num_operands v || (zero i && all_zero (i + 1)) in
      if all_zero 1 then pointed_global (Llvm.operand v 0) else None
  | _ -> None

(* The value of [inet_addr] on a decimal dotted quad "a.b.c.d", each part
   in [0, 255] written with decimal digits only, as a little-endian word:
   a + b 2^8 + c 2^16 + d 2^24.  [inet_addr] also reads hexadecimal, octal
   and shortened forms ("a.b"); those give None, as does anything else. *)
let dotted_quad text =
  let part p =
    let n = String.length p in
    if n = 0 || n > 3 || (not (String.for_all (fun c -> c >= '0' && c <= '9') p)) || (n > 1 && p.[0] = '0')
    then None
    else
      let x = int_of_string p in
      if x <= 255 then Some x else None
  in
  match String.split_on_char '.' text with
  | [ a; b; c; d ] -> (
      match (part a, part b, part c, part d) with
      | Some a, Some b, Some c, Some d -> Some (Int64.of_int (a + (b lsl 8) + (c lsl 16) + (d lsl 24)))
      | _ -> None)
  | _ -> None

(* The string a constant global of characters holds, without its
   terminating NUL: None for anything else (a writable global, whose
   contents a program may change, included). *)
let constant_string g =
  if Llvm.is_declaration g || not (Llvm.is_global_constant g) then None
  else
    match Llvm.global_initializer g with
    | Some init when Llvm.classify_value init = ConstantDataArray -> (
        match Llvm.string_of_const init with
        | Some s -> ( match String.index_opt s '\000' with Some k -> Some (String.sub s 0 k) | None -> None)
        | None -> None)
    | _ -> None

let inet_addr_value call =
  match pointed_global (Llvm.operand call 0) with
  | Some g -> Option.bind (constant_string g) dotted_quad
  | None -> None

let check_modelled call fn modelled =
  let name = Llvm.value_name fn in
  let fn_ty = Ir.global_value_type fn in
  let returns_int = Ir.is_integer (Llvm.return_type fn_ty) in
  let params = Ir.param_types fn_ty in
  match modelled with
  | Nondet ->
      if not (returns_int && params = [||]) then
        unknown call "%s does not return an integer from no arguments" name
  | Assume | Cut ->
      if not (Array.length params = 1 && Ir.is_integer params.(0)) then
        unknown call "%s does not take one integer" name
  | Wrap (_, n) ->
      (* the call converts its argument to the N-bit type, so the parameter
         and the result must be that type *)
      let is_n ty = Ir.is_integer ty && Llvm.integer_bitwidth ty = n in
      if not (is_n (Llvm.return_type fn_ty) && Array.length params = 1 && is_n params.(0)) then
        unknown call "%s does not map an i%d to an i%d" name n n
  | Output ->
      if not (Llvm.is_declaration fn) then unknown call "%s is defined in the module" name;
      if not (returns_int && Llvm.integer_bitwidth (Llvm.return_type fn_ty) = 32) then
        unknown call "%s does not return int" name
  | Region_arbitrary global -> (
      if not (Llvm.classify_type (Llvm.return_type fn_ty) = Void && params = [||]) then
        unknown call "%s does not take and return nothing" name;
      match Llvm.lookup_global global (Llvm.global_parent fn) with
      | Some g when not (Llvm.is_declaration g) -> ()
      | _ -> unknown call "%s names no global variable defined in the module" name)
  | Rand ->
      if not (returns_int && params = [||]) then
        unknown call "%s does not return an integer from no arguments" name
  | Time ->
      if not (returns_int && Array.length params = 1) then
        unknown call "%s does not return an integer from one argument" name;
      if not (is_null_argument (Llvm.operand call 0)) then
        unknown call "%s with an argument other than NULL" name
  | No_effect ->
      if not (Llvm.classify_type (Llvm.return_type fn_ty) = Void && Array.for_all Ir.is_integer params) then
        unknown call "%s does not take integers and return nothing" name
  | Descriptor | Status | Byte_swap _ | Inet_addr | Imaxabs ->
      (* glibc's declarations on x86-64 and i386 *)
      let is_bits n ty = Ir.is_integer ty && Llvm.integer_bitwidth ty = n in
      let ints n k = Array.length params = k && Array.for_all (is_bits n) params in
      let result n = is_bits n (Llvm.return_type fn_ty) in
      let fits, shape =
        match (name, modelled) with
        | "socket", _ -> (result 32 && ints 32 3, "int (int, int, int)")
        | "listen", _ -> (result 32 && ints 32 2, "int (int, int)")
        | "close", _ -> (result 32 && ints 32 1, "int (int)")
        | "accept", _ ->
            (* the two address arguments are pointers, or the indices a
               Ptr2Arr makes of pointers *)
            ( result 32
              && Array.length params = 3
              && is_bits 32 params.(0)
              && Array.for_all (fun ty -> Ir.is_pointer ty || Ir.is_integer ty) [| params.(1); params.(2) |],
              "int (int, struct sockaddr *, socklen_t *)" )
        | _, Byte_swap n -> (result n && ints n 1, Printf.sprintf "uint%d_t (uint%d_t)" n n)
        | _, Inet_addr -> (result 32 && Array.length params = 1 && Ir.is_pointer params.(0), "in_addr_t (const char *)")
        | _, Imaxabs -> (result 64 && ints 64 1, "intmax_t (intmax_t)")
        | _ -> (false, "")
      in
      if not fits then unknown call "%s is not declared as %s" name shape;
      if name = "accept" && not (is_null_argument (Llvm.operand call 1) && is_null_argument (Llvm.operand call 2))
      then unknown call "%s with an address argument other than NULL" name;
      if modelled = Inet_addr && inet_addr_value call = None then
        unknown call "%s of anything but a constant decimal dotted quad" name
  | Free ->
      (* one pointer, as <stdlib.h> declares it, or one integer: the old
         Ptr2Arr's SemanticAugmentor declares free(long long), since the
         pointer it frees has become an index *)
      if
        not
          (Llvm.classify_type (Llvm.return_type fn_ty) = Void
          && Array.length params = 1
          && (Ir.is_pointer params.(0) || Ir.is_integer params.(0)))
      then unknown call "%s does not take one pointer or integer and return nothing" name
  | Reach_error | Program_end | Uninit_marker -> ()

let classify_callee call =
  let target = Ir.callee call in
  match Llvm.classify_value target with
  | Function ->
      let name = Llvm.value_name target in
      let checked_type callee =
        if not (compatible_call_type call target) then
          unknown call "call to %s with a type other than its own" name;
        callee
      in
      if Llvm.is_intrinsic target then checked_type (Intrinsic target)
      else (
        match modelled_of_name name with
        | Some
            ( Nondet | Assume | Free | Rand | Time | No_effect | Descriptor | Status | Byte_swap _ | Inet_addr
            | Imaxabs )
          when not (Llvm.is_declaration target) ->
            (* the program's own definition is its meaning *)
            checked_type (Defined target)
        | Some Program_end when is_input_error_event name && not (Llvm.is_declaration target) ->
            (* the input's own definition of its error event *)
            checked_type (Defined target)
        | Some modelled ->
            check_modelled call target modelled;
            checked_type (Modelled (modelled, target))
        | None when Llvm.is_declaration target -> (
            (* Reported before the type: a call to an undeclared function
               gets a guessed type, which is rarely the right one. *)
            match name with
            | "malloc" | "calloc" | "realloc" ->
                unknown call
                  "call to %s (Ptr2Arr is expected to have turned the heap \
                   into arrays)"
                  name
            | _ -> unknown call "call to the external function %s" name)
        | None ->
            if
              String.starts_with ~prefix:"__VERIFIER_" name
              && name <> "__VERIFIER_assert"
            then unknown call "%s is defined in the module" name;
            checked_type (Defined target))
  | GlobalAlias -> unknown call "call through an alias"
  | GlobalIFunc -> unknown call "call through an ifunc"
  | InlineAsm -> unknown call "inline assembly"
  | _ -> unknown call "indirect call (through a function pointer)"

let main_function llmodule =
  match Llvm.lookup_function "main" llmodule with
  | None -> Outcome.stop (Input_error "the module has no main function")
  | Some main when Llvm.is_declaration main ->
      Outcome.stop (Input_error "main is declared but not defined")
  | Some main ->
      let ty = Ir.global_value_type main in
      let return = Llvm.return_type ty in
      (* `void main(void)`, which some tasks declare: its return ends the
         program as `int main` does, and the exit status is read by no
         property *)
      if not ((Ir.is_integer return && Llvm.integer_bitwidth return = 32) || Llvm.classify_type return = Void) then
        Outcome.stop (Unknown "main: it returns neither int nor void");
      (* `int main(int argc, char *argv[])`: argc may be read, and is then an
         arbitrary nonnegative value; reading argv needs a C-level contract
         for its strings, so it is refused.  After
         mem2reg the slots clang copies them into are gone, so an unused
         parameter has no use left. *)
      Array.iteri
        (fun i param ->
          if Llvm.use_begin param <> None && not (i = 0 && Ir.is_integer (Llvm.type_of param)) then
            Outcome.stop
              (Unknown
                 (if i = 1 then "main: argv is used" else Printf.sprintf "main: its parameter %d is used" (i + 1))))
        (Ir.params main);
      main

let fold_calls f acc fn =
  Llvm.fold_left_blocks
    (fun acc block ->
      Llvm.fold_left_instrs
        (fun acc instr ->
          match Llvm.instr_opcode instr with
          | Call -> f acc instr
          | _ -> acc)
        acc block)
    acc fn

(* The defined functions reachable from [main], [main] first, each once. *)
let reachable llmodule =
  let main = main_function llmodule in
  let seen = Hashtbl.create 16 in
  let rec visit order fn =
    if Hashtbl.mem seen fn then order
    else (
      Hashtbl.add seen fn ();
      fold_calls
        (fun order call ->
          match classify_callee call with
          | Defined callee -> visit order callee
          | Modelled _ | Intrinsic _ -> order)
        (fn :: order) fn)
  in
  List.rev (visit [] main)
