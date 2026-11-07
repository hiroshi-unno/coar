(* The part of a module that is translated: the functions reachable from
   [main] through direct calls.  Code that is not reached is ignored whether
   or not it is supported.

   A call is direct when its callee operand is a function.  Calls to the
   modelled externals (the SV-COMP task functions, [abort], [exit], ...) end
   the walk: their meaning is given by the translation, and a body the module
   may have for one of them (tasks define [reach_error]; Ptr2Arr defines the
   functions that carry a meaning to llvm2lts, [__p2a_arbitrary_<array>],
   [__p2a_wrap_kN] and [__p2a_wrapnn_uN]) is not followed, so none of them is
   inlined.  The exceptions are a __VERIFIER_nondet_T and __VERIFIER_assume
   the module defines: the program's own definition gives their meaning
   (tasks define a string generator and an assume that exits), so they are
   followed and inlined as any defined function. *)

type modelled =
  | Nondet  (** [__VERIFIER_nondet_T] for an integer [T]: a fresh value. *)
  | Reach_error
      (** the error event of unreach-call: [reach_error], and
          [__VERIFIER_error], its name in older SV-COMP tasks *)
  | Program_end
      (** [abort], [exit], [_Exit], [__assert_fail], and the input's error
          event Ptr2Arr renames, declared only *)
  | Assume  (** [__VERIFIER_assume] *)
  | Cut
      (** [__ptr2arr_assume] from Ptr2Arr's --assume-safety: an execution
          whose argument is 0 ends there, which Ptr2Arr defines as a call of
          [_Exit(0)]; read as a guard, an execution where it is 0 has no next
          step, which ends it as the call does *)
  | Uninit_marker  (** llvm2lts's own marker for an uninitialised value *)
  | Region_arbitrary of string
      (** [__p2a_arbitrary_<array>] from Ptr2Arr: the global array named
          after the prefix gets arbitrary contents *)
  | Wrap of bool * int * bool
      (** [__p2a_wrap_sN] (signed) or [__p2a_wrap_uN] from Ptr2Arr's
          --wrap-integers: the identity at the N-bit type in C, read as the
          reduction into that type's range where integers are unbounded.
          The last field is true for [__p2a_wrapnn_uN], the name Ptr2Arr's
          --integers=auto gives a reduction whose argument it has shown
          non-negative in the unbounded reading, so that one truncating
          remainder reduces it *)
  | Output  (** [printf], [puts], [putchar]: no effect on the state *)
  | Rand
      (** [rand]: a fresh value in [0, RAND_MAX], glibc's 2^31 - 1 (the
          values a sequence of calls returns are not related: the seed,
          set by [srand] from the time, is unknown to the verifier) *)
  | Time
      (** [time] with a null argument: a fresh value of its type (the time
          is unknown); with any other argument it would write through it,
          and is refused *)
  | No_effect  (** [srand]: no effect on the program's variables *)
  | Descriptor
      (** [socket], and [accept] with null address arguments: a fresh value
          >= -1 read as signed.  POSIX returns -1 on failure and otherwise
          the lowest descriptor not open, which depends on the environment,
          so every non-negative value is allowed (an over-approximation) *)
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
          network-order address read as a little-endian word
          ([inet_addr_value]) *)
  | Imaxabs
      (** [imaxabs]: as [llvm.abs.i64] with poison at the minimum, whose
          absolute value C leaves undefined *)

type callee =
  | Defined of Llvm.llvalue
  | Modelled of modelled * Llvm.llvalue
  | Intrinsic of Llvm.llvalue

let uninit_marker_prefix = "__llvm2lts_uninit_"
let region_arbitrary_prefix = "__p2a_arbitrary_"
let wrap_prefix = "__p2a_wrap_"
let wrap_nonneg_prefix = "__p2a_wrapnn_u"

let suffix ~prefix name =
  let k = String.length prefix in
  String.sub name k (String.length name - k)

(* [__p2a_wrap_] followed by [u] or [s] and a positive width in decimal,
   or [__p2a_wrapnn_u] followed by a width. *)
let wrap_of_name name =
  let nonneg = String.starts_with ~prefix:wrap_nonneg_prefix name in
  let rest =
    if nonneg then "u" ^ suffix ~prefix:wrap_nonneg_prefix name
    else suffix ~prefix:wrap_prefix name
  in
  let n = String.length rest in
  if n < 2 then None
  else
    let digits = String.sub rest 1 (n - 1) in
    match (rest.[0], int_of_string_opt digits) with
    | ('u' | 's'), Some w
      when w > 0 && String.for_all (fun c -> c >= '0' && c <= '9') digits ->
        Some (Wrap (rest.[0] = 's', w, nonneg))
    | _ -> None

(* Ptr2Arr's name for the input's own error event, renamed where
   reach_error() is its marker: __p2a_input_reach_error or
   __p2a_input___VERIFIER_error, possibly followed by _N to avoid a name the
   input uses. Declared only, a call of it ends the execution: it is the
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

let modelled_of_name name =
  if String.starts_with ~prefix:"__VERIFIER_nondet_" name then Some Nondet
  else if String.starts_with ~prefix:uninit_marker_prefix name then
    Some Uninit_marker
  else if String.starts_with ~prefix:region_arbitrary_prefix name then
    Some (Region_arbitrary (suffix ~prefix:region_arbitrary_prefix name))
  else if
    String.starts_with ~prefix:wrap_prefix name
    || String.starts_with ~prefix:wrap_nonneg_prefix name
  then wrap_of_name name
  else
    match name with
    | "reach_error" | "__VERIFIER_error" -> Some Reach_error
    | "abort" | "exit" | "_Exit" | "__assert_fail" -> Some Program_end
    | _ when is_input_error_event name -> Some Program_end
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
   pointer, or the index 0 Ptr2Arr makes of it. *)
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
    if n = 0 || n > 3 || not (String.for_all (fun c -> c >= '0' && c <= '9') p)
       || (n > 1 && p.[0] = '0')
    then None
    else
      let x = int_of_string p in
      if x <= 255 then Some x else None
  in
  match String.split_on_char '.' text with
  | [ a; b; c; d ] -> (
      match (part a, part b, part c, part d) with
      | Some a, Some b, Some c, Some d ->
          Some
            (Int64.of_int (a + (b lsl 8) + (c lsl 16) + (d lsl 24)))
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
        | Some s -> (
            match String.index_opt s '\000' with
            | Some k -> Some (String.sub s 0 k)
            | None -> None)
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
  | Region_arbitrary array -> (
      let returns_void =
        match Llvm.classify_type (Llvm.return_type fn_ty) with
        | Void -> true
        | _ -> false
      in
      if not (returns_void && params = [||]) then
        unknown call "%s does not take and return nothing" name;
      match Llvm.lookup_global array (Llvm.global_parent fn) with
      | Some g when not (Llvm.is_declaration g) -> ()
      | _ -> unknown call "%s names no global array defined in the module" name)
  | Wrap (_, n, _) ->
      (* The call converts its argument to the N-bit type, so the parameter
         and the result must be that type. *)
      let is_n ty = Ir.is_integer ty && Llvm.integer_bitwidth ty = n in
      if
        not
          (is_n (Llvm.return_type fn_ty)
          && Array.length params = 1
          && is_n params.(0))
      then unknown call "%s does not map an i%d to an i%d" name n n
  | Output ->
      if not (Llvm.is_declaration fn) then
        unknown call "%s is defined in the module" name;
      if not returns_int then unknown call "%s does not return an integer" name
  | Rand ->
      if not (returns_int && params = [||]) then
        unknown call "%s does not return an integer from no arguments" name
  | Time ->
      if not (returns_int && Array.length params = 1) then
        unknown call "%s does not return an integer from one argument" name;
      (* null: the constant null pointer, or the index 0 Ptr2Arr makes of it *)
      if not (is_null_argument (Llvm.operand call 0)) then
        unknown call "%s with an argument other than NULL" name
  | No_effect ->
      let returns_void =
        match Llvm.classify_type (Llvm.return_type fn_ty) with Void -> true | _ -> false
      in
      if not (returns_void && Array.for_all Ir.is_integer params) then
        unknown call "%s does not take integers and return nothing" name
  | Descriptor | Status | Byte_swap _ | Inet_addr | Imaxabs ->
      (* glibc's declarations on x86-64 and i386 *)
      let is_bits n ty = Ir.is_integer ty && Llvm.integer_bitwidth ty = n in
      let ints n k =
        Array.length params = k && Array.for_all (is_bits n) params
      in
      let result n = is_bits n (Llvm.return_type fn_ty) in
      let fits, shape =
        match (name, modelled) with
        | "socket", _ -> (result 32 && ints 32 3, "int (int, int, int)")
        | "listen", _ -> (result 32 && ints 32 2, "int (int, int)")
        | "close", _ -> (result 32 && ints 32 1, "int (int)")
        | "accept", _ ->
            (* The two address arguments are pointers, or the indices
               Ptr2Arr makes of pointers. *)
            ( result 32
              && Array.length params = 3
              && is_bits 32 params.(0)
              && Array.for_all
                   (fun ty -> Ir.is_pointer ty || Ir.is_integer ty)
                   [| params.(1); params.(2) |],
              "int (int, struct sockaddr *, socklen_t *)" )
        | _, Byte_swap n ->
            (result n && ints n 1, Printf.sprintf "uint%d_t (uint%d_t)" n n)
        | _, Inet_addr ->
            ( result 32 && Array.length params = 1 && Ir.is_pointer params.(0),
              "in_addr_t (const char *)" )
        | _, Imaxabs -> (result 64 && ints 64 1, "intmax_t (intmax_t)")
        | _ -> (false, "")
      in
      if not fits then unknown call "%s is not declared as %s" name shape;
      if name = "accept"
         && not (is_null_argument (Llvm.operand call 1)
                 && is_null_argument (Llvm.operand call 2))
      then unknown call "%s with an address argument other than NULL" name;
      (match modelled with
      | Inet_addr when inet_addr_value call = None ->
          unknown call "%s of anything but a constant decimal dotted quad" name
      | _ -> ())
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
        | Some Program_end when is_input_error_event name && not (Llvm.is_declaration target) ->
            (* the input's own definition of its error event *)
            checked_type (Defined target)
        | Some
            ( Nondet | Assume | Rand | Time | No_effect | Descriptor | Status
            | Byte_swap _ | Inet_addr | Imaxabs )
          when not (Llvm.is_declaration target) ->
            (* The program defines this task function itself (a string
               generator under a __VERIFIER_nondet_ name, an assume that
               exits): its own definition is its meaning, and it is
               translated as any defined function is, not as the model. *)
            checked_type (Defined target)
        | Some modelled ->
            check_modelled call target modelled;
            checked_type (Modelled (modelled, target))
        | None when Llvm.is_declaration target -> (
            (* Reported before the type: a call to an undeclared function
               gets a guessed type, which is rarely the right one. *)
            match name with
            | "malloc" | "calloc" | "realloc" | "free" ->
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
      (* int, or void as the SV-COMP tasks from Linux drivers write it
         (`void main(void)`): a return from main moves to the end location
         and its value is read by nothing, so the two mean the same. *)
      let is_void = Llvm.classify_type return = Llvm.TypeKind.Void in
      if not (is_void || (Ir.is_integer return && Llvm.integer_bitwidth return = 32)) then
        Outcome.stop (Unknown "main: it returns neither int nor void");
      (* Parameters are accepted only when nothing uses them, as in
         `int main(int argc, char *argv[]) { ... }` with neither read: the
         values a task is started with are then irrelevant.  After mem2reg
         the slots clang copies them into are gone, so an unused parameter
         has no use left. *)
      Array.iteri
        (fun i param ->
          if Llvm.use_begin param <> None then
            Outcome.stop
              (Unknown (Printf.sprintf "main: its parameter %d is used" (i + 1))))
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
