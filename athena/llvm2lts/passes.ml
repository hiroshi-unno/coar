(* The transformations between reading the input and checking it:

   1. the marker pre-pass: every integer scalar slot gets an arbitrary value
      where it comes into existence, so that after mem2reg no read of a
      variable is left without a definition;
   2. optionally simplifycfg, then mem2reg, then optionally licm; markers
      nothing reads are deleted after mem2reg;
   3. tail-call elimination, narrowed to self calls whose result is returned
      as it is, or, with [accumulator_recursion], also combined once by an
      add or a mul before it is returned;
   4. for output as one procedure: the check that no recursion is left, then
      inlining of every call to a defined function.

   The optional passes and steps 3 and 4 can be switched, to compare the
   verdicts with and without them; the marker, mem2reg and the narrowing are
   always used, since the translation relies on them. *)

type options = {
  simplifycfg : bool;
  licm : bool;
  tail_call_elimination : bool;
  accumulator_recursion : bool;
      (** also let tail-call elimination convert [return n + f(x);] and
          [return n * f(x);] with an accumulator.  Exact only where an add
          and a mul are read as total, associative and commutative
          operations with no guard: Pipeline.run admits it only with the
          integers unbounded *)
  inline : bool;
}

let default =
  {
    simplifycfg = false;
    licm = false;
    tail_call_elimination = true;
    accumulator_recursion = false;
    inline = true;
  }

(* The optional passes with the options that keep them from speculating:
   neither may execute an instruction on a path that did not execute it,
   which could introduce UB the program does not have. *)
let simplifycfg_pass = "simplifycfg<no-speculate-blocks>"
let licm_pass = "loop-mssa(licm<no-allowspeculation>)"

let fold_instrs f acc fn =
  Llvm.fold_left_blocks (Llvm.fold_left_instrs f) acc fn

let called_function instr =
  match Llvm.instr_opcode instr with
  | Call -> (
      let callee = Ir.callee instr in
      match Llvm.classify_value callee with Function -> Some callee | _ -> None)
  | _ -> None

let calls_named prefix instr =
  match called_function instr with
  | Some fn -> String.starts_with ~prefix (Llvm.value_name fn)
  | None -> false

let is_debug_call = calls_named "llvm.dbg."

(* -- 1. The marker pre-pass ------------------------------------------- *)

(* An integer local variable: an alloca of one integer.  Arrays, structs and
   variable-length arrays get their arbitrary contents in the translation,
   where they are declared. *)
let is_scalar_slot instr =
  Llvm.classify_value instr = Instruction Alloca
  && Ir.is_integer (Ir.allocated_type instr)
  && Llvm.int64_of_const (Llvm.operand instr 0) = Some 1L

(* A slot clang copies a parameter into.  Its declaration is marked after the
   copy, so a marker there would overwrite the argument. *)
let is_parameter_slot slot =
  let found = ref false in
  Llvm.iter_uses
    (fun use ->
      let user = Llvm.user use in
      match Llvm.classify_value user with
      | Instruction Store ->
          if
            Llvm.operand user 1 == slot
            && Llvm.classify_value (Llvm.operand user 0) = Argument
          then found := true
      | _ -> ())
    slot;
  !found

let marker_function llmodule ty =
  let name =
    Printf.sprintf "%si%d" Scope.uninit_marker_prefix (Llvm.integer_bitwidth ty)
  in
  match Llvm.lookup_function name llmodule with
  | Some fn -> fn
  | None -> Llvm.declare_function name (Llvm.function_type ty [||]) llmodule

(* Stores a fresh marker value into [slot] right after [instr], with
   [instr]'s debug location when it has one. *)
let store_marker llmodule ctx ~after slot =
  let ty = Ir.allocated_type slot in
  let builder = Llvm.builder ctx in
  Llvm.position_builder (Llvm.instr_succ after) builder;
  (match Llvm.metadata after (Llvm.mdkind_id ctx "dbg") with
  | Some location -> Llvm.set_current_debug_location builder location
  | None -> ());
  let value =
    Llvm.build_call (Llvm.function_type ty [||]) (marker_function llmodule ty)
      [||] "uninit" builder
  in
  ignore (Llvm.build_store value slot builder)

(* Two places per variable: after its alloca in the entry block, for paths
   that bypass its declaration (a goto or switch into its scope, the return
   slot), and at its declaration, so that a variable declared inside a loop
   gets a fresh value on every iteration rather than the last one. *)
let insert_markers llmodule =
  let ctx = Llvm.module_context llmodule in
  Llvm.iter_functions
    (fun fn ->
      if not (Llvm.is_declaration fn) then (
        let sites =
          fold_instrs
            (fun sites instr ->
              if is_scalar_slot instr then (instr, instr) :: sites
              else if calls_named "llvm.dbg.declare" instr then
                match Ir.declared_slot instr with
                (* a parameter's declaration (the debug variable's
                   [arg:]) is never marked: clang copies a [_Bool]
                   parameter through [zext], so the slot's store is not of
                   the argument itself and [is_parameter_slot] misses it *)
                | Some slot
                  when is_scalar_slot slot && Ir.declared_arg instr = 0
                       && not (is_parameter_slot slot) ->
                    (instr, slot) :: sites
                | _ -> sites
              else sites)
            [] fn
        in
        List.iter (fun (after, slot) -> store_marker llmodule ctx ~after slot) sites))
    llmodule

(* After mem2reg, a marker whose value nothing reads (the variable is written
   on every path before it is read) is dead.  It is deleted rather than left
   for the translation to skip: as an unknown external call it would also
   keep tail-call elimination from moving past it, and so leave recursion
   that the policy converts.  A debug intrinsic that named it is not a use;
   LLVM turns its operand into an empty location. *)
let delete_unused_markers llmodule =
  Llvm.iter_functions
    (fun fn ->
      if not (Llvm.is_declaration fn) then
        List.iter Llvm.delete_instruction
          (fold_instrs
             (fun dead instr ->
               if
                 calls_named Scope.uninit_marker_prefix instr
                 && Llvm.use_begin instr = None
               then instr :: dead
               else dead)
             [] fn))
    llmodule

(* -- 2. LLVM passes --------------------------------------------------- *)

let target_machine llmodule =
  Llvm_X86.initialize ();
  let triple = Llvm.target_triple llmodule in
  Llvm_target.TargetMachine.create ~triple (Llvm_target.Target.by_triple triple)

let run_llvm_passes llmodule passes =
  if passes <> "" then (
    let options = Llvm_passbuilder.create_passbuilder_options () in
    Llvm_passbuilder.passbuilder_options_set_verify_each options true;
    let result =
      Llvm_passbuilder.run_passes llmodule passes (target_machine llmodule)
        options
    in
    Llvm_passbuilder.dispose_passbuilder_options options;
    match result with
    | Ok () -> ()
    | Error message ->
        Outcome.stop
          (Internal_error (Printf.sprintf "passes %S: %s" passes message)))

let verify step llmodule =
  match Llvm_analysis.verify_module llmodule with
  | None -> ()
  | Some message ->
      Outcome.stop
        (Internal_error (Printf.sprintf "after %s: %s" step (String.trim message)))

(* -- 3. Tail-call elimination ----------------------------------------- *)

let rec skip_debug_calls (pos : (Llvm.llbasicblock, Llvm.llvalue) Llvm.llpos) =
  match pos with
  | Before instr when is_debug_call instr -> skip_debug_calls (Llvm.instr_succ instr)
  | _ -> pos

let is_void_call call =
  match Llvm.classify_type (Llvm.type_of call) with Void -> true | _ -> false

(* Whether [ret] returns [result] (a call or an instruction), the value
   having reached the returning block from [from] through the phi [value] if
   any. *)
let returns_result ~result ~from ret =
  if is_void_call result then Llvm.num_operands ret = 0
  else
    Llvm.num_operands ret = 1
    &&
    let value = Llvm.operand ret 0 in
    value == result
    || Llvm.instr_opcode value = PHI
       && List.exists
            (fun (v, block) -> v == result && block == from)
            (Llvm.incoming value)

(* A block that only merges values and returns: phis, debug calls, ret. *)
let rec return_of_merge_block (pos : (Llvm.llbasicblock, Llvm.llvalue) Llvm.llpos) =
  match skip_debug_calls pos with
  | Before instr when Llvm.instr_opcode instr = PHI ->
      return_of_merge_block (Llvm.instr_succ instr)
  | Before instr when Llvm.instr_opcode instr = Ret -> Some instr
  | _ -> None

(* The form tail-call elimination may convert under the policy: the call is
   followed, apart from debug calls, by a return of its result (`return
   f(x);`, or `f(x); return;`), possibly through an unconditional branch to
   the block clang merges every return into.  A call whose result is first
   combined with something (`return n + f(n - 1);`), or followed by other
   work, is not: converting it changes the order of operations. *)
let returned_as_is_from result pos =
  let from = Llvm.instr_parent result in
  match skip_debug_calls pos with
  | Before term -> (
      match Llvm.instr_opcode term with
      | Ret -> returns_result ~result ~from term
      | Br when Llvm.num_operands term = 1 -> (
          let target = Llvm.block_of_value (Llvm.operand term 0) in
          match return_of_merge_block (Llvm.instr_begin target) with
          | Some ret -> returns_result ~result ~from ret
          | None -> false)
      | _ -> false)
  | At_end _ -> false

let returned_as_is call = returned_as_is_from call (Llvm.instr_succ call)

let uses value = Llvm.fold_left_uses (fun n _ -> n + 1) 0 value

(* The accumulator form: the call is followed, apart from debug calls, by
   one add or mul that is its only use, takes the result as exactly one
   operand, is itself used once, and is returned as is (`return n + f(x);`,
   `return f(x) * n;`).  Nothing else stands between the call and the
   return, so the pass moves no instruction above the call: it only computes
   the sum or product in the opposite order, through an accumulator that
   starts at 0 or 1.  The other operand is defined before the call (it is
   not the call, and nothing but debug calls precedes the add). *)
let accumulated_as_is call =
  (not (is_void_call call))
  && uses call = 1
  &&
  match skip_debug_calls (Llvm.instr_succ call) with
  | Before acc -> (
      match Llvm.instr_opcode acc with
      | Add | Mul ->
          Llvm.num_operands acc = 2
          && (Llvm.operand acc 0 == call) <> (Llvm.operand acc 1 == call)
          && uses acc = 1
          && returned_as_is_from acc (Llvm.instr_succ acc)
      | _ -> false)
  | At_end _ -> false

(* Marks notail every self call outside the policy's form (with
   [accumulator], outside both forms), so that tailcallelim, which converts
   the self calls it may mark tail, leaves it. *)
let narrow_tail_calls ~accumulator llmodule =
  Llvm.iter_functions
    (fun fn ->
      if not (Llvm.is_declaration fn) then
        List.iter
          (fun call ->
            if
              not
                (returned_as_is call || (accumulator && accumulated_as_is call))
            then Ir.set_notail call)
          (fold_instrs
             (fun calls instr ->
               match called_function instr with
               | Some callee when callee == fn -> instr :: calls
               | _ -> calls)
             [] fn))
    llmodule

(* -- 4. No recursion left, then inlining ------------------------------ *)

let defined_callees fn =
  List.rev
    (Scope.fold_calls
       (fun acc call ->
         match Scope.classify_callee call with
         | Defined callee -> callee :: acc
         | Modelled _ | Intrinsic _ -> acc)
       [] fn)

(* A cycle of calls among the functions reachable from main, as the list of
   its functions from the first repeated one, if there is one. *)
let find_cycle llmodule =
  let state = Hashtbl.create 16 in
  let rec visit path fn =
    match Hashtbl.find_opt state fn with
    | Some `Done -> None
    | Some `Open ->
        let rec upto acc = function
          | [] -> acc
          | f :: rest -> if f == fn then f :: acc else upto (f :: acc) rest
        in
        Some (upto [ fn ] path)
    | None ->
        Hashtbl.replace state fn `Open;
        let found = List.find_map (visit (fn :: path)) (defined_callees fn) in
        Hashtbl.replace state fn `Done;
        found
  in
  visit [] (Scope.main_function llmodule)

let check_no_recursion llmodule =
  match find_cycle llmodule with
  | None -> ()
  | Some cycle ->
      Outcome.stop
        (Unknown
           (Printf.sprintf "recursion other than `return f(x);`: %s"
              (String.concat " -> " (List.map Llvm.value_name cycle))))

(* clang -O0 marks every function noinline; the inliner takes those marked
   alwaysinline.  [main] is never called, and the modelled externals a module
   defines (reach_error) are kept as calls. *)
let mark_always_inline llmodule =
  let ctx = Llvm.module_context llmodule in
  let always = Llvm.create_enum_attr ctx "alwaysinline" 0L in
  List.iter
    (fun fn ->
      if Llvm.value_name fn <> "main" then (
        Llvm.remove_enum_function_attr fn (Llvm.enum_attr_kind "noinline") Function;
        Llvm.remove_enum_function_attr fn (Llvm.enum_attr_kind "optnone") Function;
        Llvm.add_function_attr fn always Function))
    (Scope.reachable llmodule)

let run options llmodule =
  insert_markers llmodule;
  verify "the marker pre-pass" llmodule;
  if options.simplifycfg then run_llvm_passes llmodule simplifycfg_pass;
  run_llvm_passes llmodule "mem2reg";
  if options.licm then run_llvm_passes llmodule licm_pass;
  delete_unused_markers llmodule;
  verify "deleting unused markers" llmodule;
  if options.tail_call_elimination then (
    narrow_tail_calls ~accumulator:options.accumulator_recursion llmodule;
    run_llvm_passes llmodule "tailcallelim");
  if options.inline then (
    check_no_recursion llmodule;
    mark_always_inline llmodule;
    verify "the alwaysinline rewrite" llmodule;
    run_llvm_passes llmodule "always-inline")
