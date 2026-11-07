(* The transformations between reading the input and checking it:

   1. the marker pre-pass: every integer scalar slot gets an arbitrary value
      where it comes into existence, so that after mem2reg no read of a
      variable is left without a definition;
   2. optionally simplifycfg, then mem2reg, then optionally licm (both
      with every instruction that may carry UB kept alive across them); markers
      nothing reads are deleted after mem2reg;
   3. tail-call elimination, narrowed to self calls whose result is returned
      as it is;
   4. for output as one procedure: the check that no recursion is left, then
      inlining of every call to a defined function.

   The optional passes and steps 3 and 4 can be switched, to compare the
   verdicts with and without them; the marker, mem2reg and the narrowing are
   always used, since the translation relies on them. *)

type options = {
  simplifycfg : bool;
  licm : bool;
  tail_call_elimination : bool;
  inline : bool;
}

(* The direct translation keeps calls as calls, so
   inlining is off by default here; the step stays for comparing with the T2
   route, which inlines. *)
let default =
  { simplifycfg = false; licm = false; tail_call_elimination = true; inline = false }

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

(* simplifycfg deletes the computation of a condition once the branch on it
   is gone (when both successors only jump to one block, or the direction is
   known), and folds instructions it duplicates or bypasses; licm deletes the
   instructions of a loop nothing uses, sinks one whose value is used only
   after the loop to the exits (computed once instead of on every
   iteration), and reassociates an add, sub or mul with invariant operands,
   dropping nsw.  LLVM may, since such an instruction has no side effect in
   its semantics.  The translation reads overflow under nsw/nuw, division by
   zero, an oversized shift and an out-of-bounds read as UB, so these would
   delete or move that UB.  Around either pass every instruction that may
   carry such UB gets a use by a call to an external function marked
   noduplicate: an unknown callee may have side effects, so neither the call
   nor the value it reads is dead; the use is inside the loop, so the
   instruction is not sunk; licm reassociates only an operation with one
   use; and noduplicate keeps simplifycfg from threading the block.  licm
   also moves stores: one executed on every iteration with an invariant
   value before the loop, and one whose value changes into a register
   written back at the exits, so that in a loop without exits the store,
   and the out-of-bounds UB it carries, is gone.  Every store therefore gets
   a call to such a function after it taking the stored-to address, which
   may then read or write that object (also a local one whose address is
   otherwise not taken), so the store is not moved past it.  The calls are
   deleted right after the pass. *)
let keep_prefix = "__llvmfront_keep."

let may_carry_ub instr =
  Ir.is_integer (Llvm.type_of instr)
  &&
  match Llvm.instr_opcode instr with
  | Add | Sub | Mul | Shl | LShr | AShr | SDiv | UDiv | SRem | URem -> true
  | Load -> not (Llvm.is_volatile instr)
  | Call -> calls_named "llvm.abs." instr
  | _ -> false

(* A call after [instr] to the keep function taking [args]' types. *)
let insert_keep llmodule instr args =
  let ctx = Llvm.module_context llmodule in
  let tys = Array.map Llvm.type_of args in
  let fn_ty = Llvm.function_type (Llvm.void_type ctx) tys in
  let name =
    keep_prefix ^ String.concat "." (Array.to_list (Array.map Llvm.string_of_lltype tys))
  in
  let keep =
    match Llvm.lookup_function name llmodule with
    | Some fn -> fn
    | None ->
        let fn = Llvm.declare_function name fn_ty llmodule in
        Llvm.add_function_attr fn (Llvm.create_enum_attr ctx "noduplicate" 0L) Function;
        fn
  in
  let builder = Llvm.builder ctx in
  Llvm.position_builder (Llvm.instr_succ instr) builder;
  ignore (Llvm.build_call fn_ty keep args "" builder)

let insert_keeps llmodule =
  Llvm.iter_functions
    (fun fn ->
      if not (Llvm.is_declaration fn) then
        List.iter
          (fun instr ->
            if Llvm.instr_opcode instr = Store then insert_keep llmodule instr [| Llvm.operand instr 1 |]
            else insert_keep llmodule instr [| instr |])
          (List.rev
             (fold_instrs
                (fun acc i -> if may_carry_ub i || Llvm.instr_opcode i = Store then i :: acc else acc)
                [] fn)))
    llmodule

(* licm moves a getelementptr whose operands do not change in a loop before
   the loop.  The translation forms an address where it is used and keeps
   no pointer across program points, so every use in another block (other
   than by a phi) gets its own copy of the address computation right before
   it; a getelementptr has no effect, so computing it again changes
   nothing.  One left without a use is deleted. *)
let rematerialize_addresses llmodule =
  let ctx = Llvm.module_context llmodule in
  let is_gep v = Llvm.classify_value v = Instruction GetElementPtr in
  (* [v] computed right before [user] when it is a getelementptr of another
     block, with its own such operands copied likewise *)
  let rec copy_before user v =
    if is_gep v && Llvm.instr_parent v != Llvm.instr_parent user then (
      let c = Llvm.instr_clone v in
      let builder = Llvm.builder ctx in
      Llvm.position_before user builder;
      Llvm.insert_into_builder c (Llvm.value_name v) builder;
      for k = 0 to Llvm.num_operands v - 1 do
        Llvm.set_operand c k (copy_before c (Llvm.operand v k))
      done;
      c)
    else v
  in
  Llvm.iter_functions
    (fun fn ->
      if not (Llvm.is_declaration fn) then
        List.iter
          (fun gep ->
            let users = ref [] in
            Llvm.iter_uses
              (fun use ->
                let user = Llvm.user use in
                if
                  Llvm.instr_opcode user <> PHI
                  && Llvm.instr_parent user != Llvm.instr_parent gep
                  && not (List.memq user !users)
                then users := user :: !users)
              gep;
            List.iter
              (fun user ->
                let c = copy_before user gep in
                for k = 0 to Llvm.num_operands user - 1 do
                  if Llvm.operand user k == gep then Llvm.set_operand user k c
                done)
              !users;
            if Llvm.use_begin gep = None then Llvm.delete_instruction gep)
          (fold_instrs (fun acc i -> if is_gep i then i :: acc else acc) [] fn))
    llmodule

let delete_keeps llmodule =
  Llvm.iter_functions
    (fun fn ->
      if not (Llvm.is_declaration fn) then
        List.iter Llvm.delete_instruction (fold_instrs (fun acc i -> if calls_named keep_prefix i then i :: acc else acc) [] fn))
    llmodule;
  List.iter Llvm.delete_function
    (Llvm.fold_left_functions
       (fun acc fn -> if String.starts_with ~prefix:keep_prefix (Llvm.value_name fn) then fn :: acc else acc)
       [] llmodule)

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

(* -- 0. An arbitrary value for a left shift clang's check rejects ------- *)

(* The handler number clang 19 gives the shift checks (ShiftOutOfBounds) in
   [llvm.ubsantrap(i8 N)] *)
let shift_trap_handler = 20L

let is_shift_trap instr =
  calls_named "llvm.ubsantrap" instr && Llvm.int64_of_const (Llvm.operand instr 0) = Some shift_trap_handler

(* The non-debug instructions of [block], in order. *)
let block_instrs block =
  List.filter (fun i -> not (is_debug_call i)) (Llvm.fold_right_instrs (fun i acc -> i :: acc) block [])

let users v = Llvm.fold_left_uses (fun acc use -> Llvm.user use :: acc) [] v

(* The reading in which an overflowing signed operation yields an arbitrary
   value of its type, for the left shift.  A C left shift carries no [nsw],
   so the translation cannot see its overflow; the route compiles with clang's
   [-fsanitize=shift-base -fsanitize-trap=shift-base], whose check of a signed
   left shift branches to a block holding only [llvm.ubsantrap(i8 20)] and
   [unreachable] when the shifted value is negative or a bit would reach or
   pass the sign bit (C11 makes both undefined), and otherwise to the block
   that starts with the checked [shl].  Each such check is rewritten so that
   the shift yields an arbitrary value of its type where the check fails:

     P: br i1 %ok, label %S, label %T      P: br label %S
     S: %r = shl iN %a, %b            ==>  S: %r = shl iN %a, %b
                                              %h = call iN @__VERIFIER_nondet_sN()
                                              %r2 = select i1 %ok, iN %r, iN %h

   every other use of [%r] reading [%r2], and the trap block deleted.  The
   shift itself is kept, so a shift by the width or more is still poison.
   Contract: run before every other pass, on clang's -O0 output; a trap of
   another check is left alone; a shift check whose shape is not this one
   (a trap block with more than one predecessor, a successor with another
   predecessor or not starting with [shl], a width other than 8, 16, 32 or
   64, a module that defines [__VERIFIER_nondet_sN] itself) makes the
   input [Unknown], never a silent stop. *)
let havoc_rejected_shifts llmodule =
  let ctx = Llvm.module_context llmodule in
  let refuse fmt = Printf.ksprintf (fun m -> Outcome.stop (Unknown ("signed_overflow Arbitrary_value: " ^ m))) fmt in
  let nondet_function ty =
    let n = Llvm.integer_bitwidth ty in
    if not (List.mem n [ 8; 16; 32; 64 ]) then refuse "a left shift of i%d" n;
    let name = Printf.sprintf "%ss%d" Scope.nondet_prefix n in
    match Llvm.lookup_function name llmodule with
    | None -> Llvm.declare_function name (Llvm.function_type ty [||]) llmodule
    | Some fn
      when Llvm.is_declaration fn
           &&
           let rt = Llvm.return_type (Ir.global_value_type fn) in
           Llvm.classify_type rt = Llvm.TypeKind.Integer && Llvm.integer_bitwidth rt = n ->
        fn
    | Some _ -> refuse "the module defines %s itself" name
  in
  let rewrite trap_block =
    let trap_value = Llvm.value_of_block trap_block in
    match users trap_value with
    | [ br ] when Llvm.is_conditional br ->
        let cond = Llvm.condition br in
        let s0 = Llvm.successor br 0 and s1 = Llvm.successor br 1 in
        let ok_first, next = if s1 == trap_block then (true, s0) else (false, s1) in
        if (not ok_first) && not (s0 == trap_block) then refuse "a shift check not branching to its trap";
        (match users (Llvm.value_of_block next) with
        | [ only ] when only == br -> ()
        | _ -> refuse "the block after a shift check has another predecessor");
        let shl =
          match block_instrs next with
          | first :: _ when Llvm.instr_opcode first = Llvm.Opcode.Shl -> first
          | _ -> refuse "the block after a shift check does not start with the shift"
        in
        let ty = Llvm.type_of shl in
        let fn = nondet_function ty in
        let builder = Llvm.builder ctx in
        Llvm.position_builder (Llvm.instr_succ shl) builder;
        (match Llvm.metadata shl (Llvm.mdkind_id ctx "dbg") with
        | Some location -> Llvm.set_current_debug_location builder location
        | None -> ());
        let h = Llvm.build_call (Llvm.function_type ty [||]) fn [||] "shift_havoc" builder in
        let chosen =
          if ok_first then Llvm.build_select cond shl h "shift_value" builder
          else Llvm.build_select cond h shl "shift_value" builder
        in
        Llvm.replace_all_uses_with shl chosen;
        Llvm.set_operand chosen (if ok_first then 1 else 2) shl;
        Llvm.position_builder (Llvm.instr_succ br) builder;
        (match Llvm.metadata br (Llvm.mdkind_id ctx "dbg") with
        | Some location -> Llvm.set_current_debug_location builder location
        | None -> Llvm.clear_current_debug_location builder);
        ignore (Llvm.build_br next builder);
        Llvm.delete_instruction br;
        Llvm.delete_block trap_block
    | _ -> refuse "a shift trap block not reached by one conditional branch"
  in
  Llvm.iter_functions
    (fun fn ->
      if not (Llvm.is_declaration fn) then
        let traps =
          Llvm.fold_left_blocks
            (fun acc block ->
              match block_instrs block with
              | [ call; unreachable ] when is_shift_trap call && Llvm.instr_opcode unreachable = Llvm.Opcode.Unreachable ->
                  block :: acc
              | _ -> acc)
            [] fn
        in
        List.iter rewrite traps)
    llmodule;
  verify "the arbitrary value of a rejected left shift" llmodule

(* -- 3. Tail-call elimination ----------------------------------------- *)

let rec skip_debug_calls (pos : (Llvm.llbasicblock, Llvm.llvalue) Llvm.llpos) =
  match pos with
  | Before instr when is_debug_call instr -> skip_debug_calls (Llvm.instr_succ instr)
  | _ -> pos

let is_void_call call =
  match Llvm.classify_type (Llvm.type_of call) with Void -> true | _ -> false

(* Whether [ret] returns what [call] returned, the value having reached the
   returning block from [from] through the phi [value] if any. *)
let returns_result ~call ~from ret =
  if is_void_call call then Llvm.num_operands ret = 0
  else
    Llvm.num_operands ret = 1
    &&
    let value = Llvm.operand ret 0 in
    value == call
    (* the value may be a constant or an argument, which has no opcode *)
    || Llvm.classify_value value = Instruction PHI
       && List.exists
            (fun (v, block) -> v == call && block == from)
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
let returned_as_is call =
  let from = Llvm.instr_parent call in
  match skip_debug_calls (Llvm.instr_succ call) with
  | Before term -> (
      match Llvm.instr_opcode term with
      | Ret -> returns_result ~call ~from term
      | Br when Llvm.num_operands term = 1 -> (
          let target = Llvm.block_of_value (Llvm.operand term 0) in
          match return_of_merge_block (Llvm.instr_begin target) with
          | Some ret -> returns_result ~call ~from ret
          | None -> false)
      | _ -> false)
  | At_end _ -> false

(* Marks notail every self call outside the policy's form, so that
   tailcallelim, which converts the self calls it may mark tail, leaves it. *)
let narrow_tail_calls llmodule =
  Llvm.iter_functions
    (fun fn ->
      if not (Llvm.is_declaration fn) then
        List.iter
          (fun call -> if not (returned_as_is call) then Ir.set_notail call)
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
  if options.simplifycfg then (
    insert_keeps llmodule;
    run_llvm_passes llmodule simplifycfg_pass;
    delete_keeps llmodule;
    verify "simplifycfg" llmodule);
  run_llvm_passes llmodule "mem2reg";
  if options.licm then (
    insert_keeps llmodule;
    run_llvm_passes llmodule licm_pass;
    delete_keeps llmodule;
    rematerialize_addresses llmodule;
    verify "licm" llmodule);
  delete_unused_markers llmodule;
  verify "deleting unused markers" llmodule;
  if options.tail_call_elimination then (
    narrow_tail_calls llmodule;
    run_llvm_passes llmodule "tailcallelim");
  if options.inline then (
    check_no_recursion llmodule;
    mark_always_inline llmodule;
    verify "the alwaysinline rewrite" llmodule;
    run_llvm_passes llmodule "always-inline")
