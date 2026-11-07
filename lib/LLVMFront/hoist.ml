(* Loop-invariant reads of global memory, read once before the loop.

   A program the new Ptr2Arr has transformed keeps every object whose
   address is taken in a region array, so a value the loop never changes,
   such as a bound read through a pointer, is read from the array in every
   iteration.  Proving termination then needs an invariant about the array
   (this cell keeps its value), where the same value in an SSA register needs
   none.  LLVM's licm without speculation moves such a load only when it is
   executed on every iteration; this moves it also from a conditional block.

   A load is moved when its address is a global of the region arrays (which
   the translation reads as unbounded arrays, with no bounds condition) at
   indices that do not change in the loop, or a whole global; such a read has
   no effect and no undefined behaviour, so reading it once more, before the
   loop, also on a path that never reaches the original, changes nothing.
   Its value inside the loop equals the moved read when nothing in the loop
   writes that global: no store or memset/memcpy/memmove whose destination
   lies in it or cannot be traced to an object, no [__p2a_arbitrary_]
   call naming it, and no call to a defined function (which could write any
   global; conservative, as no summary of the globals a function writes is
   kept).

   A loop is a natural loop (the blocks of the back edges to one header) with
   a preheader: the header's only predecessor outside the loop, which
   branches to the header alone.  A loop without one is left as it is.
   Loops are visited innermost first, so a read moved out of an inner loop
   into its preheader, which lies in the outer loop, can be moved again.
   The index computations the moved load needs (casts and getelementptrs
   inside the loop whose operands are defined outside it) are copied into
   the preheader; the originals stay for their other uses.  Every use of the
   original load is replaced by the moved one, and the original is deleted:
   the moved one dominates the header, so it dominates every use. *)

module BlockSet = Set.Make (Int)

let is_call_to_function instr =
  Llvm.instr_opcode instr = Call && Llvm.classify_value (Ir.callee instr) = Function

(* The object a pointer lies in: a global or an alloca, through
   getelementptrs and bitcasts. *)
let rec base_object v =
  match Llvm.classify_value v with
  | GlobalVariable -> Some v
  | Instruction Alloca -> Some v
  | Instruction (GetElementPtr | BitCast) -> base_object (Llvm.operand v 0)
  | ConstantExpr -> (
      match Llvm.constexpr_opcode v with
      | GetElementPtr | BitCast -> base_object (Llvm.operand v 0)
      | _ -> None)
  | _ -> None

type writes = All | Objects of Llvm.llvalue list

let add_write w v =
  match (w, base_object v) with
  | All, _ | _, None -> All
  | Objects os, Some o -> Objects (o :: os)

let writes_object w o = match w with All -> true | Objects os -> List.memq o os

(* What the instructions of [blocks] may write; with [~except_global_stores]
   a store into a global it can be traced to is not counted. *)
let writes_of ?(except_global_stores = false) blocks =
  List.fold_left
    (fun w b ->
      Llvm.fold_left_instrs
        (fun w instr ->
          match Llvm.instr_opcode instr with
          | Store -> (
              let p = Llvm.operand instr 1 in
              match base_object p with
              | Some g when except_global_stores && Llvm.classify_value g = GlobalVariable -> w
              | _ -> add_write w p)
          | Call when is_call_to_function instr -> (
              let callee = Ir.callee instr in
              let name = Llvm.value_name callee in
              let has prefix = String.starts_with ~prefix name in
              if has "llvm.memset." || has "llvm.memcpy." || has "llvm.memmove." then
                add_write w (Llvm.operand instr 0)
              else if Llvm.is_intrinsic callee then w
              else
                match Scope.classify_callee instr with
                | Defined _ -> All
                | Modelled (Region_arbitrary global, _) -> (
                    match Llvm.lookup_global global (Llvm.global_parent callee) with
                    | Some g -> ( match w with All -> All | Objects os -> Objects (g :: os))
                    | None -> All)
                | Modelled _ | Intrinsic _ -> w)
          | Call | Invoke | CallBr -> All
          | _ -> w)
        w b)
    (Objects []) blocks

(* -- Natural loops ------------------------------------------------------ *)

type loop = {
  header : int;
  body : BlockSet.t;
  preheader : int;
}

(* The natural loops of [fn] with a preheader, innermost (smallest) first. *)
let loops_of fn =
  let blocks = Ir.basic_blocks fn in
  let nb = Array.length blocks in
  let index = Hashtbl.create nb in
  Array.iteri (fun i b -> Hashtbl.replace index b i) blocks;
  let succs =
    Array.map
      (fun b ->
        match Llvm.block_terminator b with
        | Some term -> List.map (Hashtbl.find index) (Array.to_list (Llvm.successors term))
        | None -> [])
      blocks
  in
  let preds = Array.make nb [] in
  Array.iteri (fun i ss -> List.iter (fun j -> preds.(j) <- i :: preds.(j)) ss) succs;
  (* dominators by the iterative data-flow equations; block 0 is the entry *)
  let all = BlockSet.of_list (List.init nb Fun.id) in
  let dom = Array.make nb all in
  if nb > 0 then dom.(0) <- BlockSet.singleton 0;
  let changed = ref true in
  while !changed do
    changed := false;
    for i = 1 to nb - 1 do
      let meet =
        match preds.(i) with
        | [] -> BlockSet.empty
        | p :: ps -> List.fold_left (fun s q -> BlockSet.inter s dom.(q)) dom.(p) ps
      in
      let d = BlockSet.add i meet in
      if not (BlockSet.equal d dom.(i)) then (
        dom.(i) <- d;
        changed := true)
    done
  done;
  (* the body of each header: the blocks reaching a back edge's source
     without passing the header *)
  let bodies = Hashtbl.create 8 in
  Array.iteri
    (fun t ss ->
      List.iter
        (fun h ->
          if BlockSet.mem h dom.(t) then (
            let body = ref (BlockSet.singleton h) in
            let rec visit b =
              if not (BlockSet.mem b !body) then (
                body := BlockSet.add b !body;
                List.iter visit preds.(b))
            in
            visit t;
            let previous = Option.value (Hashtbl.find_opt bodies h) ~default:BlockSet.empty in
            Hashtbl.replace bodies h (BlockSet.union previous !body)))
        ss)
    succs;
  let loops =
    Hashtbl.fold
      (fun header body acc ->
        match List.filter (fun p -> not (BlockSet.mem p body)) preds.(header) with
        | [ p ] when succs.(p) = [ header ] -> { header; body; preheader = p } :: acc
        | _ -> acc)
      bodies []
  in
  (blocks, List.sort (fun a b -> compare (BlockSet.cardinal a.body) (BlockSet.cardinal b.body)) loops)

(* -- Moving the loads --------------------------------------------------- *)

let hoist_loop blocks loop =
  let index = Hashtbl.create (Array.length blocks) in
  Array.iteri (fun i b -> Hashtbl.replace index b i) blocks;
  let inside v =
    match Llvm.classify_value v with
    | Instruction _ -> (
        match Hashtbl.find_opt index (Llvm.instr_parent v) with
        | Some i -> BlockSet.mem i loop.body
        | None -> false)
    | _ -> false
  in
  let body = List.map (fun i -> blocks.(i)) (BlockSet.elements loop.body) in
  let writes = writes_of body in
  (* a value the loop does not change, computed by copyable instructions
     from values defined outside it *)
  let rec invariant v =
    (not (inside v))
    ||
    match Llvm.instr_opcode v with
    | SExt | ZExt | Trunc | BitCast | GetElementPtr ->
        List.for_all invariant (List.init (Llvm.num_operands v) (Llvm.operand v))
    | _ -> false
  in
  let movable load =
    Llvm.instr_opcode load = Load
    && (not (Llvm.is_volatile load))
    && Ir.is_integer (Llvm.type_of load)
    && Llvm.use_begin load <> None
    &&
    let p = Llvm.operand load 0 in
    match base_object p with
    | Some g when Llvm.classify_value g = GlobalVariable ->
        (p == g || Translate.is_memoryk (Llvm.value_name g)) && invariant p && not (writes_object writes g)
    | _ -> false
  in
  let loads =
    List.concat_map (fun b -> Llvm.fold_left_instrs (fun acc i -> if movable i then i :: acc else acc) [] b) body
  in
  if loads <> [] then (
    let pre = blocks.(loop.preheader) in
    let builder = Llvm.builder (Llvm.module_context (Llvm.global_parent (Llvm.block_parent pre))) in
    (match Llvm.block_terminator pre with
    | Some term -> Llvm.position_before term builder
    | None -> assert false);
    let copies = Hashtbl.create 8 in
    let rec copy v =
      if not (inside v) then v
      else
        match Hashtbl.find_opt copies v with
        | Some c -> c
        | None ->
            let c = Llvm.instr_clone v in
            for k = 0 to Llvm.num_operands v - 1 do
              Llvm.set_operand c k (copy (Llvm.operand v k))
            done;
            Llvm.insert_into_builder c (Llvm.value_name v) builder;
            Hashtbl.replace copies v c;
            c
    in
    List.iter
      (fun load ->
        let moved = copy load in
        Llvm.replace_all_uses_with load moved;
        Llvm.delete_instruction load)
      (List.rev loads));
  List.length loads

(* Moves the loads in the functions reachable from main, the ones the
   allow-list has checked (a call elsewhere may be one [Scope.classify_callee]
   refuses); returns how many moved. *)
let run llmodule =
  List.fold_left
    (fun n fn ->
      let blocks, loops = loops_of fn in
      List.fold_left (fun n loop -> n + hoist_loop blocks loop) n loops)
    0 (Scope.reachable llmodule)

(* -- Promoting cells to registers --------------------------------------- *)

(* A cell a loop reads and writes, of a region array at an index the loop
   does not change or a whole global, held in a register across the loop: a
   read once before it, the value carried from iteration to iteration, and a
   write back at every exit.  A loop that decrements a bound through a
   pointer then decrements an integer, which a ranking function can speak
   of, rather than an array cell.

   The cell must be the only one of its global the loop accesses: every
   load and store of that global in the loop has the same address
   (structurally, from values defined outside the loop), and nothing else in
   the loop writes the global (no memset/memcpy/memmove into it, no
   [__p2a_arbitrary_] naming it, no store whose object is unknown, no call
   to a defined function).  The region arrays carry no bounds condition and
   reading or writing a cell has no other effect, so the reads and writes
   added before and after the loop, also on a path that leaves it at once,
   change nothing; a loop without exits needs no write back, since nothing
   reads the cell after it.

   LLVM does the structural part: loop-simplify gives every loop a
   preheader and exits entered only from the loop, and mem2reg builds the
   SSA form of the value across the loop's branches, from a fresh local
   slot the loop's accesses are redirected to (initialised in the
   preheader, copied back at the exits). *)

(* [a] and [b] compute the same address: one value, or the same cast or
   getelementptr of operands that do. *)
let rec same_address a b =
  a == b
  ||
  match (Llvm.classify_value a, Llvm.classify_value b) with
  | Instruction oa, Instruction ob
    when oa = ob
         && (match oa with SExt | ZExt | Trunc | BitCast | GetElementPtr -> true | _ -> false)
         && Llvm.num_operands a = Llvm.num_operands b ->
      List.for_all2 same_address
        (List.init (Llvm.num_operands a) (Llvm.operand a))
        (List.init (Llvm.num_operands b) (Llvm.operand b))
  | _ -> false

let promote_loop fn blocks loop =
  let ctx = Llvm.module_context (Llvm.global_parent fn) in
  let index = Hashtbl.create (Array.length blocks) in
  Array.iteri (fun i b -> Hashtbl.replace index b i) blocks;
  let in_body b = match Hashtbl.find_opt index b with Some i -> BlockSet.mem i loop.body | None -> false in
  let inside v =
    match Llvm.classify_value v with Instruction _ -> in_body (Llvm.instr_parent v) | _ -> false
  in
  let body = List.map (fun i -> blocks.(i)) (BlockSet.elements loop.body) in
  let rec invariant v =
    (not (inside v))
    ||
    match Llvm.instr_opcode v with
    | SExt | ZExt | Trunc | BitCast | GetElementPtr ->
        List.for_all invariant (List.init (Llvm.num_operands v) (Llvm.operand v))
    | _ -> false
  in
  let exits =
    List.fold_left
      (fun acc b ->
        match Llvm.block_terminator b with
        | None -> acc
        | Some t ->
            Array.fold_left
              (fun acc s -> if in_body s || List.memq s acc then acc else s :: acc)
              acc (Llvm.successors t))
      [] body
  in
  let dedicated exit =
    let ok = ref true in
    Llvm.iter_uses
      (fun use ->
        let user = Llvm.user use in
        match Llvm.classify_value user with
        | Instruction _ when Llvm.is_terminator user -> if not (in_body (Llvm.instr_parent user)) then ok := false
        | _ -> ())
      (Llvm.value_of_block exit);
    !ok
  in
  (* the writes other than the stores the promotion takes over *)
  let other_writes = writes_of ~except_global_stores:true body in
  (* the loads and stores of each global, by global *)
  let accesses = Hashtbl.create 8 in
  let unknown = ref false in
  List.iter
    (fun b ->
      Llvm.iter_instrs
        (fun instr ->
          let record p =
            match base_object p with
            | Some g when Llvm.classify_value g = GlobalVariable ->
                Hashtbl.replace accesses g (instr :: Option.value (Hashtbl.find_opt accesses g) ~default:[])
            | Some _ -> ()
            | None -> unknown := true
          in
          match Llvm.instr_opcode instr with
          | Load -> record (Llvm.operand instr 0)
          | Store -> record (Llvm.operand instr 1)
          | _ -> ())
        b)
    body;
  let address instr = Llvm.operand instr (if Llvm.instr_opcode instr = Load then 0 else 1) in
  let value_type instr = if Llvm.instr_opcode instr = Load then Llvm.type_of instr else Llvm.type_of (Llvm.operand instr 0) in
  let promotable g = function
    | [] -> false
    | first :: _ as all ->
        let p = address first and ty = value_type first in
        (p == g || Translate.is_memoryk (Llvm.value_name g))
        && invariant p
        && Ir.is_integer ty
        && (not (writes_object other_writes g))
        && List.exists (fun i -> Llvm.instr_opcode i = Store) all
        && List.for_all
             (fun i -> (not (Llvm.is_volatile i)) && same_address (address i) p && value_type i == ty)
             all
  in
  let cells = Hashtbl.fold (fun g all acc -> if promotable g all then (g, all) :: acc else acc) accesses [] in
  if !unknown || cells = [] || not (List.for_all dedicated exits) then 0
  else (
    let pre = blocks.(loop.preheader) in
    let entry = Llvm.entry_block fn in
    List.iter
      (fun (_, all) ->
        let first = List.hd all in
        let ty = value_type first in
        let p = address first in
        (* [p] computed before [at], its in-loop instructions copied *)
        let materialize builder =
          let copies = Hashtbl.create 4 in
          let rec copy v =
            if not (inside v) then v
            else
              match Hashtbl.find_opt copies v with
              | Some c -> c
              | None ->
                  let c = Llvm.instr_clone v in
                  for k = 0 to Llvm.num_operands v - 1 do
                    Llvm.set_operand c k (copy (Llvm.operand v k))
                  done;
                  Llvm.insert_into_builder c (Llvm.value_name v) builder;
                  Hashtbl.replace copies v c;
                  c
          in
          copy p
        in
        let builder = Llvm.builder ctx in
        Llvm.position_builder (Llvm.instr_begin entry) builder;
        let slot = Llvm.build_alloca ty "promoted" builder in
        (match Llvm.block_terminator pre with Some t -> Llvm.position_before t builder | None -> assert false);
        let initial = Llvm.build_load ty (materialize builder) "promoted.init" builder in
        ignore (Llvm.build_store initial slot builder);
        List.iter
          (fun instr ->
            match Llvm.instr_opcode instr with
            | Load -> Llvm.set_operand instr 0 slot
            | _ -> Llvm.set_operand instr 1 slot)
          all;
        List.iter
          (fun exit ->
            let rec first_non_phi = function
              | Llvm.Before i when Llvm.instr_opcode i = PHI -> first_non_phi (Llvm.instr_succ i)
              | pos -> pos
            in
            Llvm.position_builder (first_non_phi (Llvm.instr_begin exit)) builder;
            let v = Llvm.build_load ty slot "promoted.final" builder in
            ignore (Llvm.build_store v (materialize builder) builder))
          exits)
      cells;
    List.length cells)

(* Promotes the cells of the loops of the functions reachable from main;
   returns how many were promoted. *)
let promote llmodule =
  Passes.run_llvm_passes llmodule "loop-simplify";
  let n =
    List.fold_left
      (fun n fn ->
        let blocks, loops = loops_of fn in
        List.fold_left (fun n loop -> n + promote_loop fn blocks loop) n loops)
      0 (Scope.reachable llmodule)
  in
  if n > 0 then (
    Passes.run_llvm_passes llmodule "mem2reg";
    (* the read before the loop and the writes back reuse an address
       computed before the loop, which the translation does not carry
       across the loop's program point *)
    Passes.rematerialize_addresses llmodule);
  Passes.verify "promoting cells" llmodule;
  n
