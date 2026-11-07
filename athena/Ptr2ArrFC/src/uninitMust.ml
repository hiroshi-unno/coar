(* Which reads of a variable every path writes first (--uninit=check), so
   that the check of the read can be left out.

   A forward must analysis over the structured statements of a function:
   for each statement, the set of variables (scalar ones, among those asked
   about) that every path from the function's start has written when the
   statement starts. The meet is intersection. A variable is written by an
   assignment to it whole or by a call whose result it receives; a read
   does not change the set. The analysis is sound by being conservative
   where the control flow is not structured:

   - a statement with a label (a goto target, a case or default label)
     starts with the empty set, since a jump from anywhere may reach it;
   - entering a block removes the variables it declares, which C makes
     indeterminate at each entry (a loop's body is entered at every
     iteration);
   - a loop's head is the intersection of its entry and of the states at
     the ends of its iterations (the end of the body, and every continue),
     iterated to a fixpoint, which is reached since the sets only shrink;
   - the states after a loop and after a switch are the intersections of
     their breaks' (and, for a switch, of the end of its body and of its
     entry, which skips the body when no case matches and there is no
     default);
   - a goto and a return end the path.

   Contract: [analyse fd ~tracked] reads [fd] (it does not modify it) and
   returns a table from statement id to the set of variable ids written on
   every path to that statement's start, among the ids [tracked] accepts;
   a statement it does not reach (it cannot be reached, or the function
   has a construct it does not handle, which leaves the table empty) is not
   in the table and must be taken as having nothing written. *)

open Cil_types

module S = Set.Make (Int)

(* None: no path reaches here (the unit of the meet). *)
type state = S.t option

let meet a b =
  match (a, b) with
  | None, x | x, None -> x
  | Some a, Some b -> Some (S.inter a b)

exception Unhandled

let analyse fd ~tracked =
  let table : (int, S.t) Hashtbl.t = Hashtbl.create 64 in
  let written instr st =
    let add = function
      | Var v, NoOffset when tracked v -> Option.map (S.add v.vid) st
      | _ -> st
    in
    match instr with
    | Set (lv, _, _) | Call (Some lv, _, _, _) -> add lv
    | Local_init (v, _, _) -> add (Var v, NoOffset)
    | _ -> st
  in
  let record s st =
    match st with
    | None -> ()
    | Some set ->
        let prev = Hashtbl.find_opt table s.sid in
        Hashtbl.replace table s.sid
          (match prev with Some p -> S.inter p set | None -> set)
  in
  (* [breaks] and [continues] collect the states at the jumps of the
     innermost loop or switch *)
  let rec stmt ~breaks ~continues st s =
    let st = if s.labels <> [] then Some S.empty else st in
    record s st;
    match s.skind with
    | Instr i -> written i st
    | Return _ | Goto _ -> None
    | Break _ ->
        breaks := meet !breaks st;
        None
    | Continue _ ->
        continues := meet !continues st;
        None
    | If (_, b1, b2, _) ->
        meet (block ~breaks ~continues st b1) (block ~breaks ~continues st b2)
    | Block b -> block ~breaks ~continues st b
    | UnspecifiedSequence l ->
        List.fold_left (fun st (s', _, _, _, _) -> stmt ~breaks ~continues st s') st l
    | Loop (_, body, _, _, _) ->
        let rec iterate head =
          let br = ref None and co = ref None in
          let out = block ~breaks:br ~continues:co head body in
          let head' = meet head (meet out !co) in
          if Option.equal S.equal head' head then !br else iterate head'
        in
        (* the statements of the body are recorded at each round; the last
           round, with the smallest head, is the one that holds, and the
           records meet with the earlier ones *)
        iterate st
    | Switch (_, body, cases, _) ->
        let br = ref None in
        let out = block ~breaks:br ~continues st body in
        let has_default =
          List.exists (fun c -> List.exists (function Default _ -> true | _ -> false) c.labels) cases
        in
        meet (meet out !br) (if has_default then None else st)
    | TryCatch _ | TryFinally _ | TryExcept _ | Throw _ -> raise Unhandled
  and block ~breaks ~continues st b =
    let declared = List.map (fun v -> v.vid) b.blocals in
    let st = Option.map (fun set -> List.fold_left (fun s id -> S.remove id s) set declared) st in
    List.fold_left (fun st s -> stmt ~breaks ~continues st s) st b.bstmts
  in
  (try ignore (block ~breaks:(ref None) ~continues:(ref None) (Some S.empty) fd.sbody)
   with Unhandled -> Hashtbl.reset table);
  table
