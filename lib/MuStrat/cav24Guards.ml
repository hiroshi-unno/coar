(* The determinization of a ground play's choices by losing relations: Murphy
   and Kincaid, "Quantified Linear Arithmetic Satisfiability via Fine-Grained
   Strategy Improvement", CAV 2024, Section 6, specialised to a chain.

   The setting.  A formula [phi] over the result variables [y_1, .., y_k] of
   [k] choice nodes, closed otherwise (every other variable already replaced
   by its value), and per node a non-empty list of offered values, constants
   of one sort, in the order the node prefers them.  A choice vector picks
   one offered value per node; it wins when [phi] holds at it.

   The losing system.  Relations [P_1, .., P_(k+1)], [P_j] over
   [y_1, .., y_(j-1)] (so [P_1] is nullary), and the clauses
     not phi(y_1, .., y_k)                    => P_(k+1)(y_1, .., y_k)
     /\_(c offered at node j) P_(j+1)(y_<j, c) => P_j(y_<j)      (each j)
     P_1                                       => false
   [P_j(v)] reads "from the history [v], every remaining choice loses".  This
   is the system CAV 2024 Section 6 builds over a strategy skeleton (in this
   tree [StratSynth.loseCHC]) for the skeleton in which every node offers its
   values whatever was chosen above it; [loseCHC] would make one relation per
   skeleton node, a tree with one copy of the rest of the chain under every
   value, whereas here the copies under the values of one node are one
   relation, the value being an argument.  The two systems have the same
   solutions on the shared relation: every copy is defined by the same
   clauses with the history as argument.

   The run.  Given any solution [theta] of the system, each node in order
   takes the first offered value [c] for which [theta(P_(j+1))(v, c)] does not
   hold at the history [v] chosen so far.  Such a value exists at every node
   and the vector chosen wins: at the root [P_1] is false (the goal clause);
   if [P_j(v)] is false then, by the clause defining [P_j], some offered
   [c] has [P_(j+1)(v, c)] false, so the run continues with a history outside
   [P_(j+1)]; at the end the history is outside [P_(k+1)], whose clause gives
   [phi].  The least solution (forward propagation) satisfies the goal
   exactly when some choice vector wins.

   Contract of [determinize]: [Ok idx] lists, per node, the index of the
   offered value taken, and [phi] has been evaluated true at those values
   here (the argument above is not trusted alone: a label that does not
   evaluate is read as losing, and the final evaluation is checked);
   [Error reason] otherwise -- the combinations exceed [max_branches], the
   engine gives no solution, or the run or its check fails.  Asks the engine
   once and Z3 never. *)

open Core
open Common.Ext
open Ast

(* Forward propagation substitutes each relation's definition into its
   parent's, once per offered value, so the formula it builds for [P_1] has
   one copy of [phi] per choice vector; above this many vectors the system
   is not built. *)
let max_branches = 256

type node = {
  result : Ident.tvar;  (** the node's variable [y_j] in [phi] *)
  options : Logic.term list;
      (** the offered values, closed constants, in preference order *)
}

let branches nodes =
  List.fold nodes ~init:1 ~f:(fun acc n ->
      if acc > max_branches then acc else acc * List.length n.options)

(* [system ~sort ~phi nodes]: the losing system above and its relations
   [P_1 .. P_(k+1)], in that order.  Pre: [nodes] non-empty, every option
   list non-empty, the [result]s pairwise distinct and of sort [sort], and
   [phi] mentions no other variable. *)
let system ~sort ~phi nodes =
  let k = List.length nodes in
  let rels =
    List.init (k + 1) ~f:(fun _ ->
        Ident.mk_fresh_tvar ~prefix:(Some "lose_") ())
  in
  let ys = List.map nodes ~f:(fun n -> n.result) in
  let rel_sort j = Logic.Sort.mk_fun (List.init j ~f:(fun _ -> sort) @ [ Logic.BoolTerm.SBool ]) in
  let app j args = Logic.Term.mk_apps (Logic.Term.mk_var (List.nth_exn rels j)) args in
  let senv vs = Map.Poly.of_alist_exn (List.map vs ~f:(fun v -> (v, sort))) in
  let imply a b = Logic.Term.mk_apps (Logic.BoolTerm.mk_imply ()) [ a; b ] in
  let leaf =
    ( senv ys,
      imply (Logic.BoolTerm.neg_of phi) (app k (List.map ys ~f:Logic.Term.mk_var)) )
  in
  let steps =
    List.mapi nodes ~f:(fun j n ->
        let above = List.take ys j in
        let hist = List.map above ~f:Logic.Term.mk_var in
        ( senv above,
          imply
            (Logic.BoolTerm.and_of
               (List.map n.options ~f:(fun c -> app (j + 1) (hist @ [ c ]))))
            (app j hist) ))
  in
  let goal = (Map.Poly.empty, imply (app 0 []) (Logic.BoolTerm.mk_bool false)) in
  let params =
    PCSP.Params.make
    @@ Map.Poly.of_alist_exn (List.mapi rels ~f:(fun j p -> (p, rel_sort j)))
  in
  (PCSP.Problem.of_formulas ~params (Set.Poly.of_list ((leaf :: steps) @ [ goal ])), rels)

(* a closed boolean term's truth value; [None] when it does not evaluate *)
let truth t =
  try
    Some
      (Evaluator.eval
      @@ Logic.ExtTerm.to_old_fml Map.Poly.empty Map.Poly.empty
      @@ Logic.Term.beta_reduction t)
  with exn when not (Common.Timer.is_async exn) -> None

(* [run ~labels ~rels ~phi nodes]: the run above under the solution
   [labels]; [Some idx] only if [phi] evaluates true at the values taken *)
let run ~labels ~rels ~phi nodes =
  let rec go hist idx j = function
    | [] ->
        let sub =
          Map.Poly.of_alist_exn
            (List.zip_exn (List.map nodes ~f:(fun n -> n.result)) (List.rev hist))
        in
        if Stdlib.(truth (Logic.Term.subst sub phi) = Some true) then
          Some (List.rev idx)
        else None
    | n :: rest -> (
        match Map.Poly.find labels (List.nth_exn rels (j + 1)) with
        | None -> None
        | Some lab -> (
            let loses c =
              match
                truth (Logic.Term.mk_apps lab (List.rev_append hist [ c ]))
              with
              | Some false -> false
              | Some true | None -> true
            in
            match List.findi n.options ~f:(fun _ c -> not (loses c)) with
            | None -> None
            | Some (i, c) -> go (c :: hist) (i :: idx) (j + 1) rest))
  in
  go [] [] 0 nodes

(* [determinize ~solve ~sort ~phi nodes]: see the header.  [solve] is the
   engine: a solution of the system, or [None]. *)
let determinize ~solve ~sort ~phi nodes =
  if List.is_empty nodes then Error "no node with a choice"
  else if branches nodes > max_branches then
    Error (sprintf "more than %d choice vectors" max_branches)
  else
    let pcsp, rels = system ~sort ~phi nodes in
    match solve pcsp with
    | None -> Error "the engine gave no solution of the losing system"
    | Some labels -> (
        match run ~labels ~rels ~phi nodes with
        | Some idx -> Ok idx
        | None -> Error "the run under the engine's solution did not win")
