(* Symbolic labels for the determinization of a play's choices: the guard of
   each selected term read off a region of the play around its point, in the
   manner of Murphy and Kincaid, "Quantified Linear Arithmetic Satisfiability
   via Fine-Grained Strategy Improvement", CAV 2024, Section 6, whose losing
   relations range over the free variables of each node -- the positions are
   symbolic -- and whose guards are the negated relations.

   The setting.  A formula [psi] over a play's variables: the weakened
   refinement formula with every key copy's result equated to the term its
   copy plays, as a function of the copy's own argument terms.  An
   environment [env] satisfies [psi].  A copy of a key has argument terms
   [args] over the play's variables, and the key's parameters are the
   variables [xs] (one per argument).

   The label region of a copy is the model-based projection of
   [psi /\ xs = args] onto [xs] at [env] extended by [xs := args(env)]
   (Komuravelli, Gurfinkel and Chaki, CAV 2014; per theory as Bjorner and
   Janota, LPAR-20, 2015; see [MbpRegion.project]): a quantifier-free formula
   over [xs] that holds at the copy's point and implies that some valuation of
   the play's other variables puts the copy at that position with every copy
   playing its term and the formula true.  It is an existential projection of
   the history onto the key's view, so it is not a winning region over [xs]:
   another history at the same position may lose.  It is only ever used as a
   candidate guard, and a definition built from such guards is accepted only
   when it gives every copy the value it must take at its own point (the
   point condition below), after which the refinement's validity check is
   still asked.

   The decision list.  For one key, its distinct terms in some order, each
   with a guard (the disjunction of the label regions of the copies that play
   it): [if g_1 then t_1 elif .. else t_m], the last guard unread.  The point
   condition: at each copy's point the list's value is the value that copy
   must take. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* [label_region ~env ~psi ~xs ~args]: the label region above, or [None]
   (the projection declines or raises, or a value is not readable).
   Pre: [xs] are fresh (in neither [psi] nor [env]), as many as [args], and
   [env] assigns every free variable of [psi] and [args].
   Post: [Some r] only when [r] is quantifier-free, mentions some variable
   and only variables of [xs], holds at [xs := args(env)], and implies the
   existential closure of [psi /\ xs = args] over every variable but [xs]
   ([MbpRegion.project]'s contract, which also checks that [env] satisfies
   the conjunction).  Asks no Z3 question beyond what the projection asks to
   extend a model (none when [env] is total on [psi]). *)
let label_region ~env ~psi ~xs ~args =
  try
    let point = List.map args ~f:(fun a -> Evaluator.eval_term ~env a) in
    let env' =
      List.fold2_exn xs point ~init:env ~f:(fun m (x, _) v ->
          Map.Poly.set m ~key:x ~data:v)
    in
    let model = Map.Poly.map env' ~f:(Term.of_value (get_dtenv ())) in
    let phi =
      Formula.and_of
        (psi
        :: List.map2_exn xs args ~f:(fun (x, s) a ->
               Formula.eq (Term.mk_var x s) a))
    in
    MbpRegion.project ~model ~kept:xs phi
  with exn when not (Common.Timer.is_async exn) -> None

(* [decision_list branches]: [if g_1 then t_1 elif .. else t_m] over the
   [(g_i, t_i)] in order, [None] for no branch.  The last guard is unread. *)
let decision_list branches =
  match List.rev branches with
  | [] -> None
  | (_, default) :: rest ->
      Some
        (List.fold rest ~init:default ~f:(fun acc (g, t) ->
             T_bool.ifte g t acc))

let same_value v w =
  try Q.equal (Value.cast_real_of v) (Value.cast_real_of w)
  with exn when not (Common.Timer.is_async exn) -> false

(* [point_condition ~xs ~copies d]: at every [(point, value)] of [copies]
   the term [d] over [xs] evaluates to [value]; false when it does not
   evaluate. *)
let point_condition ~xs ~copies d =
  List.for_all copies ~f:(fun (point, value) ->
      try
        let env =
          Map.Poly.of_alist_exn (List.zip_exn (List.map xs ~f:fst) point)
        in
        same_value (Evaluator.eval_term ~env d) value
      with exn when not (Common.Timer.is_async exn) -> false)

(* all orders of [l], [l] itself first, then lexicographically by position
   in [l] *)
let rec permutations = function
  | [] -> [ [] ]
  | l ->
      List.concat_mapi l ~f:(fun i x ->
          List.map
            (permutations (List.filteri l ~f:(fun j _ -> j <> i)))
            ~f:(fun rest -> x :: rest))

(* the most terms whose every order is tried; above it only the given order *)
let max_permuted = 4

(* [choose ~xs ~copies branches]: the first order of [branches] (each a
   guard and a term over [xs], given in preference order) whose decision
   list meets the point condition at [copies], as [Some (d, order)] with
   [order] the positions in [branches]; [None] when no order tried does.
   Tries every order when there are at most [max_permuted] branches, the
   given order first; otherwise the given order only.
   Guarantees: [d] is an [ite] chain of the given terms under the given
   guards, so it is total and single-valued over [xs] whenever the terms
   and guards mention only [xs]. *)
let choose ~xs ~copies branches =
  let indexed = List.mapi branches ~f:(fun i b -> (i, b)) in
  let orders =
    if List.length branches <= max_permuted then permutations indexed
    else [ indexed ]
  in
  List.find_map orders ~f:(fun order ->
      match decision_list (List.map order ~f:snd) with
      | Some d when point_condition ~xs ~copies d ->
          Some (d, List.map order ~f:fst)
      | _ -> None)
