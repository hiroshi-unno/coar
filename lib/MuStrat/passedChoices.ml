(* The losing conditions of the alternatives a derivation passed over.

   A strategy check is a set of Horn clauses in which the OPPONENT's choices
   are alternative clauses with one head predicate (a derivation picks one of
   them at each node) and the checked side's choices are conjunctions of
   premises.  A counter-play is a derivation, so at each of its nodes the
   opponent took one clause and passed over the others.  When a ranking of the
   opponent is fitted to a region of the play (a step relation projected from
   the clause instances along a chain segment), the region describes the
   steps the opponent takes by repeating that move; it says nothing about
   WHERE taking it is the opponent's right choice.  On an input like
   [F a b =mu G a b \/ F (a + 2) (b + 1)] with [G] winning exactly where
   [a > b], the step [F -> F] is a clause with no guard: staying in [F] is the
   opponent's own choice, right where [G] loses, and the region of the step,
   [a' = a + 2 /\ b' = b + 1], has no ranking.  Intersected with the
   condition under which the passed-over alternative [G] cannot win, [a <= b],
   it has one, [b - a].

   What is computed.  For a clause [c] with head [P(h)], body premises
   [Q_j(u_j)] and pure body [B], its FIRING condition at a tuple [p] of
   [P]'s arguments is

     Fire_c(p) = exists vars(c). h = p /\ B /\ /\_j May_{Q_j}(u_j)

   where [May_Q(u)] is the disjunction, over the clauses [c''] with head
   [Q(h'')] and pure body [B''], of [exists vars(c''). h'' = u /\ B''] (their
   premises read as true; [true] when [Q] has more clauses than a bound,
   [false] when it has none).  The LOSING condition of [c] is the negation of
   [Fire_c] after quantifier elimination.

   Contract.  (1) [May_Q(u)] is implied by the derivability of [Q(u)] in the
   check: every derivation of [Q(u)] ends with a clause whose pure body holds.
   So [Fire_c(p)] is implied by "c can derive P(p)", and the losing condition
   [L_c(p)] implies that no derivation of [P(p)] ends with [c]: it
   under-approximates "the alternative c loses at p".  (2) A condition is
   returned only when the elimination yields a quantifier-free formula; a
   clause whose elimination fails, or whose losing condition is [true] or
   [false], gives none.  (3) [at_point] keeps a condition only where it
   evaluates to [true] at the node's ground arguments, so the clause the
   derivation took (which fires there) never contributes, and the play's own
   pair stays inside every narrowed region.

   Why narrowing is sound.  A region is a demand [R ⊇ region] on the ranking
   being fitted; a narrowed region is a subset of the unnarrowed one, so it
   only weakens that demand, and every ground pair the play asks is still a
   fact of its own.  The ranking found is still a template instance of the
   well-founded kind, and an answer still comes only from a won strategy
   check.  So the conditions decide which ranking is proposed, never a
   verdict. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* A clause of the check: its universally quantified variables, positive
   atoms, negative atoms and pure part (the clause is their disjunction, the
   negative atoms negated). *)
type clause =
  (Ident.tvar, Sort.t) Map.Poly.t
  * Atom.t Set.Poly.t
  * Atom.t Set.Poly.t
  * Formula.t

(* At most this many clauses with one head are read as alternatives (or as the
   disjuncts of a premise's [May]); more is read as no information. *)
let max_clauses_per_head = 16

let head_of ((_, ps, _, _) : clause) =
  match Set.to_list ps with
  | [ atom ] when Atom.is_pvar_app atom ->
      let pvar, sorts, args, _ = Atom.let_pvar_app atom in
      Some (pvar, sorts, args)
  | _ -> None

let freshen ((senv, ps, ns, phi) : clause) : clause =
  let ren =
    Map.Poly.of_alist_exn
    @@ List.map (Map.Poly.keys senv) ~f:(fun x ->
        (x, Ident.mk_fresh_tvar ~prefix:(Some "PC_") ()))
  in
  ( Map.Poly.of_alist_exn
    @@ List.map (Map.Poly.to_alist senv) ~f:(fun (x, s) ->
        (Map.Poly.find_exn ren x, s)),
    Set.Poly.map ps ~f:(Atom.rename ren),
    Set.Poly.map ns ~f:(Atom.rename ren),
    Formula.rename ren phi )

let clauses_with_head clauses pvar =
  List.filter clauses ~f:(fun c ->
      match head_of c with
      | Some (p, _, _) -> Ident.pvar_equal p pvar
      | None -> false)

(* [h = p] as a list of equations, [None] on an arity mismatch *)
let eqs hs ps =
  match List.map2 hs ps ~f:Formula.eq with
  | List.Or_unequal_lengths.Ok l -> Some l
  | Unequal_lengths -> None

(* the pure body of [c] and the binders it needs, conjoined with [h = args];
   [None] when [c] has no single head or its arity differs *)
let firing_body c args =
  let c = freshen c in
  let senv, _, _, phi = c in
  match head_of c with
  | None -> None
  | Some (_, _, hs) -> (
      match eqs hs args with
      | None -> None
      | Some es ->
          Some (Map.Poly.to_alist senv, es @ [ Formula.mk_neg phi ], c))

let may clauses (pvar, args) =
  let cs = clauses_with_head clauses pvar in
  if List.length cs > max_clauses_per_head then Formula.mk_true ()
  else
    Formula.or_of
    @@ List.filter_map cs ~f:(fun c ->
        match firing_body c args with
        | None -> Some (Formula.mk_true ())
        | Some (bounds, body, _) ->
            Some (Formula.exists bounds (Formula.and_of body)))

let fire clauses c args =
  match firing_body c args with
  | None -> None
  | Some (bounds, body, (_, _, ns, _)) ->
      let premises =
        List.map (Set.to_list ns) ~f:(fun atom ->
            if Atom.is_pvar_app atom then
              let pvar, _, us, _ = Atom.let_pvar_app atom in
              may clauses (pvar, us)
            else Formula.mk_true ())
      in
      Some (Formula.exists bounds (Formula.and_of (body @ premises)))

(* The losing conditions of the alternatives for [pvar], as formulas over the
   parameters [params] (fresh variables of [pvar]'s argument sorts), one per
   clause with head [pvar] whose condition is quantifier-free and neither
   [true] nor [false] after elimination; [[]] when [pvar] has more than
   [max_clauses_per_head] clauses.  [qelim] eliminates the quantifiers of a
   formula (it may return one that still has some, which is then skipped). *)
let losing_conditions ~qelim clauses pvar params =
  let cs = clauses_with_head clauses pvar in
  if List.length cs > max_clauses_per_head then []
  else
    let args = List.map params ~f:(fun (x, s) -> Term.mk_var x s) in
    List.filter_map cs ~f:(fun c ->
        match fire clauses c args with
        | None -> None
        | Some phi -> (
            let phi = Evaluator.simplify phi in
            match
              if Formula.is_quantifier_free phi then Some phi
              else
                try Some (Evaluator.simplify (qelim phi))
                with exn when not (Common.Timer.is_async exn) -> None
            with
            | Some qf when Formula.is_quantifier_free qf ->
                let l = Evaluator.simplify (Formula.mk_neg qf) in
                if Formula.is_true l || Formula.is_false l then None
                else Some l
            | _ -> None))

(* The conditions of [conds] (over [params]) that hold at the ground point
   [point], each renamed to the variables [vars] (in [params]' order).  A
   condition whose evaluation fails is not kept. *)
let at_point conds params ~point ~vars =
  let sub =
    Map.Poly.of_alist_exn
    @@ List.map2_exn params point ~f:(fun (x, _) t -> (x, t))
  in
  let ren =
    Map.Poly.of_alist_exn
    @@ List.map2_exn params vars ~f:(fun (x, _) (y, _) -> (x, y))
  in
  List.filter_map conds ~f:(fun l ->
      match Evaluator.eval (Evaluator.simplify (Formula.subst sub l)) with
      | true -> Some (Formula.rename ren l)
      | false -> None
      | exception exn when not (Common.Timer.is_async exn) -> None)

(* [at_point] at one node of a chain segment, gated by where the node sits.
   [visit] says whether the node is a visit of the ranked predicate (a node
   whose atom carries a state of the ranking being fitted).  Under
   [visits_only], a node that is not a visit contributes nothing: the other
   nodes of a segment are auxiliary predicates of the check, among them the
   ones naming the checked side's term alternatives, whose clause bodies hold
   that side's strategy constants, so their losing conditions cut a region
   into slices bounded by those constants rather than restoring where the
   ranked side's own move is right.  Contract: the result is a sub-list of
   [at_point conds params ~point ~vars] (the whole of it when [visit] or not
   [visits_only], empty otherwise), so it only drops narrowing conditions; a
   region narrowed by it contains the region narrowed by [at_point] and is
   contained in the unnarrowed one, and still contains the play's pair. *)
let at_node ~visits_only ~visit conds params ~point ~vars =
  if visits_only && not visit then [] else at_point conds params ~point ~vars
