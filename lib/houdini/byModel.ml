(** Judging candidate atoms by a countermodel, for the Houdini-style pre-pass of
    the PCSat validator ([houdini.questions.drop_by_model]): classic Houdini's
    conjunction question in front of the per-atom questions. Independent of the
    validator's functor, so that it can be tested on its own. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* What [model] makes of the ground instance [phi] of a candidate atom:
   [`False] or [`True] when substituting the model's values and simplifying
   decides it, [`Undecided] otherwise (a variable the model leaves out, an
   application of a function the simplifier does not evaluate, a quantifier
   it does not eliminate).  Sound in the one direction the caller relies
   on: [`False] only when [phi] is false in the model, since substitution
   and simplification preserve the value in it.  A model of an
   uninterpreted sort names its elements [<sort>!val!<n>], distinct names
   being distinct elements; the simplifier treats them as variables, so an
   equation between two of them is decided here by name. *)
let instantiate (model : model) phi =
  (* read by name and sort over [phi]: an entry a pooled context holds at
     another sort says nothing about [phi]'s variable *)
  let sub = model_assigned_subst ~target:(Formula.term_sort_env_of phi) model in
  let universe_element = function
    | Term.Var (Ident.Tvar n, _, _)
      when String.is_substring n ~substring:"!val!" ->
        Some n
    | _ -> None
  in
  let decide_elements phi =
    Evaluator.simplify
    @@ Formula.map_atom phi ~f:(fun atm ->
        match atm with
        | Atom.App
            (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op), [ t1; t2 ], _)
          -> (
            match (universe_element t1, universe_element t2) with
            | Some n1, Some n2 ->
                Formula.mk_bool
                  (Bool.equal (String.equal n1 n2)
                     (match op with T_bool.Eq -> true | _ -> false))
            | _ -> Formula.mk_atom atm)
        | _ -> Formula.mk_atom atm)
  in
  decide_elements @@ Evaluator.simplify @@ Formula.subst sub phi

let judge (model : model) phi =
  try
    let phi = instantiate model phi in
    if Formula.is_false phi then `False
    else if Formula.is_true phi then `True
    else `Undecided
  with exn_ when not (Common.Timer.is_async exn_) -> `Undecided

(* [judge] and, where it is undecided, a solver: [sat] asked of the instance
   with the model's values substituted ([`Unsat] makes it [`False]) and then
   of its negation ([`Unsat] makes it [`True]).  What the substitution leaves
   open -- a model element's name, a variable the model leaves out, a term
   the theory leaves open -- is left to the solver, so an [`Unsat] holds for
   every value of it, the model's included: sound in both directions as far
   as [sat]'s [`Unsat] is.  For an atom the simplifier does not decide: an
   application of a recursive function, or a quantifier over the model's
   arrays. *)
let judge_by_solver ~sat (model : model) phi =
  match judge model phi with
  | (`True | `False) as r -> r
  | `Undecided -> (
      try
        let phi = instantiate model phi in
        match sat phi with
        | `Unsat -> `False
        | _ -> (
            match sat (Formula.mk_neg phi) with
            | `Unsat -> `True
            | _ -> `Undecided)
      with exn_ when not (Common.Timer.is_async exn_) -> `Undecided)

(* [run ~stop ~ask ~judge ?aside atoms] is [(proved, dropped)]: [proved]
   the atoms of [atoms] whose conjunction one question [ask] proved,
   [dropped] the atoms of [atoms] and [aside] a countermodel [judge]d
   [`False].  Every other atom is left to the caller's per-atom question.

   Contract, for a clause question [body => head] whose [body] is fixed:
   [ask held] proves [body => /\ held] ([`Proved]) or gives a model of
   [body /\ ~(/\ held)] ([`Refuted m]).  Then every atom of [proved] has a
   valid per-atom question (its head is implied by the conjunction), and
   every atom of [dropped] has a per-atom question refuted by the very model
   that dropped it: the model satisfies [body], whichever conjunction it
   was found for, and the atom is false in it.  So when every per-atom
   question decides, keeping [proved], dropping [dropped] and asking the
   rest one by one keeps exactly the atoms the per-atom questions alone
   would keep.

   The loop: ask the held atoms; on a refutation judge the held atoms and
   the ones set aside, drop the ones judged [`False], and ask the rest of
   the held ones again; when a countermodel drops nothing but judges some
   held atom [`True] and some [`Undecided], set the undecided ones aside
   (their own questions decide them) and ask the [`True] ones again; stop
   on a proof, an undecided question, a countermodel that drops nothing
   otherwise, one held atom or fewer, or [stop ()].  [prejudge m atoms]
   is called once per countermodel, with every atom about to be judged
   against it, before [judge]: a place to judge them all at once.  [aside] (default
   none) are atoms never put in a conjunction, only judged against each
   countermodel: atoms whose questions are expensive in a conjunction, such
   as existentials over sequences. *)
let run ?(aside = []) ?(prejudge = fun _ _ -> ()) ~stop ~ask ~judge atoms =
  let rec loop held aside dropped =
    if List.length held <= 1 || stop () then ([], dropped)
    else
      match ask held with
      | `Proved -> (held, dropped)
      | `Undecided -> ([], dropped)
      | `Refuted model ->
          prejudge model (held @ aside);
          let split atoms =
            let judged = List.map atoms ~f:(fun a -> (a, judge model a)) in
            let with_ v =
              List.filter_map judged ~f:(fun (a, r) ->
                  if Stdlib.(r = v) then Some a else None)
            in
            (with_ `False, with_ `True, with_ `Undecided)
          in
          let f, t, u = split held in
          let af, at, au = split aside in
          let aside = at @ au and dropped = f @ af @ dropped in
          if not (List.is_empty f) then loop (t @ u) aside dropped
          else if (not (List.is_empty t)) && not (List.is_empty u) then
            loop t (u @ aside) dropped
          else ([], dropped)
  in
  loop atoms aside []
