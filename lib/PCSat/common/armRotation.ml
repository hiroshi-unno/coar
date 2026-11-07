(* A teacher that rotates a counterexample through the arms of a disjunction.

   A clause whose premise is a disjunction -- a transition relation written as
   one disjunct per branch, [inv(x) /\ (x' = x + 1 \/ x' = x - 1) => rank(x, x')]
   -- is violated in every arm the candidate fails, but the solver answers the
   counterexample query with one model, and on queries of the same shape it
   keeps choosing the same arm.  Then every example comes from one branch: on a
   program that can step up or down forever, the examples are the chain
   [rank(2, 3)], [rank(3, 4)], [rank(4, 5)], ..., each refuting a candidate
   ranking that the next one extends, and the two-step cycle [rank(2, 3)],
   [rank(3, 2)] that refutes every well-founded ranking at once is never
   sampled.  A logically redundant clause elsewhere in the problem changes the
   candidates, hence the solver's choice, and can decide the run.

   This asks the query again restricted to a different arm when the model
   falls in the same arm of the same disjunction as the last counterexample
   did.  A disjunction is identified by its printed form, so only a
   disjunction that recurs from one query to the next -- one of the clause's
   own premises, not a part of a candidate, which changes every round -- is
   ever rotated; the first time a disjunction is seen its arm is only
   recorded.  The arms are tried in order after the last one, and the first
   [Sat] is used.

   Contract: [reask] returns either [model] unchanged or a model the [ask]
   callback returned for [phi] conjoined with one disjunct of a conjunct of
   [phi], hence a model of [phi] whenever [ask] answers models of the formula
   it is given.  It only chooses WHICH counterexample is used, so it cannot
   change a verdict.  Only quantifier-free top-level conjuncts with at least
   two disjuncts are considered, at most one disjunction is rotated per call,
   and a model that leaves a variable of an arm unassigned makes that
   disjunction's arm undecided and the disjunction skipped.  The state (the
   last arm per printed disjunction) is process-global. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type model = ((Ident.tvar * Sort.t) * Term.t option) list

let state : (string, int) Hashtbl.t = Hashtbl.create (module String)
let reset () = Hashtbl.clear state
let asked = ref 0
let moved = ref 0

(* the index of the first arm the model makes true, if the model decides one *)
let arm_of (model : model) arms =
  let sub =
    Map.Poly.of_alist_reduce ~f:(fun t _ -> t)
    @@ List.filter_map model ~f:(fun ((x, _), t) ->
        Option.map t ~f:(fun t -> (x, t)))
  in
  List.findi arms ~f:(fun _ arm ->
      try Formula.is_true @@ Evaluator.simplify @@ Formula.subst sub arm
      with exn when not (Common.Timer.is_async exn) -> false)
  |> Option.map ~f:fst

let reask ~(ask : Formula.t -> model option) (phi : Formula.t) (model : model) :
    model =
  let disjunctions =
    List.filter_map (Formula.conjuncts_list_of phi) ~f:(fun c ->
        let arms = Formula.disjuncts_list_of c in
        if List.length arms >= 2 && Formula.is_quantifier_free c then
          Option.map (arm_of model arms) ~f:(fun i -> (Formula.str_of c, arms, i))
        else None)
  in
  (* the first recurring disjunction whose arm repeats the last one *)
  let repeating =
    List.find disjunctions ~f:(fun (key, _, i) ->
        match Hashtbl.find state key with Some j -> i = j | None -> false)
  in
  List.iter disjunctions ~f:(fun (key, _, i) -> Hashtbl.set state ~key ~data:i);
  match repeating with
  | None -> model
  | Some (key, arms, i) ->
      let n = List.length arms in
      let rec try_arm k =
        if k >= n then model
        else
          let j = (i + k) mod n in
          incr asked;
          match ask (Formula.mk_and phi (List.nth_exn arms j)) with
          | Some model' ->
              incr moved;
              Hashtbl.set state ~key ~data:j;
              model'
          | None -> try_arm (k + 1)
      in
      try_arm 1
