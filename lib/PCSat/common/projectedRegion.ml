(* A validation counterexample generalised from the model's point to a region
   over the clause's ATOM ARGUMENTS only, with every other variable of the
   clause projected out by model-based projection.

   The validator finds a model [M] of [not phi], where [phi] is a clause with
   the current candidate substituted for its unknowns.  Recorded as it is, the
   example is the clause's instance at [M]: a point, carrying whatever values
   the solver picked for variables nothing forced.  Write the clause as
   [pure(xK, xE) \/ atoms(xK)], where [xK] are the variables occurring in the
   arguments of its unknown applications and [xE] the others.  The example
   built here is

       forall xK. G(xK) => atoms(xK)

   where [G] is a model-based projection of the cell of [not phi] at [M] onto
   [xK]: the conjunction of the literals [M] makes true in [not phi] (a true
   side of each disjunction, conditional terms settled at [M]), with [xE]
   eliminated (Komuravelli, Gurfinkel and Chaki, "SMT-based model checking for
   recursive programs", CAV 2014; per theory as Bjørner and Janota, "Playing
   with quantified satisfaction", LPAR-20 short papers, 2015, give it).

   THE OBLIGATION, and it is checked per example rather than believed:
   [G(xK) => exists xE. not phi(xK, xE)] is valid.  Since [not phi] is
   [not pure /\ not atoms_c] and the candidate's atoms [atoms_c] mention only
   [xK], that one validity question gives both properties wanted:
   - IMPLIED: [G => exists xE. not pure], so every model of the clause
     satisfies the example (fix [xK] in [G], take the witness [xE]; the clause
     there is [pure \/ atoms], whose first disjunct is false);
   - REFUTES: every point of [G] falsifies the candidate's atoms, so the
     example excludes the candidate everywhere in its region.
   A model-based projection guarantees [M |= G] and [G => exists xE. cell];
   the code checks the first by evaluation and the obligation by one Z3
   validity question, so a wrong projection costs the region and never
   soundness.  The model's point satisfies [G], so the region example implies
   the point example it generalises.

   THE POINT IS KEPT BESIDE THE REGION by the caller.  A consumer that grounds
   an example's integer parameters at a default point (the template
   synthesizer's default strategy, the labeler's instantiation) reads a region
   that excludes that point as a vacuous example; recording a region IN PLACE
   of the point would leave such a consumer with nothing, and the loop
   returns the same counterexample round after round.

   Only arithmetic and Boolean variables are projected: a variable of any
   other sort among [xE] stays a parameter (it joins [xK]).  A clause whose
   [not phi] mentions a term the theory leaves open is refused, since a
   validity question about it would be read in one model only. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

let event name = Common.PhaseTime.event_here ~in_copy:false name

let refuse reason =
  event ("projected-region-refused-" ^ reason);
  Error reason

let projectable s =
  Term.is_int_sort s || Term.is_real_sort s || Term.is_bool_sort s

let atom_vars atoms =
  Set.concat_map atoms ~f:(fun atom -> Atom.term_sort_env_of atom)

(* [example ?id ?timeout_ms ?mutate ?verify ?discharge ~fenv ~exi_senv ~clause
   ~refuted model]: the projected-region example of the counterexample [model]
   to [clause] under the candidate, [refuted] being [clause] with the
   candidate substituted (so [model] satisfies [not refuted]).

   Pre: [clause] has the clause's variables free and its unknowns applied;
   [refuted] is equivalent to [clause] under the candidate; [model] is a model
   of [not refuted].
   Post: an [Ok ex] is [forall xK. G(xK) => atoms(xK)] with [G] true at the
   model and Z3 having proved [G => exists xE. not refuted]; [xE] is nonempty
   (a region with nothing projected is [WfRegion]'s, or the point's).
   [Error reason] otherwise.  Never raises except asynchronously.

   [mutate] and [verify] exist for the property test only: [mutate] rewrites
   [G] before it is checked, and [verify:false] skips the validity question,
   so that the test can show its own checks catch a wrong region. *)
let example ?(id = None) ?(timeout_ms = 1000) ?(mutate = Fn.id)
    ?(verify = true) ?discharge ~fenv ~exi_senv ~clause ~refuted
    (model : model) =
  try
    match WfRegion.clause_triple exi_senv clause with
    | None -> refuse "not-one-clause"
    | Some (ps, ns, _pure) -> (
        if Set.is_empty ps && Set.is_empty ns then refuse "no-atom"
        else
          let neg = Evaluator.simplify @@ Formula.mk_neg refuted in
          if ClauseOld.interpretation_dependent neg then
            refuse "interpretation-dependent"
          else
            let kept0 = atom_vars (Set.union ps ns) in
            let all_vars = Formula.term_sort_env_of neg in
            let kept_names = Set.Poly.map kept0 ~f:fst in
            let elim, nonproj =
              Set.partition_tf
                (Set.filter all_vars ~f:(fun (x, _) ->
                     not (Set.mem kept_names x)))
                ~f:(fun (_, s) -> projectable s)
            in
            let kept = Set.union kept0 nonproj in
            if Set.is_empty elim then refuse "nothing-to-project"
            else if Set.is_empty kept then refuse "ground-atoms"
            else
              match
                WfRegion.completed_model model (Set.union all_vars kept)
              with
              | None -> refuse "model-incomplete"
              | Some map -> (
                  match WfRegion.cell ~map neg with
                  | Error _ -> refuse "no-cell"
                  | Ok cell -> (
                      let g =
                        Interpolation.MbpProject.get_mbp_with
                          ~conditionals:Interpolation.MbpProject.Model_path_for_targets
                          ~check_validity:false
                          ~print:(fun _ -> ())
                          map elim cell
                      in
                      let g = mutate g in
                      if
                        Set.exists (Formula.term_sort_env_of g)
                          ~f:(fun (x, _) ->
                            Set.exists elim ~f:(fun (y, _) ->
                                Ident.tvar_equal x y))
                      then refuse "projection-left-a-variable"
                      else if
                        not
                          (try Evaluator.eval (Formula.subst map g)
                           with exn when not (Common.Timer.is_async exn) ->
                             false)
                      then refuse "point-outside"
                      else
                        let goal =
                          Formula.mk_imply g
                            (Formula.exists (Set.to_list elim) neg)
                        in
                        if verify && Z3Smt.Z3interface.may_not_return goal then
                          refuse "may-not-return"
                        else
                          match
                            if verify then
                              Z3Smt.Z3interface.check_valid ~id
                                ~timeout:(Some timeout_ms) fenv goal
                            else `Valid
                          with
                          | `Valid -> (
                              match
                                ExClause.make ?discharge exi_senv ps ns
                                  (Formula.mk_neg g)
                              with
                              | None -> refuse "vacuous"
                              | Some ex ->
                                  event "projected-region-built";
                                  Ok
                                    (ExClause.normalize_params
                                       (Map.key_set exi_senv) ex))
                          | `Invalid _ -> refuse "solver-refutes"
                          | _ -> refuse "undecided")))
  with exn when not (Common.Timer.is_async exn) -> refuse "raised"
