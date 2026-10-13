open Core
open Common.Ext
open Common.Combinator
open LogicOld

type pred = sort_env_map * Formula.t
type papp = pred_bind * Term.t list
type ppapp = pred * papp

type t =
  | FCon of pred
  | PApp of papp
  (* non-parametric atom *)
  (* assume that papp is ground *)
  | PPApp of ppapp (* parametric atom *)

(* An atom is a member of an example clause's atom sets, whose comparator
   looks at the tree shape of the atom's parameter map; every constructor and
   transformer below therefore returns the map in canonical shape (see
   [Common.Ext.Set.canon]). *)
(* An example is universally quantified over its parameters, so two that differ
   only by a bijection on them are the SAME example -- and every consumer that
   keys on the atom told them apart, because the canonical form below normalised
   the shape of the parameter map and not the names in it.  A refutation needs
   two atoms to be the same one, so a resolution that generalises a position and
   a resolution that generalises it again produced [$28] and [$35] and never
   met; a truth table gave them two rows, two evaluations and two sets of
   undecided cells.

   The names are therefore canonicalised too: the parameters are numbered by
   their first occurrence in a fixed traversal of the guard and then the
   arguments, so a renaming does not change the result and anything else does.
   Only parameters are renamed -- the guard's other variables are the
   predicate's own and mean what they say. *)
let canon_params (params, cond) args =
  if Map.Poly.is_empty params then ((params, cond), args)
  else
    (* every constructor goes through here, so an atom with no parameters --
       which is most of them -- must not pay for the traversal below *)
    let order =
      (* first occurrence, guard before arguments; [fvs_of] is a set, so the
         order has to come from the term structure rather than from it *)
      let seen = ref [] in
      let note x =
        if Map.Poly.mem params x && not (List.mem !seen x ~equal:Stdlib.( = ))
        then seen := x :: !seen
      in
      List.iter (Formula.terms_of cond |> Set.to_list) ~f:(fun t ->
          Set.iter (Term.tvs_of t) ~f:note);
      Set.iter (Formula.tvs_of cond) ~f:note;
      List.iter args ~f:(fun t -> Set.iter (Term.tvs_of t) ~f:note);
      List.rev !seen
    in
    let ren =
      Map.Poly.of_alist_exn
      @@ List.filter_mapi order ~f:(fun i x ->
          Option.map (Map.Poly.find params x) ~f:(fun srt ->
              (x, Term.mk_var (Ident.Tvar (sprintf "$c%d" i)) srt)))
    in
    if Map.Poly.is_empty ren then ((Map.canon params, cond), args)
    else
      let params' =
        Map.Poly.fold params ~init:Map.Poly.empty ~f:(fun ~key ~data acc ->
            match Map.Poly.find ren key with
            | Some (Term.Var (y, _, _)) -> Map.Poly.set acc ~key:y ~data
            | _ -> Map.Poly.set acc ~key ~data)
      in
      ( (Map.canon params', Formula.subst ren cond),
        List.map args ~f:(Term.subst ren) )

let canon = function
  | FCon (params, phi) -> FCon (Map.canon params, phi)
  | PApp _ as atm -> atm
  | PPApp ((params, cond), papp) -> PPApp ((Map.canon params, cond), papp)

(* [canon] runs at every construction and must stay cheap; the parameter
   renaming above walks the guard and the arguments, which measured at 13 of 120
   benchmarks no longer answering inside their budget when it was done there.
   It is wanted only where an atom is used as a KEY -- a truth-table row, a set
   element -- so it is applied at those points instead of at every construction.
   The verdicts did not move either way: this is a cost, not a semantics. *)
let canon_key = function
  | FCon (params, phi) ->
      let (params, phi), _ = canon_params (params, phi) [] in
      FCon (params, phi)
  | PApp _ as atm -> atm
  | PPApp ((params, cond), (pb, args)) ->
      let pred, args = canon_params (params, cond) args in
      PPApp (pred, (pb, args))

let mk_fcon pred = canon (FCon pred)
let mk_true () = mk_fcon (Map.Poly.empty, Formula.mk_true ())

(* Is this the atom [mk_true] builds?  It is worth a name because of who builds
   it: validation returns exactly this example when the solver can neither
   confirm nor refute a clause under the candidate -- the candidate is rejected
   and nothing is learnt -- so a [( => true)] in the example set is not a fact
   about the problem but a record that a round decided nothing.  Counting them
   separates two failures that look identical from outside: a loop whose
   validation decides and whose labeling cannot orient what it gets, and a loop
   whose validation decides nothing at all.  Measured on one input of each:
   302 counterexamples and no vacuous ones against 172 counterexamples all of
   which are vacuous. *)
let is_vacuous = function
  | FCon (params, phi) -> Map.Poly.is_empty params && Formula.is_true phi
  | _ -> false
let mk_false () = mk_fcon (Map.Poly.empty, Formula.mk_false ())
let mk_papp pvar sorts args = PApp ((pvar, sorts), args)
let mk_ppapp pred pvar sorts args = canon (PPApp (pred, ((pvar, sorts), args)))

let of_old_atom ?(bvs = Set.Poly.empty) exi_senv cond = function
  | Atom.App (Predicate.Var (pvar, sorts), terms, _) ->
      let param_senv =
        Set.Poly.union_list
          (Formula.sort_env_of cond
          :: List.map terms
               ~f:(Term.sort_env_of >> Set.filter ~f:(fst >> Set.mem bvs >> not))
          )
      in
      if
        Set.is_empty param_senv
        && (Formula.is_true cond || Formula.is_false cond)
      then mk_papp pvar sorts terms
      else
        let map =
          let s =
            Set.filter param_senv ~f:(fst >> Map.Poly.mem exi_senv >> not)
          in
          try Map.of_set_exn s
          with exn_ when not (Common.Timer.is_async exn_) ->
            failwith @@ str_of_sort_env_list Term.str_of_sort @@ Set.to_list s
        in
        mk_ppapp (map, cond) pvar sorts terms
  | Atom.App (Psym _, _, _) as atom -> (
      try if Evaluator.eval_atom atom then mk_true () else mk_false ()
      with exn_ when not (Common.Timer.is_async exn_) ->
        let param_senv = Atom.sort_env_of atom in
        mk_fcon
          ( Map.of_set_exn
            @@ Set.filter param_senv ~f:(fst >> Map.Poly.mem exi_senv >> not),
            Formula.mk_atom atom ))
  | atom ->
      failwith @@ "only atoms can be converted into examples. error with : "
      ^ Atom.str_of atom

(* A guarded example atom says [cond => P(ts)].  A solution has to make it
   hold in every model of the background theory, so the guard forces [P(ts)]
   only in the models where [cond] holds, and dropping it is licensed only when
   [cond] is VALID; a guard that is merely satisfiable licenses nothing.  Two
   examples guarded by [o = 0] and [o <> 0] over an open term [o] would, with
   both guards dropped, be [P(t)] and [not P(t)] and refute a satisfiable
   problem ([P(x) := (o = 0)] satisfies both in every model).

   This predicate is the NECESSARY half, what makes the atom itself the same
   claim in every model: [cond] is ground -- no variable, no dummy constant,
   which are universally quantified -- and the atom's arguments contain no term
   the theory leaves open.  [P (tl nil)] fails the second test: which value it
   names depends on the very model the guard constrains, and two such atoms
   under different guards may be about different values.  The caller still has
   to establish that [cond] is valid before dropping it. *)
let guard_dischargeable cond = function
  | Atom.App (Predicate.Var _, _, _) as atom ->
      Set.is_empty (Formula.term_sort_env_of cond)
      && not (ClauseOld.interpretation_dependent (Formula.mk_atom atom))
  | _ -> false

(* [of_old_atom] for a guard that is already known to hold in SOME model --
   what a constraint still says once a Z3 model's values are substituted, the
   model itself being the witness.  Satisfiable is not valid, so the model
   licenses dropping the guard only where the two coincide: a ground guard
   over symbols the theory interprets has one truth value in every model, and
   true in one is true in all.  A guard that mentions a term the theory leaves
   open (a selector on the wrong constructor, a division by zero, an
   out-of-range sequence read, an uninterpreted symbol) is true in the model
   the solver picked and may be false in another, so it is kept; the conflict
   test that compares two examples conjoins their guards, which is the sound
   use of it.  Assumes nothing of [cond]; guarantees the result claims no more
   than [cond => P(ts)] in every model. *)
let of_old_atom_known_sat ?bvs exi_senv cond atom =
  let cond =
    if
      guard_dischargeable cond atom
      && not (ClauseOld.interpretation_dependent cond)
    then Formula.mk_true ()
    else cond
  in
  of_old_atom ?bvs exi_senv cond atom

let of_ground_atom cond exi_senv t =
  of_old_atom exi_senv cond
  @@ Logic.ExtTerm.to_old_atm exi_senv Map.Poly.empty t

let is_fcon = function FCon _ -> true | _ -> false
let is_papp = function PApp _ -> true | _ -> false
let is_ppapp = function PPApp _ -> true | _ -> false

(* Does this atom say nothing at all?  A guarded atom means [cond => +-P(t)],
   so where [cond] is unsatisfiable it holds for every [P] and constrains
   nothing.  This happens after instantiation: a parameter is replaced by a
   default point that does not read the guard, and a guard such as [$1 >= 1]
   becomes [false].  The atom keeps its guard in the value, so it is still a
   distinct key, and two such atoms from DIFFERENT examples whose guards both
   became [false] are equal keys -- a propositional encoding that gives each
   key one variable then reads [false => P(t)] and [false => not P(t)] as
   [p] and [not p], a contradiction between two claims that apply nowhere.
   Only a guard that simplifies to [false] is recognised -- no solver is
   asked -- so a guard that is unsatisfiable without simplifying to [false]
   is not caught here; after instantiation at concrete points of a decided
   theory the simplifier settles the guard either way.
   An [FCon] is a pure literal of the clause, not a guard, and a false one is
   an ordinary false disjunct, so it is never vacuous.  Not [is_vacuous]
   above, which recognises the [( => true)] a round records when it learnt
   nothing -- a different emptiness, of a whole example rather than a guard. *)
let guard_is_false = function
  | PPApp ((_, phi), _) -> (
      Formula.is_false phi
      ||
      try Formula.is_false (Evaluator.simplify phi)
      with exn_ when not (Common.Timer.is_async exn_) -> false)
  | PApp _ | FCon _ -> false

(* Drop a parametric atom's guard, leaving the bare application.  Sound only
   under an interpretation in which the guard holds, so the caller must have
   established that *all* the guards it is dropping are jointly satisfiable:
   a solution has to work for every interpretation of a universally quantified
   sort, so a refutation may pick one, and in one where every guard is true
   [cond => P(t̄)] is [P(t̄)].  Dropping them one at a time would not be sound
   together. *)
let discharge_guard = function
  | PPApp ((_, _), papp) -> canon (PApp papp)
  | atom -> atom

let pvar_of = function
  | PApp ((pvar, _), _) | PPApp (_, ((pvar, _), _)) -> Some pvar
  | _ -> None

let sorts_of = function
  | PApp ((_, sorts), _) | PPApp (_, ((_, sorts), _)) -> Some sorts
  | _ -> None

let pvar_sorts_of = function
  | PApp ((pvar, sorts), _) | PPApp (_, ((pvar, sorts), _)) -> Some (pvar, sorts)
  | _ -> None

let tvs_of = function
  | FCon (_, phi) -> Formula.tvs_of phi
  | PApp ((_, _), ts) ->
      let dms =
        Set.Poly.of_list @@ List.map ~f:fst @@ LogicOld.get_dummy_term_senv ()
      in
      assert (
        List.for_all ts ~f:(fun t -> Set.is_subset (Term.tvs_of t) ~of_:dms));
      Set.Poly.empty
  | PPApp ((_, phi), ((_, _), ts)) ->
      Set.Poly.union_list (Formula.tvs_of phi :: List.map ~f:Term.tvs_of ts)

let args_of = function
  | FCon (_, _) -> None
  | PApp ((_, _), ts) -> Some ts
  | PPApp ((_, _), ((_, _), ts)) -> Some ts

let params_of = function
  | FCon (param_senv, _) -> param_senv
  | PApp (_, _) -> Map.Poly.empty
  | PPApp ((param_senv, _), _) -> param_senv

let to_old_atom = function
  | FCon (_, phi) ->
      if Formula.is_true phi then Some (Map.Poly.empty, Atom.mk_true ())
      else if Formula.is_false phi then Some (Map.Poly.empty, Atom.mk_false ())
      else None (*ToDo*)
  | PApp ((pvar, sorts), terms) ->
      Some (Map.Poly.empty, Atom.mk_pvar_app pvar sorts terms)
  | PPApp ((param_senv, phi), ((pvar, sorts), terms)) ->
      if Formula.is_true phi then
        Some (param_senv, Atom.mk_pvar_app pvar sorts terms)
      else None (*ToDo*)

let to_old_atom_with_phi = function
  | FCon (_, phi) when Fn.non Formula.is_true phi -> (phi, None)
  | PPApp ((param_senv, phi), ((pvar, sorts), terms))
    when Fn.non Formula.is_true phi ->
      (phi, Some (param_senv, Atom.mk_pvar_app pvar sorts terms))
  | atm -> (Formula.mk_true (), to_old_atom atm)

let to_atom atm =
  match to_old_atom atm with
  | None -> None
  | Some (param_senv, atm) -> Some (param_senv, Logic.ExtTerm.of_old_atom atm)

let to_old_formula pos = function
  | FCon (param_senv, phi) ->
      (param_senv, (if pos then Fn.id else Formula.mk_neg ~info:Dummy) phi)
  | PApp ((pvar, sorts), terms) ->
      ( Map.Poly.empty,
        (if pos then Fn.id else Formula.mk_neg ~info:Dummy)
        @@ Formula.mk_atom
        @@ Atom.mk_pvar_app pvar sorts terms )
  | PPApp ((param_senv, phi), ((pvar, sorts), terms)) ->
      let papp =
        (if pos then Fn.id else Formula.mk_neg ~info:Dummy)
        @@ Formula.mk_atom
        @@ Atom.mk_pvar_app pvar sorts terms
      in
      ( param_senv,
        if Formula.is_true phi then papp else Formula.mk_imply phi papp )

let to_formula pos atm =
  let param_senv, phi = to_old_formula pos atm in
  (param_senv, Logic.ExtTerm.of_old_formula phi)

let to_old_formula_and_cond = function
  | FCon (param_senv, phi) -> (param_senv, phi, Formula.mk_true ())
  | PApp ((pvar, sorts), terms) ->
      ( Map.Poly.empty,
        Formula.mk_true (),
        Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts terms )
  | PPApp ((param_senv, phi), ((pvar, sorts), terms)) ->
      (param_senv, phi, Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts terms)

(* let cond_map_of ~id fenv cond =
   if Formula.is_true cond then Map.Poly.empty
   else
     match Z3Smt.Z3interface.check_sat ~id fenv [ cond ] with
     | `Sat model ->
         List.fold_left model ~init:Map.Poly.empty
           ~f:(fun ret ((tvar, _), term) ->
             match term with
             | None -> ret
             | Some t ->
                 Map.Poly.set ret ~key:tvar ~data:(Logic.ExtTerm.of_old_term t))
     | _ -> Map.Poly.empty *)

let to_formula_and_cond atm =
  let param_senv, cond, atm = to_old_formula_and_cond atm in
  ( param_senv,
    Logic.ExtTerm.of_old_formula cond,
    Logic.ExtTerm.of_old_formula atm )

let str_of_papp ((Ident.Pvar ident, _), terms) =
  sprintf "%s(%s)" ident
  @@ String.concat_mapi_list ~sep:", " terms ~f:(fun _i t ->
      (*sprintf "[x%d] %s" (i+1) @@*)
      let str = Term.str_of ~priority:Priority.comma ~c_style:false t in
      if false then
        String.paren @@ str ^ " : " ^ Term.str_of_sort (Term.sort_of t)
      else str)

let str_of = function
  | FCon (_, phi) -> Formula.str_of phi
  | PApp papp -> str_of_papp papp
  | PPApp ((_, phi), papp) ->
      if Formula.is_true phi then sprintf "%s" (str_of_papp papp)
      else
        (* A guarded atom means [cond ==> P(args)], and it used to print as
           "(cond | P(args))", which reads as the disjunction [cond \/ P(args)]
           -- a different formula, since the equivalent one is [~cond \/
           P(args)] -- and gives no clue which side is the guard.  An example
           clause is the main evidence a reader has about what the loop is
           doing, and one printed this way was read three ways in one
           investigation, twice confidently and wrongly.  The guard goes in
           brackets in front. *)
        sprintf "[%s] %s" (Formula.str_of phi) (str_of_papp papp)

let normalize_pred tvs (param_senv, phi) =
  let phi' = Normalizer.normalize @@ Evaluator.simplify phi in
  let param_senv' =
    Map.Poly.filteri param_senv ~f:(fun ~key:v ~data:_ -> Set.mem tvs v)
  in
  (param_senv', phi')

let normalize_papp (target, terms) =
  ( target,
    List.map terms ~f:(fun term ->
        let term' =
          Normalizer.normalize_term
          @@ Evaluator.simplify_term term (*ToDo: check*)
        in
        try Term.of_value (get_dtenv ()) @@ Evaluator.eval_term term'
        with exn_ when not (Common.Timer.is_async exn_) -> term') )

let normalize = function
  | FCon pred as t -> FCon (normalize_pred (tvs_of t) pred)
  | PApp papp -> PApp (normalize_papp papp)
  | PPApp (pred, papp) as t ->
      PPApp (normalize_pred (tvs_of t) pred, normalize_papp papp)

let normalize atm = canon (normalize atm)

(* Fix the sign of every integer or real equation and disequation in the guard
   and inside the arguments (a Boolean argument can embed a formula), so that
   [e = 0] and [-e = 0] -- the same constraint -- become one value.  Which sign
   [normalize] leaves depends on the names the variables had when it ran, and a
   parametric example is normalised before its parameters are renamed to their
   canonical names, so two derivations of one example can reach the example set
   spelled differently and be kept as two.  Call this after the renaming: the
   sign is then chosen from names that no longer depend on the derivation.
   Preserves the meaning of the atom exactly (each rewritten atom is equivalent
   to the original), and is idempotent. *)
let canon_eq_signs atm =
  let fphi = Normalizer.canon_eq_signs in
  let fterm =
    Term.map_atom ~f:(fun a -> Normalizer.canon_eq_signs (Formula.mk_atom a))
  in
  canon
  @@
  match atm with
  | FCon (params, phi) -> FCon (params, fphi phi)
  | PApp (target, terms) -> PApp (target, List.map terms ~f:fterm)
  | PPApp ((params, cond), (target, terms)) ->
      PPApp ((params, fphi cond), (target, List.map terms ~f:fterm))

(* A parametric example means [forall params. cond => +-P(t)], so instantiating
   it at *any* point for its parameters yields a consequence of it: the choice
   below cannot make the example say more than it already did, and is sound
   whichever point it takes.  What the choice decides is how much the instance
   says.  The default point is [T_dt.mk_dummy_for], which does not look at
   [cond] at all -- an integer parameter becomes 0 -- so wherever the condition
   constrains that parameter the point lands outside the region the example is
   about and the instance degenerates to [false => +-P(t)], which constrains
   nothing.  A degenerate instance is not wrong, but it is not an example
   either, and two of them from different examples agree on everything, which
   is how a conflict was once claimed between two examples that apply nowhere.

   [?sat_point] is the chance to choose a point the condition admits instead:
   it is given the parameters and the condition and returns a substitution, or
   [None] when it cannot find one -- in which case the dummy point is used
   exactly as before, so an unavailable or failing solver costs only the
   generality it would have bought.  The solver is passed in rather than called
   here because this module sits below the solver interface, which is the same
   arrangement the three-valued qualifier evaluation uses. *)

(* How often a parametric atom was instantiated, and how often the point taken
   falsified the condition.  The second is the exposure of the choice above:
   where it stays at zero the default point is costing nothing on that input,
   and there is nothing for a satisfying point to buy. *)
let instantiations = ref 0

let vacuous_instantiations = ref 0
let instantiation_counts () = (!instantiations, !vacuous_instantiations)

let clear_instantiation_counts () =
  instantiations := 0;
  vacuous_instantiations := 0

let dummy_point param_senv =
  Map.Poly.mapi param_senv ~f:(fun ~key ~data -> T_dt.mk_dummy_for key data)

let point_for ?sat_point param_senv phi =
  if Map.Poly.is_empty param_senv then Map.Poly.empty
  else
    match sat_point with
    | None -> dummy_point param_senv
    | Some choose -> (
        match choose param_senv phi with
        | Some sub -> sub
        | None -> dummy_point param_senv)

let count_instance phi =
  incr instantiations;
  if Formula.is_false phi then incr vacuous_instantiations

let instantiate_gen ?sat_point = function
  | FCon (param_senv, phi) ->
      (* not counted: the counters below are about parametric *atoms*, and
         asking whether this arm's result is [false] would cost a
         simplification on a path that does not need one *)
      let sub = point_for ?sat_point param_senv phi in
      FCon (Map.Poly.empty, Formula.subst sub phi)
  | PApp papp -> PApp papp
  | PPApp ((param_senv, phi), (target, terms)) -> (
      let sub = point_for ?sat_point param_senv phi in
      let phi = Evaluator.simplify @@ Formula.subst sub phi in
      count_instance phi;
      let terms =
        List.map terms
          ~f:(Term.subst sub >> Term.elim_let >> Evaluator.simplify_term)
      in
      try
        if
          Evaluator.eval phi
          (* a [PApp]'s arguments may mention dummy constants -- that is what
             [tvs_of] asserts of one -- and a parameter of a sort variable is
             instantiated at exactly such a constant ([T_dt.mk_dummy_for]).
             Demanding *closed* arguments left every forall-sort instance a
             [PPApp] even when its condition held at the instance, and the
             consumers that keep only [PApp]s (the labeler's WF/NWF/Parity/FN
             cycle learning) therefore never saw one. *)
          && List.for_all terms ~f:(fun t ->
              Set.for_all (Term.fvs_of t) ~f:(fun x ->
                  LogicOld.is_dummy_term x None))
        then
          PApp
            ( target,
              terms
              (*List.map terms ~f:(Evaluator.eval_term >> Term.of_value (get_dtenv ()))*)
            )
        else PPApp ((Map.Poly.empty, phi), (target, terms))
      with exn_ when not (Common.Timer.is_async exn_) ->
        PPApp ((Map.Poly.empty, phi), (target, terms)))

let instantiate atm = instantiate_gen atm

(* assume all parameters in phi/ts are in dom(map) *)
let rename map = function
  | FCon (params, phi) ->
      FCon
        ( Map.rename_keys_and_drop_unused ~f:(Map.Poly.find map)
            params (* Could have a parameter not in phi *),
          Formula.rename map phi )
  | PApp ((pvar, sorts), ts) ->
      PApp ((pvar, sorts), List.map ~f:(Term.rename map) ts)
  | PPApp ((params, phi), ((pvar, sorts), ts)) ->
      PPApp
        ( ( Map.rename_keys_and_drop_unused ~f:(Map.Poly.find map)
              params (* Could have a parameter not in phi and ts *),
            Formula.rename map phi ),
          ((pvar, sorts), List.map ~f:(Term.rename map) ts) )

let rename map atm = canon (rename map atm)

let subst sub = function
  | FCon (senv, phi) -> FCon (senv, Formula.subst sub phi)
  | PApp (pred, terms) -> PApp (pred, List.map terms ~f:(Term.subst sub))
  | PPApp ((senv, phi), (pred, terms)) ->
      let senv' =
        Map.Poly.filteri senv ~f:(fun ~key ~data:_ ->
            not @@ Map.Poly.mem sub key)
      in
      PPApp
        ( (senv', Formula.subst sub phi),
          (pred, List.map terms ~f:(Term.subst sub)) )

let subst sub atm = canon (subst sub atm)

let iterate_senv (senv, his) atom =
  let ref_senv = ref [] in
  let ref_his = ref his in
  match atom with
  | FCon (params, phi) ->
      Formula.iter_term phi ~f:(function
        | Term.Var (t, s, _)
          when Map.Poly.mem params t && (not @@ Set.mem !ref_his t) ->
            ref_senv := (t, s) :: !ref_senv;
            ref_his := Set.add !ref_his t
        | _ -> ());
      (!ref_senv @ senv, !ref_his)
  | PApp _ -> (senv, his)
  | PPApp ((params, phi), (_, ts)) ->
      List.iter ts ~f:(fun t ->
          Term.iter_term t ~f:(function
            | Term.Var (t, s, _)
              when Map.Poly.mem params t && (not @@ Set.mem !ref_his t) ->
                ref_senv := (t, s) :: !ref_senv;
                ref_his := Set.add !ref_his t
            | _ -> ()));
      Formula.iter_term phi ~f:(function
        | Term.Var (t, s, _)
          when Map.Poly.mem params t && (not @@ Set.mem !ref_his t) ->
            ref_senv := (t, s) :: !ref_senv;
            ref_his := Set.add !ref_his t
        | _ -> ());
      (!ref_senv @ senv, !ref_his)

let iterate_vars bvs = function
  | FCon (_params, phi) ->
      (*let s = Map.Poly.key_set params in*)
      let tvs_set = (*Set.inter s @@*) Set.diff (Formula.fvs_of phi) bvs in
      (Set.union bvs tvs_set, Set.to_list tvs_set)
  | PApp (_, _) -> (bvs, [])
  | PPApp ((_params, phi), (_, ts)) ->
      (*let s = Map.Poly.key_set params in*)
      let tvs_set = (*Set.inter s @@*) Set.diff (Formula.fvs_of phi) bvs in
      List.fold_left ts
        ~init:Set.(union bvs tvs_set, to_list tvs_set)
        ~f:(fun (bvs, tvs) t ->
          let tvs_set' =
            (*Set.inter s @@*) Set.diff (Term.tvs_of (*ToDo*) t) bvs
          in
          (Set.union bvs tvs_set', tvs @ Set.to_list tvs_set'))

let normalize_params atm =
  let _, tvs = iterate_vars Set.Poly.empty atm in
  let map =
    Map.Poly.of_alist_exn
    @@ List.mapi tvs ~f:(fun i x ->
        (x, Ident.mk_dontcare (string_of_int (i + 1))))
  in
  rename map atm

let exists ~f = function
  | FCon _ -> false
  | PApp (_, terms) | PPApp (_, (_, terms)) -> List.exists ~f terms

(* The variables at the existential positions of an unguarded atom of a total
   predicate, when that atom is refuted by totality alone: [totpvs] maps each
   total predicate to its universally quantified positions, and the atom
   qualifies when every other position is a parameter, pairwise distinct and
   absent from the atom's universal positions.  Then [forall v. not P(t, v)]
   contradicts [forall u. exists v. P(u, v)] at [u = t].  A guarded atom does
   not qualify: [cond => not P] is vacuous where [cond] fails, so totality does
   not refute it.  The caller must still check that the returned variables
   occur nowhere else in the clause. *)
let total_atm_vars totpvs atm =
  match atm with
  | PApp ((pvar, _), terms) | PPApp (_, ((pvar, _), terms)) -> (
      let guarded =
        match atm with
        | PPApp ((_, phi), _) -> Fn.non Formula.is_true phi
        | _ -> false
      in
      match Map.Poly.find totpvs (Ident.pvar_to_tvar pvar) with
      | Some u when not guarded ->
          let params = params_of atm in
          let us, vs =
            List.partition_tf (List.mapi terms ~f:(fun i t -> (i, t)))
              ~f:(fun (i, _) -> List.mem u i ~equal:Int.equal)
          in
          let vars =
            List.map vs ~f:(function
              | _, Term.Var (x, _, _) when Map.Poly.mem params x -> Some x
              | _ -> None)
          in
          if List.exists vars ~f:Option.is_none then None
          else
            let vars = List.filter_opt vars in
            let in_us =
              Set.Poly.union_list
                (List.map us ~f:(fun (_, t) -> Term.tvs_of t))
            in
            if
              List.contains_dup vars ~compare:Ident.tvar_compare
              || List.exists vars ~f:(Set.mem in_us)
            then None
            else Some (Set.Poly.of_list vars)
      | _ -> None)
  | FCon _ -> None

(* type t =
   | FCon of pred
   | PApp of papp (* non-parametric atom *) (* assume that papp is ground *)
   | PPApp of ppapp (* parametric atom *)
*)
let equal atm1 atm2 =
  match (atm1, atm2) with
  | FCon (_, phi1), FCon (_, phi2) -> Stdlib.(phi1 = phi2)
  | PApp (_, ts1), PApp (_, ts2) -> Stdlib.(ts1 = ts2)
  | PPApp ((_, phi1), (_, ts1)), PPApp ((_, phi2), (_, ts2)) ->
      Stdlib.(phi1 = phi2) && Stdlib.(ts1 = ts2)
  | _, _ -> false

(* Do two argument lists of one predicate fail to meet for a reason visible without a solver?
   [args_never_meet a1 a2] is [true] only when some position holds two terms of the same sort that
   are distinct in every model of the theory, read off their shape:
   - two integer literals, or two real literals, with different values;
   - two applications of datatype constructors with different names (constructors of a datatype
     are disjoint), or of one constructor whose arguments are pairwise such that some position
     never meets (constructors are injective);
   - two sequence terms built only from [seq.empty], [seq.unit] and [seq.++], whose element lists
     differ in length, or have one length and some position never meets.
   Contract: when it is [true], the conjunction of the equations [a1_i = a2_i] is false in every
   model of the theory (literals, constructors and the sequence operators above are fixed by it),
   whatever else a query conjoins with it; when it is [false] nothing is claimed, and the caller
   must ask. Lists of different lengths are never claimed to be disjoint. It inspects the terms as
   they are, without simplifying them, so a literal written as an application ([- 1] as a negation
   of [1]) is not recognised and the answer is the conservative [false]; a variable, a selector or
   any other application at a position is never claimed. The labeling's search for a positive and
   a negative example that meet asks one such conjunction per pair of atoms of a predicate, and on
   inputs whose examples are mostly ground most pairs differ at a literal position -- often one
   inside a tuple, a record or a sequence literal, which a test on top-level literals alone does
   not see: on one input whose arguments are a two-integer record and a sequence, the pairs were
   about two thirds of the solve's wall clock, every one of them a solver call answering [Unsat]. *)
let args_never_meet a1 a2 =
  (* the elements of a sequence term built from empty, unit and concatenation
     alone, in order; [None] for anything else *)
  let rec seq_elems = function
    | Term.FunApp (T_seq.SqEmpty _, [], _) -> Some []
    | Term.FunApp (T_seq.SqUnit _, [ e ], _) -> Some [ e ]
    | Term.FunApp (T_seq.SqConcat _, [ s1; s2 ], _) -> (
        match (seq_elems s1, seq_elems s2) with
        | Some l1, Some l2 -> Some (l1 @ l2)
        | _ -> None)
    | _ -> None
  in
  let rec never_meet t1 t2 =
    match (t1, t2) with
    | Term.FunApp (T_int.Int n1, [], _), Term.FunApp (T_int.Int n2, [], _) ->
        not (Z.equal n1 n2)
    | Term.FunApp (T_real.Real q1, [], _), Term.FunApp (T_real.Real q2, [], _)
      ->
        not (Q.equal q1 q2)
    | ( Term.FunApp (T_dt.DTCons (c1, _, _), ts1, _),
        Term.FunApp (T_dt.DTCons (c2, _, _), ts2, _) ) ->
        (* the two terms sit at one argument position, so they have one sort
           and the constructors belong to one datatype *)
        (not (String.equal c1 c2)) || lists_never_meet ts1 ts2
    | _ -> (
        match (seq_elems t1, seq_elems t2) with
        | Some l1, Some l2 ->
            List.length l1 <> List.length l2 || lists_never_meet l1 l2
        | _ -> false)
  and lists_never_meet l1 l2 =
    List.length l1 = List.length l2 && List.exists2_exn l1 l2 ~f:never_meet
  in
  lists_never_meet a1 a2
