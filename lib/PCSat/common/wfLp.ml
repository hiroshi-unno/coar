(* A candidate for a well-founded unknown built by linear programming from the
   examples that ask it to hold.

   A well-founded unknown [W] of arity [2 n] relates a source state [x] (its
   first [n] parameters) to a target state [y] (the last [n]).  Its unit
   positive examples [forall p. cond(p) => W(s(p), t(p))] each demand that the
   candidate contain the region [{(s(p), t(p)) | cond(p)}], and nothing less:
   a candidate satisfies the example exactly when it contains the region.  So
   the region is stated as it is, by rows over the two states and the
   parameters together; Farkas' lemma, stated with coefficient 0 on the
   parameters' columns, then demands containment of the region's projection
   on the states without computing the projection and without choosing a
   point.  The candidate is the one-piece lexicographic order of affine
   components (the ranking template's instance with one piece and a true
   discriminator), which is well-founded and transitive whatever the
   components are, so nothing about its well-foundedness rests on the linear
   programs' answers.  The construction is the greedy one of lexicographic
   linear rankings over a set of regions: first with coefficients in
   [-1, 1], then unbounded (Podelski and Rybalchenko, "A complete method for
   the synthesis of linear ranking functions", VMCAI 2004, for one
   component; Ben-Amram and Genaim, "Ranking functions for linear-constraint
   loops", J. ACM 2014, for lexicographic rankings, whose construction ranks
   per transition and is complete where this one, ranking each region whole
   by one component, is not).

   Only the examples with exactly one atom, positive, on [W] are read; an
   example that mentions [W] beside another atom says something the caller
   must state with the other unknowns, and is not this module's. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* [region_of ~xs ~ys atom]: the rows of [atom]'s region over the columns
   [xs @ ys @ params], where [xs] and [ys] are fresh variables for the source
   and the target and [params] the atom's parameters in a fixed order;
   [None] when [atom] is not on a predicate application, when its arity is
   not [|xs| + |ys|], when its guard or arguments read a variable that is not
   a parameter, or when the guard and the argument equations are not linear
   comparisons over numeric columns.
   Post: [Some rows] describes a set of [(x, y, params)] whose projection on
   [(x, y)] contains every pair the atom demands (equal to it over the
   rationals, larger only where a strict comparison over a real is weakened;
   see [RankingCheck.region_rows_over]). *)
let region_of ~xs ~ys (atom : ExAtom.t) =
  let state_eqs args =
    match List.zip (xs @ ys) args with
    | Ok pairs ->
        Some
          (List.map pairs ~f:(fun ((v, s), t) -> Formula.eq (Term.mk_var v s) t))
    | Unequal_lengths -> None
  in
  let read params cond args =
    let params = Map.Poly.to_alist params in
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let fvs =
      Set.Poly.union_list (Formula.tvs_of cond :: List.map args ~f:Term.tvs_of)
    in
    if not (Set.is_subset fvs ~of_:pset) then None
    else
      Option.bind (state_eqs args) ~f:(fun eqs ->
          RankingCheck.region_rows_over (xs @ ys @ params)
            (Formula.and_of (cond :: eqs)))
  in
  match atom with
  | ExAtom.PApp (_, args) -> read Map.Poly.empty (Formula.mk_true ()) args
  | ExAtom.PPApp ((params, cond), (_, args)) -> read params cond args
  | ExAtom.FCon _ -> None

(* [unit_positive_atoms pvar examples]: the atoms of the example clauses
   that consist of exactly one positive atom, on [pvar]. *)
let unit_positive_atoms pvar (examples : ExClause.t Set.Poly.t) =
  Set.to_list examples
  |> List.filter_map ~f:(fun (cl : ExClause.t) ->
         if not (Set.is_empty cl.negative) then None
         else
           match Set.to_list cl.positive with
           | [ atom ] -> (
               match ExAtom.pvar_of atom with
               | Some p when Ident.pvar_equal p pvar -> Some atom
               | _ -> None)
           | _ -> None)

(* [mixed_positive_atoms pvar examples]: the positive atoms on [pvar] of the
   example clauses that are not one positive atom on [pvar] and have no
   negative atom on [pvar] -- a pair the clause offers [pvar] as one way of
   holding, beside atoms of other unknowns. *)
let mixed_positive_atoms pvar (examples : ExClause.t Set.Poly.t) =
  let on_pvar atom =
    match ExAtom.pvar_of atom with
    | Some p -> Ident.pvar_equal p pvar
    | None -> false
  in
  Set.to_list examples
  |> List.concat_map ~f:(fun (cl : ExClause.t) ->
         let pos = List.filter (Set.to_list cl.positive) ~f:on_pvar in
         if
           Set.exists cl.negative ~f:on_pvar
           || (Set.is_empty cl.negative && Set.length cl.positive = 1)
         then []
         else pos)

(* [state_params sorts]: fresh source and target variables for a well-founded
   unknown of argument sorts [sorts]; [None] unless the arity is even, every
   sort is [Int] or [Real], and the target's sorts are the source's. *)
let state_params sorts =
  let m = List.length sorts in
  if m = 0 || m % 2 <> 0 then None
  else if
    List.exists sorts ~f:(fun s ->
        not (Term.is_int_sort s || Term.is_real_sort s))
  then None
  else
    let s1, s2 = List.split_n sorts (m / 2) in
    if not (List.equal Stdlib.( = ) s1 s2) then None
    else
      let fresh s = (Ident.mk_fresh_tvar ~prefix:(Some "WFLP_") (), s) in
      Some (List.map s1 ~f:fresh, List.map s2 ~f:fresh)

type outcome =
  | Candidate of Logic.term * string * (Z.t list * Z.t) list
      (** the lambda over the unknown's parameters, a description, and the
          components (coefficients over the source positions, constant) *)
  | Not_applicable of string
      (** a parameter that is not numeric, or an example that is not read *)
  | No_ranking  (** the construction found nothing *)

(* [candidate ~depth ~unit_first ~direct_points ~sorts pvar examples]: for a
   well-founded unknown [pvar] of argument sorts [sorts], a lambda over
   [|sorts|] parameters denoting [RankingCheck.template_order] of components
   built level by level up to [depth] components ([RankingCheck.lex_ranking]),
   first with integer coefficients and constants in [-1, 1] when
   [unit_first] (the shape the ranking template starts from), then
   unbounded -- as linear programs over the rationals, the components scaled
   to integers, when [rational] (the default), as integer programs
   otherwise.  The components rank every region of [pvar]'s unit positive
   examples (the demands); with [mixed] they are first asked to rank the
   regions of [pvar]'s positive atoms in the other examples as well
   ([mixed_positive_atoms], the offers: a pair the candidate contains makes
   its clause hold whatever the other unknowns are), and only the demands
   when no construction ranks all of them.  An offer that is not linear is
   left out; a demand that is not linear makes the route not apply.  With
   [const_ladder] (the rungs of [RankingCheck.lex_ranking ~const_first]) the
   unbounded pass asks each question first with the component's constant
   within each rung in turn and leaves it free last: the same questions are
   decided, so a candidate is found exactly when it is without the rungs;
   only which components are returned changes.  Ground examples along one
   direction otherwise let the free constant follow the examples (a constant
   one larger each round), which a constant within the problem's literals
   cannot do past the largest of them.

   Pre: [sorts] are the old-style sorts of [pvar]'s parameters.
   Post: a [Candidate (lam, _)] is closed and denotes a well-founded,
   transitive relation for any components; it contains every demand's region
   if the solver's models are right (the caller states the examples again
   anyway).  With no region read, the components are none and the candidate
   is [false].  [Not_applicable] when a parameter is not numeric or a demand
   cannot be read as linear rows, so that a caller never proposes a candidate
   blind to an example it must satisfy; [No_ranking] when the construction
   answers nothing within [depth] levels, an undecided question being read as
   "no".  Never raises except asynchronously. *)
let candidate ?(id = None) ?(timeout_ms = 1000) ?(rational = true)
    ?(mixed = true) ?const_ladder ~depth ~unit_first ~direct_points ~sorts pvar
    examples =
  (* a point a region was built for is read through its region *)
  let examples = WfRegion.without_generalised_points examples in
  try
    match state_params sorts with
    | None -> Not_applicable "a parameter that is not a numeric state"
    | Some (xs, ys) -> (
        let n = List.length xs in
        let demands =
          List.map (unit_positive_atoms pvar examples) ~f:(region_of ~xs ~ys)
        in
        if List.exists demands ~f:Option.is_none then
          Not_applicable "an example whose region is not linear"
        else
          let demands = List.filter_opt demands in
          (* an offer no ranking contains alone (a pair from a state to
             itself, a non-terminating region) can only make the joint
             construction fail, so it is left out first *)
          let offers =
            if mixed then
              List.filter_map (mixed_positive_atoms pvar examples)
                ~f:(region_of ~xs ~ys)
              |> List.filter ~f:(fun rows ->
                     Option.is_some
                       (RankingCheck.lex_ranking ~id ~timeout_ms ~rational
                          ~direct_points ~depth:1 ~n [ rows ]))
            else []
          in
          let build rows =
            let lex ?coef_bound ?const_bound ?const_first ~rational () =
              RankingCheck.lex_ranking ~id ~timeout_ms ~rational ?coef_bound
                ?const_bound ?const_first ~direct_points ~depth ~n rows
            in
            (* the unit-coefficient pass is an integer program by nature (a
               bound on rational coefficients is not preserved by scaling
               them to integers); the unbounded pass is a linear program over
               the rationals when [rational] *)
            match
              if unit_first then
                lex ~coef_bound:Z.one ~const_bound:Z.one ~rational:false ()
              else None
            with
            | Some fs -> Some fs
            | None -> lex ?const_first:const_ladder ~rational ()
          in
          (* offers that can be ranked together with the demands by one
             linear component, kept greedily in their order (one linear
             question each); a maximal set, not necessarily a maximum one *)
          let offers =
            if List.is_empty offers then []
            else
              let one rows =
                Option.is_some
                  (RankingCheck.lex_ranking ~id ~timeout_ms ~rational
                     ~direct_points ~first_ask_only:true ~depth:1 ~n rows)
              in
              if one (demands @ offers) then offers
              else
                List.fold offers ~init:[] ~f:(fun kept o ->
                    if one (demands @ kept @ [ o ]) then kept @ [ o ] else kept)
          in
          let fs, read =
            match
              if List.is_empty offers then None else build (demands @ offers)
            with
            | Some fs -> (Some fs, List.length demands + List.length offers)
            | None -> (build demands, List.length demands)
          in
          match fs with
          | None -> No_ranking
          | Some fs ->
              let var (v, s) = Term.mk_var v s in
              let phi =
                RankingCheck.template_order (List.map xs ~f:var)
                  (List.map ys ~f:var) fs
              in
              let params = Logic.of_old_sort_env_list (xs @ ys) in
              Candidate
                ( Logic.Term.mk_lambda params (Logic.ExtTerm.of_old_formula phi),
                  sprintf "%s ranking %d of %d demand(s) and %d offer(s)"
                    (RankingCheck.str_of_components fs)
                    read
                    (List.length demands)
                    (List.length offers),
                  fs ))
  with exn when not (Common.Timer.is_async exn) ->
    Not_applicable ("raised " ^ Exn.to_string exn)
