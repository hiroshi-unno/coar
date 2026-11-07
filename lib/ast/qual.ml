(* Qualifier families: the atoms a solution template is built from, each a
   pair of an unknown's parameter list and a formula over those parameters.

   Most families rewrite qualifiers already extracted from the clauses --
   negations ([add_neg]), swaps and bounded permutations of same-sorted
   parameters, reflected halfspaces, homogenised forms, modulus atoms -- and
   [arg_equalities] makes equalities between same-sorted parameters out of
   nothing, for sorts the numeric domains say nothing about.  None of them
   can make an answer wrong: a qualifier only enlarges the hypothesis space,
   and every candidate built from one is validated; a missing qualifier only
   narrows the space.  What they cost is search.

   [extract_terms_from_quals] turns the qualifiers that mention a functional
   unknown's result parameter into candidate result terms (by affine solving
   for numeric results, otherwise by asking [qelim] to eliminate the result
   and keeping a quantifier-free, non-ground answer). *)
open Core
open Common.Ext
open Common.Combinator
open LogicOld

let split_params_by_theory =
  List.fold_left ~init:Map.Poly.empty ~f:(fun ret (tvar, sort) ->
      let term = Term.mk_var tvar sort in
      match Map.Poly.find ret sort with
      | Some env -> Map.Poly.set ret ~key:sort ~data:(Set.add env (term, []))
      | None -> Map.Poly.set ret ~key:sort ~data:(Set.Poly.singleton (term, [])))

let str_of_term_list = String.concat_map_list ~sep:"," ~f:Term.str_of
let str_of_term_list_list = String.concat_map_list ~sep:"\n" ~f:str_of_term_list

let div_mod_filter (_, phi) =
  Set.exists (Formula.funsyms_of phi) ~f:(function
    | T_int.(Div _ | Rem _) -> true
    | _ -> false)

let neg (params, phi) =
  (params, Normalizer.normalize @@ Evaluator.simplify_neg phi)

let add_neg quals = Set.union quals @@ Set.Poly.map quals ~f:neg

(* EVERY OTHER FAMILY HERE REWRITES A QUALIFIER THAT ALREADY EXISTS; this one
   makes qualifiers out of nothing but the predicate's own parameters, because
   for some sorts there is nothing to rewrite.  Extraction offers an atom only
   where some clause already wrote it, and the numeric domains generate
   halfspaces, which a datatype or an uninterpreted sort has none of -- so if no
   clause happens to compare two arguments of such a sort, the hypothesis space
   cannot say the most elementary thing an invariant says about them: that they
   are the same value.

   That gap is not theoretical.  A predicate over a mutable reference, its
   prophesied final value and a loop counter had a space of ten atoms -- four
   about the trait predicate, six about the counter -- and a positive and a
   negative example whose counters were equal, so that no numeric atom told them
   apart, and whose trait arguments made every trait atom come out as a
   satisfiable condition on the example's own parameters rather than as false,
   so that no combination of them could falsify the negative one either.  No
   candidate in that space fits those two examples, and the one atom that does
   is the equality of the two reference arguments: in the positive example the
   two are the same reference, in the negative one they are unrelated.  The
   synthesizer's answer to a space that fits nothing is to enlarge the shape and
   try again, so the run searched candidates until it was killed.

   Array- and function-sorted parameters are left out deliberately: equality
   there is extensional, and a solver pays for that on every candidate it
   checks, for a fact this corpus never needs. *)
let arg_equalities params =
  let eligible s =
    match s with
    | Sort.SArrow _ | T_array.SArray _ -> false
    | _ -> true
  in
  let indexed = List.mapi params ~f:(fun i (v, s) -> (i, v, s)) in
  Set.Poly.of_list
  @@ List.concat_map indexed ~f:(fun (i, vi, si) ->
      if not (eligible si) then []
      else
        List.filter_map indexed ~f:(fun (j, vj, sj) ->
            if i < j && String.(Term.str_of_sort si = Term.str_of_sort sj) then
              Some (params, Formula.eq (Term.mk_var vi si) (Term.mk_var vj sj))
            else None))

(* Two parameters of one predicate that have the same sort are two places where
   the same fact can be stated, and an extraction records only the place the
   clause it came from happened to mention.  A loop invariant over a mutable
   slice needs "the original slice still has length two" about its second
   parameter; the entry clause, where the two parameters coincide, states it
   about the first, so the form the invariant needs is absent from the
   hypothesis space altogether while its mirror image is present.  Three of the
   five atoms one such invariant is built from were missing in exactly that way.
   Swapping a pair of same-sorted parameters supplies the missing form.

   This cannot make an answer wrong: a qualifier is a candidate building block
   and every candidate solution built from one is validated, so the only cost is
   a larger space to search.  That cost is why this generates transpositions
   rather than every permutation -- k(k-1)/2 extra qualifiers per qualifier
   instead of k! -- which is also all that is needed to reach the mirror image of
   a fact about one parameter. *)
let add_arg_transpositions_reference quals =
  Set.union quals
  @@ Set.concat_map quals ~f:(fun (params, phi) ->
      let indexed = List.mapi params ~f:(fun i (v, s) -> (i, v, s)) in
      Set.Poly.of_list
      @@ List.concat_map indexed ~f:(fun (i, vi, si) ->
          List.filter_map indexed ~f:(fun (j, vj, sj) ->
              if
                i < j
                && Sexp.equal (Datatype.structural_sort_key si)
                     (Datatype.structural_sort_key sj)
              then
                Some
                  ( params,
                    Formula.subst
                      (Map.Poly.of_alist_exn
                         [ (vi, Term.mk_var vj sj); (vj, Term.mk_var vi si) ])
                      phi )
              else None)))

(* [same_sorted_pairs params]: the pairs [(vi, si, vj, sj)], [i < j], of
   parameters whose sorts have the same structural key, in the order the reference above
   visits them.  Computed once per parameter list instead of twice per pair
   and qualifier: computing a datatype, tuple or sequence key walks it. *)
let same_sorted_pairs params =
  let indexed =
    List.mapi params ~f:(fun i (v, s) ->
        (i, v, s, Datatype.structural_sort_key s))
  in
  List.concat_map indexed ~f:(fun (i, vi, si, keyi) ->
      List.filter_map indexed ~f:(fun (j, vj, sj, keyj) ->
          if i < j && Sexp.equal keyi keyj then Some (vi, si, vj, sj)
          else None))

(* [add_arg_transpositions quals] equals [add_arg_transpositions_reference
   quals] (the same set; [test/qual_transpositions.exe] checks it on random
   qualifiers).  It skips a swap of two parameters neither of which occurs
   free in a qualifier without binders (no quantifier, [let] or array
   lambda): substitution then rebuilds the
   qualifier itself, which the union already holds, and building it and
   comparing it against its own copy in the set was the bulk of the cost on
   inputs with many same-sorted parameters.  A qualifier with a binder is
   always substituted, since the substitution may rename a bound variable
   that clashes with the swapped names, which gives a distinct set element. *)
let binder_free phi =
  Formula.is_quantifier_free phi
  && Formula.is_let_free phi
  && Set.is_empty
       (Formula.filtered_terms_of phi ~f:(function
         | Term.FunApp (T_array.ALambda _, _, _) -> true
         | _ -> false))

(* [add_arg_transpositions ?settled quals] is [add_arg_transpositions_reference
   quals] when [settled] (default: always false) holds of no qualifier
   whose swaps the result lacks.  A binder-free qualifier [q] with
   [settled q] is not swapped: the caller asserts that its swaps are
   already in [quals].  That holds for a qualifier carried over from an
   earlier round of the closure below, since a binder-free qualifier's swaps
   are a function of the qualifier (substitution renames nothing in it) and
   that round put them in the set.  A qualifier with a binder is swapped
   whatever [settled] says, since its swaps draw fresh bound names and the
   draws must happen as they would without [settled]. *)
let add_arg_transpositions ?(settled = fun _ -> false) quals =
  (* per parameter list (by identity): its same-sorted pairs, and for each
     parameter the pairs it belongs to, so that a binder-free qualifier visits
     only the pairs touching its free variables rather than every pair of the
     list (a predicate of this corpus has 89 parameters of one sort, about
     3,900 pairs, against a qualifier of two or three variables) *)
  let pairs_memo = ref [] in
  let pairs_of params =
    match
      List.find !pairs_memo ~f:(fun (ps, _, _) -> phys_equal ps params)
    with
    | Some (_, pairs, by_var) -> (pairs, by_var)
    | None ->
        let pairs = same_sorted_pairs params in
        let by_var = Hashtbl.Poly.create () in
        List.iter pairs ~f:(fun ((vi, _, vj, _) as p) ->
            Hashtbl.add_multi by_var ~key:vi ~data:p;
            Hashtbl.add_multi by_var ~key:vj ~data:p);
        pairs_memo := (params, pairs, by_var) :: !pairs_memo;
        (pairs, by_var)
  in
  let swap params phi (vi, si, vj, sj) =
    ( params,
      Formula.subst
        (Map.Poly.of_alist_exn
           [ (vi, Term.mk_var vj sj); (vj, Term.mk_var vi si) ])
        phi )
  in
  (* Orbits of one-variable qualifiers.  For a binder-free [phi] whose only
     free variable is the parameter [x], the swaps are [phi[x := y]] for
     every other parameter [y] of [x]'s class (a swap of [x] with [y] where
     [y] does not occur is the renaming), and they depend on [phi] only
     through [phi[x := #]] (a placeholder) and the class.  So qualifiers
     equal up to that placeholder, over one class, share their swaps: two
     such, [phi1] over [x1] and [phi2] over [x2 <> x1], together give
     [{phi1[x1 := y] | y in the class}], the orbit, each giving all of it
     but the term at its own variable, which the other gives.  A group of
     two or more is therefore replaced by its orbit, built once from the
     placeholder form, where each member would otherwise rebuild nearly all
     of it (a predicate with a hundred integer parameters and the same atom
     extracted at many of them rebuilt the same hundred qualifiers for each
     one).  A group of one is swapped as before, since its own variable's
     term need not be in the orbit's form ([phi] may carry an occurrence
     sort other than the parameter's).  Settled qualifiers take no part. *)
  let placeholder = Ident.Tvar "#swap_orbit" in
  let one_var_key params phi =
    if not (binder_free phi) then None
    else
      match Set.to_list (Formula.tvs_of phi) with
      | [ x ] -> (
          match List.Assoc.find params ~equal:Ident.tvar_equal x with
          | None -> None
          | Some sx ->
              let canon =
                Formula.subst
                  (Map.Poly.singleton x (Term.mk_var placeholder sx))
                  phi
              in
              Some (x, sx, (canon, Datatype.structural_sort_key sx)))
      | _ -> None
  in
  let grouped = ref Set.Poly.empty in
  let orbits =
    Common.PhaseTime.with_phase "swap-orbits" @@ fun () ->
    let by_params = ref [] in
    Set.iter quals ~f:(fun ((params, phi) as q) ->
        match pairs_of params with
        | [], _ -> ()
        | _ when settled q -> ()
        | _ -> (
            match one_var_key params phi with
            | None -> ()
            | Some (x, sx, key) ->
                let tbl =
                  match
                    List.find !by_params ~f:(fun (ps, _) -> phys_equal ps params)
                  with
                  | Some (_, tbl) -> tbl
                  | None ->
                      let tbl = Hashtbl.PolyDeep.create () in
                      by_params := (params, tbl) :: !by_params;
                      tbl
                in
                Hashtbl.add_multi tbl ~key ~data:(q, x, sx)));
    List.concat_map !by_params ~f:(fun (params, tbl) ->
        let _, by_var = pairs_of params in
        Hashtbl.fold tbl ~init:[] ~f:(fun ~key:(canon, _) ~data acc ->
            match data with
            | [] | [ _ ] -> acc
            | (_, x, sx) :: _ ->
                List.iter data ~f:(fun (q, _, _) ->
                    grouped := Set.add !grouped q);
                let partners =
                  List.map (Hashtbl.find_multi by_var x)
                    ~f:(fun (vi, si, vj, sj) ->
                      if Ident.tvar_equal vi x then (vj, sj) else (vi, si))
                in
                List.map ((x, sx) :: partners) ~f:(fun (y, sy) ->
                    ( params,
                      Formula.subst
                        (Map.Poly.singleton placeholder (Term.mk_var y sy))
                        canon ))
                @ acc))
  in
  let swapped =
    Common.PhaseTime.with_phase "swap" @@ fun () ->
    Set.union (Set.Poly.of_list orbits)
    @@ Set.concat_map quals ~f:(fun (params, phi) ->
      match pairs_of params with
      | _ when Set.mem !grouped (params, phi) -> Set.Poly.empty
      | [], _ -> Set.Poly.empty
      | _ when settled (params, phi) && binder_free phi -> Set.Poly.empty
      | pairs, by_var ->
          Set.Poly.of_list
          @@ Common.PhaseTime.with_phase "swap-subst" @@ fun () ->
          if binder_free phi then
            (* the pairs with at least one side free in [phi], each once:
               from its first side, or from its second when the first is not
               free; a pair with neither side free would rebuild [phi] *)
            let fvs = Formula.tvs_of phi in
            List.concat_map (Set.to_list fvs) ~f:(fun v ->
                List.filter_map (Hashtbl.find_multi by_var v)
                  ~f:(fun ((vi, _, _, _) as p) ->
                    if Ident.tvar_equal vi v || not (Set.mem fvs vi) then
                      Some (swap params phi p)
                    else None))
          else List.map pairs ~f:(swap params phi))
  in
  Common.PhaseTime.with_phase "union" (fun () -> Set.union quals swapped)

(* the variables directly under [(_ int_to_bv n)] in [phi] *)
let int_to_bv_vars phi =
  Set.Poly.filter_map
    (Formula.filtered_terms_of phi ~f:(function
      | Term.FunApp (T_irb.IntToBV _, [ Term.Var _ ], _) -> true
      | _ -> false))
    ~f:(function
      | Term.FunApp (T_irb.IntToBV _, [ Term.Var (x, _, _) ], _) -> Some x
      | _ -> None)

(* [drop_non_word_forms ~words ~params ~extracted permuted] keeps every
   qualifier of [extracted] and every other one of [permuted] that puts no
   parameter outside [words] directly under [int_to_bv].  The swaps above treat
   all parameters of one sort alike, so a bit atom [bit_b(w) = 0] extracted over
   two words of an unknown that also has integer counts is offered over the
   counts too; a candidate carrying such an atom converts a count into a word,
   which the solver can only split into an unbounded quotient and a word, and
   such a validation question was left unanswered in 30 s on a loop whose other
   questions took well under a second.  Contract: the result is a subset of
   [permuted] (as is [extracted], which it contains when [permuted] does); a
   qualifier with no parameter under [int_to_bv] is always kept. *)
let drop_non_word_forms ~words ~params ~extracted permuted =
  Set.filter permuted ~f:(fun ((_, phi) as q) ->
      Set.mem extracted q
      || Set.for_all (int_to_bv_vars phi) ~f:(fun x ->
             (not (Set.mem params x)) || Set.mem words x))

(* Composing two swaps reaches a form that neither reaches alone, and a loop
   invariant did need one: of the four ways to pair a predicate's two
   mutable-reference parameters with its two integer ones, a single swap of the
   extracted qualifier reaches two and the fourth needs both swaps at once.
   Iterating to a fixed point generates the permutation group of each same-sorted
   class, which is k! per class and has to be bounded -- one predicate of this
   corpus has eight parameters of one sort.  The bound is on the size of the
   result rather than on the class, so a predicate with two small classes gets
   its sixteen forms while one with a large class stops early and keeps whatever
   the first rounds produced, which is still a superset of the single swaps. *)
let add_arg_permutations ?(limit = 256) quals =
  let grow_with transpose quals =
    let rec grow prev =
      Common.PhaseTime.event "perm-round";
      let next = transpose prev in
      if Set.length next <= Set.length prev || Set.length next > limit then next
      else grow next
    in
    grow quals
  in
  (* The same rounds as [grow_with add_arg_transpositions], each round
     swapping only the qualifiers the round before it added (and every
     qualifier with a binder): a qualifier present one round earlier already
     had its swaps added then, so swapping it again rebuilds elements the set
     holds.  Every round's set, and so the stopping test and the result, are
     those of the plain closure (checked against it by a property test). *)
  let grow_semi_naive quals =
    let rec grow older prev =
      Common.PhaseTime.event "perm-round";
      let next =
        add_arg_transpositions ~settled:(fun q -> Set.mem older q) prev
      in
      if Set.length next <= Set.length prev || Set.length next > limit then next
      else grow prev next
    in
    grow Set.Poly.empty quals
  in
  let result = grow_semi_naive quals in
  (* [COAR_PERM_CENSUS]: one line per closure, read by nothing: the
     qualifiers given, how many have a binder, the result's size and the
     mean size of a given qualifier *)
  if Option.is_some (Sys.getenv "COAR_PERM_CENSUS") then
    eprintf "[perm-census] given=%d binders=%d result=%d params=%d mean_size=%d\n%!"
      (Set.length quals)
      (Set.count quals ~f:(fun (_, phi) -> not (binder_free phi)))
      (Set.length result)
      (match Set.min_elt quals with Some (ps, _) -> List.length ps | None -> 0)
      (if Set.is_empty quals then 0
       else
         Set.sum (module Int) quals ~f:(fun (_, phi) -> Formula.ast_size phi)
         / Set.length quals);
  (* [COAR_PERM_AB]: also build the closure with the reference swaps, timed
     beside it in the same process, and count whether the two agree (exactly,
     or, where a qualifier has a binder and the reference's fresh bound names
     differ, in size) *)
  if Option.is_some (Sys.getenv "COAR_PERM_AB") then (
    let reference =
      Common.PhaseTime.with_phase "perm-reference" (fun () ->
          grow_with add_arg_transpositions_reference quals)
    in
    Common.PhaseTime.event
      (if Set.equal reference result then "perm-ab-equal"
       else if Set.length reference = Set.length result then "perm-ab-same-size"
       else "perm-ab-differ"));
  result



(* An inequality names a HALFSPACE, and its boundary can be approached from
   either side.  The extraction records whichever side the clause it came from
   stated, so a space can hold [-t >= 0] and not [t >= 0] -- and those are not
   each other's negation: negating [t <= 0] gives the STRICT [t > 0], which
   excludes the boundary, while a partition that has to put the boundary on the
   other piece needs the non-strict form.

   Measured on a liveness property over a rotation in the plane, whose
   certificate is a rank constant on each quadrant: the good quadrant is
   [a > 0 and b >= 0], the space held [-b >= 0] and not [b >= 0], so the
   quadrant could only be under-approximated as [a > 0 and b > 0] and the axis
   [b = 0] -- where the property still has to hold -- was left out.  Reflecting
   the two halfspaces already present supplies exactly the two missing atoms,
   and with a four-piece ranking template the file is proved in seconds where
   it had never been proved at all.

   This invents nothing: it reflects halfspaces the space already has, so a
   parameter no qualifier mentions gains none.  It cannot make an answer wrong
   -- a qualifier is a candidate building block and every candidate solution
   built from one is validated -- so the cost is search space only. *)
let reflect (params, phi) =
  ( params,
    Normalizer.normalize
    @@ Formula.map_atom phi ~f:(fun atom ->
           Formula.mk_atom
           @@
           match atom with
           | Atom.App (Predicate.Psym (T_int.Geq as psym), [ t1; t2 ], _) ->
               Atom.mk_psym_app psym [ T_int.mk_neg t1; T_int.mk_neg t2 ]
           | Atom.App (Predicate.Psym (T_real.RGeq as psym), [ t1; t2 ], _) ->
               Atom.mk_psym_app psym [ T_real.mk_rneg t1; T_real.mk_rneg t2 ]
           | _ -> atom) )

let add_reflections quals = Set.union quals @@ Set.Poly.map quals ~f:reflect

let add_homogeneous quals =
  Set.union quals
  @@ Set.Poly.map quals ~f:(fun (params, phi) ->
      (params, Normalizer.homogenize phi))

let rec mk_let_to_cond conds bvs fvs tvs lenv =
  let lenv' =
    Map.Poly.filteri lenv ~f:(fun ~key ~data ->
        Set.mem fvs (key, Term.sort_of data))
  in
  let conds' =
    Map.Poly.to_alist lenv'
    |> List.map ~f:(fun (var, def) ->
        Formula.eq (Term.mk_var var (Term.sort_of def)) def)
  in
  let tvs' =
    Set.union tvs (Set.Poly.union_list @@ List.map conds' ~f:Formula.sort_env_of)
  in
  let fvs' = Set.diff tvs' bvs in
  let conds' = Set.union conds (Set.Poly.of_list conds') in
  if Set.length fvs = Set.length fvs' then
    (tvs', fvs, Set.to_list conds' |> Formula.and_of)
  else mk_let_to_cond conds' bvs fvs' tvs' lenv

(* [mk_func_app_terms ?tuples term_map fenv] are the applications of every
   function of [fenv] (but the size functions) to the tuples of reached terms
   of its argument sorts -- the whole product of [term_map]'s per-sort lists,
   or, for a function [f] with [tuples f = Some ts], exactly the tuples [ts]
   (the caller's own bound; an empty list gives no application of [f]).  A
   tuple of [ts] must be well-sorted for [f]'s arguments.

   An argument sort with no reached term is filled with the sort's default
   instance ([Term.mk_dummy]): the empty sequence, a base constructor, the
   constant array of the codomain's default, an arbitrary constant of an
   uninterpreted sort.  With [reached_sorts_only], a function with such an
   argument is not applied at all when that sort is not numeric or Boolean:
   the default instance is a value no clause relates to the predicate's
   parameters.  Inputs that define one counting function per element sort
   make these applications the bulk of the integer terms -- 22 of 23 such
   functions over element sorts the predicate does not mention, each applied
   to an empty sequence at every pair of integer terms, and every sequence of
   the predicate was then read at each of them, about 250 thousand pairwise
   element equalities in one predicate.
   NOT EXACT in general: [f(d, u)] at defaults [d] is a determined function
   [g(u)] of the reached arguments (unspecified only where a default is an
   uninterpreted constant or an out-of-range read reaches the result), and a
   [g] that is not piecewise trivial (say [len d + i]) is a genuine term this
   removes.  On the shape that motivated it the loss is only of case splits:
   a recursive definition that mentions a universal of the input takes it as
   a trailing parameter (closure conversion by the reader), the default filled
   in for that parameter is the constant array, so a count over an empty
   sequence reads that constant at every step and is, by induction on the
   decreasing argument, an [ite] over integer terms the map already has and
   [0]; a read at it equals, case by case, a read at one of those terms or at
   [0].  It only narrows the term map, so it bears on which solutions are
   expressible and never on the soundness of a verdict.  A numeric or Boolean
   default ([0], [false]) is a genuine constant and is still used.
   Contract: with [reached_sorts_only] the result is a subset of the result
   without it, and equal to it when every non-scalar argument sort of every
   function is a key of [term_map]; the bound [tuples f = Some ts] is not
   affected. *)
let mk_func_app_terms ?(tuples = fun _ -> None) ?(reached_sorts_only = false)
    (term_map : (Sort.t, (Term.t * Formula.t list) Set.Poly.t) Map.Poly.t) fenv
    =
  let unreached_non_scalar sort =
    (not (Map.Poly.mem term_map sort))
    && not
         (Term.is_int_sort sort || Term.is_real_sort sort
        || Term.is_bool_sort sort || Term.is_bv_sort sort)
  in
  Map.Poly.fold fenv ~init:Set.Poly.empty
    ~f:(fun ~key:tvar ~data:(param_env, sret, _, _, _) ret ->
      if Ident.is_size_fun_var tvar then ret
      else
        let sargs = List.map ~f:snd param_env in
        Set.union ret @@ Set.Poly.of_list
        @@ List.map ~f:(Term.mk_fvar_app tvar sargs sret)
        @@
        match tuples tvar with
        | Some ts -> ts
        | None ->
        if reached_sorts_only && List.exists sargs ~f:unreached_non_scalar then (
          (* one event per function left unapplied, for a firing census *)
          Common.PhaseTime.event_here ~in_copy:false
            "func-app-unreached-sort-skipped";
          [])
        else
        List.permutation_without_repetion_of
        @@ List.map param_env ~f:(fun (_, sort) ->
            match Map.Poly.find term_map sort with
            | Some ts -> List.map ~f:fst @@ Set.to_list ts
            | _ -> [ Term.mk_dummy sort ]))

let bool_quals_of terms params =
  let quals, qdeps =
    Set.filter terms ~f:(fun (term, _dep) ->
        match term with
        | Term.Var (x, _, _) ->
            not @@ List.Assoc.mem params ~equal:Stdlib.( = ) x
        | _ -> true)
    |> Set.Poly.map ~f:(fun (t, dep) ->
        QualDep.qual_and_deps_of (Formula.eq t (T_bool.mk_true ())) dep)
    |> Set.to_list
    |> List.map ~f:(fun (qual, dep) -> (qual, (qual, dep)))
    |> List.unzip
  in
  (* Combine rather than refuse on a repeated qualifier: the same normalized
     qualifier can come from two terms with different well-definedness
     conditions, and [of_alist_exn] ended the run with an uncaught exception
     when it did.  See the sibling site in the datatype qualifiers. *)
  ( Set.Poly.of_list quals,
    List.fold qdeps ~init:Map.Poly.empty ~f:(fun acc (phi, qdep) ->
        Map.Poly.update acc phi ~f:(function
          | None -> qdep
          | Some qdep' -> QualDep.merge_dep qdep' qdep)) )

let add_quals_form_affine_eq_quals quals =
  Set.union quals @@ Set.concat
  @@ Set.Poly.filter_map quals ~f:(fun phi ->
      if Formula.is_atom phi then
        match Formula.let_atom phi with
        | Atom.App (Predicate.Psym T_bool.(Eq | Neq), [ t1; t2 ], _), _
          when AffineTerm.is_affine t1 && (Term.is_int_sort @@ Term.sort_of t1)
          ->
            Option.some @@ Set.Poly.of_list [ Formula.gt t1 t2 ]
        | _ -> None
      else None)

let add_mod_quals_terms quals terms =
  let quals' =
    let rec inner i quals =
      let quals' =
        Set.union quals
        @@ Set.Poly.map quals ~f:(fun qual ->
            Formula.map_term qual ~f:(function
              | Term.FunApp (T_int.Rem modulo, [ t1; t2 ], info) as t
                when T_int.is_int t2 ->
                  (* in [Z]: the modulus is a term's constant, of any size *)
                  let m = T_int.let_int t2 and zi = Z.of_int i in
                  if Z.(gt m zi && equal (erem m zi) zero) then
                    Term.mk_fsym_app ~info (T_int.Rem modulo)
                      [ t1; T_int.from_int i ]
                  else t
              | t -> t))
      in
      if Set.equal quals quals' then quals else inner (i + 1) quals'
    in
    inner 2 quals
  in
  if Set.equal quals' quals then (quals, terms)
  else
    (* let terms =
       Set.concat_map quals ~f:Formula.terms_of
       |> Set.filter ~f:T_int.is_mod
       |> Set.union terms
       in *)
    (quals', terms)

let mk_mod_quals params =
  Set.Poly.of_list
  @@ List.filter_map params ~f:(fun (v, s) ->
      if Fn.non Term.is_int_sort s then None
      else
        Option.some
        @@ Formula.eq
             (T_int.mk_rem Value.Euclidean (Term.mk_var v s) (T_int.from_int 2))
             (T_int.zero ()))

let mk_eq_quals_for_ith_param params i =
  if i >= List.length params || List.length params <= 1 then Set.Poly.empty
  else
    let vi, si = List.nth_exn params i in
    List.fold params ~init:Set.Poly.empty ~f:(fun acc (v, s) ->
        if Stdlib.(v = vi) || Stdlib.(s <> si) then acc
        else Set.add acc (Formula.eq (Term.mk_var vi si) (Term.mk_var v s)))

(* A census of the quantifier eliminations [extract_terms_from_quals] asks,
   per class of result sort, kept only while the phase-time account is on:
   each call is a phase [qual-qelim-<class>] and its outcome an event
   [qual-qelim-<class>-<outcome>] (bind: the answer still has a binder;
   ground: no free variable; kept: a qualifier over the arguments;
   unreadable: the answer has an operator this tree cannot read;
   unreadable-atom: the same, met by the atom decoder; skipped:
   not asked, see [skip_non_numeric]); [-repeat] counts a question already
   asked in this process up to the names of the unknown's parameters. *)
let qelim_sort_class s =
  if Term.is_irb_sort s then "irb"
  else
    match s with
    | T_seq.SSeq _ -> "seq"
    | T_dt.SDT _ -> "dt"
    | T_tuple.STuple _ -> "tuple"
    | T_array.SArray _ -> "array"
    | _ -> if Term.is_bool_sort s then "bool" else "other"

let qelim_census_seen : (string, unit) Stdlib.Hashtbl.t =
  Stdlib.Hashtbl.create 1024

let qelim_census_mutex = Stdlib.Mutex.create ()

let qelim_census_repeat cls params phi =
  if !Common.PhaseTime.on then (
    let ren =
      Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
      @@ List.mapi params ~f:(fun i (v, _) ->
          (v, Ident.Tvar (sprintf "qqp%d" i)))
    in
    let key =
      Term.str_of_sort (snd (List.last_exn params))
      ^ "|" ^ Formula.str_of (Formula.rename ren phi)
    in
    Stdlib.Mutex.lock qelim_census_mutex;
    let seen = Stdlib.Hashtbl.mem qelim_census_seen key in
    if not seen then Stdlib.Hashtbl.replace qelim_census_seen key ();
    Stdlib.Mutex.unlock qelim_census_mutex;
    if seen then Common.PhaseTime.event ("qual-qelim-" ^ cls ^ "-repeat"))


(* A memo of [extract_terms_from_quals]'s eliminations up to a renaming of
   free variables.  The swaps of same-sorted parameters ([add_arg_permutations])
   make most qualifiers of an unknown renamings of one another, and the
   elimination of the result commutes with a renaming that fixes it: for a
   bijective renaming [r] of the other free variables, [qelim (exists y.
   r(phi))] is equivalent to [r (qelim (exists y. phi))].  So one question is
   asked per class of qualifiers equal up to renaming, and the others take
   its answer renamed (the same meaning; the solver's own answer to the
   renamed question could differ only in form).  The key is the qualifier
   with its free variables renamed, by order of first occurrence in its
   printed form, to fixed names; two qualifiers share an entry only if those
   canonical forms are structurally equal, so the order only decides how
   often a renaming is recognised, never whether a reuse is right.  Only
   binder-free qualifiers are memoised (a renaming then cannot capture), and
   only an answer whose free variables are the qualifier's is stored. *)
type qelim_memo_entry =
  | Memo_kept of Formula.t (* over the canonical names *)
  | Memo_dropped of string (* the census outcome *)

let qelim_canon_prefix = "qqc!"

let qelim_canon vret phi =
  let fvs = Set.remove (Formula.tvs_of phi) vret in
  let order =
    let seen = Hash_set.Poly.create () in
    let toks =
      String.split_on_chars (Formula.str_of phi)
        ~on:[ ' '; '('; ')'; ','; '['; ']'; '\n'; '\t' ]
    in
    let from_text =
      List.filter_map toks ~f:(fun tok ->
          let x = Ident.Tvar tok in
          if Set.mem fvs x && not (Hash_set.mem seen x) then (
            Hash_set.add seen x;
            Some x)
          else None)
    in
    from_text @ List.filter (Set.to_list fvs) ~f:(Fn.non (Hash_set.mem seen))
  in
  let canon_of =
    Map.Poly.of_alist_exn
    @@ (vret, Ident.Tvar (qelim_canon_prefix ^ "r"))
       :: List.mapi order ~f:(fun i x ->
           (x, Ident.Tvar (sprintf "%s%d" qelim_canon_prefix i)))
  in
  let back =
    Map.Poly.of_alist_exn
    @@ List.filter_map (Map.Poly.to_alist canon_of) ~f:(fun (x, c) ->
        if Stdlib.(x = vret) then None else Some (c, x))
  in
  (Formula.rename canon_of phi, back, canon_of)

(* [skip_non_numeric]: a qualifier that mentions the result is not handed to
   quantifier elimination when the result sort is not an integer, a real or a
   bit-vector; it is dropped, as an elimination that leaves the binder in
   place is.  This is exact only where the solver's elimination never
   removes such a binder, which holds of no theory in general (an equation
   [r = t] is eliminated by the one-point rule); off, every such qualifier
   is asked. *)
let extract_terms_from_quals ?(skip_non_numeric = false)
    ?(exact_affine_coeff = false) ~qelim params quals =
  let vret, sret = List.last_exn params in
  let cls = qelim_sort_class sret in
  let census outcome =
    Common.PhaseTime.event ("qual-qelim-" ^ cls ^ "-" ^ outcome)
  in
  let memo : (string, (Formula.t * qelim_memo_entry) list) Hashtbl.t =
    Hashtbl.create (module String)
  in
  let quals_ret, quals_rest =
    Set.partition_tf quals ~f:(fun qual -> Set.mem (Formula.tvs_of qual) vret)
  in
  let termss, quals =
    List.partition_map (Set.to_list quals_ret) ~f:(fun phi ->
        let terms =
          if Term.is_irb_sort sret then
            Common.PhaseTime.with_phase "qual-affine" @@ fun () ->
            AffineTerm.extract_terms_from_formula ~exact_coeff:exact_affine_coeff
              (vret, sret)
              (Evaluator.simplify_term >> Normalizer.normalize_term)
              Normalizer.normalize phi
          else Set.Poly.empty
        in
        if Set.is_empty terms && skip_non_numeric && not (Term.is_irb_sort sret)
        then (
          census "skipped";
          First Set.Poly.empty)
        else if Set.is_empty terms then
          (* [qelim] reads the solver's answer back into a formula, and the
             solver may answer with an operator this tree has no term for
             (Z3 writes [seq.nth_u] for [seq.nth] outside a sequence's
             bounds, an uninterpreted function that is not [seq.nth] at an
             in-range index; over a sequence of Booleans the read is an atom,
             and the atom decoder re-raises the term decoder's message inside
             its own).  Such a qualifier is dropped: a missing qualifier only
             narrows the hypothesis space, it never makes a candidate or a
             verdict wrong.  Reading [seq.nth_u] back as [seq.nth] would be
             wrong wherever the answer applies it at an index that can be in
             range, since there it is free and [seq.nth] is not. *)
          let phi' =
            Common.PhaseTime.with_phase "qual-normalize" (fun () ->
                Normalizer.normalize phi)
          in
          Common.PhaseTime.with_phase "qual-qelim-census" (fun () ->
              qelim_census_repeat cls params phi');
          let canon =
            if binder_free phi' then Some (qelim_canon vret phi') else None
          in
          let memo_key =
            Option.map canon ~f:(fun (c, _, _) -> Formula.str_of c)
          in
          let hit =
            match (canon, memo_key) with
            | Some (c, back, _), Some key -> (
                match Hashtbl.find memo key with
                | None -> None
                | Some entries -> (
                    match
                      List.find entries ~f:(fun (c', _) ->
                          try Stdlib.(c = c')
                          with exn_ when not (Common.Timer.is_async exn_) ->
                            false)
                    with
                    | Some (_, Memo_kept q) -> Some (`Kept (Formula.rename back q))
                    | Some (_, Memo_dropped outcome) -> Some (`Dropped outcome)
                    | None -> None))
            | _ -> None
          in
          let remember entry =
            match (canon, memo_key) with
            | Some (c, _, _), Some key ->
                Hashtbl.add_multi memo ~key ~data:(c, entry)
            | _ -> ()
          in
          match hit with
          | Some (`Dropped outcome) ->
              Common.PhaseTime.event ("qual-qelim-" ^ cls ^ "-memo");
              census outcome;
              First Set.Poly.empty
          | Some (`Kept qual) ->
              Common.PhaseTime.event ("qual-qelim-" ^ cls ^ "-memo");
              census "kept";
              Second qual
          | None -> (
          match
            Common.PhaseTime.with_phase ("qual-qelim-" ^ cls) (fun () ->
                qelim @@ Formula.exists [ List.last_exn params ] phi')
          with
          | qual ->
              let remember_kept () =
                match canon with
                | Some (_, _, canon_of)
                  when binder_free qual
                       && Set.is_subset (Formula.tvs_of qual)
                            ~of_:(Set.remove (Formula.tvs_of phi') vret) ->
                    remember (Memo_kept (Formula.rename canon_of qual))
                | _ -> ()
              in
              if Formula.is_bind qual then (
                census "bind";
                remember (Memo_dropped "bind");
                First Set.Poly.empty)
              else if Formula.is_ground qual then (
                census "ground";
                remember (Memo_dropped "ground");
                First Set.Poly.empty)
              else (
                census "kept";
                remember_kept ();
                (match Sys.getenv "COAR_QUAL_QELIM_LOG" with
                | Some file when not (Term.is_irb_sort sret) ->
                    Out_channel.with_file ~append:true file ~f:(fun oc ->
                        Out_channel.output_string oc
                          (sprintf "%s\t%s\t%s\n" cls (Formula.str_of phi')
                             (Formula.str_of qual)))
                | _ -> ());
                Second qual)
          | exception (Failure msg as e)
            when (not (Common.Timer.is_async e))
                 && Common.Util.UnreadableAnswer.is_failure msg ->
              (* [unreadable-atom]: the message came wrapped by the atom
                 decoder (a Bool-valued read such as [seq.nth_u] over a
                 sequence of Booleans) *)
              census
                (if
                   String.is_prefix msg
                     ~prefix:Common.Util.UnreadableAnswer.prefix
                 then "unreadable"
                 else "unreadable-atom");
              remember (Memo_dropped "unreadable");
              First Set.Poly.empty)
        else First terms)
  in
  (Set.union quals_rest (Set.Poly.of_list quals), Set.Poly.union_list termss)

let extract_wf_terms_from_quals_terms ~qelim params_x params_y (quals, terms) =
  let rename_y_x = Formula.rename (ren_of_sort_env_list params_y params_x) in
  if false then
    ( Set.concat_map quals ~f:(fun phi ->
          let qual1 = qelim @@ Formula.exists params_y phi in
          let qual2 = qelim @@ Formula.exists params_x phi in
          Set.union
            (if Formula.(is_bind qual1 || is_ground qual1) then Set.Poly.empty
             else Set.Poly.singleton qual1)
            (if Formula.(is_bind qual2 || is_ground qual2) then Set.Poly.empty
             else Set.Poly.singleton (rename_y_x qual2))),
      terms )
  else
    ( Set.Poly.filter_map quals ~f:(fun phi ->
          if Formula.is_ground phi then None
          else
            let fvs = Formula.fvs_of phi in
            if
              Set.is_subset fvs
                ~of_:(Set.Poly.of_list @@ List.map ~f:fst params_x)
            then Some phi
            else if
              Set.is_subset fvs
                ~of_:(Set.Poly.of_list @@ List.map ~f:fst params_y)
            then Some (rename_y_x phi)
            else (* ToDo: use the information about transition predicates *)
              None),
      terms )
