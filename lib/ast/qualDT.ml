(* Qualifiers over algebraic datatypes.  [update_term_map] collects the terms
   reachable from parameters through selectors, each with the tester
   conditions that select it; [qualifiers_of] builds testers and equalities
   over them, each with the dependency (the testers) under which it is fixed
   -- a selector on the wrong constructor denotes a value the theory leaves
   open, so such a qualifier is meaningful only together with its guard.
   [guarded_payload_quals] and [selector_path_quals] build comparisons whose
   truth value is fixed by the theory without a dependency: a payload under
   its own constructor's tester, and integer fields reached only through
   selectors of single-constructor datatypes, which are total. *)
open Core
open Common.Ext
open Common.Combinator
open LogicOld

let update_term_map ~depth sort (terms : (Term.t * Formula.t list) Set.Poly.t)
    (term_map : (Sort.t, (Term.t * Formula.t list) Set.Poly.t) Map.Poly.t) =
  if depth = 0 then term_map
  else
    match sort with
    | T_dt.SDT dt ->
        Set.fold terms ~init:term_map ~f:(fun term_map (term, conds) ->
            let sel_terms =
              List.concat_map (Datatype.conses_of dt) ~f:(fun cons ->
                  let sel_terms =
                    let sels, insels =
                      let split_sels dt =
                        List.partition_tf ~f:(function
                          | Datatype.Sel _ -> true
                          | Datatype.InSel (_, dt_name, dt_args) ->
                              (not String.(dt_name = Datatype.name_of dt))
                              || not Stdlib.(dt_args = Datatype.params_of dt))
                      in
                      split_sels dt @@ Datatype.sels_of_cons cons
                    in
                    List.map (insels @ sels) ~f:(fun sel ->
                        T_dt.mk_sel dt (Datatype.name_of_sel sel) term)
                  in
                  List.map sel_terms ~f:(fun sel_term ->
                      ( sel_term,
                        (Formula.mk_atom
                        @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) term
                        )
                        :: conds )))
            in
            List.fold_left sel_terms ~init:term_map
              ~f:(fun term_map (sel_term, conds) ->
                let sel_sort = Term.sort_of sel_term in
                match Map.Poly.find term_map sel_sort with
                | Some group ->
                    Map.Poly.set term_map ~key:sel_sort
                      ~data:(Set.add group (sel_term, conds))
                | None ->
                    Map.Poly.add_exn term_map ~key:sel_sort
                      ~data:(Set.Poly.singleton (sel_term, conds))))
    | _ -> term_map

let rec is_sub_term t = function
  | Term.FunApp (_, ts, _) ->
      if List.mem ts t ~equal:Stdlib.( = ) then true
      else List.mem ts t ~equal:is_sub_term
  | _ -> false

let is_cyclic t1 t2 = is_sub_term t1 t2 || is_sub_term t2 t1

let mk_eqs (ts : (Term.t * Formula.t list) list) =
  List.concat_mapi ts ~f:(fun i2 (t2, conds2) ->
      List.foldi ts ~init:[] ~f:(fun i1 ret (t1, conds1) ->
          if
            i1 <= i2
            || Stdlib.(Term.sort_of t2 <> Term.sort_of t1)
            || Stdlib.(t2 = t1)
            || is_cyclic t2 t1
          then ret
          else
            QualDep.qual_and_deps_of (Formula.eq t2 t1) (conds2 @ conds1) :: ret))

let qualifiers_of sort (terms : (Term.t * Formula.t list) Set.Poly.t) =
  if false then
    assert (
      T_dt.is_sdt sort
      && Set.for_all terms ~f:(fst >> Term.sort_of >> Stdlib.( = ) sort));
  match sort with
  | T_dt.SDT dt ->
      let testers =
        List.concat_map (Datatype.conses_of dt) ~f:(fun cons ->
            Set.to_list
            @@ Set.Poly.map terms ~f:(fun (t, conds) ->
                   QualDep.qual_and_deps_of
                     (Formula.mk_atom
                     @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t)
                     conds))
      in
      let eqs =
        mk_eqs @@ Set.to_list
        @@ Set.filter terms ~f:(fun (t, _) ->
               (*ToDo*) Term.is_var t (*|| (T_dt.is_sdt @@ Term.sort_of t)*))
      in
      (* One qualifier may be derived twice with different dependencies: the
         qualifier is normalized before it becomes a key, while its dependency
         comes from the term it was built from, so two terms that normalize
         alike -- a selector on the wrong constructor and an ordinary variable,
         say -- collide with an unconditional dependency against a [false] one.
         The dependencies are conjoined, which is what the consumer does with
         the whole map anyway.  This was [of_alist_exn] over [dedup_keep_last],
         and [dedup_keep_last] compares whole pairs rather than keys, so a
         collision survived it and the run died with the list printed and no
         verdict. *)
      let qdep_env =
        List.fold (testers @ eqs) ~init:Map.Poly.empty ~f:(fun acc (phi, qdep) ->
            Map.Poly.update acc phi ~f:(function
              | None -> qdep
              | Some qdep' -> QualDep.merge_dep qdep' qdep))
      in
      (Map.Poly.key_set qdep_env, qdep_env)
  | _ -> (Set.Poly.empty, Map.Poly.empty)

(* Qualifiers over the payload of a constructor of a datatype that has more
   than one, each guarded by that constructor's tester:

     is_C(t) /\ (sel_C_i(t) <cmp> u)

   A selector applied to a value built by a different constructor is not fixed
   by the theory of datatypes -- SMT-LIB leaves [sel_C_i(D ...)] unspecified,
   so it can differ from model to model -- and that is why nothing else here
   builds a qualifier over such a selector without a dependency on the tester
   being chosen too.  The conjunction does not need one.  Its truth value at a
   valuation of [t] is the same in every model of the background theory: where
   [t] is built by [C], [sel_C_i(t)] is the argument [C] was applied to and
   the comparison is an ordinary integer comparison; where it is built by any
   other constructor the tester is false and so is the conjunction, whatever
   the unspecified selector denotes.  The negation, which a template reaches
   by giving the qualifier a negative sign, is the guarded implication
   [is_C(t) => not (sel_C_i(t) <cmp> u)] and is fixed for the same reason.

   So a truth-table cell for such a qualifier at a ground argument is decided:
   evaluating it on [C v] reads [v], and on [D w] the tester alone makes it
   false (if the evaluator does not fold the conjunction, the fallback validity
   query decides it for the same reason).

   Which terms [t]: every datatype-sorted term reachable from a parameter
   through selectors of single-constructor datatypes only, whose sort has more
   than one constructor.  Those selectors are total -- every value of a
   single-constructor datatype is that constructor applied to its selectors --
   so the path to [t] adds nothing open.  The walk stops at the first
   multi-constructor level: a payload of a payload would need two guards, and
   it is not generated.

   What [u] ranges over: the small constants given, the integer terms
   reachable through total selectors (integer parameters among them), and the
   other guarded payloads, whose guard is then conjoined too.  A pair of
   payloads of one term under two different constructors is skipped, its
   guard being unsatisfiable.  Only [>=] and [<=] are built; equality is their
   conjunction, which a conjunctive template can already form, and the strict
   comparisons are the negations.

   [max_depth] bounds the walk through single-constructor selectors.

   [offset] widens every comparison to [sel(t) >= u + k] and [sel(t) <= u + k]
   for each [k] in [-offset .. offset].  Two values of one constructor whose
   payloads differ by one -- [Ok 11] against [Ok 12] beside an integer [10] --
   are separated by [sel(t) <= u + 1] and by no offset-free comparison with
   [u], so without it the only way to tell them apart is a constant that
   happens to lie between them.  The offset multiplies the number of
   qualifiers by [2 * offset + 1]; the guard is untouched, so fixedness is
   unaffected. *)
let guarded_payload_quals ?(max_depth = 3) ?(offset = 0) ~(consts : Term.t list)
    (params : sort_env_list) =
  let is_single_cons dt =
    match Datatype.conses_of dt with [ _ ] -> true | _ -> false
    | exception exn_ when not (Common.Timer.is_async exn_) -> false
  in
  let is_multi_cons dt =
    match Datatype.conses_of dt with
    | _ :: _ :: _ -> true
    | _ -> false
    | exception exn_ when not (Common.Timer.is_async exn_) -> false
  in
  let sel_terms_of dt cons t =
    List.map (Datatype.sels_of_cons cons) ~f:(fun sel ->
        T_dt.mk_sel dt (Datatype.name_of_sel sel) t)
  in
  (* integer terms through total selectors, and multi-constructor terms met *)
  let rec walk depth (ints, opens) t =
    match Term.sort_of t with
    | T_int.SInt -> (t :: ints, opens)
    | T_dt.SDT dt when is_multi_cons dt -> (ints, (dt, t) :: opens)
    | T_dt.SDT dt when depth < max_depth && is_single_cons dt ->
        List.fold
          (sel_terms_of dt (List.hd_exn (Datatype.conses_of dt)) t)
          ~init:(ints, opens) ~f:(walk (depth + 1))
    | _ -> (ints, opens)
  in
  let ints, opens =
    List.fold params ~init:([], []) ~f:(fun acc (x, s) ->
        walk 0 acc (Term.mk_var x s))
  in
  (* (guard, guarded term, payload) *)
  let payloads =
    List.concat_map (List.rev opens) ~f:(fun (dt, t) ->
        List.concat_map (Datatype.conses_of dt) ~f:(fun cons ->
            let guard =
              Formula.mk_atom
              @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t
            in
            List.filter_map (sel_terms_of dt cons t) ~f:(fun s ->
                if Stdlib.(Term.sort_of s = T_int.SInt) then
                  Some (guard, t, s)
                else None)))
  in
  let consts =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ T_int.zero ()
       :: List.filter consts ~f:(fun c -> Stdlib.(Term.sort_of c = T_int.SInt))
  in
  let cmps guard s u =
    List.concat_map
      (List.range ~stop:`inclusive (-offset) offset)
      ~f:(fun k ->
        let u = if k = 0 then u else T_int.mk_add u (T_int.from_int k) in
        [
          Formula.and_of [ guard; Formula.geq s u ];
          Formula.and_of [ guard; Formula.leq s u ];
        ])
  in
  let against_plain =
    List.concat_map payloads ~f:(fun (guard, _, s) ->
        List.concat_map (consts @ List.rev ints) ~f:(cmps guard s))
  in
  let against_payloads =
    List.concat_mapi payloads ~f:(fun i (g1, t1, s1) ->
        List.concat
        @@ List.filter_mapi payloads ~f:(fun j (g2, t2, s2) ->
               if j <= i then None
               else if Stdlib.(t1 = t2) && not Stdlib.(g1 = g2) then None
               else
                 Some
                   (cmps
                      (if Stdlib.(g1 = g2) then g1 else Formula.mk_and g1 g2)
                      s1 s2)))
  in
  Set.Poly.of_list (against_plain @ against_payloads)

(* Qualifiers over the integer fields of a parameter reached through selectors
   of single-constructor datatypes -- a tuple, a record, a [&mut] pair of
   current and final value -- in two forms:

     cross:     p(x_i) <= p(x_j),  p(x_i) >= p(x_j),  p(x_i) = p(x_j)
                for two parameters [x_i], [x_j] of one sort and one path [p];
     constant:  p(x) <= c,  p(x) >= c
                for every such field and every constant [c] given.

   Those selectors are total -- every value of a single-constructor datatype
   is that constructor applied to its selectors -- so every qualifier here is
   fixed by the theory and needs no dependency.

   Why they are needed: the qualifiers extracted from a predicate's clauses
   relate terms that occur together in one atom of one clause, and a loop
   invariant over a borrowed structure is often a relation the clauses never
   state in one atom.  A predicate over the value a loop started from and the
   value it has now (both of one struct sort) needs "this field is unchanged",
   which is a relation between its two parameters, and none of its clauses
   compares them field by field.  Likewise a bound on a field that the program
   sets once, far from the loop, reaches the loop predicate only through the
   argument of another predicate's atom, never through a comparison in the
   loop's own clauses, so the constant is absent from that predicate's
   vocabulary.

   Only fields reached through at least one selector are given constant
   comparisons: an integer parameter itself is already compared with constants
   by the arithmetic part of the template.  [max_depth] bounds the walk. *)
let selector_path_quals ?(max_depth = 3) ~(cross : bool)
    ~(consts : Term.t list) (params : sort_env_list) =
  let is_single_cons dt =
    match Datatype.conses_of dt with [ _ ] -> true | _ -> false
    | exception exn_ when not (Common.Timer.is_async exn_) -> false
  in
  (* the integer fields of [t], each with the selector path leading to it,
     innermost selector first *)
  let rec leaves depth path t =
    match Term.sort_of t with
    | T_int.SInt -> if List.is_empty path then [] else [ (path, t) ]
    | T_dt.SDT dt when depth < max_depth && is_single_cons dt ->
        let cons = List.hd_exn (Datatype.conses_of dt) in
        List.concat_map (Datatype.sels_of_cons cons) ~f:(fun sel ->
            let name = Datatype.name_of_sel sel in
            leaves (depth + 1) (name :: path) (T_dt.mk_sel dt name t))
    | _ -> []
  in
  let per_param =
    List.map params ~f:(fun (x, s) -> (s, leaves 0 [] (Term.mk_var x s)))
  in
  let consts =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.filter consts ~f:(fun c -> Stdlib.(Term.sort_of c = T_int.SInt))
  in
  let with_consts =
    List.concat_map per_param ~f:(fun (_, ls) ->
        List.concat_map ls ~f:(fun (_, t) ->
            List.concat_map consts ~f:(fun c ->
                [ Formula.leq t c; Formula.geq t c ])))
  in
  let crossed =
    if not cross then []
    else
      List.concat
      @@ List.concat_mapi per_param ~f:(fun i (s1, ls1) ->
             List.filter_mapi per_param ~f:(fun j (s2, ls2) ->
                 if j <= i || not Stdlib.(s1 = s2) then None
                 else
                   Some
                     (List.concat_map ls1 ~f:(fun (p1, t1) ->
                          match
                            List.Assoc.find ls2 p1
                              ~equal:(List.equal String.equal)
                          with
                          | None -> []
                          | Some t2 ->
                              [
                                Formula.leq t1 t2;
                                Formula.geq t1 t2;
                                Formula.eq t1 t2;
                              ]))))
  in
  Set.Poly.of_list (crossed @ with_consts)
