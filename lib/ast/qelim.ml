(* Elimination of determined variables from a clause's pure part, over the
   higher-order term language [Logic].  Despite the module's name this is not
   quantifier elimination (that is [Z3interface.qelim]): the formula is read
   as a disjunction under the universal closure of its free variables, and a
   variable a disjunct determines is substituted away -- [x != t \/ C(x)]
   becomes [C(t)], a class of variables that disjuncts [x != y] identify
   becomes one variable, and a disjunct [x != c] for a constant fixes [x].
   Each step is exact for the universal closure in every model.

   [elim_free_univ_vars bounds exi_senv (uni_senv, defs, phi)] is the entry
   point: it never eliminates a variable of [bounds], of [exi_senv] (the
   unknowns) or a let-bound one, threads [defs] (the definitions of enclosing
   lets) through the same substitution, and returns the sort environment
   restricted to the variables still free.  It assumes [phi] alpha-renamed
   and let-normalised.  With [~simplify] (the default) the result is also
   simplified, which dominates its cost. *)
open Core
open Common.Ext
open Common.Combinator
open Logic

(* The largest tree a substitution [x := t] in [qelim_aux2] may produce, as the
   size of [t] times the number of occurrences of [x] it replaces; [None] (the
   default) bounds nothing.  The substitution places [t] physically at every
   occurrence, so a chain of definitions each using the previous variable more
   than once ([x2 = f x1 x1], [x3 = f x2 x2], ...) stays small in memory while
   its tree doubles with each link -- and every consumer after it walks the
   tree: the conversion between the two term representations, the evaluator,
   the encoding into Z3.  Declining a candidate is sound: the disequality it
   came from stays in the clause, and eliminating it is never required, so the
   clause is the same constraint either way.  Process-wide once set. *)
let max_subst_growth : int option Atomic.t = Atomic.make None

(* [occurrences_up_to cap x t] is [min (number of free occurrences of x in t)
   (cap + 1)], in time proportional to the part of [t] it walks until it stops:
   it counts the tree, as the consumers of the substitution's result do *)
let occurrences_up_to cap x t =
  let exception Over in
  let n = ref 0 in
  let rec go bound = function
    | Var (y, _) ->
        if Stdlib.(x = y) && not (Set.mem bound y) then (
          incr n;
          if !n > cap then raise Over)
    | Con _ -> ()
    | App (t1, t2, _) ->
        go bound t1;
        go bound t2
    | Let (y, _, t1, t2, _) ->
        go bound t1;
        go (Set.add bound y) t2
    | Bin (_, y, _, t1, _) -> go (Set.add bound y) t1
    | TyApp (t1, _, _) | TyLam (_, t1, _) -> go bound t1
  in
  try
    go Set.Poly.empty t;
    !n
  with Over -> cap + 1

let eqcs_of ?(only_bvs = None) phi =
  let eqcs, phis =
    List.partition_map (BoolTerm.disjuncts_of phi) ~f:(fun phi ->
        if BoolTerm.is_not phi then
          match Term.let_apps (BoolTerm.let_not phi) with
          | TyApp (Con (BoolTerm.Eq, _), ty, _), [ Var (x1, _); Var (x2, _) ]
            when match only_bvs with
                 | None -> true
                 | Some bvs -> Set.mem bvs x1 && Set.mem bvs x2 ->
              First (Set.Poly.of_list [ x1; x2 ], ty)
          | _ -> Second phi
        else
          match Term.let_apps phi with
          | TyApp (Con (BoolTerm.Neq, _), ty, _), [ Var (x1, _); Var (x2, _) ]
            when match only_bvs with
                 | None -> true
                 | Some bvs -> Set.mem bvs x1 && Set.mem bvs x2 ->
              First (Set.Poly.of_list [ x1; x2 ], ty)
          | _ -> Second phi)
  in
  (* [merge] unions overlapping classes until they are pairwise disjoint.  A
     round compares each class with every class kept so far, so a family of k
     classes costs k^2 set operations a round; on a predicate body with a few
     thousand argument equalities that was most of the time of this module.
     Classes in different connected components of the graph whose edges are
     the classes never meet in a round -- a kept class is a union of classes of
     one component -- so [merge] runs on each component's classes separately,
     and a component that is a single class is kept as it is (on such a family
     [merge] returns its input after one round).  The result is the same
     family, each merged class built by the same unions in the same order.
     Union-find over the variables finds the components in near-linear time. *)
  let merge eqcs =
    fix eqcs
      ~f:
        (Set.fold ~init:Set.Poly.empty ~f:(fun eqcs (eqc2, ty2) ->
             let updated = ref false in
             let eqcs' =
               Set.Poly.map eqcs ~f:(fun (eqc1, ty1) ->
                   if not @@ Set.are_disjoint eqc2 eqc1 then (
                     updated := true;
                     (Set.union eqc1 eqc2, ty1))
                   else (eqc1, ty1))
             in
             if !updated then eqcs' else Set.add eqcs (eqc2, ty2)))
      ~equal:Set.eqlen
  in
  let eqcs = Set.Poly.of_list eqcs in
  let parent = Hashtbl.Poly.create () in
  let rec find x =
    match Hashtbl.find parent x with
    | None -> x
    | Some p ->
        let r = find p in
        Hashtbl.set parent ~key:x ~data:r;
        r
  in
  Set.iter eqcs ~f:(fun (eqc, _) ->
      match Set.to_list eqc with
      | [] -> ()
      | x :: xs ->
          List.iter xs ~f:(fun y ->
              let rx = find x and ry = find y in
              if not (Ident.tvar_equal rx ry) then
                Hashtbl.set parent ~key:rx ~data:ry));
  let components = Hashtbl.Poly.create () in
  Set.iter eqcs ~f:(fun ((eqc, _) as c) ->
      Hashtbl.add_multi components ~key:(find (Set.min_elt_exn eqc)) ~data:c);
  let eqcs' =
    Hashtbl.fold components ~init:Set.Poly.empty ~f:(fun ~key:_ ~data acc ->
        match data with
        | [ c ] -> Set.add acc c
        | cs -> Set.union acc (merge (Set.Poly.of_list cs)))
  in
  (eqcs', phis)

(* Does [t] contain a beta-redex, an application whose function is a lambda?
   [Term.subst] reduces every redex it passes, whatever the substitution, so
   only on a term without one is [Term.subst] by the empty map a renaming of
   the bound variables.  Stops at the first redex and allocates nothing. *)
let rec has_beta_redex = function
  | App (Bin (Lambda, _, _, _, _), _, _) -> true
  | App (t1, t2, _) | Let (_, _, t1, t2, _) -> has_beta_redex t1 || has_beta_redex t2
  | Bin (_, _, _, t, _) | TyApp (t, _, _) | TyLam (_, t, _) -> has_beta_redex t
  | Var _ | Con _ -> false

(* [subst_all shortcuts sub (uni_senv, defs, phi)] applies [Term.subst sub] to
   [defs] and [phi].  With [shortcuts] and an empty [sub] on terms without a
   beta-redex it returns them unchanged: [Term.subst] would rebuild every node
   and give each binder a fresh name (a draw from the global counter each), so
   the two results are the same term up to the names of bound variables, and
   only the counter differs.  On a large resolvent that rebuild was a large part
   of each round of [qelim_aux1]. *)
let subst_all ~shortcuts sub (uni_senv, defs, phi) =
  if
    shortcuts && Map.Poly.is_empty sub
    && (not (has_beta_redex phi))
    && not (List.exists defs ~f:has_beta_redex)
  then (uni_senv, defs, phi)
  else
    Common.PhaseTime.with_phase "subst" @@ fun () ->
    (uni_senv, List.map defs ~f:(Term.subst sub), Term.subst sub phi)

let elim_eqcls ?(shortcuts = true) let_bounds bounds (uni_senv, defs, phi) =
  let eqcs, phis1 = eqcs_of phi in
  let sub, phis2 =
    Set.Poly.map eqcs ~f:(fun (eqc, ty) ->
        let bvs, fvs = Set.partition_tf ~f:(Map.Poly.mem bounds) eqc in
        match (Set.to_list bvs, Set.to_list fvs) with
        | [], fv :: fvs' ->
            let tt = Term.mk_var fv in
            (List.map fvs' ~f:(fun x -> (x, tt)), [])
        | (bv :: bvs' as bvs), fvs -> (
            match List.find bvs ~f:(Fn.non @@ Map.Poly.mem let_bounds) with
            | None -> (
                match fvs with
                | [] ->
                    let tt = Term.mk_var bv in
                    ( [],
                      List.map (fvs @ bvs') ~f:(fun x ->
                          BoolTerm.neq_of ty tt (Term.mk_var x)) )
                | fv :: fvs' ->
                    let tt = Term.mk_var fv in
                    ( List.map fvs' ~f:(fun x -> (x, tt)),
                      List.map bvs ~f:(fun x ->
                          BoolTerm.neq_of ty tt (Term.mk_var x)) ))
            | Some bv ->
                let bvs' = List.filter bvs ~f:(Stdlib.( <> ) bv) in
                let tt = Term.mk_var bv in
                ( List.map fvs ~f:(fun x -> (x, tt)),
                  List.map bvs' ~f:(fun x ->
                      BoolTerm.neq_of ty tt (Term.mk_var x)) ))
        | _, _ -> assert false)
    |> Set.to_list |> List.unzip
    |> Tuple2.map_both ~f1:List.concat ~f2:List.concat
  in
  let sub = Map.Poly.of_alist_exn sub in
  subst_all ~shortcuts sub (uni_senv, defs, BoolTerm.or_of @@ phis1 @ phis2)

let consts_of bounds phi =
  match Term.let_apps phi with
  | Var (x, _), [] ->
      if Map.Poly.mem bounds x then Second phi
      else First (x, BoolTerm.False, BoolTerm.SBool)
  | Con (BoolTerm.Not, _), [ Var (x, _) ] ->
      if Map.Poly.mem bounds x then Second phi
      else First (x, BoolTerm.True, BoolTerm.SBool)
  | ( TyApp (Con (BoolTerm.Neq, _), ty, _),
      ([ Var (x, _); Con (sym, _) ] | [ Con (sym, _); Var (x, _) ]) ) ->
      if Map.Poly.mem bounds x then Second phi else First (x, sym, ty)
  | ( TyApp (Con (BoolTerm.Eq, _), ty, _),
      ( [ Var (x, _); Con (BoolTerm.True, _) ]
      | [ Con (BoolTerm.True, _); Var (x, _) ] ) ) ->
      if Map.Poly.mem bounds x then Second phi else First (x, BoolTerm.False, ty)
  | ( TyApp (Con (BoolTerm.Eq, _), ty, _),
      ( [ Var (x, _); Con (BoolTerm.False, _) ]
      | [ Con (BoolTerm.False, _); Var (x, _) ] ) ) ->
      if Map.Poly.mem bounds x then Second phi else First (x, BoolTerm.True, ty)
  | _ -> Second phi

(* [elim_consts ~nnf bounds (uni_senv, defs, phi)] fixes the variables that a
   disjunct of [phi] gives one value ([x], [not x], [x <> c], [x = true],
   [x = false]) to the constant that falsifies that disjunct, and returns the
   result with a flag: whether its formula is known to be a fixed point of
   [BoolTerm.nnf_of] disjunct by disjunct.  [~nnf:false] asserts that of the
   input (each disjunct of [phi] equal to its [nnf_of]), and then the disjuncts
   are read as they are; the result is the same.
   The flag is [true] exactly when no constant was substituted (or the clause
   was found valid): the remaining disjuncts are [nnf_of] images, which [nnf_of]
   leaves as they are.  A substituted constant can break that -- [x := true] in
   a disjunct [not x /\ y] gives [not true /\ y], which [nnf_of] rewrites to
   [false /\ y] -- so after a substitution the next call must normalise again. *)
let elim_consts ?(shortcuts = true) ?(nnf = true) bounds (uni_senv, defs, phi) =
  let cm, phis1 =
    Common.PhaseTime.with_phase "nnf" (fun () ->
        if nnf then List.map (BoolTerm.disjuncts_of phi) ~f:BoolTerm.nnf_of
        else BoolTerm.disjuncts_of phi)
    |> List.partition_map ~f:(consts_of bounds)
  in
  try
    let sub =
      List.fold ~init:Map.Poly.empty cm ~f:(fun acc (x, sym, _ty) ->
          Map.force_add acc x (Term.mk_con sym))
    in
    ( subst_all ~shortcuts sub (uni_senv, defs, BoolTerm.or_of phis1),
      Map.Poly.is_empty sub )
  with exn_ when not (Common.Timer.is_async exn_) ->
    ((uni_senv, [], BoolTerm.mk_bool true), true)

let reduce (uni_senv, defs, body) =
  let fvs = Set.Poly.union_list @@ List.map ~f:Term.fvs_of (body :: defs) in
  (Map.Poly.filter_keys uni_senv ~f:(Set.mem fvs), defs, body)

(* [qelim_aux1 ~shortcuts] gives, without [shortcuts], what the plain rounds
   give, and with them the same result up to the names of bound variables (equal
   wherever [phi] and [defs] have no binder).  The shortcuts: a substitution
   that is empty is not performed ([subst_all]), and the negation normal form is
   not recomputed for a formula already in it ([elim_consts]'s flag): after an
   [elim_consts] that substituted nothing, since [elim_eqcls] substitutes a
   variable for a variable and adds disequalities between variables, neither of
   which [nnf_of] would change. *)
let rec qelim_aux1 ?(shortcuts = true) ?(nnf = true) let_bounds bounds exi_senv
    (uni_senv, defs, phi) =
  let (uni_senv', defs', phi'), fixed =
    let bounds' = Map.force_merge_list [ exi_senv; let_bounds; bounds ] in
    let ph = Common.PhaseTime.with_phase in
    let x, fixed1 =
      ph "consts" (fun () ->
          elim_consts ~shortcuts ~nnf bounds' (uni_senv, defs, phi))
    in
    let x = ph "eqcls" (fun () -> elim_eqcls ~shortcuts let_bounds bounds' x) in
    let x, fixed2 =
      ph "consts" (fun () ->
          elim_consts ~shortcuts ~nnf:(not (shortcuts && fixed1)) bounds' x)
    in
    (ph "reduce" (fun () -> reduce x), fixed2)
  in
  if Map.Poly.length uni_senv > Map.Poly.length uni_senv' then
    qelim_aux1 ~shortcuts
      ~nnf:(not (shortcuts && fixed))
      let_bounds bounds exi_senv (uni_senv', defs', phi')
  else (uni_senv', defs', phi')

let qelim_aux2 let_bounds bounds exi_senv (uni_senv, defs, phi0) =
  let bounds' = Map.force_merge_list [ exi_senv; let_bounds; bounds ] in
  let has_no_inter x s =
    (not @@ Set.mem s x) && Set.are_disjoint (Map.key_set let_bounds) s
  in
  let solve_neq (t1, t2) =
    match (t1, t2) with
    | Var (x, _), t
      when (not (Map.Poly.mem bounds' x)) && has_no_inter x (Term.fvs_of t) ->
        Some (x, t)
    | t, Var (x, _)
      when (not (Map.Poly.mem bounds' x)) && has_no_inter x (Term.fvs_of t) ->
        Some (x, t)
    (* for integers *)
    | App (App (Con ((IntTerm.(Add | Sub) as s), _), Var (x, _), _), t1, _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
    | t2, App (App (Con ((IntTerm.(Add | Sub) as s), _), Var (x, _), _), t1, _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
    | App (App (Con ((IntTerm.Add as s), _), t1, _), Var (x, _), _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
    | t2, App (App (Con ((IntTerm.Add as s), _), t1, _), Var (x, _), _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
    | App (App (Con ((IntTerm.Sub as s), _), t1, _), Var (x, _), _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app s [ t1; t2 ])
    | t2, App (App (Con ((IntTerm.Sub as s), _), t1, _), Var (x, _), _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app s [ t1; t2 ])
    (* for reals *)
    | ( App (App (Con ((RealTerm.(RAdd | RSub) as s), _), Var (x, _), _), t1, _),
        t2 )
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
    | ( t2,
        App (App (Con ((RealTerm.(RAdd | RSub) as s), _), Var (x, _), _), t1, _)
      )
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
    | App (App (Con ((RealTerm.RAdd as s), _), t1, _), Var (x, _), _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
    | t2, App (App (Con ((RealTerm.RAdd as s), _), t1, _), Var (x, _), _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
    | App (App (Con ((RealTerm.RSub as s), _), t1, _), Var (x, _), _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app s [ t1; t2 ])
    | t2, App (App (Con ((RealTerm.RSub as s), _), t1, _), Var (x, _), _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app s [ t1; t2 ])
    | _ -> None
  in
  (* The candidate elimination one disjunct yields, if any.  Everything this
     reads besides the disjunct -- [bounds'], [let_bounds], [exi_senv] -- is
     fixed for the whole call except [merged], the sort environment the
     fallback simplifies in. *)
  let cand_of merged phi =
    match Term.let_apps phi with
    | TyApp (Con (BoolTerm.Neq, _), ty, _), [ t1; t2 ] -> (
        match solve_neq (t1, t2) with
        | Some _ as res -> res
        | None when IntTerm.is_int_sort ty || RealTerm.is_real_sort ty -> (
            (* [Normalizer] emits linear combinations such as
                     [1 + x + -1 * y != 0], which none of the patterns above
                     matches; simplifying both sides first turns them back into
                     the [(1 + x) - y] shape that they do match. *)
            try
              let simplify = ExtTerm.simplify_term exi_senv merged in
              solve_neq (simplify t1, simplify t2)
            with exn_ when not (Common.Timer.is_async exn_) -> None)
        | None -> None)
    | TyApp (Con (BoolTerm.Eq, _), BoolTerm.SBool, _), [ t1; t2 ] -> (
        match (t1, t2) with
        | Var (x, _), t
          when (not (Map.Poly.mem bounds' x)) && has_no_inter x (Term.fvs_of t)
          ->
            Some (x, BoolTerm.neg_of t)
        | t, Var (x, _)
          when (not (Map.Poly.mem bounds' x)) && has_no_inter x (Term.fvs_of t)
          ->
            Some (x, BoolTerm.neg_of t)
        | _ -> None)
    | _ -> None
  in
  (* Each disjunct is carried with the candidate it yields, and only the
     disjuncts a round actually changes are re-examined.  The candidate is a
     function of the disjunct and of the sort environment, and a round changes
     neither for a disjunct the eliminated variable does not occur in: it is
     not substituted, and the only change to the environment is the removal of
     that same variable, which by then occurs nowhere.  Counted on one
     `LinearArbitrary` file before this: 996,815 examinations across 25,249
     rounds, of which 922,328 reached the fallback that simplifies both sides
     of a disequality -- almost all of the search, repeated on disjuncts that
     had not changed since the round before. *)
  (* a candidate is taken unless the bound above says its substitution would
     build too large a tree over the disjuncts and definitions it rewrites; a
     declined one is skipped, and the next disjunct's candidate is tried *)
  let within_bound defs phis_c (x, t) =
    match Atomic.get max_subst_growth with
    | None -> true
    | Some cap ->
        let size = Term.ast_size_up_to cap t in
        size <= 1
        ||
        let budget = cap / size in
        let occ =
          List.fold_until
            (defs @ List.map ~f:fst phis_c)
            ~init:0
            ~f:(fun acc u ->
              let acc = acc + occurrences_up_to (budget - acc) x u in
              if acc > budget then Stop acc else Continue acc)
            ~finish:Fn.id
        in
        occ <= budget
  in
  let rec loop uni_senv defs phis_c =
    let res =
      List.find_map phis_c ~f:(fun (_, c) ->
          match c with
          | Some xt when within_bound defs phis_c xt -> Some xt
          | _ -> None)
    in
    let res =
      match res with
      | Some (x, t) -> Some (x, t)
      | None ->
          (* the disjuncts without their candidates.  Taken here and at the exit
             below rather than at the top of the loop: the search above reads
             only the candidates, so projecting the pair rebuilt a list of every
             disjunct on every round -- 25,249 rebuilds of a 78-element list on
             one `LinearArbitrary` file -- to serve the 613 rounds that reach
             this branch, one per call. *)
          let phis = List.map ~f:fst phis_c in
          List.filter_map phis ~f:(fun phi ->
              match
                List.map
                  (BoolTerm.conjuncts_of phi)
                  ~f:(consts_of Map.Poly.empty)
              with
              | [
               First (x1, sym1, BoolTerm.SBool); First (x2, sym2, BoolTerm.SBool);
              ]
                when Stdlib.(x1 <> x2) ->
                  Some (x1, sym1, x2, sym2)
              | _ -> None)
          |> List.find_distinct_pair
               ~f:(fun (x11, sym11, x12, sym12) (x21, sym21, x22, sym22) ->
                 if
                   Stdlib.(
                     (x11 = x21 && x12 = x22 && sym11 <> sym21)
                     || (x11 = x22 && x12 = x21 && sym11 <> sym22))
                 then
                   if Stdlib.(sym11 = sym12 && sym21 = sym22) then
                     if
                       (not (Map.Poly.mem bounds' x11))
                       && not (Map.Poly.mem let_bounds x12)
                     then Some (x11, BoolTerm.neg_of @@ Term.mk_var x12)
                     else if
                       (not (Map.Poly.mem bounds' x12))
                       && not (Map.Poly.mem let_bounds x11)
                     then Some (x12, BoolTerm.neg_of @@ Term.mk_var x11)
                     else None
                   else if Stdlib.(sym11 <> sym12 && sym21 <> sym22) then
                     if
                       (not (Map.Poly.mem bounds' x11))
                       && not (Map.Poly.mem let_bounds x12)
                     then Some (x11, Term.mk_var x12)
                     else if
                       (not (Map.Poly.mem bounds' x12))
                       && not (Map.Poly.mem let_bounds x11)
                     then Some (x12, Term.mk_var x11)
                     else None
                   else None
                 else None)
    in
    match res with
    | Some (x, t) ->
        let uni_senv' = Map.Poly.remove uni_senv x in
        let sub =
          Common.PhaseTime.with_phase "aux2-simpterm" (fun () ->
              Map.Poly.singleton x @@ ExtTerm.simplify_term exi_senv uni_senv' t)
        in
        if false then
          print_endline
          @@ sprintf "[qelim_aux2] %s ==> %s" (Ident.name_of_tvar x)
               (ExtTerm.str_of t);
        (* Substitute only into the terms the eliminated variable occurs in.
           This loop removes one variable per round and then rewrites every
           definition and every disjunct, and the rewriter rebuilds a term node
           by node whether or not anything under it changed -- so a term that
           cannot mention the variable is copied in full for nothing.  Counted
           on one `LinearArbitrary` file: 1,933,549 terms rewritten across
           25,249 rounds, of which 49,255 (2.5%) mention the variable being
           eliminated and **none** came back physically equal to its input.
           The occurrence test stops at the first hit and builds no set, where
           asking for the free variables would build one per term per round. *)
        let subst_if_occurs t =
          if Term.occurs_free x t then Term.subst sub t else t
        in
        let merged' = Map.force_merge let_bounds uni_senv' in
        let step (t, c) =
          if Term.occurs_free x t then
            (* the sharing-preserving substitution rebuilds only the path down to
               the occurrences, where the ordinary one rebuilds every node and
               renames every binder it passes; the term is kept for the next
               round, so what it leaves shared is what the next round skips.
               It also enters binders itself, renaming one only where it could
               capture, so a disjunct with deeply nested binders costs one
               traversal rather than one per binder *)
            let t' =
              Common.PhaseTime.with_phase "aux2-subst" (fun () ->
                  Term.subst_sharing_linear sub t)
            in
            ( t',
              Common.PhaseTime.with_phase "aux2-cand" (fun () ->
                  cand_of merged' t') )
          else (t, c)
        in
        loop uni_senv'
          (List.map ~f:subst_if_occurs defs)
          (List.map ~f:step phis_c)
    | None -> (uni_senv, defs, List.map ~f:fst phis_c)
  in
  let uni_senv, defs, phis =
    let merged = Map.force_merge let_bounds uni_senv in
    loop uni_senv defs
      (List.map
         (List.map ~f:BoolTerm.nnf_of (BoolTerm.disjuncts_of phi0))
         ~f:(fun phi -> (phi, cand_of merged phi)))
  in
  (uni_senv, defs, BoolTerm.or_of phis)

let print_log = false

(* An instrument, read once: with [COAR_QELIM_GROWTH] set, every call of
   [app_qelim] whose result is more than four times its input as a tree, or that
   takes more than a second of CPU time, prints one line to stderr with the input's and the
   results' tree sizes (each counted up to ten million nodes) and the result's
   size as a DAG of physically distinct nodes.  It changes nothing it measures. *)
let growth_trace = Option.is_some (Sys.getenv "COAR_QELIM_GROWTH")

(* the number of physically distinct nodes of [t], up to [cap + 1] *)
let dag_size_up_to cap t =
  let seen : (int, term list) Stdlib.Hashtbl.t = Stdlib.Hashtbl.create 1024 in
  let n = ref 0 in
  let exception Over in
  let rec go t =
    let h = Stdlib.Hashtbl.hash_param 30 60 t in
    let bucket = Option.value ~default:[] (Stdlib.Hashtbl.find_opt seen h) in
    if not (List.exists bucket ~f:(phys_equal t)) then (
      Stdlib.Hashtbl.replace seen h (t :: bucket);
      incr n;
      if !n > cap then raise Over;
      match t with
      | Var _ | Con _ -> ()
      | App (t1, t2, _) | Let (_, _, t1, t2, _) ->
          go t1;
          go t2
      | Bin (_, _, _, t1, _) | TyApp (t1, _, _) | TyLam (_, t1, _) -> go t1)
  in
  try
    go t;
    !n
  with Over -> cap + 1

let report_growth ~started phi phi2 phi3 =
  let cap = 10_000_000 in
  let secs = Stdlib.Sys.time () -. started in
  let s_in = Term.ast_size_up_to cap phi in
  let s3 = Term.ast_size_up_to cap phi3 in
  if Float.(secs > 1.0) || s3 > 4 * s_in then
    Printf.eprintf "[qelim-growth] in=%d aux2=%d out=%d out_dag=%d secs=%.3f\n%!"
      s_in
      (Term.ast_size_up_to cap phi2)
      s3 (dag_size_up_to cap phi3) secs

(* [app_qelim_steps] is [app_qelim ~simplify:false] with a flag: [false] when
   no free variable was left to eliminate and the input came back as it was
   (in which case [app_qelim] does not simplify either), [true] when the
   eliminations ran and [app_qelim] would simplify their result. *)
let app_qelim_steps ?(shortcuts = true) let_bounds bounds exi_senv
    (uni_senv, defs, phi) =
  let fvs =
    Common.PhaseTime.with_phase "fvs" @@ fun () ->
    Set.diff (Term.fvs_of phi)
      (Map.key_set @@ Map.force_merge_list [ exi_senv; let_bounds; bounds ])
  in
  if Set.is_empty fvs then (
    if print_log then print_endline "[app_qelim] skipped";
    (uni_senv, defs, phi, false))
  else (
    if print_log then
      print_endline
      @@ sprintf "[app_qelim] begin eliminating %s in %s"
           (String.concat_map_set ~sep:", " ~f:Ident.name_of_tvar fvs)
           (LogicOld.Formula.str_of
           @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi);
    let uni_senv, defs, phi1 =
      Common.PhaseTime.with_phase "aux1" (fun () ->
          qelim_aux1 ~shortcuts let_bounds bounds exi_senv
            (uni_senv, defs, phi))
    in
    if print_log then print_endline "  [app_qelim] qelim_aux1";
    let uni_senv, defs, phi2 =
      Common.PhaseTime.with_phase "aux2" (fun () ->
          qelim_aux2 let_bounds bounds exi_senv (uni_senv, defs, phi1))
    in
    if print_log then (
      print_endline "  [app_qelim] qelim_aux2";
      print_endline
      @@ sprintf "[app_qelim] end: %s"
           (LogicOld.Formula.str_of
           @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi2));
    (uni_senv, defs, phi2, true))

let app_qelim ?(simplify = true) ?(shortcuts = true) let_bounds bounds exi_senv
    (uni_senv, defs, phi) =
  let started = if growth_trace then Stdlib.Sys.time () else 0. in
  let uni_senv, defs, phi2, ran =
    app_qelim_steps ~shortcuts let_bounds bounds exi_senv (uni_senv, defs, phi)
  in
  if not ran then (uni_senv, defs, phi2)
  else
    let phi3 =
      if simplify then
        Common.PhaseTime.with_phase "final-simplify" (fun () ->
            ExtTerm.simplify_formula exi_senv
              (Map.force_merge let_bounds uni_senv)
              phi2)
      else phi2
    in
    if growth_trace then report_growth ~started phi phi2 phi3;
    (uni_senv, defs, phi3)

(* Eliminate the free variables of [defs] and [phi] that are *implicitly*
   universally quantified -- a clause's own variables, not the ones a [Bind]
   node quantifies.  The old name of this function was [qelim], which reads as
   quantifier elimination and is what [Z3interface.qelim] really does; on the
   solving path here the formula is quantifier-free at every call (838 of 838
   over three benchmarks) and what the function removes is variables an equality
   or a definition determines -- six universals became three on one measured
   resolvent.

   [~simplify], which defaults to [true], is not a tidying flag: the
   simplification it controls is where nearly all of the time goes, 18.0 s of a
   22.2 s resolution phase on one benchmark, so a caller that does not need it
   should say so.

   @param [bounds] variables that must not be eliminated.
   Assumes [phi] is alpha-renamed and let-normalized. *)
let rec elim_free_univ_vars ?(simplify = true) ?(let_bounds = Map.Poly.empty)
    bounds exi_senv (uni_senv, defs, phi) =
  match phi with
  | Let (var, sort, def, body, info) -> (
      let let_bounds' = Map.Poly.set ~key:var ~data:sort let_bounds in
      match
        elim_free_univ_vars ~simplify ~let_bounds:let_bounds' bounds exi_senv
          (Map.Poly.set uni_senv ~key:var ~data:sort, def :: defs, body)
      with
      | _, [], _ -> assert false
      | uni_senv_body, def' :: defs', body' ->
          let fvs_body = Term.fvs_of body' in
          if Set.mem fvs_body var then
            let uni_senv_body' = Map.Poly.remove uni_senv_body var in
            let uni_senv_def, _, def'' =
              reduce
              @@
              if BoolTerm.is_bool_sort sort then
                let bounds_def =
                  let senv = Map.force_merge exi_senv uni_senv_body' in
                  Set.fold
                    (Set.diff
                       (Set.Poly.union_list
                          (fvs_body :: List.map ~f:Term.fvs_of defs'))
                       (Map.key_set let_bounds'))
                    ~init:bounds
                    ~f:(fun acc tvar ->
                      Map.Poly.set ~key:tvar
                        ~data:(Map.Poly.find_exn senv tvar)
                        acc)
                in
                app_qelim ~simplify let_bounds bounds_def exi_senv
                  (uni_senv, [], def')
              else (uni_senv, [], def')
            in
            ( Map.force_merge uni_senv_def uni_senv_body',
              defs',
              Let (var, sort, def'', body', info) )
          else (uni_senv_body, defs', body'))
  | _ ->
      let r = app_qelim ~simplify let_bounds bounds exi_senv (uni_senv, defs, phi) in
      Common.PhaseTime.with_phase "reduce" (fun () -> reduce r)

(* [elim_free_univ_vars] on the first-order term representation, converting in
   and out; the conversion is 0.08 s of 18 on the benchmark above, so it is not
   where this costs *)
(* [simplify_on_old_side] (on): see [elim_free_univ_vars_old].  Process-wide;
   off only for the property check that compares the two routes. *)
let simplify_on_old_side = Atomic.make true

(* Set only by the property check: the first-order route then leaves out the
   simplification, the mutant the check must tell apart.  Never set in a
   solving run. *)
let old_side_mutant = Atomic.make false

let elim_free_univ_vars_old_via_logic ~simplify bounds exi_senv (uni_senv, phi)
    =
  let uni_senv', _, phi' =
    elim_free_univ_vars ~simplify bounds exi_senv (uni_senv, [], phi)
  in
  ( uni_senv',
    Common.PhaseTime.with_phase "to-old" (fun () ->
        ExtTerm.to_old_fml exi_senv uni_senv' phi') )

(* [phi] with every quantifier block [Q x1 ... xn. body] written as the
   nest [Q x1. ... Q xn. body], inside embedded formulas too: the form the
   conversion to the higher-order representation and back gives a block,
   since that representation binds one variable per node *)
let rec nest_binder_blocks (phi : LogicOld.Formula.t) : LogicOld.Formula.t =
  let open LogicOld in
  match phi with
  | Formula.Atom (atom, info) ->
      let atom' = nest_atom atom in
      if phys_equal atom atom' then phi else Formula.mk_atom ~info atom'
  | Formula.UnaryOp (op, p, info) ->
      let p' = nest_binder_blocks p in
      if phys_equal p p' then phi else Formula.mk_unop ~info op p'
  | Formula.BinaryOp (op, p1, p2, info) ->
      let p1' = nest_binder_blocks p1 and p2' = nest_binder_blocks p2 in
      if phys_equal p1 p1' && phys_equal p2 p2' then phi
      else Formula.mk_binop ~info op p1' p2'
  | Formula.Bind (binder, args, body, info) -> (
      let body' = nest_binder_blocks body in
      match args with
      | [ _ ] when phys_equal body body' -> phi
      | [ a ] -> Formula.mk_bind ~info binder [ a ] body'
      | [] -> body'
      | _ ->
          List.fold_right args ~init:body' ~f:(fun a acc ->
              Formula.mk_bind binder [ a ] acc))
  | Formula.LetFormula (x, s, def, body, info) ->
      let def' = nest_term def and body' = nest_binder_blocks body in
      if phys_equal def def' && phys_equal body body' then phi
      else Formula.mk_let_formula ~info x s def' body'
  | Formula.LetRec _ -> phi

and nest_atom (atom : LogicOld.Atom.t) : LogicOld.Atom.t =
  let open LogicOld in
  match atom with
  | Atom.App (pred, args, info) ->
      let args' = List.map args ~f:nest_term in
      if List.for_all2_exn args args' ~f:phys_equal then atom
      else Atom.mk_app ~info pred args'
  | Atom.True _ | Atom.False _ -> atom

and nest_term (t : LogicOld.Term.t) : LogicOld.Term.t =
  let open LogicOld in
  match t with
  | Term.Var _ -> t
  | Term.FunApp (T_bool.Formula phi, args, info) ->
      let phi' = nest_binder_blocks phi in
      let args' = List.map args ~f:nest_term in
      if phys_equal phi phi' && List.for_all2_exn args args' ~f:phys_equal then t
      else Term.mk_fsym_app ~info (T_bool.Formula phi') args'
  | Term.FunApp (sym, args, info) ->
      let args' = List.map args ~f:nest_term in
      if List.for_all2_exn args args' ~f:phys_equal then t
      else Term.mk_fsym_app ~info sym args'
  | Term.LetTerm (x, s, def, body, info) ->
      let def' = nest_term def and body' = nest_term body in
      if phys_equal def def' && phys_equal body body' then t
      else Term.mk_let_term ~info x s def' body'

(* With [simplify] on, a formula with no [let] at its root and
   [simplify_on_old_side] set: the eliminations run on the higher-order form
   as always, and the simplification that ends them is the first-order
   [Evaluator.simplify] of their result converted once, which is returned as
   it is.  The route through [elim_free_univ_vars] converts that simplified
   formula to the higher-order form ([ExtTerm.simplify_formula]) and back
   again here, two whole-formula conversions per resolvent that measured a
   third of this function's time on a large input.  The two routes give the
   same formula when converting [Evaluator.simplify]'s output there and back
   is the identity, and the same environment when the variables kept are
   those free in it; the property check compares them, fresh-name draws
   included, on random formulas and on every call of benchmark inputs, and
   the route here falls back to the other one where it does not apply (a
   root [let], a lambda root, an exception in the conversion, the growth
   trace). *)
let elim_free_univ_vars_old_main ?(simplify = true) bounds exi_senv (uni_senv, phi) =
  let phi =
    Common.PhaseTime.with_phase "of-old" (fun () -> ExtTerm.of_old_formula phi)
  in
  match phi with
  | (Let _ | Bin (Lambda, _, _, _, _)) ->
      elim_free_univ_vars_old_via_logic ~simplify bounds exi_senv (uni_senv, phi)
  | _ when (not simplify) || growth_trace || not (Atomic.get simplify_on_old_side)
    ->
      elim_free_univ_vars_old_via_logic ~simplify bounds exi_senv (uni_senv, phi)
  | _ -> (
      let uni_senv1, defs, phi2, ran =
        app_qelim_steps Map.Poly.empty bounds exi_senv (uni_senv, [], phi)
      in
      let via_logic_from_steps () =
        (* the rest of [app_qelim] and [elim_free_univ_vars], as they would
           have run *)
        let phi3 =
          if ran then
            Common.PhaseTime.with_phase "final-simplify" (fun () ->
                ExtTerm.simplify_formula exi_senv uni_senv1 phi2)
          else phi2
        in
        let uni_senv', _, phi3 =
          Common.PhaseTime.with_phase "reduce" (fun () ->
              reduce (uni_senv1, defs, phi3))
        in
        ( uni_senv',
          Common.PhaseTime.with_phase "to-old" (fun () ->
              ExtTerm.to_old_fml exi_senv uni_senv' phi3) )
      in
      if not ran then via_logic_from_steps ()
      else
        match phi2 with
        | Bin (Lambda, _, _, _, _) -> via_logic_from_steps ()
        | _ -> (
            match
              Common.PhaseTime.with_phase "final-simplify" (fun () ->
                  let ph = Common.PhaseTime.with_phase in
                  ph "sf-to-old" (fun () ->
                      ExtTerm.to_old_fml exi_senv uni_senv1 phi2)
                  |> fun x ->
                  if Atomic.get old_side_mutant then x
                  else ph "sf-simplify" (fun () -> Evaluator.simplify x))
            with
            | exception e when not (Common.Timer.is_async e) ->
                (* [ExtTerm.simplify_formula]'s own retry after its first
                   attempt raised, then the rest as on the other route *)
                let phi3 =
                  try
                    ExtTerm.to_old_fml exi_senv uni_senv1 phi2
                    |> Evaluator.simplify |> ExtTerm.of_old_formula
                  with exn_ when not (Common.Timer.is_async exn_) -> raise e
                in
                let uni_senv', _, phi3 = reduce (uni_senv1, defs, phi3) in
                (uni_senv', ExtTerm.to_old_fml exi_senv uni_senv' phi3)
            | phi_old ->
                let phi_old = nest_binder_blocks phi_old in
                let fvs = LogicOld.Formula.fvs_of phi_old in
                (Map.Poly.filter_keys uni_senv1 ~f:(Set.mem fvs), phi_old)))

(* let rec qelim_clause exi_senv (uni_senv, ps, ns, phi) =
   let senv = Map.force_merge exi_senv uni_senv in
   let atms = Set.Poly.map (Set.union ps ns) ~f:(ExtTerm.to_old_atom senv) in
   let papp_tvs = of_old_sort_env_list @@ Set.to_list @@ Util.Set.concat_map atms ~f:LogicOld.Atom.term_sort_env_of in
   let bounds = (* this is essential for qualifiers extraction *) Map.force_merge (Map.Poly.of_alist_exn papp_tvs) exi_senv in
   let phi' =
     ExtTerm.simplify_formula senv (snd @@ g bounds @@ snd @@ f bounds phi)
   in
   let uni_senv', ps, ns, phi' = Clause.reduce_sort_map (uni_senv, ps, ns, phi') in
   if Map.Poly.length uni_senv > Map.Poly.length uni_senv' then
     qelim_clause exi_senv (uni_senv', ps, ns, phi')
   else (uni_senv', ps, ns, phi')

   let qelim_clause_set exi_senv = Set.Poly.map ~f:qelim_clause exi_senv *)

(* A property check's instrument ([route_check], off): every call of
   [elim_free_univ_vars_old] runs both routes -- [simplify_on_old_side] on,
   then off -- each from the same fresh-name counters, and counts the calls,
   those that drew fresh names, and those whose results (the environment as a
   list, the formula, or the exception's text) or counters afterwards differ.
   The counters are left where the first route left them, and its answer is
   returned.  A test instrument only: the second run draws the names the
   first drew again. *)
let route_check = Atomic.make false
let route_checked = Atomic.make 0
let route_drew = Atomic.make 0
let route_mismatched = Atomic.make 0

let fresh_counters =
  Ident.
    [
      tvar_count; dontcare_count; dummy_tvar_count; svar_count; evar_count;
      rvar_count; pvar_count; parameter_cout; head_arg_count;
    ]

let elim_free_univ_vars_old ?(simplify = true) bounds exi_senv (uni_senv, phi) =
  if not (Atomic.get route_check) then
    elim_free_univ_vars_old_main ~simplify bounds exi_senv (uni_senv, phi)
  else
    let get () =
      ( List.map fresh_counters ~f:Atomic.get,
        Option.map (Stdlib.Domain.DLS.get Ident.replay_key) ~f:(fun (_, n) -> !n) )
    in
    let set (cs, r) =
      List.iter2_exn fresh_counters cs ~f:Atomic.set;
      match (Stdlib.Domain.DLS.get Ident.replay_key, r) with
      | Some (_, n), Some v -> n := v
      | _ -> ()
    in
    let saved_flag = Atomic.get simplify_on_old_side in
    let run flag =
      Atomic.set simplify_on_old_side flag;
      let r =
        try
          Ok (elim_free_univ_vars_old_main ~simplify bounds exi_senv (uni_senv, phi))
        with e when not (Common.Timer.is_async e) -> Error e
      in
      Atomic.set simplify_on_old_side saved_flag;
      r
    in
    let start = get () in
    let a = run true in
    let after_a = get () in
    set start;
    let b = run false in
    let after_b = get () in
    set after_a;
    Atomic.incr route_checked;
    if Stdlib.(after_a <> start) then Atomic.incr route_drew;
    let same_results =
      match (a, b) with
      | Ok (e1, p1), Ok (e2, p2) -> (
          try
            Stdlib.compare (Map.Poly.to_alist e1) (Map.Poly.to_alist e2) = 0
            && Stdlib.compare p1 p2 = 0
          with _ -> false)
      | Error e1, Error e2 -> String.equal (Exn.to_string e1) (Exn.to_string e2)
      | _ -> false
    in
    let same = Stdlib.(after_a = after_b) && same_results in
    if not same then (
      Atomic.incr route_mismatched;
      (* [COAR_ROUTE_DIFF] (instrument only): the first differing pairs *)
      if Option.is_some (Sys.getenv "COAR_ROUTE_DIFF")
         && Atomic.get route_mismatched <= 3
      then
        let show = function
          | Ok (e, p) ->
              String.concat ~sep:","
                (List.map (Map.Poly.to_alist e) ~f:(fun (x, srt) ->
                     Ident.name_of_tvar x ^ ":" ^ Logic.ExtTerm.str_of_sort srt))
              ^ " | " ^ LogicOld.Formula.str_of p
          | Error e -> "raised " ^ Exn.to_string e
        in
        Printf.eprintf "[route-diff] counters equal %b\nA: %s\nB: %s\n%!"
          Stdlib.(after_a = after_b) (show a) (show b));
    match a with Ok r -> r | Error e -> raise e
