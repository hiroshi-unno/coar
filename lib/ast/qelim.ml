open Core
open Common.Ext
open Common.Combinator
open Logic

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
  let eqcs' =
    fix (Set.Poly.of_list eqcs)
      ~f:
        (Set.fold ~init:Set.Poly.empty ~f:(fun eqcs (eqc2, ty2) ->
             let updated = ref false in
             let eqcs' =
               Set.Poly.map eqcs ~f:(fun (eqc1, ty1) ->
                   if not @@ Set.disjoint eqc2 eqc1 then (
                     updated := true;
                     (Set.union eqc1 eqc2, ty1))
                   else (eqc1, ty1))
             in
             if !updated then eqcs' else Set.add eqcs (eqc2, ty2)))
      ~equal:Set.eqlen
  in
  (eqcs', phis)

let elim_eqcls let_bounds bounds (uni_senv, defs, phi) =
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
    |> Pair.map List.concat List.concat
  in
  let sub = Map.Poly.of_alist_exn sub in
  ( uni_senv,
    List.map defs ~f:(Term.subst sub),
    Term.subst sub @@ BoolTerm.or_of @@ phis1 @ phis2 )

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

let elim_consts bounds (uni_senv, defs, phi) =
  let cm, phis1 =
    List.map (BoolTerm.disjuncts_of phi) ~f:BoolTerm.nnf_of
    |> List.partition_map ~f:(consts_of bounds)
  in
  try
    let sub =
      List.fold ~init:Map.Poly.empty cm ~f:(fun acc (x, sym, _ty) ->
          Map.force_add acc x (Term.mk_con sym))
    in
    ( uni_senv,
      List.map defs ~f:(Term.subst sub),
      Term.subst sub @@ BoolTerm.or_of phis1 )
  with _ -> (uni_senv, [], BoolTerm.mk_bool true)

let reduce (uni_senv, defs, body) =
  let fvs = Set.Poly.union_list @@ List.map ~f:Term.fvs_of (body :: defs) in
  (Map.Poly.filter_keys uni_senv ~f:(Set.mem fvs), defs, body)

let rec qelim_aux1 let_bounds bounds exi_senv (uni_senv, defs, phi) =
  let uni_senv', defs', phi' =
    let bounds' = Map.force_merge_list [ exi_senv; let_bounds; bounds ] in
    (uni_senv, defs, phi) |> elim_consts bounds'
    |> elim_eqcls let_bounds bounds'
    |> reduce
  in
  if Map.Poly.length uni_senv > Map.Poly.length uni_senv' then
    qelim_aux1 let_bounds bounds exi_senv (uni_senv', defs', phi')
  else (uni_senv', defs', phi')

let qelim_aux2 let_bounds bounds exi_senv (uni_senv, defs, phi0) =
  let bounds' = Map.force_merge_list [ exi_senv; let_bounds; bounds ] in
  let has_no_inter x s =
    (not @@ Set.mem s x) && Set.disjoint (Map.key_set let_bounds) s
  in
  let rec loop uni_senv defs phis =
    let res =
      List.find_map phis ~f:(fun phi ->
          match Term.let_apps phi with
          | TyApp (Con (BoolTerm.Neq, _), _ty, _), [ t1; t2 ] -> (
              match (t1, t2) with
              | Var (x, _), t
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x (Term.fvs_of t) ->
                  Some (x, t)
              | t, Var (x, _)
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x (Term.fvs_of t) ->
                  Some (x, t)
              (* for integers *)
              | ( App
                    ( App (Con ((IntTerm.(Add | Sub) as s), _), Var (x, _), _),
                      t1,
                      _ ),
                  t2 )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
              | ( t2,
                  App
                    ( App (Con ((IntTerm.(Add | Sub) as s), _), Var (x, _), _),
                      t1,
                      _ ) )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
              | ( App (App (Con ((IntTerm.Add as s), _), t1, _), Var (x, _), _),
                  t2 )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
              | t2, App (App (Con ((IntTerm.Add as s), _), t1, _), Var (x, _), _)
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
              | ( App (App (Con ((IntTerm.Sub as s), _), t1, _), Var (x, _), _),
                  t2 )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app s [ t1; t2 ])
              | t2, App (App (Con ((IntTerm.Sub as s), _), t1, _), Var (x, _), _)
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app s [ t1; t2 ])
              (* for reals *)
              | ( App
                    ( App (Con ((RealTerm.(RAdd | RSub) as s), _), Var (x, _), _),
                      t1,
                      _ ),
                  t2 )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
              | ( t2,
                  App
                    ( App (Con ((RealTerm.(RAdd | RSub) as s), _), Var (x, _), _),
                      t1,
                      _ ) )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
              | ( App (App (Con ((RealTerm.RAdd as s), _), t1, _), Var (x, _), _),
                  t2 )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
              | ( t2,
                  App (App (Con ((RealTerm.RAdd as s), _), t1, _), Var (x, _), _)
                )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
              | ( App (App (Con ((RealTerm.RSub as s), _), t1, _), Var (x, _), _),
                  t2 )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app s [ t1; t2 ])
              | ( t2,
                  App (App (Con ((RealTerm.RSub as s), _), t1, _), Var (x, _), _)
                )
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x
                          (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
                  Some (x, Term.mk_sym_app s [ t1; t2 ])
              | _ -> None)
          | TyApp (Con (BoolTerm.Eq, _), BoolTerm.SBool, _), [ t1; t2 ] -> (
              match (t1, t2) with
              | Var (x, _), t
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x (Term.fvs_of t) ->
                  Some (x, BoolTerm.neg_of t)
              | t, Var (x, _)
                when (not (Map.Poly.mem bounds' x))
                     && has_no_inter x (Term.fvs_of t) ->
                  Some (x, BoolTerm.neg_of t)
              | _ -> None)
          | _ -> None)
    in
    let res =
      match res with
      | Some (x, t) -> Some (x, t)
      | None ->
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
          Map.Poly.singleton x @@ ExtTerm.simplify_term exi_senv uni_senv' t
        in
        if false then
          print_endline
          @@ sprintf "[qelim_aux2] %s ==> %s" (Ident.name_of_tvar x)
               (ExtTerm.str_of t);
        loop uni_senv'
          (List.map ~f:(Term.subst sub) defs)
          (List.map ~f:(Term.subst sub) phis)
    | None -> (uni_senv, defs, phis)
  in
  let uni_senv, defs, phis =
    loop uni_senv defs
      (List.map ~f:BoolTerm.nnf_of (BoolTerm.disjuncts_of phi0))
  in
  (uni_senv, defs, BoolTerm.or_of phis)

let print_log = false

let app_qelim ?(simplify = true) let_bounds bounds exi_senv (uni_senv, defs, phi)
    =
  let fvs =
    Set.diff (Term.fvs_of phi)
      (Map.key_set @@ Map.force_merge_list [ exi_senv; let_bounds; bounds ])
  in
  if Set.is_empty fvs then (
    if print_log then print_endline "[app_qelim] skipped";
    (uni_senv, defs, phi))
  else (
    if print_log then
      print_endline
      @@ sprintf "[app_qelim] begin eliminating %s in %s"
           (String.concat_map_set ~sep:", " ~f:Ident.name_of_tvar fvs)
           (LogicOld.Formula.str_of
           @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi);
    let uni_senv, defs, phi1 =
      qelim_aux1 let_bounds bounds exi_senv (uni_senv, defs, phi)
    in
    if print_log then print_endline "  [app_qelim] qelim_aux1";
    let uni_senv, defs, phi2 =
      qelim_aux2 let_bounds bounds exi_senv (uni_senv, defs, phi1)
    in
    if print_log then print_endline "  [app_qelim] qelim_aux2";
    let phi3 =
      if simplify then
        ExtTerm.simplify_formula exi_senv
          (Map.force_merge let_bounds uni_senv)
          phi2
      else phi2
    in
    (if print_log then
       let _fvs = Set.diff fvs (Term.fvs_of phi2) in
       print_endline
       @@ sprintf "[app_qelim] end: %s"
            (*(String.concat_map_set ~sep:", " ~f:Ident.name_of_tvar fvs)*)
            (LogicOld.Formula.str_of
            @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi2));
    (uni_senv, defs, phi3))

(* eliminate free variables in [defs] and [phi] that are universlly quantified implicitly *)
(* @param [bounds] variables that must not be eliminated *)
(* assume that [phi] is alpha-renamed and let-normalized *)
let rec qelim ?(simplify = true) ?(let_bounds = Map.Poly.empty) bounds exi_senv
    (uni_senv, defs, phi) =
  match phi with
  | Let (var, sort, def, body, info) -> (
      let let_bounds' = Map.Poly.set ~key:var ~data:sort let_bounds in
      match
        qelim ~simplify ~let_bounds:let_bounds' bounds exi_senv
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
      reduce
      @@ app_qelim ~simplify let_bounds bounds exi_senv (uni_senv, defs, phi)

let qelim_old ?(simplify = true) bounds exi_senv (uni_senv, phi) =
  let uni_senv', _, phi' =
    qelim ~simplify bounds exi_senv (uni_senv, [], ExtTerm.of_old_formula phi)
  in
  (uni_senv', ExtTerm.to_old_fml exi_senv uni_senv' phi')

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
