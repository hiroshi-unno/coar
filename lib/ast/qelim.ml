open Core
open Common
open Util
open Logic

let eqcs_of phi =
  let phis = BoolTerm.disjuncts_of phi in
  let eqcs, phis =
    List.partition2_map phis ~f:(fun phi ->
        if BoolTerm.is_not phi then
          match Term.let_apps (BoolTerm.let_not phi) with
          | TyApp(Con(BoolTerm.Eq, _), ty, _), [Var (x1, _); Var (x2, _)] -> `Fst(Set.Poly.of_list [x1; x2], ty)
          | _ -> `Snd(phi)
        else
          match Term.let_apps phi with
          | TyApp(Con(BoolTerm.Neq, _), ty, _), [Var (x1, _); Var (x2, _)] -> `Fst(Set.Poly.of_list [x1; x2], ty)
          | _ -> `Snd(phi))
  in
  let eqcs' =
    fix (Set.Poly.of_list eqcs) ~f:(Set.Poly.fold ~init:Set.Poly.empty ~f:(fun eqcs (eqc2, ty2) ->
        let updated = ref false in
        let eqcs' =
          Set.Poly.map eqcs ~f:(fun (eqc1, ty1) ->
              if not @@ Set.Poly.is_empty @@ Set.Poly.inter eqc2 eqc1 then begin
                updated := true;
                Set.Poly.union eqc1 eqc2, ty1
              end else (eqc1, ty1))
        in
        if !updated then eqcs' else Set.Poly.add eqcs (eqc2, ty2)))
      ~equal:(fun eqcs1 eqcs2 -> Stdlib.(=) (Set.Poly.length eqcs1) (Set.Poly.length eqcs2))
  in
  eqcs', phis

(** @param [bounds] variables that must not be eliminated *)
let elim_eqcls bounds phi =
  let eqcs, phis1 = phi |> eqcs_of in
  let ttsub, phis2 =
    Set.Poly.map eqcs ~f:(fun (eqc, ty) ->
        let bvs, fvs = Set.Poly.partition_tf ~f:(Logic.SortMap.mem bounds) eqc in
        match Set.Poly.to_list bvs, Set.Poly.to_list fvs with
        | [], fv :: fvs' ->
          let tt = Term.mk_var fv in
          List.map ~f:(fun x -> x, (tt, ty)) fvs',
          []
        | bv :: bvs', fvs ->
          let tt = Term.mk_var bv in
          List.map fvs ~f:(fun x -> x, (tt, ty)),
          List.map bvs' ~f:(fun x -> BoolTerm.neq_of ty tt (Term.mk_var x))
        | _, _ -> assert false)
    |> Set.Poly.to_list
    |> List.unzip
    |> Pair.map List.concat List.concat
  in
  let sub = Map.Poly.of_alist_exn @@ List.map ~f:(fun (x, (t, _)) -> x, t) ttsub in
  Term.subst sub @@ BoolTerm.or_of @@ phis1 @ phis2

(** @param [bounds] variables that must not be eliminated *)
let elim_consts bounds phi =
  let cm, phis1 =
    let phis = BoolTerm.disjuncts_of phi in
    List.partition2_map phis ~f:(fun phi ->
        if BoolTerm.is_not phi then
          match Term.let_apps (BoolTerm.let_not phi) with
          | Var (x, _), [] ->
            if Logic.SortMap.mem bounds x then `Snd(phi) else `Fst(x, BoolTerm.True, BoolTerm.SBool)
          | TyApp(Con(BoolTerm.Eq, _), ty, _), [Var (x, _); Con (sym, _)]
          | TyApp(Con(BoolTerm.Eq, _), ty, _), [Con (sym, _); Var (x, _)] ->
            if Logic.SortMap.mem bounds x then `Snd(phi) else `Fst(x, sym, ty)
          | TyApp(Con(BoolTerm.Neq, _), ty, _), [Var (x, _); Con (BoolTerm.True, _)]
          | TyApp(Con(BoolTerm.Neq, _), ty, _), [Con (BoolTerm.True, _); Var (x, _)] ->
            if Logic.SortMap.mem bounds x then `Snd(phi) else `Fst(x, BoolTerm.False, ty)
          | TyApp(Con(BoolTerm.Neq, _), ty, _), [Var (x, _); Con (BoolTerm.False, _)]
          | TyApp(Con(BoolTerm.Neq, _), ty, _), [Con (BoolTerm.False, _); Var (x, _)] ->
            if Logic.SortMap.mem bounds x then `Snd(phi) else `Fst(x, BoolTerm.True, ty)
          | _ -> `Snd(phi)
        else
          match Term.let_apps phi with
          | Var (x, _), [] ->
            if Logic.SortMap.mem bounds x then `Snd(phi) else `Fst(x, BoolTerm.False, BoolTerm.SBool)
          | TyApp(Con(BoolTerm.Neq, _), ty, _), [Var (x, _); Con (sym, _)]
          | TyApp(Con(BoolTerm.Neq, _), ty, _), [Con (sym, _); Var (x, _)] ->
            if Logic.SortMap.mem bounds x then `Snd(phi) else `Fst(x, sym, ty)
          | TyApp(Con(BoolTerm.Eq, _), ty, _), [Var (x, _); Con (BoolTerm.True, _)]
          | TyApp(Con(BoolTerm.Eq, _), ty, _), [Con (BoolTerm.True, _); Var (x, _)] ->
            if Logic.SortMap.mem bounds x then `Snd(phi) else `Fst(x, BoolTerm.False, ty)
          | TyApp(Con(BoolTerm.Eq, _), ty, _), [Var (x, _); Con (BoolTerm.False, _)]
          | TyApp(Con(BoolTerm.Eq, _), ty, _), [Con (BoolTerm.False, _); Var (x, _)] ->
            if Logic.SortMap.mem bounds x then `Snd(phi) else `Fst(x, BoolTerm.True, ty)
          | _ -> `Snd(phi))
  in
  let ttsub = cm |> List.map ~f:(fun (x, sym, _ty) -> x, Term.mk_con sym) |> List.dedup_and_sort ~compare:Stdlib.compare in
  if List.contains_dup ~compare:Stdlib.compare @@ List.map ~f:fst ttsub then
    BoolTerm.mk_bool true
  else
    let sub = Map.Poly.of_alist_exn @@ ttsub in
    Term.subst sub @@ BoolTerm.or_of phis1

let rec qelim_aux bounds exi_senv (uni_senv, phi) =
  let senv = Logic.SortMap.merge exi_senv uni_senv in
  let bounds = Logic.SortMap.merge bounds exi_senv in
  let phi' =
    Logic.ExtTerm.of_old_formula @@
    Evaluator.simplify @@ (*Normalizer.normalize @@*)
    Logic.ExtTerm.to_old_formula senv
      (elim_consts bounds @@ elim_eqcls bounds phi) []
  in
  let uni_senv', phi'' = Logic.Term.reduce_sort_map (uni_senv, phi') in
  if Stdlib.(>) (SortMap.length uni_senv) (SortMap.length uni_senv') then
    qelim_aux bounds exi_senv (uni_senv', phi'')
  else (uni_senv', phi'')
let rec qelim_aux2 bounds exi_senv (uni_senv, phi) =
  match List.find_map (BoolTerm.disjuncts_of phi) ~f:(fun phi ->
      if BoolTerm.is_not phi then
        match Term.let_apps (BoolTerm.let_not phi) with
        | TyApp(Con(BoolTerm.Eq, _), _ty, _), [Var (x, _); t]
          when not @@ Logic.SortMap.mem bounds x && not @@ Set.Poly.mem (Term.fvs_of t) x -> Some (x, t)
        | TyApp(Con(BoolTerm.Eq, _), _ty, _), [t; Var (x, _)]
          when not @@ Logic.SortMap.mem bounds x && not @@ Set.Poly.mem (Term.fvs_of t) x -> Some (x, t)
        | TyApp(Con(BoolTerm.Neq, _), BoolTerm.SBool, _), [Var (x, _); t]
          when not @@ Logic.SortMap.mem bounds x && not @@ Set.Poly.mem (Term.fvs_of t) x -> Some (x, BoolTerm.neg_of t)
        | TyApp(Con(BoolTerm.Neq, _), BoolTerm.SBool, _), [t; Var (x, _)]
          when not @@ Logic.SortMap.mem bounds x && not @@ Set.Poly.mem (Term.fvs_of t) x -> Some (x, BoolTerm.neg_of t)

        | TyApp(Con(BoolTerm.Eq, _), _ty, _), [App (App (Con (s, _), Var (x, _), _), t1, _); t2]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Add || Stdlib.(=) s IntTerm.Sub) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [t2; t1])
        | TyApp(Con(BoolTerm.Eq, _), _ty, _), [App (App (Con (s, _), t1, _), Var (x, _), _); t2]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Add) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [t2; t1])
        | TyApp(Con(BoolTerm.Eq, _), _ty, _), [App (App (Con (s, _), t1, _), Var (x, _), _); t2]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Sub) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app s [t1; t2])
        | TyApp(Con(BoolTerm.Eq, _), _ty, _), [t2; App (App (Con (s, _), Var (x, _), _), t1, _)]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Add || Stdlib.(=) s IntTerm.Sub) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [t2; t1])
        | TyApp(Con(BoolTerm.Eq, _), _ty, _), [t2; App (App (Con (s, _), t1, _), Var (x, _), _)]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Add) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [t2; t1])
        | TyApp(Con(BoolTerm.Eq, _), _ty, _), [t2; App (App (Con (s, _), t1, _), Var (x, _), _)]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Sub) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app s [t1; t2])
        | _ -> None
      else
        match Term.let_apps phi with
        | TyApp(Con(BoolTerm.Neq, _), _ty, _), [Var (x, _); t]
          when not @@ Logic.SortMap.mem bounds x && not @@ Set.Poly.mem (Term.fvs_of t) x -> Some (x, t)
        | TyApp(Con(BoolTerm.Neq, _), _ty, _), [t; Var (x, _)]
          when not @@ Logic.SortMap.mem bounds x && not @@ Set.Poly.mem (Term.fvs_of t) x -> Some (x, t)
        | TyApp(Con(BoolTerm.Eq, _), BoolTerm.SBool, _), [Var (x, _); t]
          when not @@ Logic.SortMap.mem bounds x && not @@ Set.Poly.mem (Term.fvs_of t) x -> Some (x, BoolTerm.neg_of t)
        | TyApp(Con(BoolTerm.Eq, _), BoolTerm.SBool, _), [t; Var (x, _)]
          when not @@ Logic.SortMap.mem bounds x && not @@ Set.Poly.mem (Term.fvs_of t) x -> Some (x, BoolTerm.neg_of t)

        | TyApp(Con(BoolTerm.Neq, _), _ty, _), [App (App (Con (s, _), Var (x, _), _), t1, _); t2]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Add || Stdlib.(=) s IntTerm.Sub) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [t2; t1])
        | TyApp(Con(BoolTerm.Neq, _), _ty, _), [App (App (Con (s, _), t1, _), Var (x, _), _); t2]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Add) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [t2; t1])
        | TyApp(Con(BoolTerm.Neq, _), _ty, _), [App (App (Con (s, _), t1, _), Var (x, _), _); t2]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Sub) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app s [t1; t2])
        | TyApp(Con(BoolTerm.Neq, _), _ty, _), [t2; App (App (Con (s, _), Var (x, _), _), t1, _)]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Add || Stdlib.(=) s IntTerm.Sub) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [t2; t1])
        | TyApp(Con(BoolTerm.Neq, _), _ty, _), [t2; App (App (Con (s, _), t1, _), Var (x, _), _)]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Add) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [t2; t1])
        | TyApp(Con(BoolTerm.Neq, _), _ty, _), [t2; App (App (Con (s, _), t1, _), Var (x, _), _)]
          when not @@ Logic.SortMap.mem bounds x && (Stdlib.(=) s IntTerm.Sub) &&
               not @@ Set.Poly.mem (Term.fvs_of t1) x && not @@ Set.Poly.mem (Term.fvs_of t2) x ->
          Some (x, Term.mk_sym_app s [t1; t2])
        | _ -> None) with
  | None -> uni_senv, phi
  | Some (x, t) ->
    let uni_senv' = Logic.SortMap.remove uni_senv x in
    let phi' = Term.subst (Map.Poly.singleton x t) phi in
    let phi'' = ExtTerm.of_old_formula @@
      Evaluator.simplify @@ (*Normalizer.normalize @@*)
      ExtTerm.to_old_formula (SortMap.merge exi_senv uni_senv') phi' [] in
    qelim_aux2 bounds exi_senv (uni_senv', phi'')
let qelim bounds exi_senv (uni_senv, phi) =
  let bounds = SortMap.merge bounds exi_senv in
  (uni_senv, phi)
  |> qelim_aux bounds exi_senv
  |> qelim_aux2 bounds exi_senv

let qelim_old bounds exi_senv (uni_senv, phi) =
  let uni_senv', phi' = qelim bounds exi_senv (uni_senv, Logic.ExtTerm.of_old_formula phi) in
  uni_senv', Logic.ExtTerm.to_old_formula (SortMap.merge exi_senv uni_senv') phi' []

(*let rec qelim_clause exi_senv (uni_senv, ps, ns, phi) =
  let senv = Logic.SortMap.merge exi_senv uni_senv in
  let atms = Set.Poly.map (Set.Poly.union ps ns) ~f:(fun t -> ExtTerm.to_old_atom senv t []) in
  let papp_tvs = List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ Set.Poly.to_list @@ Util.Set.concat @@ Set.Poly.map atms ~f:LogicOld.Atom.term_sort_env_of in
  let bounds = (* this is essential for qualifiers extraction *) SortMap.merge (Map.Poly.of_alist_exn papp_tvs) exi_senv in
  let phi' =
    Logic.ExtTerm.of_old_formula @@
    LogicOld.Formula.simplify @@ (*Normalizer.normalize @@*)
    Logic.ExtTerm.to_old_formula senv
      (snd @@ g bounds @@ snd @@ f bounds phi) []
  in
  let uni_senv', ps, ns, phi' = Clause.reduce_sort_map (uni_senv, ps, ns, phi') in
  if Stdlib.(>) (Map.Poly.length uni_senv) (Map.Poly.length uni_senv') then
    qelim_clause exi_senv (uni_senv', ps, ns, phi')
  else (uni_senv', ps, ns, phi')

  let qelim_clause_set exi_senv = Set.Poly.map ~f:qelim_clause exi_senv
*)