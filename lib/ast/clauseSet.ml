open Core
open Common.Ext
open Logic

type t = Clause.t Set.Poly.t

let of_old_clause_set = Set.Poly.map ~f:Clause.of_old_clause

let to_old_clause_set exi_senv = Set.Poly.map ~f:(Clause.to_old_clause exi_senv)

let svs_of cls = cls |> Set.concat_map ~f:Clause.svs_of
let pvs_of cls = cls |> Set.concat_map ~f:Clause.pvs_of

let count_pvar_apps cls =
  let pvs = pvs_of cls in
  let pos_nonlin = ref Set.Poly.empty in
  let neg_nonlin = ref Set.Poly.empty in
  pvs
  |> Set.Poly.to_list
  |> List.map ~f:(fun pvar ->
      pvar,
      cls
      |> Set.Poly.to_list
      |> List.map ~f:(fun ((_, ps, ns, _) : Clause.t) ->
          let pc = Set.Poly.count ps ~f:(fun t -> Set.Poly.mem (Term.fvs_of t) pvar) in
          let nc = Set.Poly.count ns ~f:(fun t -> Set.Poly.mem (Term.fvs_of t) pvar) in
          (*let pc = Set.Poly.count ps ~f:(Atom.occur pvar) in
            let nc = Set.Poly.count ns ~f:(Atom.occur pvar) in*)
          (if pc >= 2 then pos_nonlin := Set.Poly.add !pos_nonlin pvar);
          (if nc >= 2 then neg_nonlin := Set.Poly.add !neg_nonlin pvar);
          if pc > 0 && nc > 0 then 1, 0, 0 else 0, pc, nc)
      |> List.unzip3
      |> (fun (dcs, pcs, ncs) -> List.fold dcs ~init:0 ~f:(+),
                                 List.fold pcs ~init:0 ~f:(+),
                                 List.fold ncs ~init:0 ~f:(+))),
  Set.Poly.inter !pos_nonlin !neg_nonlin

(* val simplify_with: Set.Poly.t -> Set.Poly.t -> t -> t *)
let simplify_with positive negative = Set.Poly.filter_map ~f:(Clause.simplify_with positive negative)

(* val resolve_one_step_all: Set.Poly.t -> Set.Poly.t -> t -> t *)
let resolve_one_step_all positive negative exi_senv = Set.concat_map ~f:(Clause.resolve_one_step_all positive negative exi_senv)

(* val has_only_pure : t -> bool *)
let has_only_pure = Set.Poly.for_all ~f:Clause.has_only_pure

let to_formula clauses(*ToDo: rename*) =
  BoolTerm.and_of @@ Set.Poly.to_list @@ Set.Poly.map clauses ~f:Clause.to_formula

let of_formulas exi_senv phis =
  Set.concat_map phis ~f:(fun (uni_senv, phi) ->
      Set.Poly.map ~f:(fun (ps, ns, phi) -> uni_senv, ps, ns, phi) @@
      BoolTerm.cnf_of exi_senv uni_senv phi)

let preds_of_pos exi_senv cs tvar =
  List.map ~f:snd @@ Set.Poly.to_list @@
  Set.Poly.map ~f:(Clause.pred_of_definite exi_senv) @@
  Set.Poly.filter cs ~f:(Clause.is_definite tvar)

let preds_of_neg exi_senv cs tvar =
  List.map ~f:snd @@ Set.Poly.to_list @@
  Set.Poly.map ~f:(Clause.pred_of_co_definite exi_senv) @@
  Set.Poly.filter cs ~f:(Clause.is_co_definite tvar)

let pred_of_pos exi_senv cs tvar =
  match preds_of_pos exi_senv cs tvar with
  | [] ->
    begin
      try
        let env =
          mk_fresh_sort_env_list @@ Sort.args_of @@ Map.Poly.find_exn exi_senv tvar
        in
        env, BoolTerm.mk_bool false
      with _ -> failwith @@ Ident.name_of_tvar tvar ^ " not found (ClauseSet.pred_of_pos)"
    end
  | (env, phi) :: ps ->
    env,
    BoolTerm.or_of @@
    phi :: List.map ps ~f:(fun (env', phi') ->
        let sub = Map.Poly.of_alist_exn @@ List.map2_exn env' env ~f:(fun (x, _) (y, _) -> x, Term.mk_var y) in
        Term.subst sub phi')

let pred_of_neg exi_senv cs tvar =
  match preds_of_neg exi_senv cs tvar with
  | [] ->
    begin
      try
        let env =
          mk_fresh_sort_env_list @@ Sort.args_of @@ Map.Poly.find_exn exi_senv tvar
        in
        env, BoolTerm.mk_bool true
      with _ -> failwith @@ Ident.name_of_tvar tvar ^ " not found (ClauseSet.pred_of_neg)"
    end
  | (env, phi) :: ps ->
    env,
    BoolTerm.and_of @@
    phi :: List.map ps ~f:(fun (env', phi') ->
        let sub = Map.Poly.of_alist_exn @@ List.map2_exn env' env ~f:(fun (x, _) (y, _) -> x, Term.mk_var y) in
        Term.subst sub phi')

let pred_of exi_senv cs tvar =
  match preds_of_pos exi_senv cs tvar with
  | [] -> begin
      match preds_of_neg exi_senv cs tvar with
      | [] ->
        begin
          try
            let env =
              mk_fresh_sort_env_list @@ Sort.args_of @@ Map.Poly.find_exn exi_senv tvar
            in
            env, BoolTerm.mk_bool true
          with _ -> failwith @@ Ident.name_of_tvar tvar ^ " not found (ClauseSet.pred_of)"
        end
      | (env, phi) :: ps ->
        env,
        BoolTerm.and_of @@
        phi :: List.map ps ~f:(fun (env', phi') ->
            let sub = Map.Poly.of_alist_exn @@ List.map2_exn env' env ~f:(fun (x, _) (y, _) -> x, Term.mk_var y) in
            Term.subst sub phi')
    end
  | (env, phi) :: ps ->
    env,
    BoolTerm.or_of @@
    phi :: List.map ps ~f:(fun (env', phi') ->
        let sub = Map.Poly.of_alist_exn @@ List.map2_exn env' env ~f:(fun (x, _) (y, _) -> x, Term.mk_var y) in
        Term.subst sub phi')

let subst exi_senv sub = Set.Poly.map ~f:(Clause.subst exi_senv sub)

let str_of exi_senv cls =
  String.concat_map_set ~sep:"\n" ~f:(Clause.str_of exi_senv) cls

let simplify exi_senv = Set.Poly.map ~f:(Clause.simplify exi_senv)

let partial_sols_of ?(print=fun _ -> ()) is_valid exi_senv sol lbs clauses0 target_pvars ignored =
  let clauses =
    simplify exi_senv @@
    subst exi_senv
      (Map.Poly.filter_keys sol ~f:(fun x ->
           let x = Ident.name_of_tvar x in
           String.is_prefix x ~prefix:"WF_"(*ToDo*) ||
           String.is_prefix x ~prefix:"FN_"(*ToDo*)))
      clauses0
  in
  print @@ lazy ("clauses: " ^ str_of exi_senv clauses);
  let cl_pvars = pvs_of clauses in
  let pvars0(*assume all are ordinary pred vars*) =
    Set.Poly.filter_map cl_pvars ~f:(fun clause_pvar ->
        Set.Poly.find target_pvars ~f:(Ident.is_related_tvar clause_pvar))
  in
  print @@ lazy ("pvars0: " ^ String.concat_map_set ~sep:"," pvars0 ~f:Ident.name_of_tvar);
  let pvars = Set.Poly.map pvars0 ~f:(fun pvar -> Set.Poly.find_exn cl_pvars ~f:(fun cl_pvar -> Ident.is_related_tvar cl_pvar pvar)) in
  let pvars = Set.Poly.diff pvars ignored in
  print @@ lazy ("pvars: " ^ String.concat_map_set ~sep:"," pvars ~f:Ident.name_of_tvar);
  let lbs = Map.rename_keys (Map.Poly.of_alist_exn @@ Hashtbl.Poly.to_alist lbs) ~f:(fun pvar -> Set.Poly.find cl_pvars ~f:(fun cl_pvar -> Ident.is_related_tvar cl_pvar pvar)) in
  print @@ lazy ("sol: " ^ Logic.str_of_term_subst Logic.ExtTerm.str_of sol);
  print @@ lazy ("lbs: " ^ Logic.str_of_term_subst Logic.ExtTerm.str_of lbs);
  let table =
    Map.of_set_exn @@ Set.Poly.map pvars ~f:(fun pvar ->
        print @@ lazy ("checking " ^ Ident.name_of_tvar pvar);
        let uni_senv, pred = pred_of_neg exi_senv clauses pvar in    
        print @@ lazy ("pred: " ^ Logic.str_of_sort_env_list Logic.ExtTerm.str_of_sort uni_senv ^ "." ^ Logic.ExtTerm.str_of pred);
        let t = Map.Poly.find_exn sol pvar in
        let left =
          Normalizer.normalize @@ Evaluator.simplify @@
          Logic.ExtTerm.to_old_formula Map.Poly.empty (Map.Poly.of_alist_exn uni_senv)
            t (List.map uni_senv ~f:(fun (v, _) -> ExtTerm.mk_var v))
        in
        let check_cond2a pvs =
          let sol' = Map.Poly.mapi sol ~f:(fun ~key ~data ->
              let params, _ = Term.let_lam data in
              if Set.Poly.mem pvs key then
                match Map.Poly.find lbs key with
                | Some t -> t
                | None -> Term.mk_lambda params @@ BoolTerm.mk_bool false
              else data)
          in
          let pred = Logic.Term.subst sol' pred in
          let right =
            Normalizer.normalize @@ Evaluator.simplify @@
            Logic.ExtTerm.to_old_formula Map.Poly.empty (Map.Poly.of_alist_exn @@ uni_senv)
              pred []
          in
          is_valid @@ LogicOld.Formula.mk_imply left right
        in
        let pvs_def = Set.Poly.inter pvars @@ Logic.ExtTerm.fvs_of pred in
        let rec inner checked_sat checked_unsat pvss =
          let pvss_sat, pvss_unsat = Set.Poly.partition_tf ~f:check_cond2a pvss in
          if Set.Poly.is_empty pvss_unsat then
            Set.Poly.union checked_sat pvss_sat
          else
            let checked_sat' = Set.Poly.union checked_sat pvss_sat in
            let checked_unsat' = Set.Poly.union checked_unsat pvss_unsat in
            let pvss' = Set.Poly.diff (Set.concat_map pvss_unsat ~f:(fun pvs_unsat -> Set.Poly.map pvs_unsat ~f:(Set.Poly.remove pvs_unsat))) (Set.Poly.union checked_sat' checked_unsat') in
            inner checked_sat' checked_unsat' pvss'
        in
        let pvss = inner Set.Poly.empty Set.Poly.empty @@ Set.Poly.singleton pvs_def in
        print @@ lazy
          (sprintf "SAT2a(%s)={%s}" (Ident.name_of_tvar pvar) @@
           String.concat_map_set ~sep:"," pvss ~f:(fun pvs ->
               sprintf "{%s}" @@
               String.concat_map_set ~sep:"," pvs ~f:Ident.name_of_tvar));
        pvar, Set.Poly.map pvss ~f:(fun pvs -> Set.Poly.diff pvs_def pvs))
  in
  let rec inner not_psol =
    let added =
      Set.Poly.filter (Set.Poly.diff pvars not_psol) ~f:(fun pvar ->
          let pvss = Map.Poly.find_exn table pvar in
          Set.Poly.for_all pvss ~f:(fun pvs -> Fn.non Set.Poly.is_empty @@ Set.inter not_psol pvs))
    in
    if Set.Poly.is_empty added then not_psol else inner (Set.Poly.union not_psol added)
  in
  let res = Set.Poly.diff pvars (inner Set.Poly.empty) in
  print @@ lazy ("res: " ^ String.concat_map_set ~sep:"," res ~f:Ident.name_of_tvar);
  res
