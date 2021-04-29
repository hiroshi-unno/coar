open Core
open Common
open Util
open Ast
open Ast.LogicOld

module Make (Cfg: Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))

  let params_of_sorts sorts = SortEnv.of_list @@ List.map ~f:(fun sort -> Ident.mk_fresh_tvar (), sort) sorts

  let uninterp (Ident.Pvar pid) = Ident.Pvar ("U_" ^ pid)
  let wfpred (Ident.Pvar pid) = Ident.Pvar ("WF_" ^ pid)

  let rename_preds bpvs phi =
    let mk_papp (pvar, sorts) =
      let params = params_of_sorts sorts in
      let terms = Term.of_sort_env params in
      (params, Formula.mk_atom (Atom.mk_app (Predicate.mk_var pvar sorts) terms)) in
    let preds = Formula.pred_sort_env_of phi in
    Set.Poly.diff preds bpvs
    |> Set.Poly.map ~f:(fun (pvar, sorts) -> pvar, mk_papp (uninterp pvar, sorts))
    |> Map.of_set
    |> fun map -> Formula.subst_preds map phi

  let cnf_of query =
    let cnf = query |> Evaluator.simplify |> Formula.cnf_of Set.Poly.empty(*ToDo:check*) in
    Set.Poly.map cnf ~f:(fun (pos, neg, pure) ->
        pure :: (Set.Poly.to_list @@ Set.Poly.map pos ~f:Formula.mk_atom)
        @ (Set.Poly.to_list @@ Set.Poly.map neg ~f:(Formula.mk_atom >> Formula.mk_neg))
        |> Formula.or_of)

  let rec elim_nu query bpvs = function
    | [] ->
      Set.Poly.empty,
      rename_preds bpvs query
      |> cnf_of
      |> Set.Poly.map ~f:(fun phi ->
          let senv, phi = LogicOld.Formula.rm_forall phi in
          Formula.reduce_sort_map (Map.of_set senv, phi))
    | (Predicate.Nu, pvar, params, phi)::funcs ->
      let pvar' = uninterp pvar in
      let sargs = SortEnv.sorts_of params in
      let left =
        Formula.mk_atom
          (Atom.mk_app (Predicate.mk_var pvar' sargs)
             (Term.of_sort_env params)) in
      let bounds, phi = LogicOld.Formula.rm_forall phi in
      (*let bounds(* ToDo: this should be empty *) =
        Formula.get_ftv phi |> Set.Poly.filter_map ~f:(fun x -> if List.Assoc.mem params ~equal:Stdlib.(=) x then None else Some (x, LogicOld.T_int.SInt))
        in*)
      let uni_senv = Map.of_set @@ Set.Poly.union (SortEnv.set_of params) bounds in
      let right = rename_preds bpvs phi in
      let exi_senv, clauses = elim_nu query bpvs funcs in
      Set.Poly.add exi_senv (pvar', sargs),
      Formula.mk_imply left right
      (*|> fun phi -> Debug.print @@ lazy (Formula.str_of phi); phi*)
      |> cnf_of
      |> Set.Poly.map ~f:(fun phi -> Formula.reduce_sort_map (uni_senv, phi))
      |> Set.Poly.union clauses
    (*     Formula.mk_imply left right
           |> Set.Poly.add (elim_nu query bpvs funcs) *)
    | _ -> failwith "every mu predicate must be eliminated before appliying elim_nu to a muCLP"

  (* Dependency Graph for optimization of pfwCSP generation *)
(*
e.g.
   given muCLP (P_1 =mu P_2; P_2 =mu P_3; P_3 =mu P_1 /\ P_4; P_4 =mu P_2),
   we generate the following dependency graph G with two types of edges => and --> that
   respectively represent forward and backawrd calls:
     _____________
    |       ______|_____
    |      |      |     |
   P_1 => P_2 => P3 => P_4

where
 level(P_1) < level(P_2) < level(P_3) < level(P_4)
 P => P' iff P calls P' and level(P) < level(P')
 P --> P' iff P calls P' and level(P) >= level(P')

for each P \in {P_1, P_2, P_3, P_4},
- the arguments of P are extended with b and args(P')
  for each inductive predicate P' such that level(P') < level(P)
  if and only if P' (=> | -->)+ P (=> | -->)+ P' in G(level(P'))

- call to inductive predicate P' in P such that level(P') <= level(P) is replaced by
  - P' and WF_P' if P' (=> | -->)* P in G(level(P')),
  - P' otherwise

Here, G(l) represents the subgraph of G obtained by eliminating the nodes with the level less than l.
*)
  module DepGraph = struct
    type pvars = Ident.pvar Set.Poly.t
    type attr = {
      level: int;
      forward: pvars; (* => *)
      forward_reachable: pvars; (* =>+ *)
      backward: pvars; (* --> *)
      reachable: pvars; (* (=> | -->)+ *)
    }
    type t = (Ident.pvar, attr) Map.Poly.t
    let (=>) a b (g: t) = Set.Poly.mem (try Map.Poly.find_exn g a with _ -> failwith ("not found: " ^ Ident.name_of_pvar a)).forward b
    let (-->) a b (g: t) = Set.Poly.mem (try Map.Poly.find_exn g a with _ -> failwith ("not found: " ^ Ident.name_of_pvar a)).backward b
    let (=>+) a b (g: t) = Set.Poly.mem (try Map.Poly.find_exn g a with _ -> failwith ("not found: " ^ Ident.name_of_pvar a)).forward_reachable b
    let (=>*) a b (g: t) = (Stdlib.(=) a b) || ((a =>+ b) g)
    let (=->+) a b (g: t) = Set.Poly.mem (try Map.Poly.find_exn g a with _ -> failwith ("not found: " ^ Ident.name_of_pvar a)).reachable b
    let (=->*) a b (g: t) = (Stdlib.(=) a b) || ((a =->+ b) g)
    let level g a = (Map.Poly.find_exn g a).level
    let gen_init_graph (query: Formula.t) (funcs: MuCLP.Problem.func list) : t =
      let pvars = List.mapi ~f:(fun i (_, pvar, _, _) -> (pvar, i)) funcs in
      let level_of = let map = Map.Poly.of_alist_exn pvars in fun p ->
          match Map.Poly.find map p with None -> -1(** uninterpreted pvars are of level -1*) | Some i -> i
      in
      let occurrences_in pvar =
        List.find_map_exn funcs ~f:(fun (_, pvar', _, phi) ->
            if Stdlib.(=) pvar pvar' then Some (Formula.pvs_of phi) else None) in
      let query_node =
        (Ident.Pvar "#query",
         { level = -1; forward = Formula.pvs_of query; backward = Set.Poly.empty;
           forward_reachable = Set.Poly.empty; reachable = Set.Poly.empty }) in
      query_node
      :: List.map pvars ~f:(fun (pvar, level) ->
          let pvars' = occurrences_in pvar in
          let forward, backward = Set.Poly.partition_tf pvars' ~f:(fun pvar' -> level < level_of pvar') in
          (pvar,
           { level = level; forward = forward; backward = backward;
             forward_reachable = Set.Poly.empty; reachable = Set.Poly.empty }))
      |> Map.Poly.of_alist_exn

    let restrict_to pvs g =
      Map.Poly.filter_keys g ~f:(Set.Poly.mem pvs)
      |> Map.Poly.map ~f:(fun attr ->
          { attr with forward = Set.Poly.inter attr.forward pvs;
                      backward = Set.Poly.inter attr.backward pvs })

    let transitive_closure g =
      let rec inner g =
        let g' =
          Map.Poly.map g ~f:(fun attr ->
              let forward_reachable =
                Set.Poly.fold attr.forward_reachable ~init:attr.forward_reachable ~f:(fun forward_reachable p' ->
                    Set.Poly.union forward_reachable (Map.Poly.find_exn g p').forward_reachable) in
              let reachable =
                Set.Poly.fold attr.reachable ~init:attr.reachable ~f:(fun reachable p' ->
                    let attr' = Map.Poly.find_exn g p' in
                    Set.Poly.union reachable attr'.reachable)
              in
              { attr with forward_reachable = forward_reachable; reachable = reachable })
        in
        if Map.Poly.equal (fun attr1 attr2 ->
            Set.Poly.equal attr1.forward_reachable attr2.forward_reachable &&
            Set.Poly.equal attr1.reachable attr2.reachable) g g'
        then g' else inner g'
      in
      inner @@ Map.Poly.map g ~f:(fun attr ->
          { attr with forward_reachable = attr.forward;
                      reachable = Set.Poly.union attr.forward attr.backward })

    let str_of (g: t) =
      let str_of_pred_set ps = String.concat ~sep:";" (Set.Poly.map ~f:Ident.name_of_pvar ps |> Set.Poly.to_list) in
      Map.Poly.to_alist g
      |> List.map ~f:(fun (Ident.Pvar pname, attr) ->
          Printf.sprintf "(%s, %d, [%s], [%s], [%s], [%s])"
            pname
            attr.level (str_of_pred_set attr.forward)
            (str_of_pred_set attr.forward_reachable)
            (str_of_pred_set attr.backward)
            (str_of_pred_set attr.reachable))
      |> String.concat ~sep:";\n"
  end

  let elim_mu (g0: DepGraph.t) (query: Formula.t) (funcs: MuCLP.Problem.func list) =
    let rec inner query wfpvs nu_only = function
      | [] -> (query, nu_only, wfpvs)
      | (Predicate.Nu, _, _, _) as nu_pred :: rest ->
        inner query wfpvs (nu_pred :: nu_only) rest
      | (Predicate.Mu, pvar, params, phi) :: rest ->
        let relevant_pvs = pvar :: List.map nu_only ~f:(fun (_, pvar, _, _) -> pvar) |> Set.Poly.of_list in
        let g = g0 |> DepGraph.restrict_to relevant_pvs |> DepGraph.transitive_closure in
        Debug.print @@ lazy ("************ Filtered DepGraph for " ^ Ident.name_of_pvar pvar ^ ":");
        Debug.print @@ lazy (DepGraph.str_of g);
        let is_tainted =
          let called_outside =
            List.map nu_only ~f:(fun (_, pvar', _, phi) ->
                if let open DepGraph in (pvar =->+ pvar') g && (pvar' =->+ pvar) g then Set.Poly.empty
                else Formula.pvs_of phi) @
            List.map rest ~f:(fun (_, _, _, phi) -> Formula.pvs_of phi)
            |> Set.Poly.union_list
          in
          let open DepGraph in
          fun pvar -> Set.Poly.exists called_outside ~f:(fun pvar' ->
              Stdlib.(=) pvar pvar' || Map.Poly.mem g pvar' && (pvar' =->+ pvar) g)
        in
        let bot, top = T_bool.mk_false (), T_bool.mk_true () in
        let ext_arg b (xs_terms, xs_sorts) preds =
          preds
          |> List.filter ~f:(fun (p, _) -> let open DepGraph in (pvar =->+ p) g && (p =->+ pvar) g)
          |> List.map ~f:(fun (pvar', ys) ->
              let ys_sorts = SortEnv.sorts_of ys in
              let ys_params = params_of_sorts ys_sorts in
              let ys_terms = Term.of_sort_env ys_params in
              let phi =
                if is_tainted pvar' then
                  Formula.mk_atom @@ Atom.mk_app
                    (Predicate.mk_var pvar' (T_bool.SBool :: xs_sorts @ ys_sorts))
                    (b :: xs_terms @ ys_terms)
                else
                  Formula.mk_atom @@ Atom.mk_app
                    (Predicate.mk_var pvar' (xs_sorts @ ys_sorts))
                    (xs_terms @ ys_terms)
              in
              (pvar', (ys_params, phi)))
        in
        let bi_term, bi_param =
          let bi_name = Ident.mk_fresh_tvar () in
          Term.mk_var bi_name T_bool.SBool, (bi_name, T_bool.SBool) in
        let emb_wfp ~indirect (xs_terms, xs_sorts) =
          let ys_params = params_of_sorts xs_sorts in
          let ys_terms = Term.of_sort_env ys_params in
          let wfpva =
            Formula.mk_atom @@ Atom.mk_app
              (Predicate.mk_var (wfpred pvar) (xs_sorts @ xs_sorts))
              (xs_terms @ ys_terms) in
          let phi =
            Formula.mk_and
              (Formula.mk_atom @@ Atom.mk_app (Predicate.mk_var pvar xs_sorts) ys_terms)
              (if indirect then Formula.mk_imply (Formula.mk_atom (T_bool.mk_eq bi_term top)) wfpva else wfpva) in
          (pvar, (ys_params, phi))
        in
        let preds = List.map nu_only ~f:(fun (_, pvar, params, _) -> pvar, params) in
        let sigma_1_ =
          let dummy_args = List.map (SortEnv.sorts_of params) ~f:Term.mk_dummy in
          Map.Poly.of_alist_exn @@ ext_arg bot (dummy_args, SortEnv.sorts_of params) preds
        in
        let sigma_2_ =
          let ps = Term.of_sort_env params, SortEnv.sorts_of params in
          let psubst = ext_arg top ps preds in
          emb_wfp ~indirect:false ps :: psubst
          |> Map.Poly.of_alist_exn
        in
        let sigma_3_ =
          let ps = Term.of_sort_env params, SortEnv.sorts_of params in
          let psubst = ext_arg bi_term ps preds in
          emb_wfp ~indirect:true ps :: psubst
          |> Map.Poly.of_alist_exn
        in
        let sigma_1, sigma_2, sigma_3 =
          Formula.(subst_preds sigma_1_, subst_preds sigma_2_, subst_preds sigma_3_)
        in
        let query' = sigma_1 query in
        let wfps' =
          let sorts = SortEnv.sorts_of params in
          if DepGraph.(pvar =->+ pvar) g then Set.Poly.add wfpvs (wfpred pvar, sorts @ sorts) else wfpvs in
        let nu_only' =
          (Predicate.Nu, pvar, params, sigma_2 phi)
          :: List.map nu_only ~f:(fun (fp, pvar', params', phi) ->
              if let open DepGraph in (pvar =->+ pvar') g && (pvar' =->+ pvar) g then
                if is_tainted pvar' then
                  (fp, pvar', SortEnv.append (uncurry SortEnv.singleton bi_param) (SortEnv.append params params'), sigma_3 phi)
                else
                  (fp, pvar', SortEnv.append params params', sigma_2 phi)
              else (fp, pvar', params', sigma_1 phi))
        in
        let rest' = List.map rest ~f:(fun (fp, pvar, params, phi) -> (fp, pvar, params, sigma_1 phi)) in
        inner query' wfps' nu_only' rest'
    in
    Debug.print @@ lazy "************ Initial DepGraph:";
    Debug.print @@ lazy (DepGraph.str_of g0);
    List.rev funcs |> inner query Set.Poly.empty []

  let f (MuCLP(funcs, query) : MuCLP.Problem.t) ordpvs fnpvs fnsenv =
    let g = DepGraph.gen_init_graph query funcs in
    let query', funcs', wfpvs = elim_mu g query funcs in
    Debug.print @@ lazy "**************** elim_mu ***********";
    Debug.print @@ lazy (MuCLP.Problem.str_of @@ MuCLP.Problem.make funcs' query');
    let pvs, formulas = elim_nu query' (Set.Poly.union_list [ordpvs; wfpvs; fnpvs]) funcs' in
    let params =
      let senv =
        Logic.SortMap.merge fnsenv @@
        Map.of_set @@
        Set.Poly.map (Set.Poly.union_list [pvs; ordpvs; wfpvs; fnpvs]) ~f:(fun (Ident.Pvar n, sargs) ->
            Ident.Tvar n,
            Logic.Sort.mk_fun (List.map sargs ~f:Logic.ExtTerm.of_old_sort @ [Logic.ExtTerm.SBool])) in
      let wfpvs = Set.Poly.map wfpvs ~f:(fun (Ident.Pvar n, _) -> Ident.Tvar n) in
      let fnpvs = Set.Poly.map fnpvs ~f:(fun (Ident.Pvar n, _) -> Ident.Tvar n) in
      PCSP.Params.make ~wfpvs ~fnpvs senv in
    PCSP.Problem.of_formulas ~params (Set.Poly.map formulas ~f:(fun (senv, phi) ->
        Logic.SortMap.of_old_sort_map Logic.ExtTerm.of_old_sort senv,
        Logic.ExtTerm.of_old_formula phi))
end