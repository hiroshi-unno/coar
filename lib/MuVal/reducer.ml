open Core
open Common
open Common.Combinator
open Common.Ext
open Ast
open Ast.LogicOld

module Make (Cfg: Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  let rename_preds psenv bpvs phi =
    Set.diff psenv bpvs
    |> Set.Poly.map ~f:(fun (pvar, sorts) ->
        let params = mk_fresh_sort_env_list sorts in
        pvar, (params, Formula.mk_atom @@ Atom.mk_pvar_app (Ident.uninterp_pvar pvar) sorts @@ Term.of_sort_env params))
    |> Map.of_set_exn |> Fn.flip Formula.subst_preds phi

  let cnf_of query =
    query |> Evaluator.simplify |> Formula.cnf_of Map.Poly.empty(*ToDo:check*)
    |> Set.Poly.map ~f:(fun (pos, neg, pure) ->
        Formula.or_of @@
        pure ::
        (Set.to_list @@ Set.Poly.map pos ~f:Formula.mk_atom) @
        (Set.to_list @@ Set.Poly.map neg ~f:(Formula.mk_atom >> Formula.mk_neg)))

  let rec elim_nu (*?(id=None)*) psenv bpvs query = function
    | [] ->
      rename_preds psenv bpvs query
      |> cnf_of
      |> Set.Poly.map ~f:(fun phi ->
          let senv, phi = LogicOld.Formula.rm_quant ~forall:true phi in
          Formula.reduce_sort_map (Map.of_set_exn senv, phi)),
      Set.Poly.empty
    | (Predicate.Nu, pvar, args, phi) :: preds ->
      let pvar' = Ident.uninterp_pvar pvar in
      let bounds, phi = LogicOld.Formula.rm_quant ~forall:true phi in
      (*let bounds(* ToDo: this should be empty *) =
        Set.Poly.filter_map (Formula.tvs_of phi)
        ~f:(fun x -> if List.Assoc.mem ~equal:Stdlib.(=) args x then None else Some (x, LogicOld.T_int.SInt))
        in*)
      let uni_senv = Map.of_set_exn @@ Set.union (Set.Poly.of_list args) bounds in
      let queries, clauses = elim_nu psenv bpvs query preds in
      queries,
      Formula.mk_imply
        (Formula.mk_atom @@ Atom.pvar_app_of_senv pvar' args)
        (rename_preds psenv bpvs phi)
      (*|> fun phi -> Debug.print ~id @@ lazy (Formula.str_of phi); phi*)
      |> cnf_of |> Set.Poly.map ~f:(fun phi -> Formula.reduce_sort_map (uni_senv, phi))
      |> Set.union clauses
    | _ -> failwith "every mu predicate must be eliminated before applying elim_nu"

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
      level : int;
      forward : pvars; (* => *)
      forward_reachable : pvars; (* =>+ *)
      backward : pvars; (* --> *)
      reachable : pvars; (* (=> | -->)+ *)
    }
    type t = (Ident.pvar, attr) Map.Poly.t
    let (=>) a b (g: t) = Set.mem (try Map.Poly.find_exn g a with _ -> failwith ("not found: " ^ Ident.name_of_pvar a)).forward b
    let (-->) a b (g: t) = Set.mem (try Map.Poly.find_exn g a with _ -> failwith ("not found: " ^ Ident.name_of_pvar a)).backward b
    let (=>+) a b (g: t) = Set.mem (try Map.Poly.find_exn g a with _ -> failwith ("not found: " ^ Ident.name_of_pvar a)).forward_reachable b
    let (=>*) a b (g: t) = (Stdlib.(a = b)) || ((a =>+ b) g)
    let (=->+) a b (g: t) = Set.mem (try Map.Poly.find_exn g a with _ -> failwith ("not found: " ^ Ident.name_of_pvar a)).reachable b
    let (=->*) a b (g: t) = (Stdlib.(a = b)) || ((a =->+ b) g)
    let level g a = (Map.Poly.find_exn g a).level
    let gen_init_graph (query: Formula.t) (preds: MuCLP.Pred.t list) : t =
      let pvars = List.mapi preds ~f:(fun i (_, pvar, _, _) -> pvar, i) in
      let level_of =
        let map = Map.Poly.of_alist_exn pvars in
        fun p ->
          match Map.Poly.find map p with
          | None -> -1(** uninterpreted pvars are of level -1*) | Some i -> i
      in
      let occurrences_in pvar =
        List.find_map_exn preds ~f:(fun (_, pvar', _, phi) ->
            if Stdlib.(pvar = pvar') then Some (Formula.pvs_of phi) else None)
      in
      let query_node =
        Ident.Pvar "#query",
        { level = -1; forward = Formula.pvs_of query; backward = Set.Poly.empty;
          forward_reachable = Set.Poly.empty; reachable = Set.Poly.empty }
      in
      Map.Poly.of_alist_exn @@
      query_node
      :: List.map pvars ~f:(fun (pvar, level) ->
          let pvars' = occurrences_in pvar in
          let forward, backward =
            Set.partition_tf pvars' ~f:(fun pvar' -> level < level_of pvar')
          in
          pvar,
          { level = level; forward = forward; backward = backward;
            forward_reachable = Set.Poly.empty; reachable = Set.Poly.empty })

    let restrict_to pvs g =
      Map.Poly.filter_keys g ~f:(Set.mem pvs)
      |> Map.Poly.map ~f:(fun attr ->
          { attr with forward = Set.inter attr.forward pvs;
                      backward = Set.inter attr.backward pvs })

    let transitive_closure g =
      let rec inner g =
        let g' =
          Map.Poly.map g ~f:(fun attr ->
              let forward_reachable =
                Set.fold attr.forward_reachable ~init:attr.forward_reachable
                  ~f:(fun forward_reachable p' ->
                      Set.union forward_reachable (Map.Poly.find_exn g p').forward_reachable)
              in
              let reachable =
                Set.fold attr.reachable ~init:attr.reachable
                  ~f:(fun reachable p' ->
                      Set.union reachable (Map.Poly.find_exn g p').reachable)
              in
              { attr with forward_reachable = forward_reachable; reachable = reachable })
        in
        if Map.Poly.equal (fun attr1 attr2 ->
            Set.equal attr1.forward_reachable attr2.forward_reachable &&
            Set.equal attr1.reachable attr2.reachable) g g'
        then g' else inner g'
      in
      inner @@ Map.Poly.map g ~f:(fun attr ->
          { attr with forward_reachable = attr.forward;
                      reachable = Set.union attr.forward attr.backward })

    let str_of (g: t) =
      String.concat_map_list ~sep:";\n" ~f:(fun (Ident.Pvar pname, attr) ->
          String.paren @@ sprintf "%s, %d, [%s], [%s], [%s], [%s]"
            pname
            attr.level (Ident.str_of_pvars ~sep:";" attr.forward)
            (Ident.str_of_pvars ~sep:";" attr.forward_reachable)
            (Ident.str_of_pvars ~sep:";" attr.backward)
            (Ident.str_of_pvars ~sep:";" attr.reachable)) @@
      Map.Poly.to_alist g
  end

  let elim_mu ?(id=None) (g0: DepGraph.t) (query: Formula.t) (preds: MuCLP.Pred.t list) =
    let rec inner query wfpvs nu_only = function
      | [] -> query, nu_only, wfpvs
      | ((Predicate.Nu | Predicate.Fix), pvar, params, phi) :: rest ->
        inner query wfpvs ((Predicate.Nu, pvar, params, phi) :: nu_only) rest
      | (Predicate.Mu, pvar, params, phi) :: rest ->
        let relevant_pvs = Set.Poly.of_list @@ pvar :: List.map nu_only ~f:Quadruple.snd in
        let g = DepGraph.transitive_closure @@ DepGraph.restrict_to relevant_pvs g0 in
        Debug.print ~id @@ lazy
          ("************ Filtered DepGraph for " ^ Ident.name_of_pvar pvar ^ ":");
        Debug.print ~id @@ lazy (DepGraph.str_of g);
        let is_tainted =
          let called_outside =
            Set.Poly.union_list @@
            List.map nu_only ~f:(fun (_, pvar', _, phi) ->
                if let open DepGraph in (pvar =->+ pvar') g && (pvar' =->+ pvar) g
                then Set.Poly.empty else Formula.pvs_of phi) @
            List.map rest ~f:(Quadruple.fth >> Formula.pvs_of)
          in
          let open DepGraph in
          fun pvar -> Set.exists called_outside ~f:(fun pvar' ->
              Ident.pvar_equal pvar pvar' || Map.Poly.mem g pvar' && (pvar' =->+ pvar) g)
        in
        let bot, top = T_bool.mk_false (), T_bool.mk_true () in
        let ext_arg b (xs_terms, xs_sorts) preds =
          List.filter preds ~f:(fun (p, _) ->
              let open DepGraph in (pvar =->+ p) g && (p =->+ pvar) g)
          |> List.map ~f:(fun (pvar', ys) ->
              let ys_sorts = List.map ~f:snd ys in
              let ys_params = mk_fresh_sort_env_list ys_sorts in
              let ys_terms = Term.of_sort_env ys_params in
              let phi =
                Formula.mk_atom @@
                if is_tainted pvar' then
                  Atom.mk_pvar_app pvar' (T_bool.SBool :: xs_sorts @ ys_sorts) (b :: xs_terms @ ys_terms)
                else Atom.mk_pvar_app pvar' (xs_sorts @ ys_sorts) (xs_terms @ ys_terms)
              in
              (pvar', (ys_params, phi)))
        in
        let bi_term, bi_param =
          let bi_name = Ident.mk_fresh_tvar () in
          Term.mk_var bi_name T_bool.SBool, (bi_name, T_bool.SBool)
        in
        let emb_wfp ~indirect (xs_terms, xs_sorts) =
          let ys_params = mk_fresh_sort_env_list xs_sorts in
          let ys_terms = Term.of_sort_env ys_params in
          let wfpva =
            Formula.mk_atom @@ Atom.mk_app
              (Predicate.mk_var (Ident.wfpred_pvar pvar) @@ xs_sorts @ xs_sorts)
              (xs_terms @ ys_terms)
          in
          let phi =
            Formula.mk_and
              (Formula.mk_atom @@ Atom.mk_pvar_app pvar xs_sorts ys_terms)
              (if indirect then Formula.mk_imply (Formula.eq bi_term top) wfpva else wfpva)
          in
          (pvar, (ys_params, phi))
        in
        let preds = List.map nu_only ~f:(fun (_, pvar, params, _) -> pvar, params) in
        let sigma_1_ =
          let dummy_args = List.map (List.map ~f:snd params) ~f:Term.mk_dummy in
          Map.Poly.of_alist_exn @@ ext_arg bot (dummy_args, List.map ~f:snd params) preds
        in
        let sigma_2_ =
          let ps = Term.of_sort_env params, List.map ~f:snd params in
          let psubst = ext_arg top ps preds in
          Map.Poly.of_alist_exn @@ emb_wfp ~indirect:false ps :: psubst
        in
        let sigma_3_ =
          let ps = Term.of_sort_env params, List.map ~f:snd params in
          let psubst = ext_arg bi_term ps preds in
          Map.Poly.of_alist_exn @@ emb_wfp ~indirect:true ps :: psubst
        in
        let sigma_1, sigma_2, sigma_3 =
          Formula.(subst_preds sigma_1_, subst_preds sigma_2_, subst_preds sigma_3_)
        in
        let query' = sigma_1 query in
        let wfps' =
          let sorts = List.map ~f:snd params in
          if DepGraph.(pvar =->+ pvar) g then Set.add wfpvs (Ident.wfpred_pvar pvar, sorts @ sorts) else wfpvs
        in
        let nu_only' =
          (Predicate.Nu, pvar, params, sigma_2 phi)
          :: List.map nu_only ~f:(fun (fp, pvar', params', phi) ->
              if let open DepGraph in (pvar =->+ pvar') g && (pvar' =->+ pvar) g then
                if is_tainted pvar'
                then (fp, pvar', bi_param :: params @ params', sigma_3 phi)
                else (fp, pvar', params @ params', sigma_2 phi)
              else (fp, pvar', params', sigma_1 phi))
        in
        inner query' wfps' nu_only' @@
        List.map rest ~f:(fun (fp, pvar, params, phi) -> fp, pvar, params, sigma_1 phi)
    in
    Debug.print ~id @@ lazy "************ Initial DepGraph:";
    Debug.print ~id @@ lazy (DepGraph.str_of g0);
    inner query Set.Poly.empty [] @@ List.rev preds

  let f ?(id=None) ~exchange ~messenger (muclp : MuCLP.Problem.t) (ordpvs, fnpvs, fnsenv) =
    (*Debug.set_id id;*)
    let query', preds', wfpvs =
      elim_mu (DepGraph.gen_init_graph muclp.query muclp.preds) muclp.query muclp.preds
    in
    Debug.print ~id @@ lazy "**************** elim_mu ***********";
    Debug.print ~id @@ lazy (MuCLP.Problem.str_of @@ MuCLP.Problem.make preds' query');
    let pvs, (queries, clauses) =
      let psenv = MuCLP.Pred.pred_sort_env_of_list preds' in
      Set.Poly.map psenv ~f:(fun (pvar, sorts) -> Ident.uninterp_pvar pvar, sorts),
      elim_nu psenv (Set.Poly.union_list [ordpvs; wfpvs; fnpvs]) query' preds'
    in
    let senv =
      Map.force_merge fnsenv @@ Map.of_set_exn @@
      Set.Poly.map ~f:(fun (pvar, sargs) ->
          Ident.pvar_to_tvar pvar,
          Logic.(Sort.mk_fun @@ List.map sargs ~f:ExtTerm.of_old_sort @ [ExtTerm.SBool])) @@
      Set.Poly.union_list [pvs; ordpvs; wfpvs; fnpvs]
    in
    let kind_map =
      let wfpvs = Set.Poly.map wfpvs ~f:(fst >> Ident.pvar_to_tvar) in
      let fnpvs = Set.Poly.map fnpvs ~f:(fst >> Ident.pvar_to_tvar) in
      Map.Poly.empty |> Kind.add_kinds fnpvs Kind.FN |> Kind.add_kinds wfpvs Kind.WF
    in
    let clauses, stable_clauses =
      if exchange then (* exchange learned clauses*)
        clauses,
        Set.concat_map queries ~f:(fun (param_senv, phi) ->
            let uni_senv = Map.Poly.map param_senv ~f:Logic.ExtTerm.of_old_sort in
            Logic.ExtTerm.of_old_formula phi
            |> Logic.ExtTerm.nnf_of |> Logic.ExtTerm.cnf_of senv uni_senv
            |> Set.Poly.map ~f:(fun (ps, ns, phi) -> uni_senv, ps, ns, phi))
      else Set.union clauses queries, Set.Poly.empty
    in
    let params = PCSP.Params.make ~kind_map ~messenger ~id ~stable_clauses senv in
    PCSP.Problem.of_old_formulas ~params clauses
end
