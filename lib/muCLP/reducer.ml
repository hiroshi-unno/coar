open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld

module Config = struct
  type t = { verbose : bool; use_dwf : bool } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid Reducer Configuration (%s): %s" filename msg)
end

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let rename_preds psenv bpvs phi =
    Set.diff psenv bpvs
    |> Set.Poly.map ~f:(fun (pvar, sorts) ->
           let params = mk_fresh_sort_env_list sorts in
           ( pvar,
             ( params,
               Formula.mk_atom
               @@ Atom.mk_pvar_app (Ident.uninterp_pvar pvar) sorts
               @@ Term.of_sort_env params ) ))
    |> Map.of_set_exn
    |> Fn.flip Formula.subst_preds phi

  let cnf_of query =
    query |> Evaluator.simplify
    |> Formula.cnf_of Map.Poly.empty (*ToDo:check*)
    |> Set.Poly.map ~f:(fun (pos, neg, pure) ->
           Formula.or_of
           @@ (pure :: (Set.to_list @@ Set.Poly.map pos ~f:Formula.mk_atom))
           @ Set.to_list
           @@ Set.Poly.map neg ~f:(Formula.mk_atom >> Formula.mk_neg))

  let rec elim_nu_aux (*?(id=None)*) psenv bpvs query = function
    | [] ->
        ( rename_preds psenv bpvs query
          |> cnf_of
          |> Set.Poly.map ~f:(fun phi ->
                 let senv, phi = LogicOld.Formula.rm_quant ~forall:true phi in
                 Formula.reduce_sort_map (Map.of_set_exn senv, phi)),
          Set.Poly.empty )
    | (Predicate.Nu, pvar, args, phi) :: preds ->
        let pvar' = Ident.uninterp_pvar pvar in
        let bounds, phi = LogicOld.Formula.rm_quant ~forall:true phi in
        (*let bounds(* ToDo: this should be empty *) =
          Set.Poly.filter_map (Formula.tvs_of phi)
          ~f:(fun x -> if List.Assoc.mem ~equal:Stdlib.(=) args x then None else Some (x, LogicOld.T_int.SInt))
          in*)
        let uni_senv =
          Map.of_set_exn @@ Set.union (Set.Poly.of_list args) bounds
        in
        let queries, clauses = elim_nu_aux psenv bpvs query preds in
        ( queries,
          Formula.mk_imply
            (Formula.mk_atom @@ Atom.pvar_app_of_senv pvar' args)
            (rename_preds psenv bpvs phi)
          (*|> fun phi -> Debug.print ~id @@ lazy (Formula.str_of phi); phi*)
          |> cnf_of
          |> Set.Poly.map ~f:(fun phi ->
                 Formula.reduce_sort_map (uni_senv, phi))
          |> Set.union clauses )
    | _ ->
        failwith "every mu predicate must be eliminated before applying elim_nu"

  let elim_nu (*?(id=None)*) query preds unknowns =
    let psenv = Pred.pred_sort_env_of_list preds in
    ( elim_nu_aux psenv
        (Map.to_set @@ Kind.pred_sort_env_map_of unknowns)
        query preds,
      Kind.add_pred_env_set unknowns Kind.Ord
      @@ Set.Poly.map psenv ~f:(fun (pvar, sorts) ->
             (Ident.uninterp_pvar pvar, sorts)) )

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

    let ( => ) a b (g : t) =
      Set.mem
        (try Map.Poly.find_exn g a
         with _ -> failwith ("not found: " ^ Ident.name_of_pvar a))
          .forward b

    let ( --> ) a b (g : t) =
      Set.mem
        (try Map.Poly.find_exn g a
         with _ -> failwith ("not found: " ^ Ident.name_of_pvar a))
          .backward b

    let ( =>+ ) a b (g : t) =
      Set.mem
        (try Map.Poly.find_exn g a
         with _ -> failwith ("not found: " ^ Ident.name_of_pvar a))
          .forward_reachable b

    let ( =>* ) a b (g : t) = Stdlib.(a = b) || (a =>+ b) g

    let ( =->+ ) a b (g : t) =
      Set.mem
        (try Map.Poly.find_exn g a
         with _ -> failwith ("not found: " ^ Ident.name_of_pvar a))
          .reachable b

    let ( =->* ) a b (g : t) = Stdlib.(a = b) || (a =->+ b) g
    let level g a = (Map.Poly.find_exn g a).level

    let gen_init_graph (query : Formula.t) (preds : Pred.t list) : t =
      let pvars = List.mapi preds ~f:(fun i (_, pvar, _, _) -> (pvar, i)) in
      let level_of =
        let map = Map.Poly.of_alist_exn pvars in
        fun p ->
          match Map.Poly.find map p with
          | None -> -1 (* uninterpreted pvars are of level -1*)
          | Some i -> i
      in
      let occurrences_in pvar =
        List.find_map_exn preds ~f:(fun (_, pvar', _, phi) ->
            if Stdlib.(pvar = pvar') then Some (Formula.pvs_of phi) else None)
      in
      let query_node =
        ( Ident.Pvar "#query",
          {
            level = -1;
            forward = Formula.pvs_of query;
            backward = Set.Poly.empty;
            forward_reachable = Set.Poly.empty;
            reachable = Set.Poly.empty;
          } )
      in
      Map.Poly.of_alist_exn
      @@ query_node
         :: List.map pvars ~f:(fun (pvar, level) ->
                let pvars' = occurrences_in pvar in
                let forward, backward =
                  Set.partition_tf pvars' ~f:(fun pvar' ->
                      level < level_of pvar')
                in
                ( pvar,
                  {
                    level;
                    forward;
                    backward;
                    forward_reachable = Set.Poly.empty;
                    reachable = Set.Poly.empty;
                  } ))

    let restrict_to pvs g =
      Map.Poly.filter_keys g ~f:(Set.mem pvs)
      |> Map.Poly.map ~f:(fun attr ->
             {
               attr with
               forward = Set.inter attr.forward pvs;
               backward = Set.inter attr.backward pvs;
             })

    let transitive_closure g =
      let rec inner g =
        let g' =
          Map.Poly.map g ~f:(fun attr ->
              let forward_reachable =
                Set.fold attr.forward_reachable ~init:attr.forward_reachable
                  ~f:(fun forward_reachable p' ->
                    Set.union forward_reachable
                      (Map.Poly.find_exn g p').forward_reachable)
              in
              let reachable =
                Set.fold attr.reachable ~init:attr.reachable
                  ~f:(fun reachable p' ->
                    Set.union reachable (Map.Poly.find_exn g p').reachable)
              in
              { attr with forward_reachable; reachable })
        in
        if
          Map.Poly.equal
            (fun attr1 attr2 ->
              Set.equal attr1.forward_reachable attr2.forward_reachable
              && Set.equal attr1.reachable attr2.reachable)
            g g'
        then g'
        else inner g'
      in
      inner
      @@ Map.Poly.map g ~f:(fun attr ->
             {
               attr with
               forward_reachable = attr.forward;
               reachable = Set.union attr.forward attr.backward;
             })

    let str_of (g : t) =
      String.concat_map_list ~sep:";\n" ~f:(fun (Ident.Pvar pname, attr) ->
          String.paren
          @@ sprintf "%s, %d, [%s], [%s], [%s], [%s]" pname attr.level
               (Ident.str_of_pvars ~sep:";" attr.forward)
               (Ident.str_of_pvars ~sep:";" attr.forward_reachable)
               (Ident.str_of_pvars ~sep:";" attr.backward)
               (Ident.str_of_pvars ~sep:";" attr.reachable))
      @@ Map.Poly.to_alist g
  end

  let elim_mu ?(id = None) (dg0 : DepGraph.t) (query : Formula.t)
      (preds : Pred.t list) unknowns =
    Debug.print ~id
    @@ lazy (sprintf "************ Initial DepGraph:\n%s" (DepGraph.str_of dg0));
    let rec inner query wfpvs nu_only = function
      | [] ->
          ( (query, nu_only),
            Kind.add_pred_env_set unknowns
              (if config.use_dwf then Kind.DWF else Kind.WF)
              wfpvs )
      | ((Predicate.Nu | Predicate.Fix), pvar, params, phi) :: rest ->
          inner query wfpvs ((Predicate.Nu, pvar, params, phi) :: nu_only) rest
      | (Predicate.Mu, pvar, params, phi) :: rest ->
          let dg =
            let relevant_pvs =
              Set.Poly.of_list @@ (pvar :: List.map nu_only ~f:Quadruple.snd)
            in
            DepGraph.transitive_closure @@ DepGraph.restrict_to relevant_pvs dg0
          in
          Debug.print ~id
          @@ lazy
               (sprintf "************ Filtered DepGraph for %s:\n%s"
                  (Ident.name_of_pvar pvar) (DepGraph.str_of dg));
          let is_tainted =
            let called_outside =
              Set.Poly.union_list
              @@ List.map nu_only ~f:(fun (_, pvar', _, phi) ->
                     if
                       let open DepGraph in
                       (pvar =->+ pvar') dg && (pvar' =->+ pvar) dg
                     then Set.Poly.empty
                     else Formula.pvs_of phi)
              @ List.map rest ~f:(Quadruple.fth >> Formula.pvs_of)
            in
            let open DepGraph in
            fun pvar ->
              Set.exists called_outside ~f:(fun pvar' ->
                  Ident.pvar_equal pvar pvar'
                  || (Map.Poly.mem dg pvar' && (pvar' =->+ pvar) dg))
          in
          let prev_avail_term, prev_avail_param =
            let prev_avail_name = Ident.mk_fresh_tvar () in
            ( Term.mk_var prev_avail_name T_bool.SBool,
              (prev_avail_name, T_bool.SBool) )
          in
          let prev_params = mk_fresh_sort_env_list @@ List.map ~f:snd params in
          let prev_terms = Term.of_sort_env prev_params in
          let bot, top = (T_bool.mk_false (), T_bool.mk_true ()) in
          let ext_arg b (xs_terms, xs_sorts) =
            List.filter ~f:(fun (p, _) ->
                let open DepGraph in
                (pvar =->+ p) dg && (p =->+ pvar) dg)
            >> List.map ~f:(fun (pvar', ys) ->
                   let ys_sorts = List.map ~f:snd ys in
                   let ys_params = mk_fresh_sort_env_list ys_sorts in
                   let ys_terms = Term.of_sort_env ys_params in
                   let phi =
                     Formula.mk_atom
                     @@
                     if config.use_dwf || is_tainted pvar' then
                       Atom.mk_pvar_app pvar'
                         ((T_bool.SBool :: xs_sorts) @ ys_sorts)
                         (b
                          ::
                          (if config.use_dwf && T_bool.is_true b then prev_terms
                           else xs_terms)
                         @ ys_terms)
                     else
                       Atom.mk_pvar_app pvar' (xs_sorts @ ys_sorts)
                         ((if config.use_dwf && T_bool.is_true b then prev_terms
                           else xs_terms)
                         @ ys_terms)
                   in
                   (pvar', (ys_params, phi)))
          in
          let bi_term, bi_param =
            let bi_name = Ident.mk_fresh_tvar () in
            (Term.mk_var bi_name T_bool.SBool, (bi_name, T_bool.SBool))
          in
          let emb_wfp ~indirect (xs_terms, xs_sorts) =
            let ys_params = mk_fresh_sort_env_list xs_sorts in
            let ys_terms = Term.of_sort_env ys_params in
            let phi =
              Formula.and_of
              @@ (if config.use_dwf then
                    [
                      (* (co-)recursion *)
                      (let bi_term, xs_terms =
                         if indirect then (bi_term, xs_terms)
                         else (prev_avail_term, prev_terms)
                       in
                       Formula.mk_atom
                       @@ Atom.mk_pvar_app pvar
                            ((T_bool.SBool :: xs_sorts) @ xs_sorts)
                            ((bi_term :: xs_terms) @ ys_terms));
                    ]
                  else [])
              @ [
                  (* (co-)recursion *)
                  (let sorts, terms =
                     if config.use_dwf then
                       ( (T_bool.SBool :: xs_sorts) @ xs_sorts,
                         (top :: ys_terms) @ ys_terms )
                     else (xs_sorts, ys_terms)
                   in
                   Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts terms);
                  (* guard *)
                  (if indirect then Formula.mk_imply (Formula.eq bi_term top)
                   else if config.use_dwf then
                     Formula.mk_imply (Formula.eq prev_avail_term top)
                   else Fn.id)
                  @@ Formula.mk_atom
                  @@ Atom.mk_pvar_app (Ident.wfpred_pvar pvar)
                       (xs_sorts @ xs_sorts)
                       ((if indirect then xs_terms
                         else if config.use_dwf then prev_terms
                         else xs_terms)
                       @ ys_terms);
                ]
            in
            (pvar, (ys_params, phi))
          in
          let preds =
            List.map nu_only ~f:(fun (_, pvar, params, _) -> (pvar, params))
          in
          let sigma_1, sigma_2, sigma_3 =
            let sorts = List.map ~f:snd params in
            let sigma_1_ =
              let dummy_args = List.map sorts ~f:Term.mk_dummy in
              (if config.use_dwf then
                 let ys_params = mk_fresh_sort_env_list sorts in
                 let ys_terms = Term.of_sort_env ys_params in
                 [
                   ( pvar,
                     ( ys_params,
                       Formula.mk_atom
                       @@ Atom.mk_pvar_app pvar
                            ((T_bool.SBool :: sorts) @ sorts)
                            ((bot :: dummy_args) @ ys_terms) ) );
                 ]
               else [])
              @ ext_arg bot (dummy_args, sorts) preds
            in
            let sigma_2_, sigma_3_ =
              let ps = (Term.of_sort_env params, sorts) in
              ( emb_wfp ~indirect:false ps
                :: ext_arg
                     (if config.use_dwf then prev_avail_term else top)
                     ps preds,
                emb_wfp ~indirect:true ps :: ext_arg bi_term ps preds )
            in
            Formula.
              ( subst_preds @@ Map.Poly.of_alist_exn @@ sigma_1_,
                subst_preds @@ Map.Poly.of_alist_exn @@ sigma_2_,
                subst_preds @@ Map.Poly.of_alist_exn @@ sigma_3_ )
          in
          let query' = sigma_1 query in
          let wfpvs' =
            let sorts = List.map ~f:snd params in
            if DepGraph.(pvar =->+ pvar) dg then
              Set.add wfpvs (Ident.wfpred_pvar pvar, sorts @ sorts)
            else wfpvs
          in
          let nu_only' =
            ( Predicate.Nu,
              pvar,
              (if config.use_dwf then prev_avail_param :: prev_params else [])
              @ params,
              sigma_2 phi )
            :: List.map nu_only ~f:(fun (fp, pvar', params', phi) ->
                   if
                     let open DepGraph in
                     (pvar =->+ pvar') dg && (pvar' =->+ pvar) dg
                   then
                     if config.use_dwf || is_tainted pvar' then
                       (fp, pvar', (bi_param :: params) @ params', sigma_3 phi)
                     else (fp, pvar', params @ params', sigma_2 phi)
                   else (fp, pvar', params', sigma_1 phi))
          in
          inner query' wfpvs' nu_only'
          @@ List.map rest ~f:(fun (fp, pvar, params, phi) ->
                 (fp, pvar, params, sigma_1 phi))
    in
    inner query Set.Poly.empty [] @@ List.rev preds

  let f ?(id = None) ~exchange ~messenger (muclp : Problem.t) unknowns =
    (*Debug.set_id id;*)
    Debug.print ~id @@ lazy "**************** elim_mu ***********";
    let (query', preds'), unknowns' =
      elim_mu
        (DepGraph.gen_init_graph muclp.query muclp.preds)
        muclp.query muclp.preds unknowns
    in
    Debug.print ~id @@ lazy (Problem.str_of @@ Problem.make preds' query');
    Debug.print ~id @@ lazy "**************** elim_nu ***********";
    let (queries, clauses), (exi_senv, kind_map) =
      elim_nu query' preds' unknowns'
    in
    let clauses, stable_clauses =
      if exchange then
        (* exchange learned clauses*)
        ( clauses,
          Set.concat_map queries ~f:(fun (param_senv, phi) ->
              let uni_senv = Logic.of_old_sort_env_map param_senv in
              Logic.ExtTerm.of_old_formula phi
              |> Logic.ExtTerm.nnf_of
              |> Logic.ExtTerm.cnf_of exi_senv uni_senv
              |> Set.Poly.map ~f:(fun (ps, ns, phi) -> (uni_senv, ps, ns, phi)))
        )
      else (Set.union clauses queries, Set.Poly.empty)
    in
    let params =
      PCSP.Params.make ~kind_map ~messenger ~id ~stable_clauses exi_senv
    in
    PCSP.Problem.of_old_formulas ~params clauses
end
