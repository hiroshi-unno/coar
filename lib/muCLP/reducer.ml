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
    | pred :: preds
      when Stdlib.( = ) pred.Pred.kind Predicate.Nu
           || Stdlib.( = ) pred.Pred.kind Predicate.Fix ->
        let pvar' = Ident.uninterp_pvar pred.name in
        let bounds, phi = LogicOld.Formula.rm_quant ~forall:true pred.body in
        (*let bounds(* ToDo: this should be empty *) =
          Set.Poly.filter_map (Formula.tvs_of phi)
          ~f:(fun x -> if List.Assoc.mem ~equal:Stdlib.(=) args x then None else Some (x, LogicOld.T_int.SInt))
          in*)
        let uni_senv =
          Map.of_set_exn @@ Set.union (Set.Poly.of_list pred.args) bounds
        in
        let queries, clauses = elim_nu_aux psenv bpvs query preds in
        ( queries,
          Formula.mk_imply
            (Formula.mk_atom @@ Atom.pvar_app_of_senv pvar' pred.args)
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
  (* e.g.
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

     Here, G(l) represents the subgraph of G obtained by eliminating the nodes with the level less than l. *)
  module DepGraph = struct
    type pvars = Ident.pvar_set

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

    let ( =-> ) a b (g : t) =
      let attr =
        try Map.Poly.find_exn g a
        with _ -> failwith ("not found: " ^ Ident.name_of_pvar a)
      in
      Set.mem attr.backward b || Set.mem attr.forward b

    let ( =>+ ) a b (g : t) =
      Set.mem
        (try Map.Poly.find_exn g a
         with _ -> failwith ("not found: " ^ Ident.name_of_pvar a))
          .forward_reachable b

    let ( =>* ) a b (g : t) = Stdlib.(a = b) || (a =>+ b) g

    let reach_set_of g pvar =
      (try Map.Poly.find_exn g pvar
       with _ -> failwith ("not found: " ^ Ident.name_of_pvar pvar))
        .reachable

    let ( =->+ ) a b (g : t) = Set.mem (reach_set_of g a) b
    let ( =->* ) a b (g : t) = Stdlib.(a = b) || (a =->+ b) g

    let rev_reach_set_of pvars (g : t) pvar =
      Set.filter pvars ~f:(fun pvar' -> (pvar' =->+ pvar) g)

    let level g a =
      try (Map.Poly.find_exn g a).level
      with _ ->
        if true then -1
        (* uninterpreted pvars are of level -1*) else
          failwith ("not found: " ^ Ident.name_of_pvar a)

    let gen_init_graph (query : Formula.t) (preds : Pred.t list) : t =
      let pvars = List.mapi preds ~f:(fun i pred -> (pred.name, i)) in
      let level_of =
        let map = Map.Poly.of_alist_exn pvars in
        fun p ->
          match Map.Poly.find map p with
          | None -> -1 (* uninterpreted pvars are of level -1*)
          | Some i -> i
      in
      let occurrences_in pvar =
        List.find_map_exn preds ~f:(fun pred ->
            if Stdlib.( = ) pvar pred.name then Some (Formula.pvs_of pred.body)
            else None)
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
               Set.partition_tf pvars' ~f:(fun pvar' -> level < level_of pvar')
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
                    try
                      Set.union forward_reachable
                        (Map.Poly.find_exn g p').forward_reachable
                    with _ -> forward_reachable)
              in
              let reachable =
                Set.fold ~init:attr.reachable attr.reachable
                  ~f:(fun reachable p' ->
                    try Set.union reachable (Map.Poly.find_exn g p').reachable
                    with _ -> reachable)
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

    let k_transitive_closure g k =
      let rec inner g =
        let g' =
          Map.Poly.map g ~f:(fun attr ->
              let reachable =
                Set.fold ~init:attr.reachable attr.reachable
                  ~f:(fun reachable p' ->
                    try Set.union reachable (Map.Poly.find_exn g p').reachable
                    with _ -> reachable)
              in
              { attr with reachable })
        in
        if
          Map.Poly.equal
            (fun attr1 attr2 -> Set.equal attr1.reachable attr2.reachable)
            g g'
        then g'
        else inner g'
      in
      inner
      @@ Map.Poly.map g ~f:(fun attr ->
          {
            attr with
            reachable =
              Set.filter ~f:(fun pvar -> level g pvar > k)
              @@ Set.union attr.forward attr.backward;
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

  let elim_mu ?(id = None) (query : Formula.t) (preds : Pred.t list) unknowns =
    let (dg0 : DepGraph.t) = DepGraph.gen_init_graph query preds in
    Debug.print ~id
    @@ lazy (sprintf "************ Initial DepGraph:\n%s" (DepGraph.str_of dg0));
    let rec inner query wfpvs nu_only = function
      | [] ->
          ( (query, nu_only),
            Kind.add_pred_env_set unknowns
              (if config.use_dwf then Kind.DWF else Kind.WF)
              wfpvs )
      | pred :: rest -> (
          match pred.Pred.kind with
          | Predicate.(Nu | Fix) ->
              inner query wfpvs
                ({ pred with kind = Predicate.Nu } :: nu_only)
                rest
          | Predicate.Mu ->
              let dg =
                let relevant_pvs =
                  Set.Poly.of_list
                    (pred.name :: List.map nu_only ~f:(fun pred -> pred.name))
                in
                DepGraph.transitive_closure
                @@ DepGraph.restrict_to relevant_pvs dg0
              in
              Debug.print ~id
              @@ lazy
                   (sprintf "************ Filtered DepGraph for %s:\n%s"
                      (Ident.name_of_pvar pred.name)
                      (DepGraph.str_of dg));
              let is_tainted =
                let called_outside =
                  Set.Poly.union_list
                  @@ List.map nu_only ~f:(fun pred' ->
                      if
                        let open DepGraph in
                        (pred.name =->+ pred'.name) dg
                        && (pred'.name =->+ pred.name) dg
                      then Set.Poly.empty
                      else Formula.pvs_of pred'.body)
                  @ List.map rest ~f:(fun pred -> Formula.pvs_of pred.body)
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
              let prev_params =
                mk_fresh_sort_env_list @@ List.map ~f:snd pred.args
              in
              let prev_terms = Term.of_sort_env prev_params in
              let bot, top = (T_bool.mk_false (), T_bool.mk_true ()) in
              let ext_arg b (xs_terms, xs_sorts) =
                List.filter ~f:(fun (p, _) ->
                    let open DepGraph in
                    (pred.name =->+ p) dg && (p =->+ pred.name) dg)
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
                           (if config.use_dwf && T_bool.is_true b then
                              prev_terms
                            else xs_terms)
                          @ ys_terms)
                      else
                        Atom.mk_pvar_app pvar' (xs_sorts @ ys_sorts)
                          ((if config.use_dwf && T_bool.is_true b then
                              prev_terms
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
                           @@ Atom.mk_pvar_app pred.name
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
                       Formula.mk_atom @@ Atom.mk_pvar_app pred.name sorts terms);
                      (* guard *)
                      (if indirect then
                         Formula.mk_imply (Formula.eq bi_term top)
                       else if config.use_dwf then
                         Formula.mk_imply (Formula.eq prev_avail_term top)
                       else Fn.id)
                      @@ Formula.mk_atom
                      @@ Atom.mk_pvar_app
                           (Ident.wfpred_pvar pred.name)
                           (xs_sorts @ xs_sorts)
                           ((if indirect then xs_terms
                             else if config.use_dwf then prev_terms
                             else xs_terms)
                           @ ys_terms);
                    ]
                in
                (pred.name, (ys_params, phi))
              in
              let preds =
                List.map nu_only ~f:(fun pred -> (pred.name, pred.args))
              in
              let sigma_1, sigma_2, sigma_3 =
                let sorts = List.map ~f:snd pred.args in
                let sigma_1_ =
                  let dummy_args = List.map sorts ~f:Term.mk_dummy in
                  (if config.use_dwf then
                     let ys_params = mk_fresh_sort_env_list sorts in
                     let ys_terms = Term.of_sort_env ys_params in
                     [
                       ( pred.name,
                         ( ys_params,
                           Formula.mk_atom
                           @@ Atom.mk_pvar_app pred.name
                                ((T_bool.SBool :: sorts) @ sorts)
                                ((bot :: dummy_args) @ ys_terms) ) );
                     ]
                   else [])
                  @ ext_arg bot (dummy_args, sorts) preds
                in
                let sigma_2_, sigma_3_ =
                  let ps = (Term.of_sort_env pred.args, sorts) in
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
                let sorts = List.map ~f:snd pred.args in
                if DepGraph.(pred.name =->+ pred.name) dg then
                  Set.add wfpvs (Ident.wfpred_pvar pred.name, sorts @ sorts)
                else wfpvs
              in
              let nu_only' =
                {
                  pred with
                  kind = Predicate.Nu;
                  args =
                    (if config.use_dwf then prev_avail_param :: prev_params
                     else [])
                    @ pred.args;
                  body = sigma_2 pred.body;
                }
                :: List.map nu_only ~f:(fun pred' ->
                    if
                      let open DepGraph in
                      (pred.name =->+ pred'.name) dg
                      && (pred'.name =->+ pred.name) dg
                    then
                      if config.use_dwf || is_tainted pred'.name then
                        {
                          pred' with
                          args = (bi_param :: pred.args) @ pred'.args;
                          body = sigma_3 pred'.body;
                        }
                      else
                        {
                          pred' with
                          args = pred.args @ pred'.args;
                          body = sigma_2 pred'.body;
                        }
                    else { pred' with body = sigma_1 pred'.body })
              in
              inner query' wfpvs' nu_only'
              @@ List.map rest ~f:(fun pred ->
                  { pred with body = sigma_1 pred.body }))
    in
    inner query Set.Poly.empty [] @@ List.rev preds

  let elim_mu_ppm ?(id = None) ?(use_scc = true) ?(use_alt_dep = true)
      ?(ignore_nu_components = false) (query : Formula.t) (preds : Pred.t list)
      unknowns =
    let open Graph in
    let open Pack.Digraph in
    let sccs =
      if use_scc then (
        let graph = create ~size:(List.length preds) () in
        let vertices = List.init (List.length preds) ~f:V.create in
        List.iteri preds ~f:(fun i predi ->
            let pvs_body = Formula.pvs_of predi.body in
            List.iteri preds ~f:(fun j predj ->
                if Set.mem pvs_body predj.name then
                  add_edge graph (List.nth_exn vertices i)
                    (List.nth_exn vertices j)));
        Components.scc_list graph)
      else [ List.init (List.length preds) ~f:V.create ]
    in
    let elim_mu_ppm_scc scc_i scc =
      let preds =
        List.filter_mapi preds ~f:(fun i pred ->
            if List.exists scc ~f:(fun v -> V.label v = i) then Some pred
            else None)
      in
      if
        List.for_all preds ~f:(fun pred ->
            match pred.Pred.kind with Predicate.Mu -> false | _ -> true)
      then (preds, (Map.Poly.empty, Map.Poly.empty))
      else
        let (dg0 : DepGraph.t) = DepGraph.gen_init_graph query preds in
        Debug.print ~id
        @@ lazy
             (sprintf "************ DepGraph for the %s SCC:\n%s"
                (Ordinal.string_of (Ordinal.make (scc_i + 1)))
                (DepGraph.str_of dg0));
        let sorts_map =
          Hashtbl.Poly.of_alist_exn
          @@ List.map preds ~f:(fun pred ->
              ( Ident.pvar_to_tvar pred.name,
                List.map ~f:(snd >> Logic.ExtTerm.of_old_sort) pred.args ))
        in
        let pvs =
          Set.Poly.of_list @@ List.map preds ~f:(fun pred -> pred.name)
        in
        let nwf =
          if use_alt_dep then (
            let alt_dep, amax =
              let rec loop alt_dep = function
                | [] -> alt_dep
                | (name_i, is_mu_i, i) :: pvars' ->
                    let ai =
                      let dg = DepGraph.k_transitive_closure dg0 i in
                      Debug.print ~id
                      @@ lazy
                           (sprintf "************ k-reachability analysis:\n%s"
                              (DepGraph.str_of dg));
                      Integer.max_list
                      @@ 1
                         :: List.filter_map alt_dep
                              ~f:(fun (name_j, is_mu_j, aj) ->
                                let open DepGraph in
                                if
                                  Set.exists pvs ~f:(fun k ->
                                      (name_i =->* k) dg && (k =-> name_j) dg)
                                  && Set.exists pvs ~f:(fun k ->
                                      (name_j =->* k) dg && (k =-> name_i) dg)
                                then
                                  if Stdlib.(is_mu_i = is_mu_j) then Some aj
                                  else Some (1 + aj)
                                else None)
                    in
                    Debug.print ~id
                    @@ lazy
                         (sprintf "%s has the alternation depth of %d"
                            (Ident.name_of_pvar name_i)
                            ai);
                    loop ((name_i, is_mu_i, ai) :: alt_dep) pvars'
              in
              let res =
                List.map ~f:(fun (name_i, _, ai) -> (name_i, ai))
                @@ loop [] @@ List.rev
                @@ List.mapi preds ~f:(fun i pred ->
                    ( pred.name,
                      (match pred.kind with Predicate.Mu -> true | _ -> false),
                      i ))
              in
              ( Map.Poly.of_alist_exn res,
                Integer.max_list @@ List.map ~f:snd res )
            in
            Debug.print ~id @@ lazy (sprintf "amax = %d" amax);
            let max_pri =
              if ignore_nu_components then
                if (amax + 1) mod 2 = 0 then (amax + 1) / 2 else (amax + 2) / 2
              else amax + 1
            in
            Debug.print ~id @@ lazy (sprintf "#ord = %d" max_pri);
            let trunc =
              if ignore_nu_components then fun sigma_i ->
                if sigma_i mod 2 = 0 then sigma_i / 2 else (sigma_i + 1) / 2
              else Fn.id
            in
            let sigma =
              Map.Poly.of_alist_exn
              @@ List.map preds ~f:(fun pred ->
                  let pri = 2 + amax - Map.Poly.find_exn alt_dep pred.name in
                  let pri =
                    match pred.Pred.kind with
                    | Predicate.(Nu | Fix) ->
                        if pri mod 2 = 0 then pri else pri - 1
                    | Predicate.Mu -> if pri mod 2 = 0 then pri - 1 else pri
                  in
                  Debug.print ~id
                  @@ lazy
                       (sprintf "%s has the priority of %d |-> #%d"
                          (Ident.name_of_pvar pred.name)
                          pri (trunc pri));
                  (Ident.pvar_to_tvar pred.name, pri))
            in
            let acc_set =
              Set.Poly.of_list
              @@ List.init
                   (if amax mod 2 = 0 then amax / 2 else (amax + 1) / 2)
                   ~f:(fun i -> 2 * (i + 1))
            in
            Debug.print ~id
            @@ lazy
                 (sprintf "acc_set: %s"
                    (String.concat_map_set ~sep:"," acc_set ~f:string_of_int));
            Kind.
              {
                name = Ident.Tvar ("PR" ^ string_of_int scc_i);
                sorts_shared = [];
                sorts_map;
                max_pri;
                sigma;
                trunc;
                acc_set;
              })
          else
            let max_pri = List.length preds in
            Debug.print ~id @@ lazy (sprintf "#ord = %d" max_pri);
            let trunc = Fn.id in
            let sigma =
              Map.Poly.of_alist_exn
              @@ List.mapi preds ~f:(fun i pred ->
                  let pri = i + 1 in
                  Debug.print ~id
                  @@ lazy
                       (sprintf "%s has the priority of %d |-> #%d"
                          (Ident.name_of_pvar pred.name)
                          pri (trunc pri));
                  (Ident.pvar_to_tvar pred.name, pri))
            in
            let acc_set =
              Set.Poly.of_list
              @@ List.filter_map preds ~f:(fun pred ->
                  match pred.Pred.kind with
                  | Predicate.(Nu | Fix) ->
                      Some
                        (Map.Poly.find_exn sigma (Ident.pvar_to_tvar pred.name))
                  | Predicate.Mu -> None)
            in
            Debug.print ~id
            @@ lazy
                 (sprintf "acc_set: %s"
                    (String.concat_map_set ~sep:"," acc_set ~f:string_of_int));
            Kind.
              {
                name = Ident.Tvar ("PR" ^ string_of_int scc_i);
                sorts_shared = [];
                sorts_map;
                max_pri;
                sigma;
                trunc;
                acc_set;
              }
        in
        let rec inner nu_only wfpvs = function
          | [] ->
              ( nu_only,
                Set.fold ~init:(Map.Poly.empty, Map.Poly.empty) wfpvs
                  ~f:(fun acc (l, r) ->
                    let wftvar =
                      Ident.mk_parity_tvar nwf.name
                        (Ident.Tvar
                           (Ident.name_of_tvar l ^ "@" ^ string_of_int
                           @@ Map.Poly.find_exn nwf.sigma l))
                        (Ident.Tvar
                           (Ident.name_of_tvar r ^ "@" ^ string_of_int
                           @@ Map.Poly.find_exn nwf.sigma r))
                    in
                    Kind.add_pred_env_set acc
                      (Kind.Parity (nwf, (l, r)))
                      (Set.Poly.singleton
                         ( Ident.tvar_to_pvar wftvar,
                           List.map ~f:Logic.ExtTerm.to_old_sort
                           @@ Hashtbl.Poly.find_exn nwf.sorts_map l
                           @ Hashtbl.Poly.find_exn nwf.sorts_map r ))) )
          | (pred : Pred.t) :: rest ->
              let sigma =
                Set.Poly.filter_map ~f:(fun (pvar_r, sorts_r) ->
                    if
                      List.for_all preds ~f:(fun pred ->
                          not @@ Ident.pvar_equal pvar_r pred.name)
                    then None
                    else
                      let params_r = mk_fresh_sort_env_list sorts_r in
                      let phi =
                        let terms_r = Term.of_sort_env params_r in
                        let wftvar =
                          Ident.mk_parity_tvar nwf.name
                            (Ident.Tvar
                               (Ident.name_of_pvar pred.name
                               ^ "@" ^ string_of_int
                               @@ Map.Poly.find_exn nwf.sigma
                               @@ Ident.pvar_to_tvar pred.name))
                            (Ident.Tvar
                               (Ident.name_of_pvar pvar_r ^ "@" ^ string_of_int
                               @@ Map.Poly.find_exn nwf.sigma
                               @@ Ident.pvar_to_tvar pvar_r))
                        in
                        Formula.and_of
                          [
                            (* (co-)recursion *)
                            Formula.mk_atom
                            @@ Atom.mk_pvar_app pvar_r sorts_r terms_r;
                            (* guard *)
                            Formula.mk_atom
                            @@ Atom.mk_pvar_app
                                 (Ident.tvar_to_pvar wftvar)
                                 (List.map ~f:snd pred.args @ sorts_r)
                                 (Term.of_sort_env pred.args @ terms_r);
                          ]
                      in
                      Some (pvar_r, (params_r, phi)))
                @@ Set.filter
                     ~f:(fst >> Ident.pvar_to_tvar >> Hashtbl.Poly.mem sorts_map)
                @@ Formula.pred_sort_env_of pred.body
              in
              let wfpvs' =
                Set.union wfpvs
                  (Set.Poly.map sigma ~f:(fun (pvar_r, _) ->
                       (Ident.pvar_to_tvar pred.name, Ident.pvar_to_tvar pvar_r)))
              in
              let nu_only' =
                Pred.
                  {
                    pred with
                    kind = Predicate.Nu;
                    body = Formula.subst_preds (Map.of_set_exn sigma) pred.body;
                  }
                :: nu_only
              in
              inner nu_only' wfpvs' rest
        in
        inner [] Set.Poly.empty (List.rev preds)
    in
    let predss, res = List.unzip @@ List.mapi sccs ~f:elim_mu_ppm_scc in
    let senvs, kind_maps = List.unzip res in
    ( ( query,
        List.concat
        @@ List.filter_map preds ~f:(fun pred ->
               let pvs_body = Formula.pvs_of pred.body in
               if
                 List.for_all preds ~f:(fun pred' ->
                     not @@ Set.mem pvs_body pred'.name)
               then Some { pred with kind = Predicate.Nu }
               else None)
           :: predss ),
      ( Map.force_merge_list @@ (fst unknowns :: senvs),
        Map.force_merge_list @@ (snd unknowns :: kind_maps) ) )

  let f ?(id = None) ~exchange ~messenger ?(use_ppm = false) ?(use_scc = true)
      ?(ignore_nu_components = false) ?(use_alt_dep = true) (muclp : Problem.t)
      unknowns =
    (*Debug.set_id id;*)
    Debug.print ~id @@ lazy "**************** elim_mu ***********";
    let (query', preds'), unknowns' =
      if use_ppm then
        elim_mu_ppm ~id ~use_scc ~use_alt_dep ~ignore_nu_components muclp.query
          muclp.preds unknowns
      else elim_mu ~id muclp.query muclp.preds unknowns
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
