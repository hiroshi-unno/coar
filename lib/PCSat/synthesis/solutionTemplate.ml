open Core
open Common
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon
open Template.Function

type candidate = (Ident.tvar, Logic.Sort.t * Logic.term) Map.Poly.t

type candidate_or_unsat_core =
  | Candidate of candidate
  | UnsatCore of (Ident.tvar, parameter_update_type Set.Poly.t) Map.Poly.t

module Config = struct
  type pex =
    | Quantify
    | InstDefault
    | InstRand of int [@@deriving yojson]
  type t = {
    predicate_template: Template.Predicate.Config.t ext_file;
    wf_predicate_template: Template.WFPredicate.Config.t ext_file;
    fn_predicate_template: Template.FNPredicate.Config.t ext_file;
    int_function_template: Template.IntFunction.Config.t ext_file;
    update_strategy: TemplateUpdateStrategy.Config.t;
    qualifier_generator: Qualifier.Generator.Config.t ext_file;
    smt_timeout: int option;
    ask_smt_timeout: bool;
    extract_qualifiers: bool;
    extract_terms: bool;
    extract_seeds: bool;
    reduce_quals_terms: bool;
    sync_threshold: int option;
    restart_threshold: int option;
    pex: pex;
    verbose: bool
  } [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    Template.Predicate.Config.load_ext_file cfg.predicate_template >>= fun predicate_template ->
    Template.WFPredicate.Config.load_ext_file cfg.wf_predicate_template >>= fun wf_predicate_template ->
    Template.FNPredicate.Config.load_ext_file cfg.fn_predicate_template >>= fun fn_predicate_template ->
    Template.IntFunction.Config.load_ext_file cfg.int_function_template >>= fun int_function_template ->
    TemplateUpdateStrategy.Config.instantiate_ext_files cfg.update_strategy >>= fun update_strategy ->
    Qualifier.Generator.Config.load_ext_file cfg.qualifier_generator >>= fun qualifier_generator ->
    Ok { cfg with predicate_template = predicate_template;
                  wf_predicate_template = wf_predicate_template;
                  fn_predicate_template = fn_predicate_template;
                  int_function_template = int_function_template;
                  update_strategy = update_strategy;
                  qualifier_generator = qualifier_generator }

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x ->
          instantiate_ext_files x >>= fun x ->
          Ok (ExtFile.Instance x)
        | Error msg ->
          error_string
          @@ Printf.sprintf
            "Invalid SolutionTemplate Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (ExtFile.Instance x)

  module type ConfigType = sig val config: t end
end

module type SolutionTemplateType = sig
  val initialize : unit -> unit
  val instantiate : State.u -> candidate
end

module Make (Cfg : Config.ConfigType) (APCSP: PCSP.Problem.ProblemType) : SolutionTemplateType = struct
  let config = Cfg.config

  module Debug = Common.Debug.Make (val (Common.Debug.Config.(if config.verbose then enable else disable)))

  module TemplateUpdateStrategy : TemplateUpdateStrategy.TemplateUpdateStrategyType =
    TemplateUpdateStrategy.Make (struct let config = config.update_strategy end) (APCSP)

  module QualifierGenerator =
    Qualifier.Generator.Make (struct let config = ExtFile.unwrap_or_abort config.qualifier_generator end) (APCSP)

  let extracted_qualifiers =
    if not config.extract_qualifiers then Map.Poly.empty
    else
      List.fold (Logic.SortMap.to_alist @@ PCSP.Problem.senv_of APCSP.problem) ~init:Map.Poly.empty
        ~f:(fun acc (Ident.Tvar name, sort) ->
            let sorts = List.map (Logic.Sort.args_of sort) ~f:Logic.ExtTerm.to_old_sort in
            let args = LogicOld.SortEnv.of_sorts sorts in
            let quals =
              Set.Poly.of_list @@ List.map ~f:snd @@
              QualifierGenerator.generate (Ident.Pvar name) args Set.Poly.empty (SortMap.empty, (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)) 0
            in
            Map.Poly.add_exn acc ~key:(Ident.Pvar name) ~data:(args, quals))
  let extracted_terms =
    Map.force_merge
      (if not config.extract_terms then Map.Poly.empty
       else
         Map.Poly.map extracted_qualifiers ~f:(fun (args, phis) ->
             args,
             Set.Poly.filter ~f:Term.is_numerical_compound(*ToDo*) @@
             Set.concat @@ Set.Poly.map phis ~f:Formula.terms_of))
      (if not config.extract_seeds then Map.Poly.empty
       else
         Map.Poly.map extracted_qualifiers ~f:(fun (args, phis) ->
             args,
             Set.Poly.map phis ~f:Formula.funsyms_of
             |> Set.concat
             |> Set.Poly.filter_map ~f:(function T_int.Int i when Z.Compare.(<>) i Z.zero -> Some (T_int.mk_int (Z.abs i)) | _ -> None)))

  let template_modules : (Ident.tvar, (module Template.Function.Type)) Map.Poly.t =
    let dtenv = PCSP.Problem.dtenv_of APCSP.problem in
    Logic.SortMap.to_map @@
    Logic.SortMap.mapi (PCSP.Problem.senv_of APCSP.problem) ~f:(fun ~key ~data ->
        let tvar = key in
        let sorts = Logic.Sort.args_of data |> List.map ~f:Logic.ExtTerm.to_old_sort in
        let function_template =
          if PCSP.Problem.is_wf_pred APCSP.problem tvar then
            (module Template.WFPredicate.Make
                 (struct let config = ExtFile.unwrap_or_abort config.wf_predicate_template end)
                 (struct
                   let name = tvar
                   let sorts = sorts
                   (* let dtenv = dtenv *)
                 end) : Template.Function.Type)
          else if PCSP.Problem.is_fn_pred APCSP.problem tvar then
            (module Template.FNPredicate.Make
                 (struct let config = ExtFile.unwrap_or_abort config.fn_predicate_template end)
                 (struct
                   let name = tvar
                   let sorts = sorts
                   (* let dtenv = dtenv *)
                 end) : Template.Function.Type)
          else if PCSP.Problem.is_ord_pred APCSP.problem tvar then
            (module Template.Predicate.Make
                 (struct let config = ExtFile.unwrap_or_abort config.predicate_template end)
                 (struct
                   let name = tvar
                   let sorts = sorts
                   let dtenv = dtenv
                   let fenv = (PCSP.Problem.fenv_of APCSP.problem )
                 end) : Template.Function.Type)
          else if PCSP.Problem.is_int_fun APCSP.problem tvar then
            (module Template.IntFunction.Make
                 (struct let config = ExtFile.unwrap_or_abort config.int_function_template end)
                 (struct
                   let name = tvar
                   let sorts = sorts
                   (* let dtenv = dtenv *)
                 end) : Template.Function.Type)
          else failwith "not supported"
        in
        function_template)

  let construct_candidate
      (temp_param_senv : Logic.SortMap.t)
      (templates : (Ident.tvar * (Logic.Sort.t * Logic.term)) list)
      (tvar_qualifiers_map : (Ident.tvar, (Ident.tvar * (Ident.tvar * (int * SortEnv.t * Formula.t)) list) list) Map.Poly.t)
      (model : ((Ident.tvar * Logic.Sort.t) * Logic.term option) list) =
    let temp_param_sub =
      Logic.SortMap.to_map @@
      Logic.SortMap.mapi temp_param_senv ~f:(fun ~key ~data ->
          (match List.find model ~f:(fun ((x, _), _) -> Stdlib.(=) x key) with
           | None -> (key, data), None
           | Some opt -> opt)
          |> Logic.ExtTerm.remove_dontcare_elem (* ToDo: support parameteric candidate solution and CEGIS(T)*)
          |> snd)
    in
    List.map templates ~f:(fun (tvar, (sort, term)) ->
        let hole_qualifiers_map = Map.Poly.find_exn tvar_qualifiers_map tvar in
        let hole_sub =
          Map.Poly.of_alist_exn @@
          List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
              hole,
              if List.is_empty quals then
                let sorts = Logic.Sort.args_of sort in
                Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ SortEnv.list_of @@ SortEnv.of_sorts @@ List.map ~f:Logic.ExtTerm.to_old_sort sorts) @@
                Logic.BoolTerm.mk_bool true
              else
                let _, (_, senv, _) = List.hd_exn quals in
                Template.Generator.gen_from_qualifiers (senv, quals))
        in
        (*Debug.print @@ lazy (Logic.ExtTerm.str_of term);*)
        let term' = Logic.ExtTerm.subst temp_param_sub @@ Logic.ExtTerm.subst hole_sub term in
        (*Debug.print @@ lazy (Logic.ExtTerm.str_of term');*)
        assert (Set.Poly.is_empty @@ Logic.ExtTerm.fvs_of term');
        (tvar, (sort, term')))
    |> Map.Poly.of_alist_exn

  let old_eval_qual polarity npfvs (_param_senv, cond, _sorts, args) (key, (_, params, phi)) =
    let fvs = Set.Poly.union_list @@ List.map ~f:LogicOld.Term.tvs_of args in
    let fenv = Set.Poly.empty in (*TODO: generate fenv*)
    if Set.Poly.is_empty @@ Set.Poly.inter fvs npfvs then
      let phi =
        let sub = Map.Poly.of_alist_exn @@ List.zip_exn (List.map ~f:fst @@ LogicOld.SortEnv.list_of params) args in
        Formula.subst sub phi in
      match Evaluator.check ~cond (Z3Smt.Z3interface.is_valid fenv) phi with
      | Some true ->
        Logic.ExtTerm.geq_of (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      | Some false ->
        Logic.ExtTerm.leq_of (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      | None ->
        (*Debug.print @@ lazy (Formula.str_of phi ^ " couldn't be evaluated.  This may cause a violation of the progress property.");*)
        if not polarity then Logic.ExtTerm.mk_bool true
        else Logic.ExtTerm.eq_of Logic.ExtTerm.SInt (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
    else (*never use*)Logic.ExtTerm.eq_of Logic.ExtTerm.SInt (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())

  let eval_qual tt fenv polarity npfvs atom (key, (qi, _params, _phi)) =
    let fvs = ExAtom.tvs_of atom in
    if Set.Poly.is_empty @@ Set.Poly.inter fvs npfvs then
      let ai = TruthTable.index_of_atom tt fenv (ExAtom.normalize_params atom) in
      let e = tt.table.{qi, ai} in
      if e = 1 then Logic.ExtTerm.geq_of (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      else if e = -1 then Logic.ExtTerm.leq_of (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      else begin
        (*Debug.print @@ lazy (ExAtom.str_of atom ^ " on " ^ Formula.str_of phi ^ " couldn't be evaluated.  This may cause a violation of the progress property.");*)
        if not polarity then Logic.ExtTerm.mk_bool true
        else Logic.ExtTerm.eq_of Logic.ExtTerm.SInt (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      end
    else (*never use*)Logic.ExtTerm.eq_of Logic.ExtTerm.SInt (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())

  let cgen_from_fcon tvar_template_map tvar_qualifiers_map npfvs polarity (param_senv, phi) =
    let hole_map =
      Formula.fvar_apps_of phi
      |> Set.Poly.to_list
      |> List.concat_map ~f:(fun fvar_app ->
          let tvar, sorts, args, _ = Term.let_fvar_app fvar_app in
          let sorts = List.take sorts (List.length sorts - 1) in
          let hole_qualifiers_map = Map.Poly.find_exn tvar_qualifiers_map tvar in
          List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
              hole,
              if List.is_empty quals then
                Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ SortEnv.list_of @@ SortEnv.of_sorts sorts) @@
                Logic.BoolTerm.mk_bool true
              else
                let _, (_, qsenv, _) = List.hd_exn quals in
                Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ SortEnv.list_of qsenv) @@
                Logic.BoolTerm.and_of @@ List.map quals ~f:(old_eval_qual polarity npfvs (param_senv, Formula.mk_true (), sorts, args))))
      |> Map.Poly.of_alist_exn
    in
    Logic.ExtTerm.of_old_formula phi
    |> Logic.Term.subst tvar_template_map
    |> Logic.Term.subst hole_map

  let cgen_from_ppapp vs tvar_template_map
      (tvar_qualifiers_map : (Ident.tvar, (Ident.tvar * (Ident.tvar * (int * SortEnv.t * Formula.t)) list) list) Map.Poly.t)
      npfvs polarity atom =
    let pvar = match ExAtom.pvar_of atom with Some pvar -> pvar | None -> failwith "cgen_from_papp" in
    let sorts = match ExAtom.sorts_of atom with Some sorts -> sorts | None -> failwith "cgen_from_papp" in
    let hole_qualifiers_map = Map.Poly.find_exn tvar_qualifiers_map (Ident.Tvar (Ident.name_of_pvar pvar)) in
    let tt = TruthTable.get_table (VersionSpace.truth_table_of vs) pvar in
    let fenv = VersionSpace.fenv_of vs in
    let hole_map =
      (List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
           hole,
           if List.is_empty quals then
             Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ SortEnv.list_of @@ SortEnv.of_sorts sorts) @@
             Logic.BoolTerm.mk_bool true
           else
             let _, (_, qsenv, _) = List.hd_exn quals in
             Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ SortEnv.list_of qsenv) @@
             Logic.BoolTerm.and_of @@ List.map quals ~f:(eval_qual tt fenv polarity npfvs atom))) @
      (match ExAtom.args_of atom with
       | None -> assert false
       | Some args ->
         Set.Poly.union_list @@ List.map ~f:Term.fvar_apps_of args
         |> Set.Poly.to_list
         |> List.concat_map ~f:(fun fvar_app ->
             let tvar, sorts, args, _ = Term.let_fvar_app fvar_app in
             let sorts = List.take sorts (List.length sorts - 1) in
             let hole_qualifiers_map = Map.Poly.find_exn tvar_qualifiers_map tvar in
             List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
                 hole,
                 if List.is_empty quals then
                   Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ SortEnv.list_of @@ SortEnv.of_sorts sorts) @@
                   Logic.BoolTerm.mk_bool true
                 else
                   let _, (_, qsenv, _) = List.hd_exn quals in
                   Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ SortEnv.list_of qsenv) @@
                   Logic.BoolTerm.and_of @@ List.map quals ~f:(old_eval_qual polarity npfvs (ExAtom.params_of atom, Formula.mk_true (), sorts, args)))))
      |> Map.Poly.of_alist_exn
    in
    ExAtom.to_formula polarity atom |> snd
    |> Logic.Term.subst tvar_template_map
    |> Logic.Term.subst hole_map

  let cgen_from_exatom (vs:VersionSpace.t) tvar_template_map
      (tvar_qualifiers_map : (Ident.tvar, (Ident.tvar * (Ident.tvar * (int * SortEnv.t * Formula.t)) list) list) Map.Poly.t)
      npfvs polarity atom =
    match atom with
    | ExAtom.FCon (param_senv, phi) ->
      (if polarity then ident else Logic.BoolTerm.neg_of) @@
      cgen_from_fcon tvar_template_map tvar_qualifiers_map npfvs polarity (param_senv, phi)
    | ExAtom.PApp ((_, _), _) | ExAtom.PPApp ((_, _), ((_, _), _)) ->
      cgen_from_ppapp vs tvar_template_map tvar_qualifiers_map npfvs polarity atom

  let _ = Random.init 0
  let cgen_from_pex (vs:VersionSpace.t) tvar_template_map
      (tvar_qualifiers_map : (Ident.tvar, (Ident.tvar * (Ident.tvar * (int * SortEnv.t * Formula.t)) list) list) Map.Poly.t)
      npfvs clause =
    let phi =
      Logic.BoolTerm.or_of @@ Set.Poly.to_list @@
      Set.Poly.union
        (Set.Poly.map clause.ExClause.positive ~f:(cgen_from_exatom vs tvar_template_map tvar_qualifiers_map npfvs true))
        (Set.Poly.map clause.ExClause.negative ~f:(cgen_from_exatom vs tvar_template_map tvar_qualifiers_map npfvs false))
    in
    let param_senv =
      Logic.SortMap.of_old_sort_map Logic.ExtTerm.of_old_sort @@ ExClause.params_of clause
    in
    match config.pex with
    | Quantify -> Logic.BoolTerm.forall (Map.Poly.to_alist param_senv) phi
    | InstRand num ->
      assert (num > 0);
      if Map.Poly.is_empty param_senv then phi
      else
        List.init num ~f:(fun k ->
            let sub = Map.Poly.mapi param_senv ~f:(fun ~key:_ ~data ->
                if k = 0 then Logic.ExtTerm.mk_dummy data
                else
                  match data with
                  | Logic.IntTerm.SInt -> Logic.ExtTerm.mk_int (Z.of_int @@ Util.rand_int ())
                  | Logic.BoolTerm.SBool -> Logic.BoolTerm.mk_bool @@ Random.bool ()
                  | _(*ToDo*) -> Logic.ExtTerm.mk_dummy data) in
            Logic.Term.subst sub phi)
        |> Logic.BoolTerm.and_of
        |> Logic.BoolTerm.forall (Map.Poly.to_alist param_senv)
    | InstDefault ->
      let sub = Map.Poly.mapi param_senv ~f:(fun ~key ~data -> 
          match data with
          | Logic.DatatypeTerm.SUS _ -> Logic.Term.mk_var key
          | _ ->Logic.ExtTerm.mk_dummy data
        ) in
      Logic.Term.subst sub phi
      |> Logic.BoolTerm.forall (Map.Poly.to_alist param_senv)

  (* for SMT Solver *)
  let ctx = ref (Z3.mk_context [("model", "true"); ("unsat_core", "true")])(*dummy*)
  let solver = ref (Z3.Solver.mk_solver !ctx None)(*dummy*)
  let z3dtenv = ref (Z3Smt.Z3interface.z3_dtenv_of_dtenv !ctx @@ PCSP.Problem.dtenv_of APCSP.problem)
  let smt_timeout : int option ref = ref config.smt_timeout
  (* for restart *)
  let iters_after_updated = ref 0
  (* for ucore-based template update *)
  let ref_key_tvar_update_list_map = ref Map.Poly.empty
  (* for incremental solving *)
  let ref_quals = ref (Hashtbl.Poly.create ())
  let old_sample = ref Set.Poly.empty
  let ref_templates = ref (Logic.SortMap.empty, [], [], Map.Poly.empty)

  let initialize () =
    (* for SMT Solver *)
    ctx := Z3.mk_context [("model", "true"); ("unsat_core", "true")](*dummy*);
    solver := Z3.Solver.mk_solver !ctx None(*dummy*);
    z3dtenv := Z3Smt.Z3interface.z3_dtenv_of_dtenv !ctx @@ PCSP.Problem.dtenv_of APCSP.problem;
    smt_timeout := config.smt_timeout;
    (* for restart *)
    iters_after_updated := 0;
    (* for ucore-based template update *)
    ref_key_tvar_update_list_map := Map.Poly.empty;
    (* for incremental solving *)
    ref_quals := Hashtbl.Poly.create ();
    old_sample := Set.Poly.empty;
    ref_templates := Logic.SortMap.empty, [], [], Map.Poly.empty

  let get_key =
    let key_cnt = ref 0 in
    fun () -> incr key_cnt; Printf.sprintf "#S_%d" !key_cnt
  let find_candidate sample
      (vs: VersionSpace.t)
      ((temp_param_senv : Logic.SortMap.t),
       (templates : (Ident.tvar * (Logic.Sort.t * (parameter_update_type * Logic.term))) list),
       (temp_param_cnstrs : (Ident.tvar * (parameter_update_type * Logic.term)) list),
       (tvar_qualifiers_map : (Ident.tvar, (Ident.tvar * (Ident.tvar * (int * SortEnv.t * Formula.t)) list) list) Map.Poly.t)) =
    let fenv = VersionSpace.fenv_of vs in
    let tvar_update_map =
      Map.Poly.of_alist_exn @@ List.map templates ~f:(fun (tvar, (_, (update_label, _))) -> tvar, update_label) in
    let templates =
      List.map templates ~f:(fun (tvar, (sort, (_, term))) -> tvar, (sort, term)) in
    let tvar_template_map =
      Map.Poly.of_alist_exn @@ List.map ~f:(fun (tvar, (_, t)) -> tvar, t) templates in
    let key_constr_map, key_tvar_update_list_map =
      Set.Poly.fold ~init:(Map.Poly.empty, !ref_key_tvar_update_list_map) sample
        ~f:(fun (key_constr_map, key_tvar_update_list_map) clause ->
            Debug.print @@ lazy (sprintf "gen constr of example:%s" (ExClause.str_of clause));
            let npfvs = Set.Poly.filter (ExClause.tvs_of clause) ~f:(fun x -> List.Assoc.mem ~equal:Stdlib.(=) templates x) in
            let pvars = ExClause.pvs_of clause in
            let update_map =
              Set.Poly.union
                (Set.Poly.map pvars ~f:Ident.name_of_pvar)
                (Set.Poly.map npfvs ~f:Ident.name_of_tvar)
              |> Set.Poly.map ~f:(fun name ->
                  Ident.Tvar name, Map.Poly.find_exn tvar_update_map (Ident.Tvar name))
              |> Set.Poly.to_list
            in
            let key = get_key () in
            let constr =
              clause
              |> cgen_from_pex vs tvar_template_map tvar_qualifiers_map npfvs
              |> (fun phi -> Logic.ExtTerm.to_old_formula temp_param_senv phi [])
              |> Evaluator.simplify in
            Debug.print @@ lazy (sprintf "constr:[%s] %s" key (Formula.str_of constr));
            Map.Poly.add_exn key_constr_map ~key ~data:constr,
            Map.Poly.add_exn key_tvar_update_list_map ~key ~data:update_map)
    in
    let key_constr_map, key_tvar_update_list_map =
      (*if !iters_after_updated = 0 then*)
      let used_param_senv =
        Set.of_map key_constr_map
        |> Set.concat_map ~f:(fun (_, phi) -> Formula.tvs_of phi)
        |> Set.concat_map ~f:(fun (Ident.Tvar x) ->
            Set.Poly.of_list [Ident.Tvar x;
                              Ident.Tvar (x ^ "#pos"(*ToDo*));
                              Ident.Tvar (x ^ "#neg"(*ToDo*))]) in
      List.fold temp_param_cnstrs ~init:(key_constr_map, key_tvar_update_list_map)
        ~f:(fun (key_constr_map, key_tvar_update_list_map) (tvar, (update_label, cnstr)) ->
            let key = get_key () in
            let param_constr =
              let dis_map = Logic.SortMap.to_map @@
                Logic.SortMap.filter_mapi temp_param_senv ~f:(fun ~key ~data ->
                    assert (Ident.is_parameter key);
                    if Set.Poly.mem used_param_senv key then None
                    else Some (Term.mk_dummy (Logic.ExtTerm.to_old_sort data))) in
              Logic.ExtTerm.to_old_formula temp_param_senv cnstr []
              |> Formula.subst dis_map
              |> Evaluator.simplify
            in
            (* Debug.print @@ lazy ("param_constr: " ^ Formula.str_of param_constr); *)
            Map.Poly.add_exn key_constr_map ~key ~data:param_constr,
            Map.Poly.add_exn key_tvar_update_list_map ~key ~data:[(tvar, update_label)])
        (*else key_constr_map, key_tvar_update_list_map*)
    in
    ref_key_tvar_update_list_map := key_tvar_update_list_map;
    Debug.print @@ lazy "constraints generated";
    match Z3Smt.Z3interface.check_sat_unsat_core_main ~timeout:!smt_timeout !solver !ctx fenv !z3dtenv key_constr_map with
    | `Sat model -> Debug.print @@ lazy "sat";
      let model = List.map model ~f:(fun ((x, s), t_opt) ->
          (x, Logic.ExtTerm.of_old_sort s),
          Option.(t_opt >>= fun t -> return (Logic.ExtTerm.of_old_term t))) in
      Candidate (construct_candidate temp_param_senv templates tvar_qualifiers_map model)
    | `Unsat unsat_keys ->
      Debug.print @@ lazy ("unsat, reason:" ^ (String.concat unsat_keys ~sep:","));
      let unsat_keys = List.map unsat_keys ~f:(fun str -> String.sub str ~pos:1 ~len:(String.length str - 2)) in
      let pvar_labels_map =
        List.fold unsat_keys ~init:Map.Poly.empty ~f:(fun map key ->
            let pvar_update_list = Map.Poly.find_exn key_tvar_update_list_map key in
            List.fold pvar_update_list ~init:map ~f:(fun map (pvar, label) ->
                Map.Poly.update map pvar ~f:(function
                    | Some labels -> Set.Poly.add labels label
                    | None -> Set.Poly.singleton label))) in
      UnsatCore pvar_labels_map
    (*| `Unknown _reason -> (*failwith reason*)(*UnsatCore Map.Poly.empty*) (*ToDo*)*)
    | `Unknown reason ->
      Debug.print @@ lazy ("unkonwn:" ^ reason);
      UnsatCore (Map.Poly.map tvar_update_map ~f:(fun _ -> Set.Poly.singleton TimeOut))
    | `Timeout ->
      Debug.print @@ lazy "timeout";
      UnsatCore (Map.Poly.map tvar_update_map ~f:(fun _ -> Set.Poly.singleton TimeOut))

  let initialize_templates vs =
    ref_quals := if config.reduce_quals_terms then VersionSpace.reduced_quals_of vs else VersionSpace.quals_of vs;
    let fenv = VersionSpace.fenv_of vs in
    PCSP.Problem.senv_of APCSP.problem
    |> Logic.SortMap.to_alist
    |> List.fold ~init:(Logic.SortMap.empty, [], [], Map.Poly.empty)
      ~f:(fun (temp_param_senv, templates, temp_param_cnstrs, tvar_qualifiers_map)
           (tvar, sort) ->
           let (module FT) = Map.Poly.find_exn template_modules tvar in
           let pvar = Ident.Pvar (Ident.name_of_tvar tvar) in
           let quals = Hashtbl.Poly.find_exn !ref_quals pvar in
           let terms = if config.reduce_quals_terms then VersionSpace.reduced_terms_of_pvar pvar vs else VersionSpace.terms_of_pvar pvar vs in
           let tt = TruthTable.get_table (VersionSpace.truth_table_of vs) pvar in
           let template, temp_param_cnstrs', temp_param_senv', qualifiers = 
             FT.gen_template (Set.Poly.to_list quals) (Set.Poly.to_list terms) in
           let qualifiers =
             List.map qualifiers ~f:(fun (tvar, quals) ->
                 tvar,
                 List.map quals ~f:(fun (tvar, (env, phi)) ->
                     tvar, (TruthTable.index_of_qual tt fenv phi, env, phi))) in
           Logic.SortMap.merge temp_param_senv temp_param_senv',
           (tvar, (sort, template)) :: templates,
           (List.map temp_param_cnstrs' ~f:(fun cnstr -> tvar, cnstr)) @ temp_param_cnstrs,
           Map.Poly.add_exn tvar_qualifiers_map ~key:tvar ~data:qualifiers)

  let update_components vs =
    Map.Poly.iteri template_modules ~f:(
      fun ~key ~data:(module FT) ->
        let name = Ident.name_of_tvar key in
        let pvar = Ident.Pvar name in
        let depth, _, quals, terms = VersionSpace.components_of_pvar pvar vs in
        let quals =
          if Set.Poly.is_empty quals then begin
            let quals = match Map.Poly.find extracted_qualifiers pvar with Some (_, quals) -> FT.adjust_quals quals | None -> Set.Poly.empty in
            (*Debug.print @@ lazy (sprintf "adding qualifiers for %s:\n%s\n" (Ident.name_of_tvar key)
                                   (String.concat ~sep:"\n" (Set.Poly.to_list @@ Set.Poly.map ~f:Formula.str_of quals)));*)
            quals
          end else quals in
        let terms =
          if Set.Poly.is_empty terms then
            match Map.Poly.find extracted_terms pvar with Some (_, terms) -> terms | None -> Set.Poly.empty
          else terms in
        let params = FT.params_of () in
        let depth, quals, terms = FT.gen_quals_terms (depth, quals, terms) in
        Debug.print @@ lazy
          (sprintf "[%s](%s)\ndepth: %d, #quals: %d, #terms: %d"
             name
             (SortEnv.str_of (Term.str_of_sort) params)
             depth
             (Set.Poly.length quals)
             (Set.Poly.length terms));
        (* Debug.print @@ lazy (VersionSpace.str_of_components name (depth, params, quals, terms)); *)
        VersionSpace.update_components key (depth, params, quals, terms) vs);
    VersionSpace.update_truth_table vs

  let instantiate examples =
    let vs = State.version_space_of examples in
    let rec inner () =
      if !iters_after_updated = 0 then begin
        update_components vs;
        ref_templates := initialize_templates vs;
        Debug.print @@ lazy "templates generated";
        ctx := Z3.mk_context [("model", "true"); ("unsat_core", "true")];
        solver := Z3.Solver.mk_solver !ctx None;
        z3dtenv := Z3Smt.Z3interface.z3_dtenv_of_dtenv !ctx @@ PCSP.Problem.dtenv_of APCSP.problem;
        Debug.print @@ lazy "solver initialized";
      end;
      Hashtbl.Poly.iteri (VersionSpace.truth_table_of vs) ~f:(fun ~key ~data ->
          let alist = List.init (TruthTable.length_of_atoms data) ~f:(fun i -> i, 0) in
          Debug.print @@ lazy ("\n" ^ TruthTable.str_of ~alist:(Some alist) (key, data)));
      let reduced_quals = if config.reduce_quals_terms then VersionSpace.reduced_quals_of vs else VersionSpace.quals_of vs in
      if !iters_after_updated <> 0 &&
         not @@ (Hashtbl.Poly.equal (fun b1 b2 -> Set.Poly.length b1 = Set.Poly.length b2) reduced_quals !ref_quals) then begin
        Debug.print @@ lazy ("#quals changed");
        ref_quals := reduced_quals;
        ref_key_tvar_update_list_map := Map.Poly.empty;
        iters_after_updated := 0;
        old_sample := Set.Poly.empty;
        inner ()
      end else
        match config.restart_threshold with
        | Some threshold when !iters_after_updated >= threshold ->
          ref_key_tvar_update_list_map := Map.Poly.empty;
          iters_after_updated := 0;
          old_sample := Set.Poly.empty;
          Map.Poly.iter template_modules ~f:(fun (module FT) ->  FT.restart ());
          inner ()
        | _ ->
          if config.ask_smt_timeout then begin
            Out_channel.print_endline ("current timeout: " ^ (match !smt_timeout with None -> "null" | Some n -> string_of_int n));
            Out_channel.flush Out_channel.stdout;
            smt_timeout := int_of_string_opt @@ In_channel.input_line_exn In_channel.stdin
          end;
          let diff_sample = match examples with
            | State.Continue (vs, _a) ->
              let (dpos, dneg, undecided) = VersionSpace.examples_of vs in
              Set.Poly.diff (Set.Poly.union_list [dpos; dneg; undecided]) !old_sample
            | _ -> assert false
          in
          match find_candidate diff_sample vs !ref_templates with
          | Candidate candidate ->
            iters_after_updated := !iters_after_updated + 1;
            old_sample := Set.Poly.union diff_sample !old_sample;
            candidate
          | UnsatCore pvar_labels_map ->
            ref_key_tvar_update_list_map := Map.Poly.empty;
            iters_after_updated := 0;
            old_sample := Set.Poly.empty;
            TemplateUpdateStrategy.update template_modules examples pvar_labels_map;
            (match config.sync_threshold with
             | None -> ()
             | Some thre -> Map.Poly.iter template_modules ~f:(fun (module FT) ->  FT.sync thre));
            inner ()
    in
    inner ()
end
