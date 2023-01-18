open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon
open Template.Function

type cand = (Ident.tvar, Logic.Sort.t * Logic.term) Map.Poly.t
type candidate =
  | Cands of cand * (cand * Ident.tvar) list
  | OutSpace of Ident.tvar list

type candidate_or_unsat_core =
  | Candidate of cand
  | UnsatCore of (Ident.tvar, parameter_update_type Set.Poly.t) Map.Poly.t

type smt_solver_instance = {
  mutable ctx : Z3.context;
  mutable solver : Z3.Solver.solver;
  mutable z3dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t;
  mutable z3fenv : (Ident.tvar, Z3.FuncDecl.func_decl) Map.Poly.t;
  mutable smt_timeout : int option;
}

module Config = struct
  type pex =
    | Quantify
    | InstDefault
    | InstRand of int [@@deriving yojson]
  type predicate_template =
    | DNF of Template.PredicateDNF.Config.t ext_file
    | Flex of Template.PredicateFlex.Config.t ext_file [@@deriving yojson]
  type wf_predicate_template =
    | WF of Template.WFPredicate.Config.t ext_file
    | WF_Flex of Template.WFPredicateFlex.Config.t ext_file [@@deriving yojson]
  type fn_predicate_template =
    | FN of Template.FNPredicate.Config.t ext_file
    | FN_Flex of Template.FNPredicateFlex.Config.t ext_file [@@deriving yojson]
  type int_function_template =
    | IntFun of Template.IntFunction.Config.t ext_file
    | IntFun_Flex of Template.IntFunctionFlex.Config.t ext_file [@@deriving yojson]
  type t = {
    predicate_template: predicate_template;
    wf_predicate_template: wf_predicate_template;
    fn_predicate_template: fn_predicate_template;
    int_function_template: int_function_template;
    ne_predicate_template: Template.NEPredicate.Config.t ext_file;
    update_strategy: TemplateUpdateStrategy.Config.t;
    qualifier_generator: Qualifier.Generator.Config.t ext_file;
    smt_timeout: int option;
    extract_qualifiers: bool;
    extract_terms: bool;
    extract_seeds: bool;
    reduce_quals_terms: bool;
    sync_threshold: int option;
    restart_threshold: int option;
    auto_incr_shape_interval: int option;
    pex: pex;
    verbose: bool
  } [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    (match cfg.predicate_template with
     | DNF cfg ->
       Template.PredicateDNF.Config.load_ext_file cfg >>= fun predicate_template ->
       Ok (DNF predicate_template)
     | Flex cfg ->
       Template.PredicateFlex.Config.load_ext_file cfg >>= fun predicate_template ->
       Ok (Flex predicate_template)) >>= fun predicate_template ->

    (match cfg.wf_predicate_template with
     | WF cfg ->
       Template.WFPredicate.Config.load_ext_file cfg >>= fun wf_predicate_template ->
       Ok (WF wf_predicate_template)
     | WF_Flex cfg ->
       Template.WFPredicateFlex.Config.load_ext_file cfg >>= fun wf_predicate_template ->
       Ok (WF_Flex wf_predicate_template)) >>= fun wf_predicate_template ->

    (match cfg.fn_predicate_template with
     | FN cfg ->
       Template.FNPredicate.Config.load_ext_file cfg >>= fun fn_predicate_template ->
       Ok (FN fn_predicate_template)
     | FN_Flex cfg ->
       Template.FNPredicateFlex.Config.load_ext_file cfg >>= fun fn_predicate_template ->
       Ok (FN_Flex fn_predicate_template)) >>= fun fn_predicate_template ->

    (match cfg.int_function_template with
     | IntFun cfg ->
       Template.IntFunction.Config.load_ext_file cfg >>= fun int_function_template ->
       Ok (IntFun int_function_template)
     | IntFun_Flex cfg ->
       Template.IntFunctionFlex.Config.load_ext_file cfg >>= fun int_function_template ->
       Ok (IntFun_Flex int_function_template)) >>= fun int_function_template ->
    Template.NEPredicate.Config.load_ext_file cfg.ne_predicate_template >>= fun ne_predicate_template ->
    TemplateUpdateStrategy.Config.instantiate_ext_files cfg.update_strategy >>= fun update_strategy ->
    Qualifier.Generator.Config.load_ext_file cfg.qualifier_generator >>= fun qualifier_generator ->
    Ok { cfg with predicate_template = predicate_template;
                  wf_predicate_template = wf_predicate_template;
                  fn_predicate_template = fn_predicate_template;
                  ne_predicate_template = ne_predicate_template;
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
          error_string @@ Printf.sprintf
            "Invalid SolutionTemplate Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (ExtFile.Instance x)

  module type ConfigType = sig val config: t end
end

module type SolutionTemplateType = sig
  val initialize : unit -> unit
  val instantiate : State.u -> candidate
end

module Make (RLCfg : RLConfig.ConfigType) (Cfg : Config.ConfigType) (APCSP: PCSP.Problem.ProblemType) : SolutionTemplateType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))
  let _ = Debug.set_id id

  module TemplateUpdateStrategy : TemplateUpdateStrategy.TemplateUpdateStrategyType =
    TemplateUpdateStrategy.Make (RLCfg) (struct let config = config.update_strategy end) (APCSP)

  module QualifierGenerator =
    Qualifier.Generator.Make (struct let config = ExtFile.unwrap_or_abort config.qualifier_generator end) (APCSP)

  let extracted_qualifiers =
    if not config.extract_qualifiers then Map.Poly.empty
    else
      Map.Poly.to_alist @@ PCSP.Problem.senv_of APCSP.problem
      |> List.fold ~init:Map.Poly.empty
        ~f:(fun acc (Ident.Tvar name, sort) ->
            let sorts = List.map (Logic.Sort.args_of sort) ~f:Logic.ExtTerm.to_old_sort in
            let args = LogicOld.sort_env_list_of_sorts sorts in
            let quals =
              Set.Poly.map ~f:snd @@
              QualifierGenerator.generate (Ident.Pvar name) args Set.Poly.empty (Map.Poly.empty, ClauseGraph.create ()) 0
            in
            Map.Poly.add_exn acc ~key:(Ident.Pvar name) ~data:(args, quals))
  let extracted_terms =
    Map.force_merge
      (if not config.extract_terms then Map.Poly.empty
       else
         Map.Poly.map extracted_qualifiers ~f:(fun (args, phis) ->
             args,
             Set.Poly.filter ~f:Term.is_numerical_compound(*ToDo*) @@
             Set.concat_map phis ~f:Formula.terms_of))
      (if not config.extract_seeds then Map.Poly.empty
       else
         Map.Poly.map extracted_qualifiers ~f:(fun (args, phis) ->
             args,
             Set.concat_map phis ~f:Formula.funsyms_of
             |> Set.Poly.filter_map ~f:(function T_int.Int i when Z.Compare.(i <> Z.zero) -> Some (T_int.mk_int @@ Z.abs i) | _ -> None)))

  let template_modules : (Ident.tvar, (module Template.Function.Type)) Map.Poly.t =
    Map.Poly.mapi (PCSP.Problem.senv_of APCSP.problem) ~f:(fun ~key ~data ->
        let tvar = key in
        let sorts = Logic.Sort.args_of data |> List.map ~f:Logic.ExtTerm.to_old_sort in
        let module M = struct
          let name = tvar
          let sorts = sorts
          let dtenv = PCSP.Problem.dtenv_of APCSP.problem
          let fenv = PCSP.Problem.fenv_of APCSP.problem
          let sol_space = PCSP.Problem.sol_space_of APCSP.problem
          let id = id
        end in
        if PCSP.Problem.is_ord_pred APCSP.problem tvar then
          match config.predicate_template with
          | DNF predicate_template ->
            (module Template.PredicateDNF.Make
                 (struct let config = ExtFile.unwrap_or_abort predicate_template end)
                 (M) : Template.Function.Type)
          | Flex predicate_template ->
            (module Template.PredicateFlex.Make
                 (struct let config = ExtFile.unwrap_or_abort predicate_template end)
                 (M) : Template.Function.Type)
        else if PCSP.Problem.is_ne_pred APCSP.problem tvar then
          (module Template.NEPredicate.Make
               (struct let config = ExtFile.unwrap_or_abort config.ne_predicate_template end)
               (M) : Template.Function.Type)
        else if PCSP.Problem.is_wf_pred APCSP.problem tvar then
          match config.wf_predicate_template with
          | WF wf_predicate_template ->
            (module Template.WFPredicate.Make
                 (struct let config = ExtFile.unwrap_or_abort wf_predicate_template end)
                 (M) : Template.Function.Type)
          | WF_Flex wf_predicate_template ->
            (module Template.WFPredicateFlex.Make
                 (struct let config = ExtFile.unwrap_or_abort wf_predicate_template end)
                 (M) : Template.Function.Type)
        else if PCSP.Problem.is_fn_pred APCSP.problem tvar then
          match config.fn_predicate_template with
          | FN fn_predicate_template ->
            (module Template.FNPredicate.Make
                 (struct let config = ExtFile.unwrap_or_abort fn_predicate_template end)
                 (M) : Template.Function.Type)
          | FN_Flex fn_predicate_template ->
            (module Template.FNPredicateFlex.Make
                 (struct let config = ExtFile.unwrap_or_abort fn_predicate_template end)
                 (M) : Template.Function.Type)
        else if PCSP.Problem.is_int_fun APCSP.problem tvar then
          match config.int_function_template with
          | IntFun int_function_template ->
            (module Template.IntFunction.Make
                 (struct let config = ExtFile.unwrap_or_abort int_function_template end)
                 (M) : Template.Function.Type)
          | IntFun_Flex int_function_template ->
            (module Template.IntFunctionFlex.Make
                 (struct let config = ExtFile.unwrap_or_abort int_function_template end)
                 (M) : Template.Function.Type)
        else if PCSP.Problem.is_nwf_pred APCSP.problem tvar then
          let public_name, parameter_sorts, tag_infos =
            match Map.Poly.find (PCSP.Problem.kind_map_of APCSP.problem) tvar with
            | Some (PCSP.Kind.NWF(nwf, _tag)) ->
              nwf.name,
              List.map ~f:Logic.ExtTerm.to_old_sort @@ nwf.param_sorts,
              Hashtbl.Poly.map nwf.tag_infos ~f:(List.map ~f:Logic.ExtTerm.to_old_sort)
            | _ -> assert false
          in
          let module M : Template.NWFPredicate.ArgType = struct
            let public_name = public_name
            let parameter_sorts = parameter_sorts
            let tag_infos = tag_infos
            let dtenv = PCSP.Problem.dtenv_of APCSP.problem
            let fenv = PCSP.Problem.fenv_of APCSP.problem
            let id = id
          end in
          match config.wf_predicate_template with
          | WF wf_predicate_template ->
            let module Config : Template.WFPredicate.Config.ConfigType = struct
              let config = ExtFile.unwrap_or_abort wf_predicate_template
            end in
            Template.NWFPredicate.make ~id ~public_name (module Config) (module M)
          | WF_Flex _ -> failwith @@ sprintf "not supported %s" (Ident.name_of_tvar tvar)
        else failwith @@ sprintf "not supported %s" (Ident.name_of_tvar tvar))

  type tvar_qualifiers_map = (Ident.tvar, (Ident.tvar * (Ident.tvar * (int * sort_env_list * Formula.t)) list) list) Map.Poly.t
  let construct_candidate
      (temp_param_senv : Logic.sort_env_map)
      (templates : (Ident.tvar * (Logic.Sort.t * Logic.term)) list)
      (tvar_qualifiers_map : tvar_qualifiers_map)
      (model : Logic.model) =
    let temp_param_sub =
      Map.Poly.mapi temp_param_senv ~f:(fun ~key ~data ->
          (match List.find model ~f:(fun ((x, _), _) -> Stdlib.(x = key)) with
           | None -> (key, data), None | Some opt -> opt)
          |> Logic.ExtTerm.remove_dontcare_elem (* ToDo: support parameteric candidate solution and CEGIS(T)*)
          |> snd)
    in
    Map.Poly.of_alist_exn @@ List.map templates ~f:(fun (tvar, (sort, term)) ->
        let hole_qualifiers_map = Map.Poly.find_exn tvar_qualifiers_map tvar in
        let hole_sub =
          Map.Poly.of_alist_exn @@ List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
              hole,
              if List.is_empty quals then
                let sorts = Logic.Sort.args_of sort in
                Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ sort_env_list_of_sorts @@ List.map ~f:Logic.ExtTerm.to_old_sort sorts) @@
                Logic.BoolTerm.mk_bool true
              else
                let _, (_, senv, _) = List.hd_exn quals in
                Template.Generator.gen_from_qualifiers (senv, quals))
        in
        (* Debug.print @@ lazy (Logic.ExtTerm.str_of term); *)
        let term' = Logic.ExtTerm.subst temp_param_sub @@ Logic.ExtTerm.subst hole_sub term in
        (* Debug.print @@ lazy (Logic.ExtTerm.str_of term'); *)
        assert (Set.Poly.is_empty @@ Logic.ExtTerm.fvs_of term');
        (tvar, (sort, term')))

  let old_eval_qual polarity unknowns (_param_senv, cond, _sorts, args) (key, (_, params, phi)) =
    let fvs = Set.Poly.union_list @@ List.map ~f:LogicOld.Term.tvs_of args in
    let fenv = Map.Poly.empty in (*TODO: generate fenv*)
    if Set.Poly.is_empty @@ Set.Poly.inter fvs unknowns then
      let phi =
        let sub = Map.Poly.of_alist_exn @@ List.zip_exn (List.map ~f:fst params) args in
        Formula.subst sub phi
      in
      match Evaluator.check ~cond (Z3Smt.Z3interface.is_valid ~id fenv) phi with
      | Some true -> Logic.ExtTerm.geq_of (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      | Some false -> Logic.ExtTerm.leq_of (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      | None ->
        (*Debug.print @@ lazy (Formula.str_of phi ^ " couldn't be evaluated.  This may cause a violation of the progress property.");*)
        if not polarity then Logic.ExtTerm.mk_bool true
        else Logic.ExtTerm.eq_of Logic.ExtTerm.SInt (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
    else (*never use*)Logic.ExtTerm.eq_of Logic.ExtTerm.SInt (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())

  let eval_qual tt fenv qdeps polarity unknowns atom (key, (qi, _params, _phi)) =
    let fvs = ExAtom.tvs_of atom in
    if Set.Poly.is_empty @@ Set.Poly.inter fvs unknowns then
      let ai = TruthTable.index_of_atom ~id tt fenv qdeps (ExAtom.instantiate @@ ExAtom.normalize_params atom) in
      let e = tt.table.{qi, ai} in
      if e = 1 then Logic.ExtTerm.geq_of (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      else if e = -1 then Logic.ExtTerm.leq_of (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      else begin
        (*Debug.print @@ lazy (ExAtom.str_of atom ^ " on " ^ Formula.str_of phi ^ " couldn't be evaluated.  This may cause a violation of the progress property.");*)
        if not polarity then Logic.ExtTerm.mk_bool true
        else Logic.ExtTerm.eq_of Logic.ExtTerm.SInt (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())
      end
    else (*never use*)Logic.ExtTerm.eq_of Logic.ExtTerm.SInt (Logic.Term.mk_var key) (Logic.ExtTerm.zero ())

  let cgen_from_fcon tvar_template_map tvar_qualifiers_map unknowns polarity (param_senv, phi) =
    try
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
                  let senv = List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ sort_env_list_of_sorts sorts in
                  Logic.Term.mk_lambda senv @@ Logic.BoolTerm.mk_bool true
                else
                  let senv =
                    let _, (_, qsenv, _) = List.hd_exn quals in
                    List.map ~f:Logic.ExtTerm.of_old_sort_bind qsenv
                  in
                  Logic.Term.mk_lambda senv @@
                  Logic.BoolTerm.and_of @@ List.map quals ~f:(old_eval_qual polarity unknowns (param_senv, Formula.mk_true (), sorts, args))))
        |> Map.Poly.of_alist_exn
      in
      Logic.ExtTerm.of_old_formula phi
      |> Logic.Term.subst tvar_template_map
      |> Logic.Term.subst hole_map
    with _ -> (*ToDo*)failwith "multiple occurrences of a function variable not supported"

  let cgen_from_ppapp vs tvar_template_map
      (tvar_qualifiers_map : tvar_qualifiers_map)
      unknowns polarity atom =
    let pvar = match ExAtom.pvar_of atom with Some pvar -> pvar | None -> failwith "cgen_from_papp" in
    let sorts = match ExAtom.sorts_of atom with Some sorts -> sorts | None -> failwith "cgen_from_papp" in
    let hole_qualifiers_map = Map.Poly.find_exn tvar_qualifiers_map (Ident.pvar_to_tvar pvar) in
    let tt = TruthTable.get_table (VersionSpace.truth_table_of vs) pvar in
    let fenv = VersionSpace.fenv_of vs in
    let qdeps = VersionSpace.qdeps_of pvar vs in
    let hole_map =
      Map.Poly.of_alist_exn @@
      List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
          hole,
          if List.is_empty quals then
            Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ sort_env_list_of_sorts sorts) @@
            Logic.BoolTerm.mk_bool true
          else
            let _, (_, qsenv, _) = List.hd_exn quals in
            Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind qsenv) @@
            Logic.BoolTerm.and_of @@ List.map quals ~f:(eval_qual tt fenv qdeps polarity unknowns atom)) @
      match ExAtom.args_of atom with
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
                  Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ sort_env_list_of_sorts sorts) @@
                  Logic.BoolTerm.mk_bool true
                else
                  let _, (_, qsenv, _) = List.hd_exn quals in
                  Logic.Term.mk_lambda (List.map ~f:Logic.ExtTerm.of_old_sort_bind qsenv) @@
                  Logic.BoolTerm.and_of @@ List.map quals ~f:(old_eval_qual polarity unknowns (ExAtom.params_of atom, Formula.mk_true (), sorts, args))))
    in
    ExAtom.to_formula polarity atom |> snd
    |> Logic.Term.subst tvar_template_map
    |> Logic.Term.subst hole_map

  let cgen_from_exatom (vs:VersionSpace.t) tvar_template_map
      (tvar_qualifiers_map : tvar_qualifiers_map)
      unknowns polarity = function
    | ExAtom.FCon (param_senv, phi) ->
      (if polarity then Fn.id else Logic.BoolTerm.neg_of) @@
      cgen_from_fcon tvar_template_map tvar_qualifiers_map unknowns polarity (param_senv, phi)
    | (ExAtom.PApp ((_, _), _) | ExAtom.PPApp ((_, _), ((_, _), _))) as atom ->
      cgen_from_ppapp vs tvar_template_map tvar_qualifiers_map unknowns polarity atom

  let _ = Random.init 0
  let cgen_from_pex (vs:VersionSpace.t) tvar_template_map
      (tvar_qualifiers_map : tvar_qualifiers_map)
      unknowns clause =
    let phi =
      Logic.BoolTerm.or_of @@ Set.Poly.to_list @@
      Set.Poly.union
        (Set.Poly.map clause.ExClause.positive ~f:(cgen_from_exatom vs tvar_template_map tvar_qualifiers_map unknowns true))
        (Set.Poly.map clause.ExClause.negative ~f:(cgen_from_exatom vs tvar_template_map tvar_qualifiers_map unknowns false))
    in
    let param_senv =
      Logic.of_old_sort_env_map Logic.ExtTerm.of_old_sort @@ ExClause.params_of clause
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
                  | Logic.IntTerm.SInt -> Logic.ExtTerm.mk_int (Z.of_int @@ Integer.rand_int ())
                  | Logic.BoolTerm.SBool -> Logic.BoolTerm.mk_bool @@ Random.bool ()
                  | _(*ToDo*) -> Logic.ExtTerm.mk_dummy data) in
            Logic.Term.subst sub phi)
        |> Logic.BoolTerm.and_of
        |> Logic.BoolTerm.forall (Map.Poly.to_alist param_senv)
    | InstDefault ->
      let sub =
        Map.Poly.mapi param_senv ~f:(fun ~key ~data ->
            match data with
            | Logic.DatatypeTerm.SUS _ -> Logic.Term.mk_var key
            | _ ->Logic.ExtTerm.mk_dummy data)
      in
      Logic.BoolTerm.forall (Map.Poly.to_alist param_senv) @@
      Logic.Term.subst sub phi

  (* for SMT Solver *)

  let create_smt_instance () =
    let ctx =  Z3.mk_context [("model", "true"); ("unsat_core", "true")](*dummy*) in
    let solver = Z3.Solver.mk_solver ctx None(*dummy*) in
    let z3dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of APCSP.problem in
    let z3fenv = Z3Smt.Z3interface.z3_fenv_of ctx [] [] (Atomic.get LogicOld.ref_fenv) z3dtenv in
    let smt_timeout = config.smt_timeout in
    { ctx; solver; z3dtenv; z3fenv; smt_timeout }

  let recreate_smt_instance instance =
    let ctx = Z3.mk_context [("model", "true"); ("unsat_core", "true")](*dummy*) in
    let z3dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of APCSP.problem in
    let z3fenv = Z3Smt.Z3interface.z3_fenv_of ctx [] [] (Atomic.get LogicOld.ref_fenv) z3dtenv in
    instance.ctx <- ctx;
    instance.solver <- Z3.Solver.mk_solver ctx None(*dummy*);
    instance.z3dtenv <- z3dtenv;
    instance.z3fenv <- z3fenv;
    instance.smt_timeout <- config.smt_timeout

  let default_smt_instance = create_smt_instance ()
  let partial_sol_smt_instance =
    Map.Poly.map (PCSP.Problem.partial_sol_targets_of APCSP.problem)
      ~f:(fun _ -> create_smt_instance ())
  let partial_sol_checking_smt_instance =
    Map.Poly.map (PCSP.Problem.partial_sol_targets_of APCSP.problem)
      ~f:(fun _ -> create_smt_instance ())
  let reset_all_smt_instance () =
    recreate_smt_instance default_smt_instance;
    Map.Poly.iter partial_sol_smt_instance ~f:recreate_smt_instance
  let iters_after_updated = ref 0
  let incr_times = ref 0
  (* for ucore-based template update *)
  let ref_key_tvar_update_list_map = ref Map.Poly.empty
  (* for incremental solving *)
  let ref_quals = ref (Hashtbl.Poly.create ())
  let old_sample = ref Set.Poly.empty
  let ref_templates = ref (Map.Poly.empty, [], [], Map.Poly.empty)
  let ref_redundant_exs = ref (Set.Poly.empty)
  let initialize () =
    (* for SMT Solver *)
    Z3.Solver.reset default_smt_instance.solver;
    default_smt_instance.smt_timeout <- config.smt_timeout;
    (* for restart *)
    iters_after_updated := 0;
    (* for ucore-based template update *)
    ref_key_tvar_update_list_map := Map.Poly.empty;
    (* for incremental solving *)
    ref_quals := Hashtbl.Poly.create ();
    old_sample := Set.Poly.empty;
    ref_templates := Map.Poly.empty, [], [], Map.Poly.empty

  (* let sel_env = ref Map.Poly.empty *)

  type lc = { label: string; constr: string } [@@ deriving to_yojson]
  type ucores = string list [@@ deriving to_yojson]

  let get_key =
    let key_cnt = ref 0 in
    fun () ->
      incr key_cnt;
      Printf.sprintf "#S%d_%d" (match id with | Some id -> id | None -> 0) !key_cnt
  let find_candidate ?(untrack_sample=Set.Poly.empty)
      (smt_solver_instance: smt_solver_instance)
      sample
      (vs: VersionSpace.t)
      ((temp_param_senv : Logic.sort_env_map),
       (templates : (Ident.tvar * (Logic.Sort.t * (parameter_update_type * Logic.term))) list),
       (temp_param_cnstrs : (Ident.tvar * (parameter_update_type * Logic.term)) list),
       (tvar_qualifiers_map : tvar_qualifiers_map)) =
    (* let uenv = VersionSpace.uenf_of vs in *)
    let tvar_update_map =
      Map.Poly.of_alist_exn @@ List.map templates ~f:(fun (tvar, (_, (update_label, _))) -> tvar, update_label) in
    let templates =
      List.map templates ~f:(fun (tvar, (sort, (_, term))) -> tvar, (sort, term)) in
    let tvar_template_map =
      Map.Poly.of_alist_exn @@ List.map ~f:(fun (tvar, (_, t)) -> tvar, t) templates in
    let untrack_constrs =
      Set.Poly.map untrack_sample ~f:(fun clause ->
          Debug.print @@ lazy (sprintf "gen untrack_constrs of example: %s" @@ ExClause.str_of clause);
          let unknowns = Set.Poly.filter (ExClause.tvs_of clause) ~f:(List.Assoc.mem ~equal:Stdlib.(=) templates) in
          let constr =
            clause
            |> cgen_from_pex vs tvar_template_map tvar_qualifiers_map unknowns
            |> (fun phi -> Logic.ExtTerm.to_old_formula Map.Poly.empty temp_param_senv phi [])
            |> Evaluator.simplify in
          Debug.print @@ lazy (sprintf "untrack constr: %s" @@ Formula.str_of constr);
          constr)
      |> Set.Poly.to_list
    in
    let key_constr_map, key_tvar_update_list_map =
      Set.Poly.fold ~init:(Map.Poly.empty, !ref_key_tvar_update_list_map) sample
        ~f:(fun (key_constr_map, key_tvar_update_list_map) clause ->
            Debug.print @@ lazy (sprintf "gen constr of example:%s" @@ ExClause.str_of clause);
            let unknowns = Set.Poly.filter (ExClause.tvs_of clause) ~f:(List.Assoc.mem ~equal:Stdlib.(=) templates) in
            let update_map =
              Set.Poly.union
                (Set.Poly.map (ExClause.pvs_of clause) ~f:Ident.name_of_pvar)
                (Set.Poly.map unknowns ~f:Ident.name_of_tvar)
              |> Set.Poly.map ~f:(fun name ->
                  Ident.Tvar name, Map.Poly.find_exn tvar_update_map @@ Ident.Tvar name)
              |> Set.Poly.to_list
            in
            let key = get_key () in
            let constr =
              clause
              |> cgen_from_pex vs tvar_template_map tvar_qualifiers_map unknowns
              |> (fun phi -> Logic.ExtTerm.to_old_formula Map.Poly.empty temp_param_senv phi [])
              |> Evaluator.simplify in
            if RLCfg.config.enable && RLCfg.config.show_unsat_core then
              Out_channel.print_endline (Printf.sprintf "labeled constraint: %s" (Yojson.Safe.to_string @@ lc_to_yojson { label = key; constr = Formula.str_of constr }));
            Debug.print @@ lazy (sprintf "constr: [%s] %s" key (Formula.str_of constr));
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
              let dis_map =
                Map.Poly.filter_mapi temp_param_senv ~f:(fun ~key ~data ->
                    assert (Ident.is_parameter key);
                    if Set.Poly.mem used_param_senv key then None
                    else Some (Term.mk_dummy @@ Logic.ExtTerm.to_old_sort data)) in
              Logic.ExtTerm.to_old_formula Map.Poly.empty temp_param_senv cnstr []
              |> (fun phi ->
                  if PCSP.Problem.is_ne_pred APCSP.problem tvar then phi
                  else Formula.subst dis_map phi)
              |> Evaluator.simplify
            in
            if RLCfg.config.enable && RLCfg.config.show_unsat_core then
              Out_channel.print_endline (Printf.sprintf "labeled bounds constraint: %s" (Yojson.Safe.to_string @@ lc_to_yojson { label = key; constr = Formula.str_of param_constr }));
            Debug.print @@ lazy (sprintf "bounds constr: [%s] %s" key (Formula.str_of param_constr));
            Map.Poly.add_exn key_constr_map ~key ~data:param_constr,
            Map.Poly.add_exn key_tvar_update_list_map ~key ~data:[(tvar, update_label)])
        (*else key_constr_map, key_tvar_update_list_map*)
    in
    (* let key_constr_map =
       let phi = UTermEnv.to_formula uenv in
       if Formula.is_true phi then key_constr_map
       else if Map.Poly.exists key_constr_map ~f:(fun phi1 -> Stdlib.(Formula.str_of phi1 = Formula.str_of phi) then key_constr_map
       else begin
        let key = get_key () in
        Debug.print @@ lazy (sprintf "uterm_constr %s: %s" key (Formula.str_of phi));
        Map.Poly.add_exn key_constr_map ~key:(key) ~data:(phi)
       end
       in *)
    ref_key_tvar_update_list_map := key_tvar_update_list_map;
    Debug.print @@ lazy "constraints generated";
    match Z3Smt.Z3interface.check_sat_unsat_core_main
            ~timeout:smt_solver_instance.smt_timeout
            ~untrack_phis:untrack_constrs
            smt_solver_instance.solver
            smt_solver_instance.ctx
            smt_solver_instance.z3fenv
            smt_solver_instance.z3dtenv
            key_constr_map with
    | `Sat model -> Debug.print @@ lazy "sat";
      let model =
        List.map model ~f:(fun ((x, s), t_opt) ->
            (x, Logic.ExtTerm.of_old_sort s),
            Option.(t_opt >>= fun t -> return @@ Logic.ExtTerm.of_old_term t))
      in
      Candidate (construct_candidate temp_param_senv templates tvar_qualifiers_map model)
    | `Unsat unsat_keys ->
      Debug.print @@ lazy ("unsat, reason:" ^ String.concat ~sep:"," unsat_keys);
      let unsat_keys = List.map unsat_keys ~f:(fun str -> String.sub str ~pos:1 ~len:(String.length str - 2)) in
      if RLCfg.config.enable && RLCfg.config.show_unsat_core then
        Out_channel.print_endline (Printf.sprintf "unsat cores: %s" @@ Yojson.Safe.to_string @@ ucores_to_yojson unsat_keys);
      let pvar_labels_map =
        List.fold unsat_keys ~init:Map.Poly.empty ~f:(fun map key ->
            match Map.Poly.find key_tvar_update_list_map key with
            | Some pvar_update_list ->
              List.fold pvar_update_list ~init:map ~f:(fun map (pvar, label) ->
                  Map.Poly.update map pvar ~f:(function
                      | Some labels -> Set.Poly.add labels label
                      | None -> Set.Poly.singleton label))
            | None -> map)
      in
      UnsatCore pvar_labels_map
    (*| `Unknown _reason -> (*failwith reason*)(*UnsatCore Map.Poly.empty*) (*ToDo*)*)
    | `Unknown reason ->
      Debug.print @@ lazy ("unknown:" ^ reason);
      UnsatCore (Map.Poly.map tvar_update_map ~f:(fun _ -> Set.Poly.singleton TimeOut))
    | `Timeout ->
      Debug.print @@ lazy "timeout";
      UnsatCore (Map.Poly.map tvar_update_map ~f:(fun _ -> Set.Poly.singleton TimeOut))

  let reduce_quals vs =
    let table = VersionSpace.truth_table_of vs in
    if not config.reduce_quals_terms then 
      VersionSpace.quals_map_of vs
    else
      Hashtbl.Poly.map table ~f:(fun tt ->
          let qlist = List.init (TruthTable.length_of_quals tt) ~f:Fn.id in
          let alist = Map.Poly.of_alist_exn @@ List.init (TruthTable.length_of_atoms tt) ~f:(fun i -> i, 0(* dummy *)) in
          (if config.reduce_quals_terms then TruthTable.reduced_qlist_of tt (qlist, alist) else qlist)
          |> List.map ~f:(IncrArray.get tt.qarr) |> Set.Poly.of_list)
  let reduce_terms pvar vs =
    if config.reduce_quals_terms
    then VersionSpace.reduced_terms_of_pvar pvar vs
    else VersionSpace.terms_of_pvar pvar vs
  let initialize_templates vs =
    ref_quals := reduce_quals vs;
    PCSP.Problem.senv_of APCSP.problem |> Map.Poly.to_alist
    |> List.fold ~init:(Map.Poly.empty, [], [], Map.Poly.empty)
      ~f:(fun (temp_param_senv, templates, temp_param_cnstrs, tvar_qualifiers_map)
           (tvar, sort) ->
           let (module FT) = Map.Poly.find_exn template_modules tvar in
           let pvar = Ident.tvar_to_pvar tvar in
           let tt = TruthTable.get_table (VersionSpace.truth_table_of vs) pvar in
           let template, temp_param_cnstrs', temp_param_senv', qualifiers =
             FT.gen_template ~tag:(PCSP.Problem.tag_of APCSP.problem tvar)
               (Set.Poly.to_list @@ Hashtbl.Poly.find_exn !ref_quals pvar)
               (VersionSpace.qdeps_of pvar vs)
               (Set.Poly.to_list @@ reduce_terms pvar vs)
           in
           let qualifiers =
             List.map qualifiers ~f:(fun (tvar, quals) ->
                 tvar,
                 List.map quals ~f:(fun (tvar, (env, phi)) ->
                     tvar,
                     (TruthTable.index_of_qual ~id tt
                        (VersionSpace.fenv_of vs) (VersionSpace.qdeps_of pvar vs) phi,
                      env, phi)))
           in
           Map.force_merge temp_param_senv temp_param_senv',
           (tvar, (sort, template)) :: templates,
           List.map temp_param_cnstrs' ~f:(fun cnstr -> tvar, cnstr) @ temp_param_cnstrs,
           Map.Poly.add_exn tvar_qualifiers_map ~key:tvar ~data:qualifiers)

  (** init quals for nwf predicate tempalte *)
  let _ =
    Map.Poly.iteri template_modules ~f:(fun ~key ~data:(module FT) ->
        match Map.Poly.find extracted_qualifiers @@ Ident.tvar_to_pvar key with
        | Some (_, quals) -> FT.init_quals (PCSP.Problem.tag_of APCSP.problem key) quals
        | _ -> ())

  let update_hspaces vs =
    Map.Poly.iteri template_modules ~f:(fun ~key ~data:(module FT) ->
        let tag = PCSP.Problem.tag_of APCSP.problem key in
        let name = Ident.name_of_tvar key in
        let pvar = Ident.Pvar name in
        let depth, _, quals, qdeps, terms = VersionSpace.hspace_of_pvar pvar vs in
        let quals =
          if Set.Poly.is_empty quals then begin
            let quals =
              match Map.Poly.find extracted_qualifiers pvar with
              | Some (_, quals) -> FT.adjust_quals ~tag quals | None -> Set.Poly.empty in
            (*Debug.print @@ lazy
            (sprintf "adding qualifiers for %s:\n%s\n"
            (Ident.name_of_tvar key)
            (String.concat_set ~sep:"\n" (Set.Poly.map ~f:Formula.str_of quals)));*)
            quals
          end else quals in
        let terms =
          if Set.Poly.is_empty terms then
            match Map.Poly.find extracted_terms pvar with
            | Some (_, terms) -> terms | None -> Set.Poly.empty
          else terms in
        let params = FT.params_of ~tag in
        let depth, quals, qdeps, terms = FT.gen_quals_terms ~tag (depth, quals, qdeps, terms) in
        Debug.print @@ lazy
          (sprintf "[%s](%s):\n#quals : %d\n#terms : %d\n%s"
             name
             (str_of_sort_env_list (Term.str_of_sort) params)
             (Set.Poly.length quals)
             (Set.Poly.length terms)
             (FT.str_of ()));
        (* Debug.print @@ lazy (VersionSpace.str_of_hspace name (depth, params, quals, qdeps, terms)); *)
        VersionSpace.update_hspace key (depth, params, quals, qdeps, terms) vs);
    VersionSpace.update_truth_table ~id vs

  let out_space_of () =
    let out = Map.Poly.filter template_modules ~f:(fun (module FT) -> Fn.non FT.in_space ()) in
    if Map.Poly.is_empty out then []
    else Map.Poly.keys out

  let is_non_redundant_partial_sol vs key cand =
    Debug.print @@ lazy
      (sprintf "*** check if the cand partial sol of [%s] is non-redundant" @@
       Ident.name_of_tvar key);
    let z3_expr_of smt_instance =
      Z3Smt.Z3interface.of_formula_with_z3fenv
        smt_instance.ctx [] [] smt_instance.z3fenv smt_instance.z3dtenv
    in
    let sol = PCSP.Problem.sol_of_candidate APCSP.problem @@ CandSol.make cand in
    let rand_infos = Map.Poly.find_exn (PCSP.Problem.partial_sol_targets_of APCSP.problem) key in
    let smt_instance = Map.Poly.find_exn partial_sol_checking_smt_instance key in
    Set.Poly.exists rand_infos ~f:(fun rand_info ->
        let term = Map.Poly.find_exn sol rand_info.name in
        let params =
          List.mapi ~f:(fun i (_, s) -> Ident.Tvar (sprintf "x%d" i), s) @@
          fst @@ Logic.ExtTerm.let_lam term
        in
        let uni_senv = Map.Poly.of_alist_exn params in
        let args = List.map params ~f:(fun (v, _) -> Logic.ExtTerm.mk_var v) in
        begin match VersionSpace.lower_bound_of vs key with
          | Some old_term ->
            Z3Smt.Z3interface.z3_solver_add smt_instance.solver @@
            List.return @@ z3_expr_of smt_instance @@ Formula.mk_neg @@
            Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv old_term args
          | _ -> ()
        end;
        Z3.Solver.push smt_instance.solver;
        Z3Smt.Z3interface.z3_solver_add smt_instance.solver @@
        List.return @@ z3_expr_of smt_instance @@
        Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv term args;
        let ret =
          (* check whether [term] is subsumed by [old_term] *)
          match Z3.Solver.check smt_instance.solver [] with
          | Z3.Solver.SATISFIABLE -> true | _ -> false
        in
        Z3.Solver.pop smt_instance.solver 1; ret)

  let get_random_parameter bound pvar sargs vs =
    let random_term_of = function
      | Logic.IntTerm.SInt ->
        Logic.ExtTerm.mk_int @@ Z.of_int @@ Random.int (2 * bound + 1) - bound
      | Logic.RealTerm.SReal ->
        let fb = float_of_int bound in
        Logic.ExtTerm.mk_real @@ Q.of_float @@ Random.float_range (-.fb) fb
      | Logic.BoolTerm.SBool ->
        Logic.BoolTerm.mk_bool @@ Random.bool ()
      | data(*ToDo*) -> Logic.ExtTerm.mk_dummy data
    in
    let table = Hashtbl.Poly.find_exn (VersionSpace.truth_table_of vs) pvar in
    List.mapi sargs ~f:(fun i s ->
        if Array.length table.aarr <= 0 then random_term_of s
        else
          let ri = Random.int @@ Array.length table.aarr in
          match ExAtom.to_old_atom table.aarr.(ri) with
          | Some (_, Atom.App (_, ts, _))
            when Set.Poly.is_empty @@ Term.tvs_of @@ List.nth_exn ts i ->
            Logic.ExtTerm.of_old_term @@ List.nth_exn ts i
          | _ -> random_term_of s)

  let partial_candidates_of diff_sample vs =
    let open PCSP.Params in
    let partial_targets = PCSP.Problem.partial_sol_targets_of APCSP.problem in
    if Map.Poly.is_empty partial_targets then []
    else
      let senv = PCSP.Problem.senv_of APCSP.problem in
      let diff_sample =
        let clause_graph = VersionSpace.example_graph_of vs in
        (* filter out query clauses *)
        Set.Poly.map diff_sample ~f:(fun ex ->
            ex,
            ClauseGraph.Example ex
            |> ClauseGraph.pred_clause_vertexs_of clause_graph.graph
            |> Set.Poly.of_list
            |> Set.Poly.filter_map ~f:(function ClauseGraph.Clause cl -> Some cl | _ -> None))
      in
      let rand_examples (* positive examples used instead of query claues *) =
        Map.Poly.map partial_targets ~f:(Set.concat_map ~f:(fun rand_info ->
            if not @@ Map.Poly.mem senv rand_info.name then Set.Poly.empty
            else
              let sargs = Logic.Sort.args_of @@ Map.Poly.find_exn senv rand_info.name in
              Set.Poly.of_list @@ List.init rand_info.random_ex_size ~f:(fun _ ->
                  let atm =
                    Logic.ExtTerm.to_old_atom senv Map.Poly.empty
                      (Logic.ExtTerm.mk_var_app rand_info.name @@
                       get_random_parameter rand_info.random_ex_bound
                         (Ident.tvar_to_pvar rand_info.name)
                         sargs vs) []
                  in
                  ExClause.mk_unit_pos @@ ExAtom.of_old_atom senv (Formula.mk_true ()) atm)))
      in
      let preds = Map.key_set partial_targets in
      let dep_graph = PCSP.Problem.dep_graph_of APCSP.problem in
      Map.Poly.mapi rand_examples ~f:(fun ~key ~data ->
          Debug.print @@ lazy (sprintf "*** rand examples of [%s]" @@ Ident.name_of_tvar key);
          Debug.print @@ lazy (ExClauseSet.str_of data);
          let diff_ex =
            let is_clause_must_satisfy = Clause.is_clause_must_satisfy preds @@ Map.Poly.find_exn dep_graph key in
            Set.Poly.filter_map diff_sample ~f:(fun (ex, cl) ->
                if Set.Poly.for_all cl ~f:is_clause_must_satisfy then Some ex else None)
          in
          Debug.print @@ lazy (sprintf "used examples of [%s]" @@ Ident.name_of_tvar key);
          Debug.print @@ lazy (ExClauseSet.str_of diff_ex);
          let smt_instance = Map.Poly.find_exn partial_sol_smt_instance key in
          find_candidate ~untrack_sample:data smt_instance diff_ex vs !ref_templates)
      |> Map.Poly.to_alist |> List.filter_map ~f:(function
          | (key, Candidate cand) ->
            if is_non_redundant_partial_sol vs key cand then begin
              Debug.print @@ lazy (sprintf "*** generated a new candidate partial solution for [%s]" @@ Ident.name_of_tvar key);
              Some (cand, key)
            end else None
          | _ -> None)

  let instantiate state =
    let vs = State.version_space_of state in
    old_sample := Set.Poly.diff !old_sample !ref_redundant_exs;
    ref_redundant_exs := Set.Poly.empty;
    let messenger = PCSP.Problem.messenger_of APCSP.problem in
    let rec inner () =
      Messenger.receive_request messenger id;
      if !iters_after_updated = 0 then begin
        update_hspaces vs;
        ref_templates := initialize_templates vs;
        Debug.print @@ lazy "templates generated";
        reset_all_smt_instance ();
        Debug.print @@ lazy "solver initialized";
      end;
      if false then (*ToDo*)
        Hashtbl.Poly.iteri (VersionSpace.truth_table_of vs) ~f:(fun ~key ~data ->
            let alist = Map.Poly.of_alist_exn @@ List.init (TruthTable.length_of_atoms data) ~f:(fun i -> i, 0) in
            let qlist = List.init (TruthTable.length_of_quals data) ~f:Fn.id in
            Debug.print @@ lazy ("\n" ^ TruthTable.str_of (key, data) (qlist, alist)));
      let reduced_quals = reduce_quals vs in
      let eqlen b1 b2 = Set.Poly.length b1 = Set.Poly.length b2 in
      if !iters_after_updated <> 0 &&
         not @@ Hashtbl.Poly.equal eqlen reduced_quals !ref_quals then begin
        Debug.print @@ lazy "#quals has changed";
        ref_quals := reduced_quals;
        ref_key_tvar_update_list_map := Map.Poly.empty;
        iters_after_updated := 0;
        old_sample := Set.Poly.empty;
        inner ()
      end else
        match config.restart_threshold with
        | Some threshold when !iters_after_updated >= threshold ->
          iters_after_updated := 0;
          old_sample := Set.Poly.empty;
          ref_key_tvar_update_list_map := Map.Poly.empty;
          begin match config.auto_incr_shape_interval with
            | Some interval when
                interval > 1 && !incr_times mod interval < interval - 1 -> 
              Map.Poly.iter template_modules ~f:(fun (module FT) -> FT.next ());
              incr incr_times;
              inner ()
            | _ ->
              Map.Poly.iter template_modules ~f:(fun (module FT) -> FT.restart ());
              incr_times := 0;
              inner ()
          end
        | _ ->
          if RLCfg.config.enable && RLCfg.config.ask_smt_timeout then begin
            Out_channel.print_endline ("current timeout: " ^ match default_smt_instance.smt_timeout with None -> "null" | Some n -> string_of_int n);
            Out_channel.flush Out_channel.stdout;
            default_smt_instance.smt_timeout <- int_of_string_opt @@ In_channel.input_line_exn In_channel.stdin
          end;
          let diff_sample = Set.Poly.diff (VersionSpace.examples_of vs) !old_sample in
          match find_candidate default_smt_instance diff_sample vs !ref_templates with
          | Candidate cand ->
            iters_after_updated := !iters_after_updated + 1;
            old_sample := Set.Poly.union_list [!ref_redundant_exs; diff_sample; !old_sample];
            let pcands = partial_candidates_of diff_sample vs in
            Debug.print @@ lazy "*** all candidate partial solutions generated";
            Cands (cand, pcands)
          | UnsatCore pvar_labels_map ->
            ref_key_tvar_update_list_map := Map.Poly.empty;
            iters_after_updated := 0;
            old_sample := Set.Poly.empty;
            TemplateUpdateStrategy.update template_modules state pvar_labels_map;
            (match config.sync_threshold with
             | None -> ()
             | Some thre -> Map.Poly.iter template_modules ~f:(fun (module FT) -> FT.sync thre));
            (match out_space_of () with
             | [] -> inner ()
             | outs -> OutSpace outs)
    in
    inner ()
end
