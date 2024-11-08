open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSatCommon
open Template.Function

type candidate =
  | Cands of Logic.cand_map * (Logic.cand_map * Ident.tvar) list
  | OutSpace of Ident.tvar list

type candidate_or_unsat_core =
  | Candidate of Logic.cand_map
  | UnsatCore of
      ExClauseSet.t * (Ident.tvar, parameter_update_type Set.Poly.t) Map.Poly.t

type smt_solver_instance = {
  mutable ctx : Z3.context;
  mutable solver : Z3.Solver.solver;
  mutable z3dtenv : (Datatype.t * Z3.Sort.sort) Set.Poly.t;
  mutable z3fenv : (Ident.tvar, Z3.FuncDecl.func_decl) Map.Poly.t;
  mutable smt_timeout : int option;
}

module Config = struct
  type pex_strategy = Quantify | InstDefault | InstRand of int
  [@@deriving yojson]

  type predicate_template =
    | DNF of Template.PredicateDNF.Config.t ext_file
    | Flex of Template.PredicateFlex.Config.t ext_file
    | Arrays of Template.PredicateArrays.Config.t ext_file
  [@@deriving yojson]

  type wf_predicate_template =
    | WF of Template.WFPredicate.Config.t ext_file
    | WF_Flex of Template.WFPredicateFlex.Config.t ext_file
  [@@deriving yojson]

  type fn_predicate_template =
    | FN of Template.FNPredicate.Config.t ext_file
    | FN_Flex of Template.FNPredicateFlex.Config.t ext_file
  [@@deriving yojson]

  type int_function_template =
    | IntFun of Template.IntFunction.Config.t ext_file
    | IntFun_Flex of Template.IntFunctionFlex.Config.t ext_file
  [@@deriving yojson]

  type regex_template = RegEx of Template.RegEx.Config.t ext_file
  [@@deriving yojson]

  type t = {
    verbose : bool;
    pex_strategy : pex_strategy;
    predicate_template : predicate_template;
    wf_predicate_template : wf_predicate_template;
    fn_predicate_template : fn_predicate_template;
    ne_predicate_template : Template.NEPredicate.Config.t ext_file;
    adm_predicate_template : Template.AdmPredicate.Config.t ext_file;
    integ_predicate_template : Template.IntegPredicate.Config.t ext_file;
    int_function_template : int_function_template;
    regex_template : regex_template;
    update_strategy : TemplateUpdateStrategy.Config.t;
    qualifier_generator : Qualifier.Generator.Config.t ext_file;
    extract_qualifiers : bool;
    extract_terms : bool;
    extract_constants : bool;
    reduce_quals_terms : bool;
    learn_quals_from_ucores : bool;
    smt_timeout : int option;
    sync_threshold : int option;
    restart_threshold : int option;
  }
  [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    (match cfg.predicate_template with
    | DNF cfg ->
        Template.PredicateDNF.Config.load_ext_file cfg
        >>= fun predicate_template -> Ok (DNF predicate_template)
    | Flex cfg ->
        Template.PredicateFlex.Config.load_ext_file cfg
        >>= fun predicate_template -> Ok (Flex predicate_template)
    | Arrays cfg ->
        Template.PredicateArrays.Config.load_ext_file cfg
        >>= fun predicate_template -> Ok (Arrays predicate_template))
    >>= fun predicate_template ->
    (match cfg.wf_predicate_template with
    | WF cfg ->
        Template.WFPredicate.Config.load_ext_file cfg
        >>= fun wf_predicate_template -> Ok (WF wf_predicate_template)
    | WF_Flex cfg ->
        Template.WFPredicateFlex.Config.load_ext_file cfg
        >>= fun wf_predicate_template -> Ok (WF_Flex wf_predicate_template))
    >>= fun wf_predicate_template ->
    (match cfg.fn_predicate_template with
    | FN cfg ->
        Template.FNPredicate.Config.load_ext_file cfg
        >>= fun fn_predicate_template -> Ok (FN fn_predicate_template)
    | FN_Flex cfg ->
        Template.FNPredicateFlex.Config.load_ext_file cfg
        >>= fun fn_predicate_template -> Ok (FN_Flex fn_predicate_template))
    >>= fun fn_predicate_template ->
    Template.NEPredicate.Config.load_ext_file cfg.ne_predicate_template
    >>= fun ne_predicate_template ->
    Template.AdmPredicate.Config.load_ext_file cfg.adm_predicate_template
    >>= fun adm_predicate_template ->
    Template.IntegPredicate.Config.load_ext_file cfg.integ_predicate_template
    >>= fun integ_predicate_template ->
    (match cfg.int_function_template with
    | IntFun cfg ->
        Template.IntFunction.Config.load_ext_file cfg
        >>= fun int_function_template -> Ok (IntFun int_function_template)
    | IntFun_Flex cfg ->
        Template.IntFunctionFlex.Config.load_ext_file cfg
        >>= fun int_function_template -> Ok (IntFun_Flex int_function_template))
    >>= fun int_function_template ->
    (match cfg.regex_template with
    | RegEx cfg ->
        Template.RegEx.Config.load_ext_file cfg >>= fun regex_template ->
        Ok (RegEx regex_template))
    >>= fun regex_template ->
    TemplateUpdateStrategy.Config.instantiate_ext_files cfg.update_strategy
    >>= fun update_strategy ->
    Qualifier.Generator.Config.load_ext_file cfg.qualifier_generator
    >>= fun qualifier_generator ->
    Ok
      {
        cfg with
        predicate_template;
        wf_predicate_template;
        fn_predicate_template;
        ne_predicate_template;
        adm_predicate_template;
        integ_predicate_template;
        int_function_template;
        regex_template;
        update_strategy;
        qualifier_generator;
      }

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid SolutionTemplate Configuration (%s): %s"
                 filename msg)

  module type ConfigType = sig
    val config : t
  end
end

module type SolutionTemplateType = sig
  (*val initialize : unit -> unit*)
  val synthesize : int -> State.u -> candidate
  val init_incr : unit -> unit
end

module Make
    (RLCfg : RLConfig.ConfigType)
    (Cfg : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : SolutionTemplateType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  module TemplateUpdateStrategy :
    TemplateUpdateStrategy.TemplateUpdateStrategyType =
    TemplateUpdateStrategy.Make
      (RLCfg)
      (struct
        let config = config.update_strategy
      end)
      (APCSP)

  module QualifierGenerator =
    Qualifier.Generator.Make
      (struct
        let config = ExtFile.unwrap_or_abort config.qualifier_generator
      end)
      (APCSP)

  let extracted_qualifiers =
    if not config.extract_qualifiers then Map.Poly.empty
    else
      PCSP.Problem.senv_of APCSP.problem
      |> Map.Poly.fold ~init:Map.Poly.empty
           ~f:(fun ~key:(Ident.Tvar name) ~data:sort acc ->
             let args =
               LogicOld.sort_env_list_of_sorts
               @@ List.map (Logic.Sort.args_of sort)
                    ~f:Logic.ExtTerm.to_old_sort
             in
             let quals =
               Set.Poly.map ~f:snd
               @@ QualifierGenerator.generate (Ident.Pvar name) args
                    Set.Poly.empty
                    (Map.Poly.empty, ClauseGraph.create ())
                    0
             in
             Map.Poly.add_exn acc ~key:(Ident.Pvar name) ~data:(args, quals))

  let extracted_terms =
    if not config.extract_terms then Map.Poly.empty
    else
      Map.Poly.map extracted_qualifiers ~f:(fun (args, phis) ->
          ( args,
            Set.filter ~f:(fun t ->
                Fn.non Term.is_bool_sort (Term.sort_of t)
                && Term.is_compound (*ToDo*) t)
            @@ Set.concat_map phis ~f:Formula.terms_of ))

  let extracted_consts =
    if not config.extract_constants then Set.Poly.empty
    else
      Set.Poly.filter_map ~f:(function
        | T_int.Int i -> Some (T_int.mk_int i)
        | T_real.Real r -> Some (T_real.mk_real r)
        | T_string.StrConst s -> Some (T_string.make s)
        | _ -> None (*ToDo*))
      @@ Formula.funsyms_of
      @@ PCSP.Problem.old_formula_of APCSP.problem

  let template_modules :
      (Ident.tvar, (module Template.Function.Type)) Map.Poly.t =
    Map.Poly.mapi (PCSP.Problem.senv_of APCSP.problem)
      ~f:(fun ~key:tvar ~data ->
        let module M = struct
          let name = tvar

          let sorts =
            List.map ~f:Logic.ExtTerm.to_old_sort @@ Logic.Sort.args_of data

          (*let dtenv = PCSP.Problem.dtenv_of APCSP.problem*)
          let fenv = PCSP.Problem.fenv_of APCSP.problem
          let sol_space = PCSP.Problem.sol_space_of APCSP.problem
          let id = id
          let with_cond = PCSP.Problem.is_adm_pred_with_cond APCSP.problem tvar
        end in
        if PCSP.Problem.is_ord_pred APCSP.problem tvar then
          match config.predicate_template with
          | DNF predicate_template ->
              (module Template.PredicateDNF.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort predicate_template
                        end)
                        (M) : Template.Function.Type)
          | Flex predicate_template ->
              (module Template.PredicateFlex.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort predicate_template
                        end)
                        (M) : Template.Function.Type)
          | Arrays predicate_template ->
              (module Template.PredicateArrays.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort predicate_template
                        end)
                        (M) : Template.Function.Type)
        else if
          PCSP.Problem.is_wf_pred APCSP.problem tvar
          || PCSP.Problem.is_dwf_pred APCSP.problem tvar
        then
          match config.wf_predicate_template with
          | WF wf_predicate_template ->
              (module Template.WFPredicate.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort wf_predicate_template
                        end)
                        (M) : Template.Function.Type)
          | WF_Flex wf_predicate_template ->
              (module Template.WFPredicateFlex.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort wf_predicate_template
                        end)
                        (M) : Template.Function.Type)
        else if PCSP.Problem.is_nwf_pred APCSP.problem tvar then
          let name, parameter_sorts, tag_infos =
            match
              Map.Poly.find (PCSP.Problem.kind_map_of APCSP.problem) tvar
            with
            | Some (Kind.NWF (nwf, _tag)) ->
                ( nwf.name,
                  List.map nwf.param_sorts ~f:Logic.ExtTerm.to_old_sort,
                  Hashtbl.Poly.map nwf.tag_infos
                    ~f:(List.map ~f:Logic.ExtTerm.to_old_sort) )
            | _ -> assert false
          in
          let module M : Template.NWFPredicate.ArgType = struct
            let name = name
            let sorts = parameter_sorts
            let tag_infos = tag_infos

            (*let dtenv = PCSP.Problem.dtenv_of APCSP.problem*)
            let fenv = PCSP.Problem.fenv_of APCSP.problem
            let id = id
          end in
          match config.wf_predicate_template with
          | WF wf_predicate_template ->
              let module Config : Template.WFPredicate.Config.ConfigType =
              struct
                let config = ExtFile.unwrap_or_abort wf_predicate_template
              end in
              Template.NWFPredicate.make ~id ~name (module Config) (module M)
          | WF_Flex _ ->
              failwith @@ sprintf "not supported: %s" (Ident.name_of_tvar tvar)
        else if PCSP.Problem.is_fn_pred APCSP.problem tvar then
          match config.fn_predicate_template with
          | FN fn_predicate_template ->
              (module Template.FNPredicate.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort fn_predicate_template
                        end)
                        (M) : Template.Function.Type)
          | FN_Flex fn_predicate_template ->
              (module Template.FNPredicateFlex.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort fn_predicate_template
                        end)
                        (M) : Template.Function.Type)
        else if PCSP.Problem.is_ne_pred APCSP.problem tvar then
          (module Template.NEPredicate.Make
                    (struct
                      let config =
                        ExtFile.unwrap_or_abort config.ne_predicate_template
                    end)
                    (M) : Template.Function.Type)
        else if PCSP.Problem.is_adm_pred APCSP.problem tvar then
          (module Template.AdmPredicate.Make
                    (struct
                      let config =
                        ExtFile.unwrap_or_abort config.adm_predicate_template
                    end)
                    (M) : Template.Function.Type)
        else if PCSP.Problem.is_integ_pred APCSP.problem tvar then
          (module Template.IntegPredicate.Make
                    (struct
                      let config =
                        ExtFile.unwrap_or_abort config.integ_predicate_template
                    end)
                    (M) : Template.Function.Type)
        else if PCSP.Problem.is_int_fun APCSP.problem tvar then
          match config.int_function_template with
          | IntFun int_function_template ->
              (module Template.IntFunction.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort int_function_template
                        end)
                        (M) : Template.Function.Type)
          | IntFun_Flex int_function_template ->
              (module Template.IntFunctionFlex.Make
                        (struct
                          let config =
                            ExtFile.unwrap_or_abort int_function_template
                        end)
                        (M) : Template.Function.Type)
        else if PCSP.Problem.is_regex APCSP.problem tvar then
          match config.regex_template with
          | RegEx regex_template ->
              (module Template.RegEx.Make
                        (struct
                          let config = ExtFile.unwrap_or_abort regex_template
                        end)
                        (M) : Template.Function.Type)
        else
          failwith
          @@ sprintf "unsupported kind of %s: %s" (Ident.name_of_tvar tvar)
               (Kind.str_of @@ PCSP.Problem.kind_of APCSP.problem tvar))

  type qualifiers_map =
    ( Ident.tvar,
      (Ident.tvar * (Ident.tvar * (int * sort_env_list * Formula.t)) list) list
    )
    Map.Poly.t

  let candidate_of_model (temp_param_senv : Logic.sort_env_map)
      (templates : Logic.cand_map) (qualifiers_map : qualifiers_map)
      (model : Logic.model) =
    let temp_param_sub =
      Map.Poly.mapi temp_param_senv ~f:(fun ~key ~data ->
          (match List.find model ~f:(fun ((x, _), _) -> Stdlib.(x = key)) with
          | None -> ((key, data), None)
          | Some opt -> opt)
          |> Logic.ExtTerm.remove_dontcare_elem
             (* ToDo: support parameteric candidate solution and CEGIS(T)*)
          |> snd)
    in
    Map.Poly.mapi templates ~f:(fun ~key:tvar ~data:(sort, term) ->
        let args_senv = sort_env_list_of_sorts @@ Logic.Sort.args_of sort in
        let hole_qualifiers_map = Map.Poly.find_exn qualifiers_map tvar in
        let hole_sub =
          Map.Poly.of_alist_exn
          @@ List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
                 ( hole,
                   if List.is_empty quals then
                     Logic.Term.mk_lambda args_senv
                     @@ Logic.BoolTerm.mk_bool true
                   else
                     let senv =
                       let _, (_, qsenv, _) = List.hd_exn quals in
                       Logic.of_old_sort_env_list qsenv
                     in
                     Logic.ExtTerm.simplify_formula Map.Poly.empty
                       (Map.Poly.of_alist_exn senv)
                     @@ Logic.ExtTerm.subst temp_param_sub
                     @@ Template.Generator.gen_from_qualifiers (senv, quals) ))
        in
        (*Debug.print @@ lazy ("size before: " ^ string_of_int @@ Logic.ExtTerm.ast_size term);*)
        (* Debug.print @@ lazy (Logic.ExtTerm.str_of term); *)
        let term' = Logic.ExtTerm.subst temp_param_sub term in
        (*Debug.print @@ lazy ("size mid: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');*)
        (* Debug.print @@ lazy (Logic.ExtTerm.str_of term'); *)
        let term' = Logic.ExtTerm.subst hole_sub term' in
        (*Debug.print @@ lazy ("size after: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');*)
        (* Debug.print @@ lazy (Logic.ExtTerm.str_of term'); *)
        assert (Set.is_empty @@ Logic.ExtTerm.fvs_of term');
        (sort, term'))

  let old_eval_qual polarity unknowns (_param_senv, cond, _sorts, args)
      (key, (_, params, phi)) =
    let fvs = Set.Poly.union_list @@ List.map ~f:LogicOld.Term.tvs_of args in
    let fenv = Map.Poly.empty in
    (*TODO: generate fenv*)
    if Set.is_empty @@ Set.inter fvs unknowns then
      let phi =
        let sub =
          Map.Poly.of_alist_exn @@ List.zip_exn (List.map ~f:fst params) args
        in
        Formula.subst sub phi
      in
      match Evaluator.check ~cond (Z3Smt.Z3interface.is_valid ~id fenv) phi with
      | Some true -> Logic.ExtTerm.(geq_of (mk_var key) (zero ()))
      | Some false -> Logic.ExtTerm.(leq_of (mk_var key) (zero ()))
      | None ->
          (*Debug.print @@ lazy (Formula.str_of phi ^ " couldn't be evaluated.  This may cause a violation of the progress property.");*)
          if not polarity then Logic.ExtTerm.mk_bool true
          else Logic.ExtTerm.(eq_of SInt (mk_var key) (zero ()))
    else (*never use*) Logic.ExtTerm.(eq_of SInt (mk_var key) (zero ()))

  let eval_qual tt fenv qdeps polarity unknowns atom (key, (qi, _params, _phi))
      =
    if Set.is_empty @@ Set.inter (ExAtom.tvs_of atom) unknowns then
      (*Debug.print @@ lazy "before";*)
      let atom = ExAtom.normalize_params atom in
      (*Debug.print @@ lazy "mid";*)
      let atom = ExAtom.instantiate atom in
      (*Debug.print @@ lazy "after";*)
      let ai = TruthTable.index_of_atom ~id tt fenv qdeps atom in
      match tt.table.{qi, ai} with
      | 1 -> Logic.ExtTerm.(geq_of (mk_var key) (zero ()))
      | -1 -> Logic.ExtTerm.(leq_of (mk_var key) (zero ()))
      | _ ->
          (*Debug.print @@ lazy (ExAtom.str_of atom ^ " on " ^ Formula.str_of phi ^ " couldn't be evaluated.  This may cause a violation of the progress property.");*)
          if not polarity then Logic.ExtTerm.mk_bool true
          else Logic.ExtTerm.(eq_of SInt (mk_var key) (zero ()))
    else (*never use*) Logic.ExtTerm.(eq_of SInt (mk_var key) (zero ()))

  let cgen_from_fcon template_map qualifiers_map unknowns polarity
      (param_senv, phi) =
    try
      Debug.print @@ lazy "[cgen_from_fcon] generating hole map";
      let hole_map =
        Formula.fvar_apps_of phi |> Set.to_list
        |> List.concat_map ~f:(fun fvar_app ->
               let tvar, sorts, args, _ = Term.let_fvar_app fvar_app in
               let arg_sorts, _ = List.rest_last sorts in
               let hole_qualifiers_map =
                 Map.Poly.find_exn qualifiers_map tvar
               in
               List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
                   ( hole,
                     if List.is_empty quals then
                       let senv =
                         Logic.of_old_sort_env_list
                         @@ sort_env_list_of_sorts arg_sorts
                       in
                       Logic.Term.mk_lambda senv @@ Logic.BoolTerm.mk_bool true
                     else
                       let senv =
                         let _, (_, qsenv, _) = List.hd_exn quals in
                         Logic.of_old_sort_env_list qsenv
                       in
                       Logic.Term.mk_lambda senv @@ Logic.BoolTerm.and_of
                       @@ List.map quals
                            ~f:
                              (old_eval_qual polarity unknowns
                                 ( param_senv,
                                   Formula.mk_true (),
                                   arg_sorts,
                                   args )) )))
        |> Map.Poly.of_alist_exn
      in
      let term = Logic.ExtTerm.of_old_formula phi in
      (*Debug.print @@ lazy ("size before: " ^ string_of_int @@ Logic.ExtTerm.ast_size term);*)
      let term' = Logic.ExtTerm.subst template_map term in
      (*Debug.print @@ lazy ("size mid: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');*)
      let term' = Logic.ExtTerm.subst hole_map term' in
      (*Debug.print @@ lazy ("size after: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');*)
      term'
    with _ ->
      (*ToDo*)
      failwith "multiple occurrences of a function variable not supported"

  let cgen_from_ppapp vs template_map qualifiers_map unknowns polarity atom =
    let pvar, sorts =
      match (ExAtom.pvar_of atom, ExAtom.sorts_of atom) with
      | Some pvar, Some sorts -> (pvar, sorts)
      | _ -> failwith "cgen_from_ppapp"
    in
    let hole_qualifiers_map =
      Map.Poly.find_exn qualifiers_map (Ident.pvar_to_tvar pvar)
    in
    let tt = TruthTable.get_table (VersionSpace.truth_table_of vs) pvar in
    let fenv = VersionSpace.fenv_of vs in
    let qdeps = VersionSpace.qdeps_of pvar vs in
    Debug.print @@ lazy "[cgen_from_ppapp] generating hole map";
    let hole_map =
      Map.Poly.of_alist_exn
      @@ List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
             ( hole,
               if List.is_empty quals then
                 let senv =
                   Logic.of_old_sort_env_list @@ sort_env_list_of_sorts sorts
                 in
                 Logic.Term.mk_lambda senv @@ Logic.BoolTerm.mk_bool true
               else
                 let senv =
                   let _, (_, qsenv, _) = List.hd_exn quals in
                   Logic.of_old_sort_env_list qsenv
                 in
                 Logic.Term.mk_lambda senv @@ Logic.BoolTerm.and_of
                 @@ List.map quals
                      ~f:(eval_qual tt fenv qdeps polarity unknowns atom) ))
      @
      match ExAtom.args_of atom with
      | None -> assert false
      | Some args ->
          List.map ~f:Term.fvar_apps_of args
          |> Set.Poly.union_list |> Set.to_list
          |> List.concat_map ~f:(fun fvar_app ->
                 let tvar, sorts, args, _ = Term.let_fvar_app fvar_app in
                 let arg_sorts, _ = List.rest_last sorts in
                 let hole_qualifiers_map =
                   Map.Poly.find_exn qualifiers_map tvar
                 in
                 List.map hole_qualifiers_map ~f:(fun (hole, quals) ->
                     ( hole,
                       if List.is_empty quals then
                         let senv =
                           Logic.of_old_sort_env_list
                           @@ sort_env_list_of_sorts arg_sorts
                         in
                         Logic.Term.mk_lambda senv
                         @@ Logic.BoolTerm.mk_bool true
                       else
                         let senv =
                           let _, (_, qsenv, _) = List.hd_exn quals in
                           Logic.of_old_sort_env_list qsenv
                         in
                         let param_senv = ExAtom.params_of atom in
                         Logic.Term.mk_lambda senv @@ Logic.BoolTerm.and_of
                         @@ List.map quals
                              ~f:
                                (old_eval_qual polarity unknowns
                                   ( param_senv,
                                     Formula.mk_true (),
                                     arg_sorts,
                                     args )) )))
    in
    let _, term = ExAtom.to_formula polarity atom in
    (*Debug.print @@ lazy ("size before: " ^ string_of_int @@ Logic.ExtTerm.ast_size term);*)
    let term' = Logic.Term.subst template_map term in
    (*Debug.print @@ lazy ("size mid: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');*)
    let term' = Logic.Term.subst hole_map term' in
    (*Debug.print @@ lazy ("size after: " ^ string_of_int @@ Logic.ExtTerm.ast_size term');*)
    term'

  let cgen_from_exatom vs template_map qualifiers_map unknowns polarity =
    function
    | ExAtom.FCon (param_senv, phi) ->
        (if polarity then Fn.id else Logic.BoolTerm.neg_of)
        @@ cgen_from_fcon template_map qualifiers_map unknowns polarity
             (param_senv, phi)
    | (ExAtom.PApp ((_, _), _) | ExAtom.PPApp ((_, _), ((_, _), _))) as atom ->
        cgen_from_ppapp vs template_map qualifiers_map unknowns polarity atom

  let _ = Random.init 0

  let cgen_from_pex vs template_map qualifiers_map unknowns clause =
    let phi =
      let f = cgen_from_exatom vs template_map qualifiers_map unknowns in
      Logic.BoolTerm.or_of @@ Set.to_list
      @@ Set.union
           (Set.Poly.map clause.ExClause.positive ~f:(f true))
           (Set.Poly.map clause.ExClause.negative ~f:(f false))
    in
    let param_senv = Logic.of_old_sort_env_map @@ ExClause.params_of clause in
    match config.pex_strategy with
    | Quantify -> Logic.BoolTerm.forall (Map.Poly.to_alist param_senv) phi
    | InstRand num ->
        assert (num > 0);
        if Map.Poly.is_empty param_senv then phi
        else
          let open Logic in
          BoolTerm.forall (Map.Poly.to_alist param_senv)
          @@ BoolTerm.and_of
          @@ List.init num ~f:(fun k ->
                 let sub =
                   Map.Poly.mapi param_senv ~f:(fun ~key:_ ~data ->
                       if k = 0 then ExtTerm.mk_dummy data
                       else
                         match data with
                         | IntTerm.SInt ->
                             ExtTerm.mk_int (Z.of_int @@ Integer.rand_int ())
                         | BoolTerm.SBool -> BoolTerm.mk_bool @@ Random.bool ()
                         | _ (*ToDo*) -> ExtTerm.mk_dummy data)
                 in
                 Term.subst sub phi)
    | InstDefault ->
        let sub =
          Map.Poly.mapi param_senv ~f:(fun ~key ~data ->
              match data with
              | Logic.DatatypeTerm.SUS _ -> Logic.Term.mk_var key
              | _ -> Logic.ExtTerm.mk_dummy data)
        in
        Logic.BoolTerm.forall (Map.Poly.to_alist param_senv)
        @@ if Map.Poly.is_empty sub then phi else Logic.Term.subst sub phi

  (* for SMT Solver *)

  let create_smt_instance () =
    let ctx =
      Z3.mk_context [ ("model", "true"); ("unsat_core", "true") ]
      (*dummy*)
    in
    let solver = Z3.Solver.mk_solver ctx None (*dummy*) in
    let z3dtenv =
      Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx
      @@ PCSP.Problem.dtenv_of APCSP.problem
    in
    let z3fenv =
      Z3Smt.Z3interface.z3_fenv_of ~id ctx [] [] (LogicOld.get_fenv ()) z3dtenv
    in
    let smt_timeout = config.smt_timeout in
    { ctx; solver; z3dtenv; z3fenv; smt_timeout }

  let default_smt_instance = create_smt_instance ()
  let ucore_smt_instance = create_smt_instance ()

  let partial_sol_smt_instance =
    Map.Poly.map ~f:(fun _ -> create_smt_instance ())
    @@ PCSP.Problem.partial_sol_targets_of APCSP.problem

  let partial_sol_checking_smt_instance =
    Map.Poly.map ~f:(fun _ -> create_smt_instance ())
    @@ PCSP.Problem.partial_sol_targets_of APCSP.problem

  let reset_smt_instance instance =
    (*Z3.Solver.reset instance.solver;*)
    let instance' = create_smt_instance () in
    instance.ctx <- instance'.ctx;
    instance.solver <- instance'.solver;
    instance.z3dtenv <- instance'.z3dtenv;
    instance.z3fenv <- instance'.z3fenv;
    instance.smt_timeout <- instance'.smt_timeout

  let reset_all_smt_instances () =
    reset_smt_instance default_smt_instance;
    reset_smt_instance ucore_smt_instance;
    Map.Poly.iter partial_sol_smt_instance ~f:reset_smt_instance

  (* for restart and templates/quals/terms update *)
  let iters_after_updated = ref 0

  (* for unsat-core-based template update *)
  let ref_key_tvar_update_list_map = ref Map.Poly.empty

  (* for unsat-core-based qualifier learning *)
  let ref_key_clause_map = ref Map.Poly.empty

  (* for incremental solving *)
  let prev_sample = ref Set.Poly.empty

  let ref_templates =
    ref (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)

  let ref_templates_ucore =
    ref (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)

  let init_incr () =
    Debug.print @@ lazy "PCSat initialized";
    iters_after_updated := 0;
    ref_key_tvar_update_list_map := Map.Poly.empty;
    ref_key_clause_map := Map.Poly.empty;
    prev_sample := Set.Poly.empty
  (*let initialize () =
    (* for SMT Solver *)
    reset_all_smt_instances ();
    init_incr ();
    (* for incremental solving *)
    ref_templates := Map.Poly.empty, Map.Poly.empty, Map.Poly.empty, Map.Poly.empty;
    ref_templates_ucore := Map.Poly.empty, Map.Poly.empty, Map.Poly.empty, Map.Poly.empty*)

  (* let sel_env = ref Map.Poly.empty *)

  type lc = { label : string; constr : string } [@@deriving to_yojson]
  type ucores = string list [@@deriving to_yojson]

  let get_key =
    let key_cnt = ref 0 in
    fun () ->
      incr key_cnt;
      sprintf "#S%d_%d" (match id with Some id -> id | None -> 0) !key_cnt

  type constr = parameter_update_type * Logic.term

  let find_candidate ?(temporary_sample = Set.Poly.empty)
      (smt_solver_instance : smt_solver_instance) sample (vs : VersionSpace.t)
      ( (temp_param_senv : Logic.sort_env_map),
        (templates : (Ident.tvar, Logic.Sort.t * constr) Map.Poly.t),
        (temp_param_cnstrs : (Ident.tvar, constr Set.Poly.t) Map.Poly.t),
        (qualifiers_map : qualifiers_map) ) =
    (* let uenv = VersionSpace.uenf_of vs in *)
    let tvar_update_map = Map.Poly.map templates ~f:(snd >> fst) in
    let templates =
      Map.Poly.map templates ~f:(fun (sort, (_, term)) -> (sort, term))
    in
    let template_map = Map.Poly.map templates ~f:snd in
    let temporary_constrs =
      Set.Poly.map temporary_sample ~f:(fun clause ->
          Debug.print
          @@ lazy
               (sprintf "gen temporary_constrs of temporary example: %s"
               @@ ExClause.str_of clause);
          let unknowns =
            Set.filter (ExClause.tvs_of clause) ~f:(Map.Poly.mem templates)
          in
          let constr =
            ( temp_param_senv,
              cgen_from_pex vs template_map qualifiers_map unknowns clause )
            |> Logic.ExtTerm.to_old_fml Map.Poly.empty
            |> Evaluator.simplify
          in
          Debug.print
          @@ lazy (sprintf "temporary constr: %s" @@ Formula.str_of constr);
          constr)
    in
    let key_constr_map, key_tvar_update_list_map, key_clause_map =
      Set.fold
        ~init:
          (Map.Poly.empty, !ref_key_tvar_update_list_map, !ref_key_clause_map)
        sample
        ~f:(fun
            (key_constr_map, key_tvar_update_list_map, key_clause_map) clause ->
          Debug.print
          @@ lazy (sprintf "gen constr of example: %s" @@ ExClause.str_of clause);
          let unknowns =
            Set.filter (ExClause.tvs_of clause) ~f:(Map.Poly.mem templates)
          in
          let update_map =
            Set.union
              (Set.Poly.map (ExClause.pvs_of clause) ~f:Ident.name_of_pvar)
              (Set.Poly.map unknowns ~f:Ident.name_of_tvar)
            |> Set.Poly.map ~f:(fun name ->
                   ( Ident.Tvar name,
                     Map.Poly.find_exn tvar_update_map @@ Ident.Tvar name ))
            |> Set.to_list
          in
          let key = get_key () in
          let constr =
            let constr =
              ( temp_param_senv,
                cgen_from_pex vs template_map qualifiers_map unknowns clause )
              |> Logic.ExtTerm.to_old_fml Map.Poly.empty
              |> Evaluator.simplify
            in
            if
              Set.exists
                (Formula.term_sort_env_of constr)
                ~f:(snd >> Term.is_string_sort)
              || Set.exists (Formula.funsyms_of constr) ~f:(function
                   | T_string.StrConst _ -> true
                   | _ -> false)
            then
              (* ite expressions are eliminated if the theory of strings is involved *)
              constr |> Formula.elim_ite |> Evaluator.simplify
            else constr
          in
          if RLCfg.config.enable && RLCfg.config.show_unsat_core then (
            RLConfig.lock ();
            Debug.print_stdout
            @@ lazy
                 (sprintf "labeled constraint: %s"
                 @@ Yojson.Safe.to_string
                 @@ lc_to_yojson { label = key; constr = Formula.str_of constr }
                 );
            RLConfig.unlock ());
          Debug.print
          @@ lazy (sprintf "constr: [%s] %s" key (Formula.str_of constr));
          ( Map.Poly.add_exn key_constr_map ~key ~data:constr,
            Map.Poly.add_exn key_tvar_update_list_map ~key ~data:update_map,
            Map.Poly.add_exn key_clause_map ~key ~data:clause ))
    in
    let key_constr_map, key_tvar_update_list_map =
      (*if !iters_after_updated = 0 then*)
      let used_param_senv =
        Set.of_map key_constr_map
        |> Set.concat_map ~f:(snd >> Formula.tvs_of)
        |> Set.concat_map ~f:(fun (Ident.Tvar x) ->
               Set.Poly.of_list
               @@ [
                    Ident.Tvar x;
                    Ident.Tvar (x ^ "#pos" (*ToDo*));
                    Ident.Tvar (x ^ "#neg" (*ToDo*));
                  ])
      in
      Map.Poly.fold temp_param_cnstrs
        ~init:(key_constr_map, key_tvar_update_list_map)
        ~f:(fun ~key:tvar ~data (key_constr_map, key_tvar_update_list_map) ->
          Set.fold data ~init:(key_constr_map, key_tvar_update_list_map)
            ~f:(fun
                (key_constr_map, key_tvar_update_list_map)
                (update_label, cnstr)
              ->
              let key = get_key () in
              let param_constr =
                Evaluator.simplify
                @@ (if PCSP.Problem.is_ne_pred (*ToDo*) APCSP.problem tvar then
                      Fn.id
                    else
                      Formula.subst
                      @@ Map.Poly.filter_mapi temp_param_senv
                           ~f:(fun ~key ~data ->
                             assert (Ident.is_parameter key);
                             if Set.mem used_param_senv key then None
                             else Some (Logic.mk_old_dummy data)))
                @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                     (temp_param_senv, cnstr)
              in
              if RLCfg.config.enable && RLCfg.config.show_unsat_core then (
                RLConfig.lock ();
                Debug.print_stdout
                @@ lazy
                     (sprintf "labeled bounds constraint: %s"
                     @@ Yojson.Safe.to_string
                     @@ lc_to_yojson
                          { label = key; constr = Formula.str_of param_constr }
                     );
                RLConfig.unlock ());
              if Formula.is_true param_constr then
                (key_constr_map, key_tvar_update_list_map)
              else (
                Debug.print
                @@ lazy
                     (sprintf "bounds constr: [%s] %s" key
                        (Formula.str_of param_constr));
                ( Map.Poly.add_exn key_constr_map ~key ~data:param_constr,
                  Map.Poly.add_exn key_tvar_update_list_map ~key
                    ~data:[ (tvar, update_label) ] ))))
      (*else key_constr_map, key_tvar_update_list_map*)
    in
    (*let key_constr_map =
      let phi = UTermEnv.to_formula uenv in
      if Formula.is_true phi then key_constr_map
      else if Map.Poly.exists key_constr_map ~f:(fun phi1 -> Stdlib.(Formula.str_of phi1 = Formula.str_of phi) then key_constr_map
      else begin
        let key = get_key () in
        Debug.print @@ lazy (sprintf "uterm_constr %s: %s" key (Formula.str_of phi));
        Map.Poly.add_exn key_constr_map ~key:(key) ~data:(phi)
      end
      in*)
    ref_key_tvar_update_list_map := key_tvar_update_list_map;
    ref_key_clause_map := key_clause_map;
    Debug.print @@ lazy "constraints generated";
    match
      Z3Smt.Z3interface.incr_check_sat_unsat_core ~id
        ~timeout:smt_solver_instance.smt_timeout ~non_tracked:temporary_constrs
        smt_solver_instance.solver smt_solver_instance.ctx
        smt_solver_instance.z3fenv smt_solver_instance.z3dtenv key_constr_map
    with
    | `Sat model ->
        Debug.print @@ lazy "sat";
        let model =
          List.map model ~f:(fun ((x, s), t_opt) ->
              ( (x, Logic.ExtTerm.of_old_sort s),
                Option.(t_opt >>= (Logic.ExtTerm.of_old_term >> return)) ))
        in
        Candidate
          (candidate_of_model temp_param_senv templates qualifiers_map model)
    | `Unsat unsat_keys ->
        Debug.print
        @@ lazy ("unsat, reason:" ^ String.concat ~sep:"," unsat_keys);
        let unsat_keys =
          List.map unsat_keys ~f:(fun s ->
              String.sub s ~pos:1 ~len:(String.length s - 2))
        in
        let ucores =
          Set.Poly.of_list
          @@ List.filter_map unsat_keys ~f:(fun key ->
                 Map.Poly.find key_clause_map key)
        in
        Debug.print
        @@ lazy (sprintf "*** unsat cores:\n%s" (ExClauseSet.str_of ucores));
        if RLCfg.config.enable && RLCfg.config.show_unsat_core then (
          RLConfig.lock ();
          Debug.print_stdout
          @@ lazy
               (sprintf "unsat cores: %s" @@ Yojson.Safe.to_string
               @@ ucores_to_yojson unsat_keys);
          RLConfig.unlock ());
        let pvar_labels_map =
          List.fold unsat_keys ~init:Map.Poly.empty ~f:(fun map key ->
              match Map.Poly.find key_tvar_update_list_map key with
              | Some pvar_update_list ->
                  List.fold pvar_update_list ~init:map
                    ~f:(fun map (pvar, label) ->
                      Map.Poly.update map pvar ~f:(function
                        | Some labels -> Set.add labels label
                        | None -> Set.Poly.singleton label))
              | None -> map)
        in
        UnsatCore (ucores, pvar_labels_map)
    (*| `Unknown _reason -> (*failwith reason*)(*UnsatCore Map.Poly.empty*) (*ToDo*)*)
    | `Unknown reason ->
        Debug.print @@ lazy ("unknown:" ^ reason);
        UnsatCore
          ( Set.Poly.empty,
            Map.Poly.map tvar_update_map ~f:(fun _ ->
                Set.Poly.singleton TimeOut) )
    | `Timeout ->
        Debug.print @@ lazy "timeout";
        UnsatCore
          ( Set.Poly.empty,
            Map.Poly.map tvar_update_map ~f:(fun _ ->
                Set.Poly.singleton TimeOut) )

  let initialize_templates ~ucore vs =
    let init =
      (Map.Poly.empty, Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)
    in
    Map.Poly.fold (PCSP.Problem.senv_of APCSP.problem) ~init
      ~f:(fun
          ~key:tvar
          ~data:sort
          (temp_param_senv, template_map, temp_param_cnstrs, quals_map)
        ->
        let (module FT) = Map.Poly.find_exn template_modules tvar in
        let pvar = Ident.tvar_to_pvar tvar in
        let tt = TruthTable.get_table (VersionSpace.truth_table_of vs) pvar in
        let template, temp_param_cnstrs', temp_param_senv', hole_qualifiers_map
            =
          FT.gen_template ~tag:(PCSP.Problem.tag_of APCSP.problem tvar) ~ucore
          @@ VersionSpace.hspace_of_pvar pvar vs
        in
        let hole_qualifiers_map =
          List.map hole_qualifiers_map ~f:(fun (tvar, quals) ->
              ( tvar,
                List.map quals ~f:(fun (tvar, (env, phi)) ->
                    ( tvar,
                      ( TruthTable.index_of_qual ~id tt (VersionSpace.fenv_of vs)
                          (VersionSpace.qdeps_of pvar vs)
                          phi,
                        env,
                        phi ) )) ))
        in
        ( Map.force_merge temp_param_senv temp_param_senv',
          Map.Poly.add_exn template_map ~key:tvar ~data:(sort, template),
          List.fold temp_param_cnstrs' ~init:temp_param_cnstrs
            ~f:(fun acc elem ->
              match Map.Poly.find acc tvar with
              | None ->
                  Map.Poly.add_exn acc ~key:tvar ~data:(Set.Poly.singleton elem)
              | Some data ->
                  Map.Poly.set acc ~key:tvar ~data:(Set.add data elem)),
          Map.Poly.add_exn quals_map ~key:tvar ~data:hole_qualifiers_map ))

  (** init quals for nwf predicate tempalte *)
  let _ =
    Map.Poly.iteri template_modules ~f:(fun ~key ~data:(module FT) ->
        match Map.Poly.find extracted_qualifiers @@ Ident.tvar_to_pvar key with
        | Some (_, quals) ->
            FT.init_quals (PCSP.Problem.tag_of APCSP.problem key) quals
        | _ -> ())

  let reduce_quals_terms vs =
    if config.reduce_quals_terms then (
      let reduced_quals_map =
        Hashtbl.Poly.map (VersionSpace.truth_table_of vs) ~f:(fun tt ->
            let qlist = List.init (TruthTable.length_of_quals tt) ~f:Fn.id in
            let alist =
              Map.Poly.of_alist_exn
              @@ List.init (TruthTable.length_of_atoms tt) ~f:(fun i ->
                     (i, 0 (* dummy *)))
            in
            Set.Poly.of_list
            @@ List.map ~f:(IncrArray.get tt.qarr)
            @@ TruthTable.reduced_qlist_of tt (qlist, alist))
      in
      let reduced_terms_map = VersionSpace.terms_map_of (*ToDo*) vs in
      let changed = ref false in
      Map.Poly.iteri template_modules ~f:(fun ~key ~data:(module FT) ->
          let pvar = Ident.tvar_to_pvar key in
          let reduced_quals = Hashtbl.Poly.find_exn reduced_quals_map pvar in
          let reduced_terms = Hashtbl.Poly.find_exn reduced_terms_map pvar in
          let hspace = VersionSpace.hspace_of_pvar pvar vs in
          changed :=
            !changed
            || (not (Set.eqlen reduced_quals hspace.quals))
            || not (Set.eqlen reduced_terms hspace.terms);
          let hspace =
            { hspace with quals = reduced_quals; terms = reduced_terms }
          in
          VersionSpace.update_hspace key hspace vs);
      !changed)
    else false

  let quals_terms_map =
    Map.Poly.mapi template_modules ~f:(fun ~key ~data:(module FT) ->
        let tag = PCSP.Problem.tag_of APCSP.problem key in
        let pvar = Ident.tvar_to_pvar key in
        let quals =
          match Map.Poly.find extracted_qualifiers pvar with
          | Some (_, quals) -> FT.adjust_quals ~tag quals
          | None -> Set.Poly.empty
        in
        if true then
          Debug.print
          @@ lazy
               (sprintf "adding qualifiers for %s:\n%s\n"
                  (Ident.name_of_tvar key)
                  (String.concat_set ~sep:"\n"
                     (Set.Poly.map ~f:Formula.str_of quals)));
        let terms =
          match Map.Poly.find extracted_terms pvar with
          | Some (_, terms) -> terms
          | None -> Set.Poly.empty
        in
        (ref quals, ref terms))

  let update_hspaces vs =
    Map.Poly.iteri template_modules ~f:(fun ~key ~data:(module FT) ->
        let tag = PCSP.Problem.tag_of APCSP.problem key in
        let name = Ident.name_of_tvar key in
        Debug.print @@ lazy ("** updating the hypothesis space of " ^ name);
        let pvar = Ident.Pvar name in
        let ref_quals, ref_terms = Map.Poly.find_exn quals_terms_map key in
        let hspace =
          FT.update_hspace ~tag
          @@ {
               (VersionSpace.hspace_of_pvar pvar vs) with
               params = FT.params_of ~tag;
               quals = !ref_quals;
               terms = !ref_terms;
               consts = extracted_consts;
             }
        in
        Debug.print
        @@ lazy
             (sprintf "[%s](%s):\n#quals: %d\n#terms: %d\n#consts: %d\n%s" name
                (str_of_sort_env_list Term.str_of_sort hspace.params)
                (Set.length hspace.quals) (Set.length hspace.terms)
                (Set.length hspace.consts) (FT.str_of ()));
        (* Debug.print @@ lazy (VersionSpace.str_of_hspace name hspace); *)
        VersionSpace.update_hspace key hspace vs);
    VersionSpace.update_truth_table ~id vs

  let out_space_of () =
    Map.Poly.keys
    @@ Map.Poly.filter template_modules ~f:(fun (module FT) ->
           Fn.non FT.in_space ())

  let is_non_redundant_partial_sol vs key cand =
    Debug.print
    @@ lazy
         (sprintf "*** check if the cand partial sol of [%s] is non-redundant"
         @@ Ident.name_of_tvar key);
    let z3_expr_of smt_instance =
      Z3Smt.Z3interface.of_formula_with_z3fenv smt_instance.ctx [] []
        smt_instance.z3fenv smt_instance.z3dtenv
    in
    let sol =
      PCSP.Problem.sol_of_candidate APCSP.problem @@ CandSol.make cand
    in
    let smt_instance =
      Map.Poly.find_exn partial_sol_checking_smt_instance key
    in
    Map.Poly.find_exn (PCSP.Problem.partial_sol_targets_of APCSP.problem) key
    |> Set.exists ~f:(fun rand_info ->
           let term = Map.Poly.find_exn sol rand_info.PCSP.Params.name in
           let params =
             List.mapi ~f:(fun i (_, s) -> (Ident.Tvar (sprintf "x%d" i), s))
             @@ fst @@ Logic.ExtTerm.let_lam term
           in
           let uni_senv = Map.Poly.of_alist_exn params in
           let args = List.map params ~f:(fst >> Logic.ExtTerm.mk_var) in
           (match VersionSpace.lower_bound_of vs key with
           | None -> ()
           | Some old_term ->
               Z3Smt.Z3interface.z3_solver_add smt_instance.solver
               @@ List.return
               @@ z3_expr_of ~id smt_instance
               @@ Formula.mk_neg
               @@ Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv old_term
                    args);
           Z3.Solver.push smt_instance.solver;
           Z3Smt.Z3interface.z3_solver_add smt_instance.solver
           @@ List.return
           @@ z3_expr_of ~id smt_instance
           @@ Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv term args;
           let ret =
             (* check whether [term] is subsumed by [old_term] *)
             match Z3.Solver.check smt_instance.solver [] with
             | Z3.Solver.SATISFIABLE -> true
             | _ -> false
           in
           Z3.Solver.pop smt_instance.solver 1;
           ret)

  let partial_candidates_of diff_sample vs =
    let open PCSP.Params in
    let target_pvars =
      Map.key_set @@ PCSP.Problem.partial_sol_targets_of APCSP.problem
    in
    if Set.is_empty target_pvars then []
    else (
      Debug.print @@ lazy "generating partial candidates";
      let diff_sample =
        (* filter out query clauses *)
        Set.Poly.map diff_sample ~f:(fun ex ->
            ( ex,
              ClauseGraph.Example ex
              |> ClauseGraph.pred_clause_vertexs_of
                   (VersionSpace.example_graph_of vs).graph
              |> Set.Poly.filter_map ~f:(function
                   | ClauseGraph.Clause c -> Some c
                   | _ -> None) ))
      in
      let rand_examples (* positive examples used instead of query claues *) =
        let get_random_parameter bound pvar sargs vs =
          let table =
            Hashtbl.Poly.find_exn (VersionSpace.truth_table_of vs) pvar
          in
          List.mapi sargs ~f:(fun i s ->
              if Array.length table.aarr <= 0 then
                Logic.ExtTerm.random_term_of bound s
              else
                let ri = Random.int @@ Array.length table.aarr in
                match ExAtom.to_old_atom table.aarr.(ri) with
                | Some (_, Atom.App (_, ts, _))
                  when Set.is_empty @@ Term.tvs_of @@ List.nth_exn ts i ->
                    Logic.ExtTerm.of_old_term @@ List.nth_exn ts i
                | _ -> Logic.ExtTerm.random_term_of bound s)
        in
        Map.Poly.map
          (PCSP.Problem.partial_sol_targets_of APCSP.problem)
          ~f:
            (Set.concat_map ~f:(fun rand_info ->
                 let exi_senv = PCSP.Problem.senv_of APCSP.problem in
                 match Map.Poly.find exi_senv rand_info.name with
                 | None -> Set.Poly.empty
                 | Some sort ->
                     let sargs = Logic.Sort.args_of sort in
                     Set.Poly.of_list
                     @@ List.init rand_info.random_ex_size ~f:(fun _ ->
                            Logic.ExtTerm.mk_var_app rand_info.name
                            @@ get_random_parameter rand_info.random_ex_bound
                                 (Ident.tvar_to_pvar rand_info.name)
                                 sargs vs
                            |> Fn.flip
                                 (Logic.ExtTerm.to_old_atom exi_senv
                                    Map.Poly.empty)
                                 []
                            |> ExAtom.of_old_atom exi_senv (Formula.mk_true ())
                            |> ExClause.mk_unit_pos)))
      in
      let res =
        Map.Poly.data
        @@ Map.Poly.filter_mapi rand_examples ~f:(fun ~key ~data ->
               Debug.print
               @@ lazy
                    (sprintf "*** rand examples of [%s]\n%s"
                       (Ident.name_of_tvar key) (ExClauseSet.str_of data));
               let diff_ex =
                 let f =
                   Clause.must_be_satisfied ~print:Debug.print target_pvars
                   @@ Map.Poly.find_exn
                        (PCSP.Problem.dep_graph_of APCSP.problem)
                        key
                 in
                 Set.Poly.filter_map diff_sample ~f:(fun (ex, cl) ->
                     if Set.for_all cl ~f then Some ex else None)
               in
               Debug.print
               @@ lazy
                    (sprintf "used examples of [%s]" @@ Ident.name_of_tvar key);
               Debug.print @@ lazy (ExClauseSet.str_of diff_ex);
               match
                 find_candidate ~temporary_sample:data
                   (Map.Poly.find_exn partial_sol_smt_instance key)
                   diff_ex vs !ref_templates
               with
               | Candidate cand ->
                   if is_non_redundant_partial_sol vs key cand then (
                     Debug.print
                     @@ lazy
                          (sprintf
                             "*** generated a new candidate partial solution \
                              for [%s]"
                          @@ Ident.name_of_tvar key);
                     Some (cand, key))
                   else None
               | UnsatCore _ -> None)
      in
      Debug.print @@ lazy "*** all candidate partial solutions generated";
      res)

  let print_truth_table = false

  let synthesize num_iters state =
    let vs = State.version_space_of state in
    let rec inner () =
      Common.Messenger.receive_request
        (PCSP.Problem.messenger_of APCSP.problem)
        id;
      if !iters_after_updated = 0 then (
        update_hspaces vs;
        ignore @@ reduce_quals_terms vs;
        ref_templates := initialize_templates ~ucore:false vs;
        ref_templates_ucore := initialize_templates ~ucore:true vs;
        Debug.print @@ lazy "templates generated";
        reset_all_smt_instances ();
        Debug.print @@ lazy "solver initialized");
      let quals_terms_changed =
        !iters_after_updated <> 0 && reduce_quals_terms vs
      in
      if print_truth_table then
        Hashtbl.Poly.iteri (VersionSpace.truth_table_of vs)
          ~f:(fun ~key ~data ->
            let alist =
              Map.Poly.of_alist_exn
              @@ List.init (TruthTable.length_of_atoms data) ~f:(fun i ->
                     (i, 0))
            in
            let qlist = List.init (TruthTable.length_of_quals data) ~f:Fn.id in
            Debug.print
            @@ lazy ("\n" ^ TruthTable.str_of (key, data) (qlist, alist)));
      if quals_terms_changed then (
        Debug.print @@ lazy "#quals has changed by the qualifier reduction";
        init_incr ();
        inner ())
      else
        match config.restart_threshold with
        | Some threshold when !iters_after_updated >= threshold -> (
            init_incr ();
            TemplateUpdateStrategy.update template_modules num_iters state None;
            match out_space_of () with [] -> inner () | outs -> OutSpace outs)
        | _ -> (
            if RLCfg.config.enable && RLCfg.config.ask_smt_timeout then (
              RLConfig.lock ();
              Debug.print_stdout
              @@ lazy
                   (sprintf "current timeout: %s"
                   @@
                   match default_smt_instance.smt_timeout with
                   | None -> "null"
                   | Some n -> string_of_int n);
              Out_channel.flush Out_channel.stdout;
              default_smt_instance.smt_timeout <-
                int_of_string_opt @@ In_channel.input_line_exn In_channel.stdin;
              RLConfig.unlock ());
            let diff_sample =
              Set.diff (VersionSpace.examples_of vs) !prev_sample
            in
            match
              find_candidate default_smt_instance diff_sample vs !ref_templates
            with
            | Candidate cand ->
                iters_after_updated := !iters_after_updated + 1;
                prev_sample := Set.Poly.union_list [ diff_sample; !prev_sample ];
                let part_cands = partial_candidates_of diff_sample vs in
                Cands (cand, part_cands)
            | UnsatCore (ucores, pvar_labels_map) ->
                init_incr ();
                let quals_changed, pvar_labels_map =
                  if config.learn_quals_from_ucores then (
                    reset_smt_instance ucore_smt_instance;
                    match
                      find_candidate ucore_smt_instance ucores vs
                        !ref_templates_ucore
                    with
                    | Candidate cand ->
                        Map.Poly.iteri template_modules
                          ~f:(fun ~key ~data:(module FT) ->
                            let ref_quals, _ref_terms =
                              Map.Poly.find_exn quals_terms_map key
                            in
                            let tag = PCSP.Problem.tag_of APCSP.problem key in
                            match Map.Poly.find cand key with
                            | None -> ()
                            | Some (_s, t) ->
                                let new_quals =
                                  try
                                    let phi =
                                      let params = FT.params_of ~tag in
                                      let uni_senv =
                                        Logic.of_old_sort_env_map
                                        @@ Map.Poly.of_alist_exn params
                                      in
                                      Logic.ExtTerm.to_old_formula
                                        Map.Poly.empty uni_senv
                                        t (*ToDo: t may have non-boolean type*)
                                      @@ List.map params
                                           ~f:(fst >> Logic.ExtTerm.mk_var)
                                    in
                                    let pos, neg = Formula.atoms_of phi in
                                    let pos =
                                      Set.Poly.map ~f:Formula.mk_atom pos
                                    in
                                    let neg =
                                      Set.Poly.map ~f:Formula.mk_atom neg
                                    in
                                    let tag =
                                      PCSP.Problem.tag_of APCSP.problem key
                                    in
                                    Set.union pos neg
                                    |> Set.Poly.map ~f:(fun q ->
                                           (FT.params_of ~tag, q))
                                    |> QualifierGenerator.elim_neg
                                    |> Set.Poly.map ~f:snd
                                  with _ -> Set.Poly.empty
                                in
                                if true then
                                  Debug.print
                                  @@ lazy
                                       (sprintf
                                          "adding qualifiers for %s:\n%s\n"
                                          (Ident.name_of_tvar key)
                                          (String.concat_set ~sep:"\n"
                                             (Set.Poly.map ~f:Formula.str_of
                                                new_quals)));
                                (*print_endline @@ Formula.str_of phi;*)
                                ref_quals := Set.union !ref_quals new_quals);
                        (true, Map.Poly.empty)
                    | UnsatCore (_, pvar_labels_map') ->
                        (* ToDo: pvar_labels_map is ignored *)
                        (false, pvar_labels_map'))
                  else (false, pvar_labels_map)
                in
                if quals_changed then inner ()
                else (
                  TemplateUpdateStrategy.update template_modules num_iters state
                    (Some pvar_labels_map);
                  Debug.print @@ lazy "*** all templates updated";
                  (match config.sync_threshold with
                  | None -> ()
                  | Some thre ->
                      Map.Poly.iter template_modules ~f:(fun (module FT) ->
                          FT.sync thre));
                  match out_space_of () with
                  | [] -> inner ()
                  | outs -> OutSpace outs))
    in
    inner ()
end
