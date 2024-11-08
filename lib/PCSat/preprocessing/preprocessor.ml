open Core
open Common
open Common.Util
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSatCommon

module Config = struct
  type t = {
    enable : bool;
    verbose : bool;
    resolution_threshold : int;
    simplification_with_smt : bool;
    num_elim_bool_vars : int;
    propagate_lb_ub : bool;
    reduce_pvar_args : bool;
  }
  [@@deriving yojson]

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
            @@ sprintf "Invalid Preprocessor Configuration (%s): %s" filename
                 msg)

  let make enable verbose resolution_threshold num_elim_bool_vars
      reduce_pvar_args =
    {
      enable;
      verbose;
      resolution_threshold;
      simplification_with_smt = false;
      num_elim_bool_vars;
      propagate_lb_ub = false;
      reduce_pvar_args;
    }
end

module type PreprocessorType = sig
  val solve :
    ?bpvs:Ident.tvar Set.Poly.t ->
    ?oracle:PCSP.Problem.oracle ->
    (?oracle:PCSP.Problem.oracle -> PCSP.Problem.t -> State.output Or_error.t) ->
    PCSP.Problem.t ->
    State.output Or_error.t

  val preprocess :
    ?bpvs:Ident.tvar Set.Poly.t ->
    ?oracle:CandSolOld.t option ->
    ?normalize_params:bool ->
    PCSP.Problem.t ->
    (sort_env_map * (Ident.pvar * (sort_env_list * Formula.t)) Set.Poly.t)
    option
    * PCSP.Problem.t
end

module Make (Config : Config.ConfigType) = struct
  let config = Config.config
  let m = Debug.Config.(if config.verbose then enable else disable)

  module Debug = Debug.Make ((val m))

  module PvarEliminator =
    PvarEliminator.Make
      ((val m))
      (struct
        let resolution_threshold = config.resolution_threshold
        let propagate_lb_ub = config.propagate_lb_ub
      end)

  module DimReducer = DimReducer.Make ((val m))

  let simplify_clause ~id ~fenv ?(timeout = Some 20000) exi_senv (uni_senv, phi)
      =
    let simp =
      if config.simplification_with_smt then
        Z3Smt.Z3interface.simplify ~id fenv ~timeout
      else Fn.id
    in
    let phi =
      Logic.ExtTerm.to_old_fml exi_senv (uni_senv, phi)
      (*|> (fun phi -> Debug.print @@ lazy ("orig: " ^ Formula.str_of phi); phi)*)
      |> Normalizer.normalize
      (*|> (fun phi -> Debug.print @@ lazy ("normalized: " ^ Formula.str_of phi); phi)*)
      |> Evaluator.simplify
      (*|> (fun phi -> Debug.print @@ lazy ("simplified: " ^ Formula.str_of phi); phi)*)
      |> (fun phi -> try simp phi with _ -> phi)
      (*|> (fun ret -> Debug.print @@ lazy ("Z3 simplified: " ^ Formula.str_of ret); ret)*)
      |> Logic.ExtTerm.of_old_formula
    in
    (*Out_channel.output_char Out_channel.stdout 'q';
      Out_channel.flush Out_channel.stdout;*)
    (* Debug.print @@ lazy ("[Preprocessor.simplify_clause] qelim"); *)
    let uni_senv, _, phi =
      Qelim.qelim Map.Poly.empty exi_senv (uni_senv, [], phi)
    in
    (*Debug.print @@ lazy
       ("quantifier eliminated: " ^ Logic.ExtTerm.str_of_formula exi_senv uni_senv phi);*)
    (uni_senv, phi)

  let simplify ?(timeout = Some 20000) pcsp =
    let id = PCSP.Problem.id_of pcsp in
    let fenv = PCSP.Problem.fenv_of pcsp in
    if PCSP.Problem.is_cnf pcsp then pcsp
    else
      PCSP.Problem.map_if_raw_no_exn pcsp
        ~f:
          (Set.Poly.map
             ~f:(simplify_clause ~id ~fenv ~timeout @@ PCSP.Problem.senv_of pcsp))

  (** obsolete *)
  let const_predicates ?(bpvs = Set.Poly.empty) exi_senv (uni_senv, phis) =
    let ppvs, npvs =
      let clauses =
        Set.Poly.map ~f:(fun (ps, ns, phi) -> (uni_senv, ps, ns, phi))
        @@ Formula.cnf_of (Logic.to_old_sort_env_map exi_senv)
        @@ Formula.and_of phis
      in
      let pvar_count, _ = ClauseSetOld.count_pvar_apps bpvs clauses in
      ( Set.Poly.filter_map pvar_count ~f:(fun (pvar, (_, _, nc)) ->
            if nc = 0 then Some pvar else None),
        Set.Poly.filter_map pvar_count ~f:(fun (pvar, (_, pc, _)) ->
            if pc = 0 then Some pvar else None) )
    in
    let atoms = uncurry Set.union @@ Formula.atoms_of @@ Formula.and_of phis in
    let const_map pvs value =
      Set.Poly.map pvs ~f:(fun pv ->
          match Set.find atoms ~f:(Atom.is_pvar_app_of pv) with
          | None -> assert false
          | Some pvar_app ->
              let pvar, sorts, _, _ = Atom.let_pvar_app pvar_app in
              ((pvar, sort_env_list_of_sorts sorts), value))
    in
    Set.union
      (const_map ppvs (Formula.mk_true ()))
      (const_map npvs (Formula.mk_false ()))

  let expand_bool_formula exi_senv (uni_senv, phi) =
    if Map.Poly.for_all uni_senv ~f:(Stdlib.( <> ) T_bool.SBool) then
      Set.Poly.singleton (uni_senv, phi)
    else
      (* assume that variables defined by uni_senv occur in phi*)
      let fvs =
        (*ToDo*)
        Formula.cnf_of (Logic.to_old_sort_env_map exi_senv) phi
        |> Set.concat_map ~f:(fun (_ps, _ns, phi) ->
               (*Set.union (Set.concat_map ~f:Atom.fvs_of @@ Set.union ps ns) @@*)
               Formula.fvs_of phi)
      in
      let bool_senv, other_senv =
        Map.Poly.partition_mapi uni_senv ~f:(fun ~key ~data ->
            if Stdlib.(data = T_bool.SBool) && Set.mem fvs key then First data
            else Second data)
      in
      let num_bool_vars = Map.Poly.length bool_senv in
      if 0 < num_bool_vars && num_bool_vars <= config.num_elim_bool_vars then
        Map.Poly.to_alist bool_senv
        |> List.power (fun (x, _) ->
               [ (x, T_bool.mk_true ()); (x, T_bool.mk_false ()) ])
        |> List.map ~f:(fun map ->
               (other_senv, Formula.subst (Map.Poly.of_alist_exn map) phi))
        |> Set.Poly.of_list
      else Set.Poly.singleton (uni_senv, phi)

  let expand_bool pcsp =
    if PCSP.Problem.is_cnf pcsp then pcsp
    else
      PCSP.Problem.map_if_raw_old pcsp
        ~f:(Set.concat_map ~f:(expand_bool_formula (PCSP.Problem.senv_of pcsp)))

  let solve_and_extend solver pcsp =
    let open Or_error in
    solver pcsp >>= fun (sol, info) ->
    return
      ( PCSP.Problem.extend_sol sol (PCSP.Problem.sol_for_eliminated_of pcsp),
        info )

  let recover_params_of_sol elimed_params_logs sol =
    let open Or_error in
    sol >>= fun (sol, info) ->
    let sol' =
      match sol with
      | PCSP.Problem.Sat sol ->
          PCSP.Problem.Sat
            (PCSP.Problem.recover_elimed_params_of_sol elimed_params_logs sol)
      | sol -> sol
    in
    return (sol', info)

  let preprocess ?(bpvs = Set.Poly.empty) ?(oracle = None)
      ?(normalize_params = false) pcsp =
    Debug.print @@ lazy "**************** preprocessing  ****************";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
    Debug.print @@ lazy "************************************************";
    let pcsp = PCSP.Problem.normalize pcsp in
    Debug.print @@ lazy "normalized:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      Debug.print @@ lazy "";*)
    let pcsp = PCSP.Problem.to_nnf pcsp in
    Debug.print @@ lazy "NNF transformed:";
    Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
    (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      Debug.print @@ lazy "";*)
    (*let pcsp = PCSP.Problem.to_cnf pcsp in
      Debug.print @@ lazy "CNF transformed:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      Debug.print @@ lazy "";*)*)
    if not config.enable then (
      let pcsp = PCSP.Problem.to_cnf pcsp in
      Debug.print @@ lazy "CNF transformed:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      Debug.print @@ lazy "************************************************";
      (None (*ToDo:use oracle*), pcsp))
    else
      let pcsp =
        PCSP.Problem.(
          remove_unused_params @@ simplify ~timeout:(Some 1000) pcsp)
      in
      Debug.print @@ lazy "simplified:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      let pcsp =
        PCSP.Problem.(
          remove_unused_params
          @@ elim_unsat_wf_predicates ~print:Debug.print pcsp)
      in
      Debug.print @@ lazy "unsat wf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      let pcsp =
        PCSP.Problem.(remove_unused_params @@ elim_dup_nwf_predicate pcsp)
      in
      Debug.print @@ lazy "duplicate nwf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      Debug.print @@ lazy "*************** start elim pvars ***************";
      let param_logs =
        DimReducer.init_param_logs_of @@ PCSP.Problem.senv_of pcsp
      in
      let sol_for_eliminated, pcsp = PvarEliminator.elim_pvs ~bpvs pcsp in
      let pcsp = PCSP.Problem.(remove_unused_params pcsp) in
      Debug.print @@ lazy "predicate variables eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      Debug.print @@ lazy "**************** end elim pvars ****************";
      Debug.print @@ lazy "************* start elim pvar args *************";
      let pcsp =
        if config.reduce_pvar_args then
          PCSP.Problem.remove_unused_params
          @@ DimReducer.elim_pcsp_args ~bpvs param_logs pcsp
        else pcsp
      in
      Debug.print @@ lazy "************** end elim pvar args **************";
      let oracle =
        match oracle with
        | None -> None
        | Some sol ->
            Debug.print @@ lazy "oracle solution:";
            let sol' =
              PCSP.Problem.Sat
                (Map.of_set_exn
                @@ Set.Poly.map ~f:(fun ((x, _), t) -> (x, t))
                @@ snd @@ Ast.CandSol.of_old sol)
            in
            Debug.print @@ lazy (PCSP.Problem.str_of_sygus_solution sol');
            Debug.print @@ lazy "";
            let psenv, map = sol in
            Option.some
            @@ ( psenv,
                 Set.Poly.map map ~f:(fun (pvar, (senv, phi)) ->
                     let arr, _sargs = Map.Poly.find_exn param_logs pvar in
                     ( pvar,
                       ( List.filteri senv ~f:(fun i _bind -> Array.get arr i),
                         phi ) )) )
      in
      let pcsp = PCSP.Problem.(remove_unused_params @@ expand_bool pcsp) in
      Debug.print @@ lazy "boolean variables expanded:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      let pcsp =
        PCSP.Problem.(remove_unused_params @@ elim_dup_nwf_predicate pcsp)
      in
      Debug.print @@ lazy "duplicate nwf predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      let pcsp =
        PCSP.Problem.(remove_unused_params @@ elim_dup_fn_predicate pcsp)
      in
      Debug.print @@ lazy "duplicate fn predicates eliminated:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      let pcsp = PCSP.Problem.to_nnf pcsp in
      Debug.print @@ lazy "NNF transformed:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      let pcsp = PCSP.Problem.to_cnf pcsp in
      Debug.print @@ lazy "CNF transformed:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      let pcsp =
        PCSP.Problem.(
          remove_unused_params @@ simplify ~timeout:(Some 1000) pcsp)
      in
      Debug.print @@ lazy "simplified:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      let pcsp = PCSP.Problem.normalize pcsp in
      Debug.print @@ lazy "normalized:";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
        Debug.print @@ lazy "";*)
      let pcsp =
        if normalize_params then (
          let pcsp =
            PCSP.Problem.(remove_unused_params @@ normalize_uni_senv pcsp)
          in
          Debug.print @@ lazy "universally quantified variables normalized:";
          Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
          (*Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
            Debug.print @@ lazy "";*)
          pcsp)
        else pcsp
      in
      Debug.print @@ lazy "*********** preprocessed constraints ***********";
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      Debug.print @@ lazy "************************************************";
      ( oracle,
        let params = PCSP.Problem.params_of pcsp in
        PCSP.Problem.update_params pcsp
        @@ {
             params with
             PCSP.Params.args_record = param_logs;
             PCSP.Params.sol_for_eliminated =
               (try Map.force_merge sol_for_eliminated params.sol_for_eliminated
                with _ -> (*ToDo*) sol_for_eliminated);
           } )

  let solve ?(bpvs = Set.Poly.empty) ?(oracle = None)
      (solver :
        ?oracle:PCSP.Problem.oracle -> PCSP.Problem.t -> State.output Or_error.t)
      pcsp =
    Debug.set_id @@ PCSP.Problem.id_of pcsp;
    PvarEliminator.id := PCSP.Problem.id_of pcsp;
    if config.enable then
      let oracle, pcsp =
        let bpvs =
          Set.union bpvs @@ ClauseSet.pvs_of
          @@ PCSP.Problem.stable_clauses_of pcsp
        in
        preprocess ~bpvs ~oracle ~normalize_params:true pcsp
      in
      recover_params_of_sol (PCSP.Problem.args_record_of pcsp)
      @@ solve_and_extend (solver ~oracle) pcsp
    else
      let pcsp =
        PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf
        @@ PCSP.Problem.normalize pcsp
      in
      Debug.print @@ lazy (PCSP.Problem.str_of_info pcsp);
      Debug.print @@ lazy (PCSP.Problem.str_of pcsp);
      solver ~oracle pcsp
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : PreprocessorType)
