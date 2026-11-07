(* A predicate constraint solver without CEGIS: after PCSat's preprocessing
   (predicate elimination and argument erasure, whose solution extension runs
   afterwards), every remaining unknown is given one template with real
   parameters ([Templates]), the clauses with the templates substituted become
   polynomial quantified entailments ([Translate]) together with the
   templates' kind conditions, and PolyQEnt is asked for the parameters.

   Contract.  A [Sat] answer is a solution: the parameters PolyQEnt returns
   are checked against the kind conditions, and every clause of the
   preprocessed problem with the instantiated templates substituted is
   re-checked valid by Z3 over its own sorts before the answer is given, so
   neither PolyQEnt nor its own SMT back end is trusted.  This back end never
   answers [Unsat]: PolyQEnt's [unsat] or [unknown] says only that these
   template shapes, with its certificate shapes and degree bounds, admit no
   parameters, so it is [Unknown].  A problem outside what the templates and
   the translation cover (an unknown of a kind other than admissible, an
   integer or datatype argument, a non-polynomial term) is declined with a
   message on stderr and answered [Unknown]; nothing is sent for it.  A
   failure to run PolyQEnt is an [Error], as the wrapper reports it. *)
open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld

module type SolverType = sig
  val solve :
    ?timeout:int option ->
    ?print_sol:bool ->
    PCSP.Problem.t ->
    PCSP.Problem.solution Or_error.t
end

let no_info =
  PCSatCommon.State.
    { num_cegis_iters = 0; unsat_witness = None; kind_certificates = Map.Poly.empty }

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let unknown msg =
    prerr_endline ("PolyQEnt templates: " ^ msg);
    Ok (PCSP.Problem.Unknown, no_info)

  (* every clause of [pcsp] valid under [sol], asked of Z3; an undecided
     clause counts as not valid *)
  let valid_under pcsp sol =
    let fenv = PCSP.Problem.fenv_of pcsp in
    PCSP.Problem.check_valid
      (fun uni_senv t ->
        let phi =
          Logic.ExtTerm.to_old_fml (PCSP.Problem.senv_of pcsp) uni_senv t
        in
        try Z3Smt.Z3interface.is_valid_exn ~id:None fenv phi
        with Z3Smt.Z3interface.Unknown ->
          Debug.print @@ lazy ("undecided: " ^ Formula.str_of phi);
          false)
      pcsp sol

  (* the templates of [pcsp]'s unknowns with [pieces] absolute-value pieces,
     and the entailments of its clauses under them (kind conditions apart) *)
  let translate ~pieces pcsp =
    let exi_senv = PCSP.Problem.senv_of pcsp in
    let templates =
      Map.Poly.mapi exi_senv ~f:(fun ~key ~data ->
          let args, _ = Logic.Sort.args_ret_of data in
          let arg_sorts = List.map args ~f:Logic.ExtTerm.to_old_sort in
          ( arg_sorts,
            Templates.of_kind ~pieces ~cond_scaled:config.cond_scaled
              (PCSP.Problem.kind_of pcsp key)
              arg_sorts ))
    in
    let instantiate pvar args =
      match Map.Poly.find templates (Ident.pvar_to_tvar pvar) with
      | Some (_, templ) -> templ.Templates.body ~abs:false args
      | None ->
          Templates.decline "an application of %s, which is not an unknown"
            (Ident.name_of_pvar pvar)
    in
    let pqes =
      Set.to_list (PCSP.Problem.formulas_of pcsp)
      |> List.concat_map ~f:(fun (uni_senv, t) ->
          Translate.pqes_of_clause ~max:config.max_pqes ~instantiate
            ( Logic.to_old_sort_env_map uni_senv,
              Logic.ExtTerm.to_old_fml exi_senv uni_senv t ))
    in
    if List.length pqes > config.max_pqes then
      Templates.too_large "%d entailments, more than %d" (List.length pqes)
        config.max_pqes;
    (templates, pqes)

  (* [translate] with [config.adm_pieces] pieces, and with fewer, down to
     none, while the translation is too large *)
  let rec translate_fitting ~pieces pcsp =
    try translate ~pieces pcsp
    with Templates.Too_large msg when pieces > 0 ->
      prerr_endline
        (sprintf "PolyQEnt templates: %s with %d piece(s); trying %d" msg
           pieces (pieces - 1));
      translate_fitting ~pieces:(pieces - 1) pcsp

  (* the solution the parameter values [value] give, checked: the kind
     conditions on the values, then every clause of [pcsp] by Z3 *)
  let checked_solution pcsp templates value =
    let sub =
      Map.Poly.of_alist_exn
      @@ List.concat_map (Map.Poly.data templates) ~f:(fun (_, t) ->
          List.map t.Templates.params ~f:(fun x -> (x, value x)))
    in
    let kinds_ok =
      List.for_all
        (List.concat_map (Map.Poly.data templates) ~f:(fun (_, t) ->
             t.Templates.kind_conds))
        ~f:(fun phi -> Evaluator.eval (Formula.subst sub phi))
    in
    let sol =
      Map.Poly.map templates ~f:(fun (arg_sorts, templ) ->
          let args =
            List.mapi arg_sorts ~f:(fun i s -> (Ident.Tvar (sprintf "x%d" i), s))
          in
          let body =
            Formula.subst sub
            @@ templ.Templates.body ~abs:true
                 (List.map args ~f:(Tuple2.uncurry Term.mk_var))
          in
          Logic.ExtTerm.mk_lambda
            (List.map args ~f:(fun (x, s) -> (x, Logic.ExtTerm.of_old_sort s)))
            (Logic.ExtTerm.of_old_formula body))
    in
    Debug.print
    @@ lazy
         (sprintf "the parameters give:\n%s"
            (PCSP.Problem.str_of_solution (PCSP.Problem.Sat sol)));
    if not kinds_ok then
      unknown "the parameters violate a kind condition; unknown"
    else if not (valid_under pcsp sol) then
      unknown "the instantiated templates were not re-validated; unknown"
    else Ok (PCSP.Problem.Sat sol, no_info)

  let solve_preprocessed polyqent pcsp =
    let (module PolyQEnt : PolyQEnt.Solver.SolverType) = polyqent in
    Debug.print
    @@ lazy
         (sprintf "******* the problem after preprocessing:\n%s"
            (PCSP.Problem.str_of pcsp));
    match translate_fitting ~pieces:config.adm_pieces pcsp with
    | exception (Templates.Decline msg | Templates.Too_large msg) ->
        unknown ("declined: " ^ msg)
    | templates, [] ->
        (* no entailment: any parameters meeting the kind conditions do, and
           0 meets every one *)
        checked_solution pcsp templates (fun _ -> T_real.rzero ())
    | templates, pqes -> (
        let params =
          Map.Poly.of_alist_exn
          @@ List.concat_map (Map.Poly.data templates) ~f:(fun (_, t) ->
              List.map t.Templates.params ~f:(fun x -> (x, T_real.SReal)))
        in
        let kind_conds =
          List.concat_map (Map.Poly.data templates) ~f:(fun (_, t) ->
              t.Templates.kind_conds)
        in
        let problem =
          PCSP.Problem.make ~prefix:(Some "q") (pqes @ kind_conds)
            SMT.Problem.
              {
                decl_reading = SMT.Problem.Synthesize;
                lifted_universals = Map.Poly.empty;
                candidates = Map.Poly.empty;
                uni_sort = Set.Poly.empty;
                uni_senv = Map.Poly.empty;
                exi_senv = params;
                dep_map = Map.Poly.empty;
                kind_map = Map.Poly.map params ~f:(fun _ -> Kind.RealFun);
                fenv = Map.Poly.empty;
                dtenv = Map.Poly.empty;
              }
        in
        Debug.print
        @@ lazy
             (sprintf "******* generated PQEs:\n%s" (PCSP.Problem.str_of problem));
        let open Or_error.Monad_infix in
        PolyQEnt.solve problem >>= function
        | PCSP.Problem.Sat model ->
            (* a parameter the entailments do not mention is not in the
               model; 0 meets every kind condition *)
            checked_solution pcsp templates (fun x ->
                match Map.Poly.find model x with
                | Some t ->
                    Logic.ExtTerm.to_old_term Map.Poly.empty Map.Poly.empty t []
                | None -> T_real.rzero ())
        | Unsat _ | Unknown | OutSpace _ | Timeout ->
            unknown "PolyQEnt found no parameters for these templates; unknown")

  let solve ?(timeout = None) ?(print_sol = false) pcsp =
    ignore timeout;
    let open Or_error.Monad_infix in
    ExtFile.unwrap config.preprocessor >>= fun pcfg ->
    ExtFile.unwrap config.polyqent >>= fun qcfg ->
    let polyqent = PolyQEnt.Solver.make qcfg in
    let (module Preprocessor : Preprocessing.Preprocessor.PreprocessorType) =
      Preprocessing.Preprocessor.make pcfg
    in
    Preprocessor.solve
      (fun ?oracle p ->
        ignore oracle;
        solve_preprocessed polyqent p)
      pcsp
    >>= fun (sol, _) ->
    if print_sol then print_endline (PCSP.Problem.str_of_solution sol);
    Ok sol
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
