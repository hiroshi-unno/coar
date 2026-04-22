open Core
open Common
open Common.Util
open Preprocessing
open Ast

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let pcsp_solver () (* ToDo *) =
    let open Or_error in
    ExtFile.unwrap config.pcsp_solver >>= fun cfg ->
    Ok
      PCSPSolver.(
        (module Solver.Make (struct
          let config = cfg
        end) : Solver.SolverType))

  let preprocess ~print problem =
    problem
    |> (if config.simplify then Problem.simplify else Fn.id)
    |> (if config.reduce then Problem.reduce else Fn.id)
    |> (if config.slice_forward then Problem.slice_forward else Fn.id)
    |> (if config.slice_backward then Problem.slice_backward else Fn.id)
    |> (if config.gen_lemmas_with_ai then Problem.gen_lemmas ~print else Fn.id)
    |>
    if config.gen_determ_conjs then Problem.gen_determ_conjs ~print ~config
    else Fn.id
  (*|> Problem.infer |> snd*)

  let solve ?(print_sol = false) ?(dtenv = Map.Poly.empty) muclp =
    let open Or_error.Monad_infix in
    (Problem.of_muclp ~dtenv muclp
    |> preprocess ~print:Debug.print
    |>
    if true then ProofSearch.solve ~print:Debug.print ~config pcsp_solver
    else RelProofSearch.solve ~print:Debug.print ~config pcsp_solver)
    >>= fun (sol, _) ->
    if print_sol then print_endline @@ MuCLP.Problem.str_of_solution sol;
    Ok sol

  let solve_pcsp ?(print_sol = false) pcsp =
    let (module Preprocessor : Preprocessor.PreprocessorType) =
      Preprocessor.(
        make @@ Config.make config.enable_pvar_elim config.verbose 4 4 true)
    in
    Debug.print
    @@ lazy "************* converting pfwCSP to muCLP ***************";
    Preprocessor.solve
      (fun ?oracle pcsp ->
        ignore oracle;
        let open Or_error.Monad_infix in
        solve ~print_sol:false
          ~dtenv:(PCSP.Problem.dtenv_of pcsp)
          (MuCLP.Util.of_chc ~print:Debug.print ~only_pos:false pcsp)
        >>= fun sol ->
        let sol =
          match sol with
          | MuCLP.Problem.Valid -> PCSP.Problem.Sat Map.Poly.empty (* ToDo *)
          | MuCLP.Problem.Invalid -> PCSP.Problem.Unsat None (*ToDo*)
          | MuCLP.Problem.Unknown -> PCSP.Problem.Unknown
          | MuCLP.Problem.Timeout -> PCSP.Problem.Timeout
        in
        if print_sol then print_endline (PCSP.Problem.str_of_solution sol);
        Or_error.return
          (sol, { PCSatCommon.State.num_cegis_iters = -1 (*ToDo*) }))
      pcsp

  let solve_smt ?(print_sol = false) g =
    Debug.print
    @@ lazy (sprintf "original input: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      let senv = Set.to_list @@ LogicOld.Formula.sort_env_of g in
      LogicOld.Formula.mk_exists_if_bounded senv g
    in
    Debug.print @@ lazy (sprintf "closed: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      LogicOld.Formula.move_quantifiers_to_front @@ Normalizer.normalize
      @@ Evaluator.simplify @@ LogicOld.Formula.elim_ite @@ Normalizer.normalize
      @@ LogicOld.Formula.elim_let
      @@ Normalizer.normalize_let ~rename:true
      @@ Typeinf.typeinf_formula
           ~print:(*Debug.print*) (fun _ -> ())
           ~default:(Some LogicOld.T_int.SInt (*ToDo*))
      @@ LogicOld.Formula.aconv_tvar g
    in
    Debug.print
    @@ lazy (sprintf "prenex normal form: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      Normalizer.normalize @@ Evaluator.simplify @@ LogicOld.Formula.rm_div_mod
      @@ LogicOld.Formula.elim_redundant_quantifiers g
    in
    Debug.print @@ lazy (sprintf "input: %s\n" (LogicOld.Formula.str_of g));
    let quantifiers, f = LogicOld.Formula.split_quantifiers g in
    let res =
      match Qsat.decide_theory quantifiers with
      | QBF ->
          let open Qsat.QSAT (Mbp.Boolean) in
          solve ~config ~print:Debug.print quantifiers f
      | LRA ->
          let open Qsat.QSAT (Mbp.LRA) in
          solve ~config ~print:Debug.print quantifiers f
      | LIA ->
          let open Qsat.QSAT (Mbp.LIA) in
          solve ~config ~print:Debug.print quantifiers f
    in
    let solution =
      match res with
      | SAT -> SMT.Problem.Sat [ (*ToDo*) ]
      | UNSAT -> SMT.Problem.Unsat
    in
    if print_sol then
      print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
    Ok solution
end
