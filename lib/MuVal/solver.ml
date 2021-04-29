open Core
open Async
open Common
open Common.Util
open Config
open Ast
open MuCLP.Problem

module Make (Cfg: Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))
  module Reducer = Reducer.Make (struct let config = config end)
  module Qelim = MuCLP.Qelim.Make (struct let config = config.qelim end)

  let pcsp_solver =
    let open Or_error in
    ExtFile.unwrap config.pcsp_solver >>= fun cfg ->
    Ok (module (PCSPSolver.Solver.Make (struct let config = cfg end)) : PCSPSolver.Solver.SolverType)


  let fenv = Set.Poly.empty (*TODO: generate fenv*)

  let preprocess muclp =
    muclp
    |> (if config.check_problem then MuCLP.Problem.check_problem else ident)
    |> (fun muclp -> Debug.print @@ lazy
           (Printf.sprintf "Input muCLP: %s\n"
            @@ MuCLP.Problem.str_of muclp); muclp)
    |> MuCLP.Problem.simplify
    |> MuCLP.Optimizer.optimize
    |> (fun muclp -> Debug.print @@ lazy
           (Printf.sprintf "Simplified/Optimized muCLP: %s\n"
            @@ MuCLP.Problem.str_of muclp); muclp)

  let pcsp_of muclp ordpvs fnpvs fnsenv =
    let muclp =
      muclp
      |> MuCLP.Problem.aconv_tvar |> MuCLP.Problem.complete_tsort
      |> MuCLP.Problem.complete_psort (Util.Map.of_set @@ Set.Poly.union ordpvs fnpvs)
    in
    Debug.print @@ lazy
      (Printf.sprintf "Preprocessed muCLP: %s\n"
       @@ MuCLP.Problem.str_of muclp);
    let pcsp = Reducer.f muclp ordpvs fnpvs fnsenv in
    Debug.print @@ lazy
      (Printf.sprintf "******* Generated pfwCSP:\n%s"
       @@ (PCSP.Problem.str_of pcsp));
    pcsp

  let prove_forall_only muclp fnpvs fnsenv : (solution * int) Deferred.Or_error.t =
    let pcsp : PCSP.Problem.t = pcsp_of muclp Set.Poly.empty fnpvs fnsenv in
    Deferred.return pcsp_solver >>=? fun pcsp_solver ->
    let (module PCSPSolver) = pcsp_solver in
    let pcsp = PCSP.Problem.map_if_raw ~f:(Set.Poly.map ~f:Logic.Term.refresh) pcsp in
    Deferred.return (PCSPSolver.solve pcsp)
    >>=? function
    | PCSP.Problem.Sat _, num_iters -> Deferred.return (Ok (Valid, num_iters))
    | Unsat, num_iters -> Deferred.return (Ok (Invalid, num_iters))
    | Unknown, num_iters -> Deferred.return (Ok (Unknown, num_iters))

  let prove muclp =
    if MuCLP.Problem.is_onlyforall muclp then begin
      (** no exist encoding required *)
      prove_forall_only muclp Set.Poly.empty Logic.SortMap.empty
    end else begin
      Debug.print @@ lazy (Printf.sprintf "original: %s\n" @@ MuCLP.Problem.str_of muclp);
      let muclp, fnpvs, fnsenv1 = Qelim.encode_top_exists muclp Set.Poly.empty in
      Debug.print @@ lazy (Printf.sprintf "top encoded: %s\n" @@ MuCLP.Problem.str_of muclp);
      let muclp, fnpvs, fnsenv2 = Qelim.encode_body_exists muclp fnpvs in
      Debug.print @@ lazy (Printf.sprintf "body encoded: %s\n" @@ MuCLP.Problem.str_of muclp);
      prove_forall_only muclp fnpvs (Logic.SortMap.merge fnsenv1 fnsenv2)
    end

  let rec solve_primary flip_on_failure muclp =
    prove muclp
    >>=? (function
        | Unknown, num_iters ->
          if flip_on_failure then solve_dual false muclp
          else Deferred.return (Ok (Unknown, num_iters))
        | x -> Deferred.return (Ok x))
  and solve_dual flip_on_failure muclp =
    prove (MuCLP.Problem.get_dual muclp)
    >>=? (function
        | Unknown, num_iters ->
          if flip_on_failure then solve_primary false muclp
          else Deferred.return (Ok (Unknown, num_iters))
        | (res, num_iters) ->
          Deferred.return (Ok (flip_solution res, num_iters)))

  let solve ?(print_sol=false) muclp =
    Debug.print @@ lazy "======== MuVal ========";
    Deferred.Result.return (preprocess muclp) >>=? fun muclp ->
    let mode =
      if Stdlib.(=) config.mode Config.Auto then
        if MuCLP.Problem.is_onlyforall muclp then begin
          (if MuCLP.Problem.is_onlynu muclp then
             Debug.print @@ lazy "vvvv muCLP shape: only forall-nu"
           else if MuCLP.Problem.is_onlymu muclp then
             Debug.print @@ lazy "vvvv muCLP shape: only forall-mu"
           else
             Debug.print @@ lazy "vvvv muCLP shape: only forall");
          Config.Prove
        end else if MuCLP.Problem.is_onlyexists muclp then begin
          (if MuCLP.Problem.is_onlynu muclp then
             Debug.print @@ lazy "vvvv muCLP shape: only exists-nu"
           else if MuCLP.Problem.is_onlymu muclp then
             Debug.print @@ lazy "vvvv muCLP shape: only exists-mu"
           else
             Debug.print @@ lazy "vvvv muCLP shape: only exists");
          Config.Disprove
        end else begin
          (if MuCLP.Problem.is_onlynu muclp then
             Debug.print @@ lazy "vvvv muCLP shape: only nu"
           else if MuCLP.Problem.is_onlymu muclp then
             Debug.print @@ lazy "vvvv muCLP shape: only mu"
           else
             Debug.print @@ lazy "vvvv muCLP shape: otherwise");
          Config.Prove
        end
      else config.mode 
    in
    (match mode with
     | Config.Auto -> assert false
     | Config.Prove ->
       Debug.print @@ lazy "-=-=-=-= proving -=-=-=-=";
       solve_primary true muclp
     | Config.Disprove ->
       Debug.print @@ lazy "-=-=-=-= disproving -=-=-=-=";
       solve_dual true muclp
     | Config.Parallel ->
       Debug.print @@ lazy "-=-=-=-= proving/disproving -=-=-=-=";
       Deferred.any [
         solve_primary false muclp;
         solve_dual false muclp
         (** ToDo: wait instead of returning Unknown *)
       ] >>=? function (solution, num_iters) ->
         Core.print_endline @@
         sprintf "%s,%d"
           (MuCLP.Problem.str_of_solution solution)
           num_iters;
         Out_channel.flush stdout;
         Shutdown.set_default_force (fun () -> Deferred.return ());
         shutdown 0;
         Deferred.Or_error.return (solution, num_iters))
    >>=? (function
        (*| Unknown, _ -> Deferred.Or_error.error_string "Unknown output"*)
        | (solution, iteration) ->
          Debug.print @@ lazy "=========================";
          if print_sol then print_endline @@
            if config.output_iteration then
              Printf.sprintf "%s,%d" (MuCLP.Problem.str_of_solution solution) iteration
            else
              Printf.sprintf "%s" (MuCLP.Problem.str_of_solution solution);
          Deferred.Or_error.return (solution, iteration))

  let solve_pcsp ?(print_sol=false) pcsp =
    let pvar_eliminator =
      let cfg =
        let open PCSat.PvarEliminator.Config in
        { verbose = config.verbose;
          preprocess = true;
          resolution_threshold = 4;
          simplification_with_smt = true;
          num_elim_bool_vars = 4;
          propagate_lb_ub = false; }
      in
      Ok (PCSat.PvarEliminator.make cfg)
    in
    Deferred.return pvar_eliminator >>=? fun pvar_eliminator ->
    let (module PvarEliminator : PCSat.PvarEliminator.PvarEliminatorType) = pvar_eliminator in
    Debug.print @@ lazy "************* converting pfwCSP to muCLP ***************";
    PvarEliminator.elim_async (fun pcsp ->
        solve ~print_sol:false (MuCLP.Problem.of_chc pcsp) >>=? fun (solution, iteration) ->
        let solution =
          match solution with
          | MuCLP.Problem.Valid -> PCSP.Problem.Sat (Map.Poly.empty(* ToDo *))
          | MuCLP.Problem.Invalid -> PCSP.Problem.Unsat
          | MuCLP.Problem.Unknown -> PCSP.Problem.Unknown
        in
        if print_sol then print_endline @@
          if config.output_iteration then
            Printf.sprintf "%s,%d" (PCSP.Problem.str_of_solution solution) iteration
          else
            Printf.sprintf "%s" (PCSP.Problem.str_of_solution solution);
        Deferred.Or_error.return (solution, iteration)) pcsp
  let solve_lts ?(print_sol=false) (lts, p) =
    Debug.print @@ lazy "************* converting LTS to muCLP ***************";
    Debug.print (lazy ("input LTS:\n" ^ LTS.Problem.str_of_lts lts));
    let lvs, cps, lts = LTS.Problem.analyze lts in
    Debug.print (lazy ("simplified LTS:\n" ^ LTS.Problem.str_of_lts lts));
    match p with
    | LTS.Problem.Term | LTS.Problem.NonTerm ->
      solve ~print_sol:false (MuCLP.Problem.of_lts ~live_vars:(Some lvs) ~cut_points:(Some cps) (lts, p)) >>=? fun (solution, iteration) ->
      let res =
        match solution with
        | MuCLP.Problem.Valid -> "YES"
        | MuCLP.Problem.Invalid -> "NO"
        | MuCLP.Problem.Unknown -> "MAYBE"
      in
      if print_sol then print_endline @@
        if config.output_iteration then
          Printf.sprintf "%s,%d" res iteration
        else
          Printf.sprintf "%s" res;
      Deferred.Or_error.return (solution, iteration)
    | LTS.Problem.CondTerm ->
      let muclp = MuCLP.Problem.of_lts ~live_vars:(Some lvs) ~cut_points:(Some cps) (lts, LTS.Problem.Term) in
      let pre_term, muclp_term =
        let MuCLP.Problem.MuCLP (funcs, entry) = muclp in
        let bounds, phi, _ = if LogicOld.Formula.is_forall entry then LogicOld.Formula.let_forall entry else LogicOld.SortEnv.empty, entry, LogicOld.Dummy in
        let atm, _ = LogicOld.Formula.let_atom phi in
        let _, sorts, args, _ = LogicOld.Atom.let_pvar_app atm in
        let senv = Logic.SortMap.of_old_sort_env Logic.ExtTerm.of_old_sort bounds in
        let pre = LogicOld.Formula.mk_atom @@ LogicOld.Atom.mk_pvar_app (Ident.Pvar "PreTerm") sorts args in
        (senv, pre), MuCLP.Problem.MuCLP (funcs, LogicOld.Formula.forall bounds @@ LogicOld.Formula.mk_imply pre phi)
      in
      let pre_nonterm, muclp_nonterm =
        let MuCLP.Problem.MuCLP (funcs, entry) = MuCLP.Problem.get_dual muclp in
        let bounds, phi, _ = if LogicOld.Formula.is_exists entry then LogicOld.Formula.let_exists entry else LogicOld.SortEnv.empty, entry, LogicOld.Dummy in
        let atm, _ = LogicOld.Formula.let_atom phi in
        let _, sorts, args, _ = LogicOld.Atom.let_pvar_app atm in
        let senv = Logic.SortMap.of_old_sort_env Logic.ExtTerm.of_old_sort bounds in
        let pre = LogicOld.Formula.mk_atom @@ LogicOld.Atom.mk_pvar_app (Ident.Pvar "PreNonTerm") sorts args in
        (senv, pre), MuCLP.Problem.MuCLP (funcs, LogicOld.Formula.forall bounds @@ LogicOld.Formula.mk_imply pre phi)
      in
      let ord_pvs_term = LogicOld.Formula.pred_sort_env_of @@ snd pre_term in
      let ord_pvs_nonterm = LogicOld.Formula.pred_sort_env_of @@ snd pre_nonterm in
      let muclp_nonterm, fnpvs, fnsenv = Qelim.encode_body_exists muclp_nonterm Set.Poly.empty in
      let pcsp_term = PCSP.Problem.add_non_emptiness (Set.Poly.choose_exn ord_pvs_term) (pcsp_of muclp_term ord_pvs_term Set.Poly.empty Map.Poly.empty) in
      let pcsp_nonterm = PCSP.Problem.add_non_emptiness (Set.Poly.choose_exn ord_pvs_nonterm) (pcsp_of muclp_nonterm ord_pvs_nonterm fnpvs fnsenv) in
      Debug.print @@ lazy (Printf.sprintf "pfwCSP for Termination:\n%s\n" @@ PCSP.Problem.str_of pcsp_term);
      Debug.print @@ lazy (Printf.sprintf "pfwCSP for Non-termination:\n%s\n" @@ PCSP.Problem.str_of pcsp_nonterm);
      Deferred.return pcsp_solver >>=? fun pcsp_solver ->
      let (module PCSPSolver) = pcsp_solver in
      Out_channel.output_string Out_channel.stdout "timeout in sec: ";
      Out_channel.flush Out_channel.stdout;
      let timeout = try Some (int_of_string @@ In_channel.input_line_exn In_channel.stdin) with _ -> None in
      let rec refine term nonterm unknown pos neg =
        Out_channel.output_string Out_channel.stdout "action (term/nonterm/unknown/pos/neg/end): ";
        Out_channel.flush Out_channel.stdout;
        match In_channel.input_line_exn In_channel.stdin with 
        | "term" ->
          let phi =
            let pre = Logic.ExtTerm.of_old_formula @@ snd pre_term in
            Logic.BoolTerm.and_of
              [Logic.BoolTerm.imply_of pre (Logic.ExtTerm.of_old_formula (LogicOld.Formula.mk_and unknown (LogicOld.Formula.mk_neg neg)));
               Logic.BoolTerm.imply_of (Logic.ExtTerm.of_old_formula pos) pre] in
          let pcsp = PCSP.Problem.add_formula (fst pre_term, phi) pcsp_term in
          Deferred.return
            (match timeout with
             | None -> PCSPSolver.solve ~bpvs:(Set.Poly.map ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) ord_pvs_term) pcsp
             | Some tm ->
               Timer.enable_timeout tm ident ignore
                 (fun () -> PCSPSolver.solve ~bpvs:(Set.Poly.map ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) ord_pvs_term) pcsp)
                 (fun _ res -> res)
                 (fun _ -> function Timer.Timeout -> Or_error.return (PCSP.Problem.Unknown, -1) | e -> raise e))
          >>=? (function
              | PCSP.Problem.Sat sol, _ ->
                (*Out_channel.print_endline @@ CandSol.str_of sol;*)
                let phi =
                  Z3Smt.Z3interface.simplify fenv @@ Evaluator.simplify @@
                  Logic.ExtTerm.to_old_formula (fst pre_term)
                    (Logic.Term.subst sol @@ Logic.ExtTerm.of_old_formula @@ snd pre_term) [] in
                let term = Z3Smt.Z3interface.simplify fenv @@ Evaluator.simplify @@ LogicOld.Formula.or_of [phi; term] in
                let unknown = Z3Smt.Z3interface.simplify fenv @@ Evaluator.simplify @@ LogicOld.Formula.and_of [LogicOld.Formula.mk_neg phi; unknown] in
                Out_channel.print_endline @@ LogicOld.Formula.str_of @@ term;
                if Z3Smt.Z3interface.is_sat fenv unknown then
                  refine term nonterm unknown (LogicOld.Formula.mk_false ()) (LogicOld.Formula.mk_false ())
                else begin
                  Out_channel.print_endline "maximality is guaranteed";
                  Deferred.Or_error.return (Unknown, -1)(*Dummy*)
                end
              | Unsat, _ ->
                if LogicOld.Formula.is_false pos && LogicOld.Formula.is_false neg then begin
                  Out_channel.print_endline "maximally weak precondition for non-termination:";
                  Out_channel.print_endline @@ LogicOld.Formula.str_of @@ unknown;
                  Deferred.Or_error.return (Unknown, -1)(*Dummy*)
                end else begin
                  Out_channel.print_endline "the specified constraints for positive and negative examples are incorrect";
                  refine term nonterm unknown (LogicOld.Formula.mk_false ()) (LogicOld.Formula.mk_false ())
                end
              | Unknown, _ -> refine term nonterm unknown (LogicOld.Formula.mk_false ()) (LogicOld.Formula.mk_false ()))
        | "nonterm" ->
          let phi =
            let pre = Logic.ExtTerm.of_old_formula @@ snd pre_nonterm in
            Logic.BoolTerm.and_of
              [Logic.BoolTerm.imply_of pre (Logic.ExtTerm.of_old_formula (LogicOld.Formula.mk_and unknown (LogicOld.Formula.mk_neg neg)));
               Logic.BoolTerm.imply_of (Logic.ExtTerm.of_old_formula pos) pre] in
          let pcsp = PCSP.Problem.add_formula (fst pre_nonterm, phi) pcsp_nonterm in
          Deferred.return
            (match timeout with
             | None -> PCSPSolver.solve ~bpvs:(Set.Poly.map ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) ord_pvs_nonterm) pcsp
             | Some tm ->
               Timer.enable_timeout tm ident ignore
                 (fun () -> PCSPSolver.solve ~bpvs:(Set.Poly.map ~f:(fun (Ident.Pvar x, _) -> Ident.Tvar x) ord_pvs_nonterm) pcsp)
                 (fun _ res -> res)
                 (fun _ -> function Timer.Timeout -> Or_error.return (PCSP.Problem.Unknown, -1) | e -> raise e))
          >>=? (function
              | PCSP.Problem.Sat sol, _ ->
                (*Out_channel.print_endline @@ Ast.CandSol.str_of sol;*)
                let phi =
                  Z3Smt.Z3interface.simplify fenv @@ Evaluator.simplify @@
                  Logic.ExtTerm.to_old_formula (fst pre_nonterm)
                    (Logic.Term.subst sol @@ Logic.ExtTerm.of_old_formula @@ snd pre_nonterm) [] in
                let nonterm = Z3Smt.Z3interface.simplify fenv @@ Evaluator.simplify @@ LogicOld.Formula.or_of [phi; nonterm] in
                let unknown = Z3Smt.Z3interface.simplify fenv @@ Evaluator.simplify @@ LogicOld.Formula.and_of [LogicOld.Formula.mk_neg phi; unknown] in
                Out_channel.print_endline @@ LogicOld.Formula.str_of @@ nonterm;
                if Z3Smt.Z3interface.is_sat fenv unknown then
                  refine term nonterm unknown (LogicOld.Formula.mk_false ()) (LogicOld.Formula.mk_false ())
                else begin
                  Out_channel.print_endline "maximality is guaranteed";
                  Deferred.Or_error.return (Unknown, -1)(*Dummy*)
                end
              | Unsat, _ ->
                if LogicOld.Formula.is_false pos && LogicOld.Formula.is_false neg then begin
                  Out_channel.print_endline "maximally weak precondition for termination:";
                  Out_channel.print_endline @@ LogicOld.Formula.str_of @@ unknown;
                  Deferred.Or_error.return (Unknown, -1)(*Dummy*)
                end else begin
                  Out_channel.print_endline "the specified constraints for positive and negative examples are incorrect";
                  refine term nonterm unknown (LogicOld.Formula.mk_false ()) (LogicOld.Formula.mk_false ())
                end
              | Unknown, _ -> refine term nonterm unknown (LogicOld.Formula.mk_false ()) (LogicOld.Formula.mk_false ()))
        | "pos" ->
          Out_channel.output_string Out_channel.stdout "positive examples: ";
          Out_channel.flush Out_channel.stdout;
          (match MuCLP.Parser.formula_from_string @@ In_channel.input_line_exn In_channel.stdin with
           | Ok phi -> refine term nonterm unknown (LogicOld.Formula.mk_or pos phi) neg
           | Error msg -> failwith (Error.to_string_hum msg))
        | "neg" ->
          Out_channel.output_string Out_channel.stdout "negative examples: ";
          Out_channel.flush Out_channel.stdout;
          (match MuCLP.Parser.formula_from_string @@ In_channel.input_line_exn In_channel.stdin with
           | Ok phi -> refine term nonterm unknown pos (LogicOld.Formula.mk_or neg phi)
           | Error msg -> failwith (Error.to_string_hum msg))
        | "unknown" ->
          Out_channel.print_endline @@ LogicOld.Formula.str_of @@ unknown;
          refine term nonterm unknown pos neg
        | "end" -> Deferred.Or_error.return (Unknown, -1)(*Dummy*)
        | _ -> refine term nonterm unknown pos neg
      in
      refine (LogicOld.Formula.mk_false ()) (LogicOld.Formula.mk_false ()) (LogicOld.Formula.mk_true ()) (LogicOld.Formula.mk_false ()) (LogicOld.Formula.mk_false ())
end