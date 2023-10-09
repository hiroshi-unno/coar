open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

module Make (Cfg: Config.ConfigType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  let mk_solver ctx =
    let solver = Z3.Fixedpoint.mk_fixedpoint ctx in
    let params = Z3.Params.mk_params ctx in
    Z3.Params.add_symbol params
      (Z3.Symbol.mk_string ctx "engine") (Z3.Symbol.mk_string ctx "spacer");
    (*Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "spacer.use_inductive_generalizer") false;*)
    if config.solution_needed then begin
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "print_answer") true;
      (* xform.slice, xform.inline_linear, and xform.inline_eager need to be disabled to obtain a sound solution from SPACER *)
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "xform.slice") false;
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "xform.inline_linear") false;
      Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "xform.inline_eager") false
    end;
    (*Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "validate") true;*)
    (*Z3.Params.add_bool params (Z3.Symbol.mk_string ctx "print_fixedpoint_extensions") false;*)
    Z3.Fixedpoint.set_parameters solver params;
    solver

  let solve ?(print_sol=false) pcsp =
    (*let module Printer =
      Printer.Solver.Make(struct
        let config = {
          Printer.Config.pvar_eliminator = Instance (PCSat.PvarEliminator.Config.make false false 4 0 true);
          Printer.Config.lts_format = Printer.Config.PCSP;
          Printer.Config.smt_format = Printer.Config.SMT2;
        }
      end)
      in
      print_endline @@ Printer.string_of_pcsp pcsp;*)
    let ctx =
      let options =
        match config.timeout with
        | None -> []
        | Some timeout -> ["timeout", string_of_int @@ timeout * 1000]
      in
      Z3.mk_context options
    in
    let solver = mk_solver ctx(*ToDo*) in
    assert (Set.is_empty @@ PCSP.Problem.wfpvs_of pcsp &&
            Set.is_empty @@ PCSP.Problem.fnpvs_of pcsp
            (* ToDo: check if pcsp is of CHC *));
    let pcsp = PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf pcsp in
    Debug.print @@ lazy ("input:\n" ^ PCSP.Problem.str_of pcsp);
    let dtenv = Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx @@ PCSP.Problem.dtenv_of pcsp in
    let fenv = PCSP.Problem.fenv_of pcsp in
    let exi_senv = PCSP.Problem.senv_of pcsp in
    (*let query_name = "__query__" in
      let exi_senv =
      Map.Poly.add_exn exi_senv ~key:(Ident.Tvar query_name) ~data:Logic.BoolTerm.SBool
      in*)
    let penv =
      List.map (Map.Poly.to_alist @@ exi_senv) ~f:(fun (Ident.Tvar name, sort) ->
          Ident.Pvar name,
          let arg_sorts =
            List.map (Logic.Sort.args_of sort)
              ~f:(Logic.ExtTerm.to_old_sort >> Z3Smt.Z3interface.of_sort ctx dtenv)
          in
          let symbol = Z3.Symbol.mk_string ctx name in
          Z3.FuncDecl.mk_func_decl ctx symbol arg_sorts (Z3.Boolean.mk_sort ctx))
    in
    List.iter penv ~f:(snd >> Z3.Fixedpoint.register_relation solver);
    let qs =
      PCSP.Problem.clauses_of pcsp
      |> Set.Poly.filter_map ~f:(fun (uni_senv, ps, ns, phi) ->
          let phi = Formula.aconv_tvar @@ Logic.ExtTerm.to_old_formula exi_senv uni_senv phi [] in
          (*print_endline @@ "a: " ^ Formula.str_of phi;*)
          let senv, phi =
            (** assume that [phi] is alpha-renamed *)
            Formula.elim_let_equivalid @@ Normalizer.normalize_let ~rename:true phi
          in
          (*print_endline @@ "b: " ^ Formula.str_of phi;*)
          let uni_senv = Map.force_merge uni_senv @@ Map.Poly.map ~f:Logic.ExtTerm.of_old_sort senv in
          let body =
            Formula.and_of @@
            Formula.mk_neg phi ::
            (Set.to_list @@ Set.Poly.map ns
               ~f:(Fn.flip (Logic.ExtTerm.to_old_atom exi_senv uni_senv) [] >> Formula.mk_atom))
          in
          let head =
            Formula.or_of @@ Set.to_list @@
            match Set.length ps with
            | 0 -> Set.Poly.empty
            (*Set.Poly.singleton @@ Atom.mk_pvar_app query_name [] []*)
            | 1 ->
              Set.Poly.map ps
                ~f:(Fn.flip (Logic.ExtTerm.to_old_atom exi_senv uni_senv) [] >> Formula.mk_atom)
            | _ -> failwith "head disjunction not supported"
          in
          (*print_endline @@ "c: " ^ Formula.str_of @@ Formula.mk_imply body head;*)
          let quantified_senv, phi' =
            Formula.rm_quant ~forall:true @@ Formula.mk_imply body head
          in
          (*print_endline @@ "d: " ^ Formula.str_of phi';*)
          let senv =
            Map.Poly.to_alist @@ Map.force_merge_list [
              Map.Poly.map ~f:Logic.ExtTerm.to_old_sort uni_senv;
              Map.of_set_exn quantified_senv
            ]
          in
          if Set.is_empty ps then begin
            (*print_endline @@ LogicOld.str_of_sort_env_map LogicOld.Term.str_of_sort @@ Map.Poly.of_alist_exn senv;*)
            let phi' = (*Formula.aconv_tvar @@*) Formula.forall senv phi' in
            let c = Z3Smt.Z3interface.of_formula ctx [](*senv*) penv fenv dtenv phi' in
            Debug.print @@ lazy
              ("adding query: " ^ Formula.str_of (Evaluator.simplify_neg phi'));
            (*print_endline @@ Z3.Expr.to_string c;*)
            Some (Z3.Boolean.mk_not ctx c)
          end else begin
            let phi' = (*Formula.aconv_tvar @@*) Formula.forall senv phi' in
            let c = Z3Smt.Z3interface.of_formula ctx [](*senv*) penv fenv dtenv phi' in
            Debug.print @@ lazy
              ("adding rule: " ^ Formula.str_of (Evaluator.simplify phi'));
            Z3.Fixedpoint.add_rule solver c None; None
          end)
    in
    if false then begin
      (* make smt string *)
      let prefix = ref "" in
      let inputs =
        let reg_assert = Str.regexp "^(assert \\(.*\\)$" in
        let reg_forall = Str.regexp "^(forall " in
        Z3.Fixedpoint.to_string solver
        |> String.split_on_chars ~on:['\n']
        |> List.map ~f:(fun line ->
            if Str.string_match reg_assert line 0 then
              let matched_str = Str.matched_group 1 line in
              let line' = !prefix in
              line'
              ^
              if not @@ Str.string_match reg_forall matched_str 0 then begin
                prefix := ")\n";
                "(assert (forall () " ^ matched_str
              end else begin
                prefix := "";
                line
              end else line) in
      let reg_anno = Str.regexp "(! \\| :weight.*[0-9])" in
      let inputs = List.map inputs ~f:(fun s -> Str.global_replace reg_anno "" s) in
      let inputs = inputs @ [ !prefix ] in
      (* let inputs = inputs @ if !exists_query then [ sprintf "(assert (forall ((M Bool)) (not (%s))))" query_name ] else [] in *)
      let inputs = inputs @ [ "(check-sat)" ] in
      (* let inputs = if config.produce_proofs then
          "(set-option :produce-proofs true)" :: inputs @ ["(get-proof)"]
         else inputs in *)
      let inputs = inputs @ ["(exit)"] in
      print_endline @@ String.concat ~sep:"\n" inputs
    end;
    try
      Debug.print @@ lazy "********************";
      let solution =
        let rec loop () =
          match Z3.Fixedpoint.query solver (Z3.Boolean.mk_or ctx @@ Set.to_list qs)
          (*Z3.Fixedpoint.query_r solver
                  [List.Assoc.find_exn penv ~equal:Stdlib.(=) (Ident.Pvar query_name)]*) with
          | Z3.Solver.UNSATISFIABLE ->
            Debug.print @@ lazy "Unsatisfiable!";
            (match Z3.Fixedpoint.get_answer solver with
             | Some expr ->
               (*let expr = Z3.Expr.simplify expr None in*)
               let phi =
                 (*Debug.print @@ lazy ("Z3 solution: " ^ Z3.Expr.to_string expr);*)
                 try Z3Smt.Z3interface.formula_of [] penv dtenv expr
                 with _ -> Debug.print @@ lazy "failed conversion"; failwith "conversion"
               in
               (*Debug.print @@ lazy ("answer: " ^ Formula.str_of phi);*)
               let sol =
                 Map.of_set_exn @@
                 Set.Poly.filter_map (Formula.conjuncts_of phi) ~f:(fun phi ->
                     if Formula.is_true phi then None(*ToDo*)
                     else
                       try
                         let lhs, rhs, _ =
                           Formula.rm_quant ~forall:true phi |> snd |> Formula.let_eq
                         in
                         let pvapp, _ = Formula.let_atom @@ T_bool.let_formula lhs in
                         let pvar, _, args, _ = Atom.let_pvar_app pvapp in
                         let params = List.map args ~f:(Term.let_var >> fst) in
                         let body = Formula.aconv_tvar @@ T_bool.let_formula rhs in
                         let params = Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort params in
                         Option.return
                           (Ident.pvar_to_tvar pvar,
                            Logic.ExtTerm.mk_lambda params (Logic.ExtTerm.of_old_formula body))
                       with _ ->
                         failwith @@ "cannot get a solution from Spacer: " ^ Formula.str_of phi)
               in
               let sol =
                 Map.force_merge sol @@
                 Map.Poly.filter_mapi exi_senv ~f:(fun ~key ~data ->
                     if Map.Poly.mem sol key then None
                     else
                       let args, _ = Logic.Sort.args_ret_of data in
                       let params = Logic.sort_env_list_of_sorts args in
                       Some (Logic.ExtTerm.mk_lambda params @@ Logic.BoolTerm.mk_bool true))
               in
               (*Debug.print @@ lazy ("SyGuS solution: " ^ PCSP.Problem.str_of_sygus_solution @@ PCSP.Problem.Sat sol);*)
               Debug.print @@ lazy (CandSol.str_of @@ CandSol.make @@ Map.Poly.mapi sol ~f:(fun ~key ~data -> Map.Poly.find_exn exi_senv key, data));
               if config.check_validity &&
                  not @@ PCSP.Problem.check_valid (fun uni_senv t ->
                      let phi =
                        Logic.ExtTerm.to_old_formula (PCSP.Problem.senv_of pcsp) uni_senv
                          t []
                      in
                      (*print_endline @@ "checking " ^ Formula.str_of phi;*)
                      try Z3Smt.Z3interface.is_valid_exn ~id:None (FunEnv.mk_empty ()) phi
                      with Z3Smt.Z3interface.Unknown ->
                        Debug.print @@ lazy "a solution returned by Spacer could be wrong";
                        not config.conservative_check)
                    pcsp sol then
                 if config.solve_again_if_invalid then begin
                   Debug.print @@ lazy "a solution returned by Spacer is wrong";
                   loop ()
                 end else failwith "a solution returned by Spacer is wrong"
               else PCSP.Problem.Sat sol
             | None -> failwith "no solution returned by Z3")
          | Z3.Solver.SATISFIABLE ->
            Debug.print @@ lazy "Satisfiable!";
            (match Z3.Fixedpoint.get_answer solver with
             | Some expr ->
               Debug.print @@ lazy ("model: " ^ Z3.Expr.to_string expr);
             | None -> ());
            PCSP.Problem.Unsat
          | Z3.Solver.UNKNOWN -> PCSP.Problem.Unknown
        in loop ()
      in
      Debug.print @@ lazy "********************";
      if print_sol then print_endline (PCSP.Problem.str_of_solution solution);
      Or_error.return solution
    with
    | Z3.Error reason ->
      if String.(reason = "spacer canceled" || reason = "canceled") then
        raise PCSP.Problem.Timeout(*ToDo*)
      else begin
        Debug.print @@ lazy (sprintf "Z3 Error: %s" reason);
        Or_error.return (PCSP.Problem.Unknown)
        (* Or_error.error_string reason*)
      end
end