open Core
open Common.Ext
open Ast
open Ast.Logic

let from_smt2_file ?(skolem_pred=false) file =
  let open Or_error in
  file
  |> In_channel.create
  |> Lexing.from_channel
  |> SMT.Parser.program SMT.Lexer.token
  |> SMT.Smtlib2.toplevel >>= fun (phis, tvs, pvs, fnp_env, wfp_env, fenv, dtenv) ->
  let phis = Typeinf.typeinf ~to_sus:true phis in
  let res = Problem.make ~skolem_pred (phis, tvs, pvs, fnp_env, wfp_env, fenv, dtenv) in
  Ok res

let from_clp_file file =
  file
  |> In_channel.create
  |> Lexing.from_channel
  |> LPParser.parser_main_logic_program LPLexer.token
  |> List.map ~f:(fun (head, body) -> LogicOld.Formula.mk_imply body head)
  |> (fun phis ->
      let params =
        let pvs = Set.Poly.union_list @@ List.map phis ~f:LogicOld.Formula.pred_sort_env_of in
        (* ToDo *)
        let fnpvs = Set.Poly.filter_map pvs ~f:(fun (Ident.Pvar n, _) ->
            if String.is_prefix ~prefix:"FN_" @@ n then Some (Ident.Tvar n) else None) in
        let wfpvs = Set.Poly.filter_map pvs ~f:(fun (Ident.Pvar n, _) ->
            if String.is_prefix ~prefix:"WF_" @@ n then Some (Ident.Tvar n) else None) in
        let exi_senv =
          pvs
          |> Set.Poly.map ~f:(fun (Ident.Pvar n, sargs) ->
              (Ident.Tvar n,
               Sort.mk_fun (List.map sargs ~f:ExtTerm.of_old_sort @ [ExtTerm.SBool])))
          |> Map.of_set_exn
        in
        Params.make ~fnpvs ~wfpvs exi_senv
      in
      let res =
        (*Problem.normalize @@*)
        Problem.of_formulas ~params @@
        Set.Poly.of_list @@
        List.rev_map phis ~f:(fun phi ->
            let uni_senv = LogicOld.Formula.term_sort_env_of phi in
            Map.of_set_exn @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind uni_senv,
            ExtTerm.of_old_formula phi)
      in
      Ok res)

