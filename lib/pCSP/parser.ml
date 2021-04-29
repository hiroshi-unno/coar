open Core
open Common.Util
open Ast
open Logic

let from_smt2_file ?(skolem_pred=false) file =
  let open Or_error in
  file
  |> In_channel.create
  |> Lexing.from_channel
  |> SMT.Parser.program SMT.Lexer.token
  |> SMT.Smtlib2.toplevel >>= fun (phis, _, pvs, fenv, dtenv) ->
  (* print_endline "before typeinf:";
     List.iter phis ~f:(fun phi -> print_endline (LogicOld.Formula.str_of phi)); *)
  let phis = List.map phis ~f:Typeinf.typeinf in
  (* print_endline "after typeinf:";
     List.iter phis ~f:(fun phi -> print_endline (LogicOld.Formula.str_of phi)); *)
  let dummy_sus_senv = Map.Poly.fold dtenv ~init:([]) ~f:(
      fun  ~key:name ~data:dt senv -> 
        if LogicOld.Datatype.is_undef dt then begin
          ((Ident.Tvar("dummy_" ^ name)),
           (LogicOld.T_dt.SUS(name, LogicOld.Datatype.args_of dt)))::senv
        end else senv      
    ) in
  LogicOld.dummy_term_senv := LogicOld.SortEnv.of_list dummy_sus_senv;
  let exi_senv = 
    pvs
    |> Set.Poly.map ~f:(fun (Ident.Pvar n, sargs) ->
        (Ident.Tvar n,
         Sort.mk_fun (List.map sargs ~f:ExtTerm.of_old_sort @ [ExtTerm.SBool])))
    |> Logic.SortMap.of_set
  in
  Ok (if skolem_pred then
        List.rev_map phis ~f:(fun phi ->
            let senv, fsenv, phi = LogicOld.Formula.skolemize_pred @@ LogicOld.Formula.nnf_of phi in
            Logic.SortMap.of_set @@ Set.Poly.of_list @@ List.map fsenv ~f:(fun (x, sort) -> x, Logic.ExtTerm.of_old_sort sort),
            (Logic.SortMap.of_old_sort_map ExtTerm.of_old_sort senv, ExtTerm.of_old_formula phi))
        |> List.unzip
        |> (fun (fsenvs, phis) ->
            let fsenvs = fsenvs |> List.map ~f:(Map.change_keys ~f:(fun (Ident.Pvar x) -> Ident.Tvar x)) in
            let fnpvs = Set.Poly.of_list @@ List.concat_map ~f:Map.Poly.keys fsenvs in
            Set.Poly.of_list phis
            |> Problem.of_formulas ~params:(Params.make ~fenv ~fnpvs (Logic.SortMap.merge_list (exi_senv :: fsenvs)))
            |> Problem.update_params_dtenv)
      else
        List.rev_map phis ~f:(fun phi ->
            let senv, fsenv, phi = LogicOld.Formula.skolemize_fun @@ LogicOld.Formula.nnf_of phi in
            Logic.SortMap.of_set @@ Set.Poly.of_list @@ List.map fsenv ~f:(fun (x, sort) -> x, Logic.ExtTerm.of_old_sort sort),
            (Logic.SortMap.of_old_sort_map ExtTerm.of_old_sort senv, ExtTerm.of_old_formula phi))
        |> List.unzip
        |> (fun (fsenvs, phis) ->
            Set.Poly.of_list phis
            |> Problem.of_formulas ~params:(Params.make ~fenv (Logic.SortMap.merge_list (exi_senv :: fsenvs)))
            |> Problem.update_params_dtenv))

let from_clp_file file =
  file
  |> In_channel.create
  |> Lexing.from_channel
  |> LPParser.parser_main_logic_program LPLexer.token
  |> List.map ~f:(fun (hd, body) -> LogicOld.Formula.mk_imply body hd)
  |> (fun phis ->
      (* ToDo *)
      let pvs = Set.Poly.union_list @@ List.map phis ~f:LogicOld.Formula.pred_sort_env_of in
      let exi_senv =
        pvs
        |> Set.Poly.map ~f:(fun (Ident.Pvar n, sargs) ->
            (Ident.Tvar n,
             Sort.mk_fun (List.map sargs ~f:ExtTerm.of_old_sort @ [ExtTerm.SBool])))
        |> Logic.SortMap.of_set
      in
      let wfpvs = Set.Poly.filter_map pvs ~f:(fun (Ident.Pvar n, _) ->
          if String.is_prefix ~prefix:"WF_" @@ n then Some (Ident.Tvar n) else None) in
      let fnpvs = Set.Poly.filter_map pvs ~f:(fun (Ident.Pvar n, _) ->
          if String.is_prefix ~prefix:"FN_" @@ n then Some (Ident.Tvar n) else None) in
      let formulas = Set.Poly.of_list @@ List.rev_map phis ~f:(fun phi ->
          let uni_senv = LogicOld.Formula.term_sort_env_of phi in
          Logic.SortMap.of_set @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind uni_senv,
          ExtTerm.of_old_formula phi) in
      Ok (Problem.of_formulas ~params:(Params.make ~wfpvs ~fnpvs exi_senv) formulas))
