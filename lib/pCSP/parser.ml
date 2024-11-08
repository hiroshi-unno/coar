open Core
open Common.Ext
open Ast
open Ast.Logic

let from_smt2_file ~print ~inline ?(skolem_pred = false)
    ?(uni_senv = Map.Poly.empty) ?(exi_senv = Map.Poly.empty)
    ?(kind_map = Map.Poly.empty) ?(fenv = Map.Poly.empty)
    ?(dtenv = Map.Poly.empty) filename =
  let ic = filename |> In_channel.create in
  let lexbuf = Lexing.from_channel ic in
  let phis, envs =
    lexbuf
    |> SMT.(Parser.program Lexer.token)
    |> SMT.Smtlib2.toplevel ~print ~inline []
         { uni_senv; exi_senv; kind_map; fenv; dtenv }
  in
  In_channel.close ic;
  let phis =
    Typeinf.typeinf ~print ~to_sus:true ~instantiate_num_to_int:true phis
  in
  Problem.make ~skolem_pred phis envs

let from_gzipped_smt2_file ~print ~inline ?(skolem_pred = false)
    ?(uni_senv = Map.Poly.empty) ?(exi_senv = Map.Poly.empty)
    ?(kind_map = Map.Poly.empty) ?(fenv = Map.Poly.empty)
    ?(dtenv = Map.Poly.empty) filename =
  let ic = filename |> Gzip.open_in in
  let lexbuf = Lexing.from_function (fun b len -> Gzip.input ic b 0 len) in
  let phis, envs =
    lexbuf
    |> SMT.(Parser.program Lexer.token)
    |> SMT.Smtlib2.toplevel ~print ~inline []
         { uni_senv; exi_senv; kind_map; fenv; dtenv }
  in
  Gzip.close_in ic;
  let phis =
    Typeinf.typeinf ~print ~to_sus:true ~instantiate_num_to_int:true phis
  in
  Problem.make ~skolem_pred phis envs

let from_clp_file filename =
  let ic = filename |> In_channel.create in
  let lexbuf = Lexing.from_channel ic in
  let phis =
    lexbuf
    |> LPParser.parser_main_logic_program LPLexer.token
    |> List.map ~f:(fun (head, body) -> LogicOld.Formula.mk_imply body head)
  in
  In_channel.close ic;
  let params =
    let psenv =
      Set.Poly.union_list @@ List.map phis ~f:LogicOld.Formula.pred_sort_env_of
    in
    let kind_map =
      (* ToDo *)
      let fnpvs =
        Set.Poly.filter_map psenv ~f:(fun (Ident.Pvar n, _) ->
            if String.is_prefix ~prefix:"FN_" n then Some (Ident.Tvar n)
            else None)
      in
      let wfpvs =
        Set.Poly.filter_map psenv ~f:(fun (Ident.Pvar n, _) ->
            if String.is_prefix ~prefix:"WF_" n then Some (Ident.Tvar n)
            else None)
      in
      Map.Poly.empty
      |> Kind.add_kinds fnpvs Kind.FN
      |> Kind.add_kinds wfpvs Kind.WF
    in
    Params.make ~kind_map @@ of_old_sort_env_map @@ Map.of_set_exn
    @@ LogicOld.Term.pred_to_sort_env psenv
  in
  (*Problem.normalize @@*)
  Problem.of_formulas ~params
  @@ Set.Poly.of_list
  @@ List.rev_map phis ~f:(fun phi ->
         ( Map.of_set_exn @@ Logic.of_old_sort_env_set
           @@ LogicOld.Formula.term_sort_env_of phi,
           ExtTerm.of_old_formula phi ))
