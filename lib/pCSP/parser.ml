open Core
open Common.Ext
open Common.Util
open Ast
open Ast.Logic

let from_smt2_file ~print ~inline ?(skolem_pred = false)
    ?(uni_senv = Map.Poly.empty) ?(exi_senv = Map.Poly.empty)
    ?(kind_map = Map.Poly.empty) ?(fenv = Map.Poly.empty)
    ?(dtenv = Map.Poly.empty) filename =
  let sexps =
    let ic = In_channel.create filename in
    let lexbuf = Lexing.from_channel ic in
    Lexing.set_filename lexbuf filename;
    try
      let res = SMT.Parser.program SMT.Lexer.token lexbuf in
      In_channel.close ic;
      res
    with e ->
      LexingHelper.print_error_information lexbuf;
      In_channel.close ic;
      raise e
  in
  let phis, envs =
    SMT.Smtlib2.toplevel ~print ~inline []
      { uni_senv; exi_senv; kind_map; fenv; dtenv }
      sexps
  in
  let phis =
    Typeinf.typeinf ~print ~default:(Some Ast.LogicOld.T_int.SInt (*ToDo*))
      ~to_sus:true phis
  in
  Problem.make ~skolem_pred phis envs

let from_gzipped_smt2_file ~print ~inline ?(skolem_pred = false)
    ?(uni_senv = Map.Poly.empty) ?(exi_senv = Map.Poly.empty)
    ?(kind_map = Map.Poly.empty) ?(fenv = Map.Poly.empty)
    ?(dtenv = Map.Poly.empty) filename =
  let sexps =
    let ic = Gzip.open_in filename in
    let lexbuf = Lexing.from_function (fun b len -> Gzip.input ic b 0 len) in
    Lexing.set_filename lexbuf filename;
    try
      let res = SMT.Parser.program SMT.Lexer.token lexbuf in
      Gzip.close_in ic;
      res
    with e ->
      LexingHelper.print_error_information lexbuf;
      Gzip.close_in ic;
      raise e
  in
  let phis, envs =
    SMT.Smtlib2.toplevel ~print ~inline []
      { uni_senv; exi_senv; kind_map; fenv; dtenv }
      sexps
  in
  let phis =
    Typeinf.typeinf ~print ~default:(Some Ast.LogicOld.T_int.SInt (*ToDo*))
      ~to_sus:true phis
  in
  Problem.make ~skolem_pred phis envs

let from_clp_file ~print filename =
  let res =
    let ic = In_channel.create filename in
    let lexbuf = Lexing.from_channel ic in
    Lexing.set_filename lexbuf filename;
    try
      let res = LPParser.parser_main_logic_program LPLexer.token lexbuf in
      In_channel.close ic;
      res
    with e ->
      LexingHelper.print_error_information lexbuf;
      In_channel.close ic;
      raise e
  in
  let phis =
    List.map res ~f:(fun (head, body) -> LogicOld.Formula.mk_imply body head)
  in
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
    try
      Params.make ~kind_map @@ of_old_sort_env_map @@ Map.of_set_exn
      @@ LogicOld.Term.pred_to_sort_env psenv
    with _ ->
      print
      @@ lazy
           (sprintf "pred sort env:\n%s"
           @@ LogicOld.str_of_pred_sort_env_set LogicOld.Term.str_of_sort psenv
           );
      failwith
        "The sort of a predicate variable is defined multiple times in the \
         environment, causing a conflict."
  in
  (*Problem.normalize @@*)
  Problem.of_formulas ~params
  @@ Set.Poly.of_list
  @@ List.rev_map phis ~f:(fun phi ->
         ( Map.of_set_exn @@ Logic.of_old_sort_env_set
           @@ LogicOld.Formula.term_sort_env_of phi,
           ExtTerm.of_old_formula phi ))
