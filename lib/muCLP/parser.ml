open Core
open Common.Util.LexingHelper
open Common.Combinator
open Ast.LogicOld
open Problem

let typing ~print muclp =
  { preds =
      List.map muclp.preds ~f:(fun (fix, pvar, args, phi) ->
          let _, phi, _ =
            Formula.mk_forall args phi
            |> Ast.Typeinf.typeinf_formula ~print ~instantiate_num_to_int:true
            |> Formula.let_forall
          in
          fix, pvar, args, phi);
    query = Ast.Typeinf.typeinf_formula ~print ~instantiate_num_to_int:true muclp.query }

let parse_from_lexbuf ~print lexbuf =
  try Ok (typing ~print @@ HESParser.toplevel HESLexer.main lexbuf)
  with
  | HESParser.Error ->
    print_endline @@ sprintf "%s: syntax error" (get_position_string lexbuf);
    Result.fail @@ Error.of_string (sprintf "%s: syntax error" (get_position_string lexbuf))
  | HESLexer.SyntaxError error ->
    print_endline @@ sprintf "%s: syntax error" (get_position_string lexbuf);
    Result.fail @@ Error.of_string (sprintf "%s: syntax error: %s" (get_position_string lexbuf) error)

let parse_formula_from_lexbuf ~print lexbuf =
  try
    Ok (Ast.Typeinf.typeinf_formula ~print ~instantiate_num_to_int:true @@
        HESParser.formula HESLexer.main lexbuf)
  with
  | HESParser.Error ->
    Result.fail @@ Error.of_string (sprintf "%s: syntax error" (get_position_string lexbuf))
  | HESLexer.SyntaxError error ->
    Result.fail @@ Error.of_string (sprintf "%s: syntax error: %s" (get_position_string lexbuf) error)

let from_file ~print = In_channel.create >> Lexing.from_channel >> parse_from_lexbuf ~print
let from_string ~print = Lexing.from_string >> parse_from_lexbuf ~print
let formula_from_string ~print = Lexing.from_string >> parse_formula_from_lexbuf ~print
