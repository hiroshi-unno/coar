open Core
open Common.Util.LexingHelper
open Common.Combinator
open Problem

let parse_muclp_from_lexbuf ~print lexbuf =
  try Ok (typeinf ~print @@ HESParser.toplevel HESLexer.main lexbuf) with
  | HESParser.Error ->
      print_endline @@ sprintf "%s: syntax error" (get_position_string lexbuf);
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error" (get_position_string lexbuf))
  | HESLexer.SyntaxError error ->
      print_endline @@ sprintf "%s: syntax error" (get_position_string lexbuf);
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s" (get_position_string lexbuf) error)

let parse_query_from_lexbuf ~print lexbuf =
  try
    Ok
      (Ast.Typeinf.typeinf_formula ~print ~instantiate_num_to_int:true
      @@ HESParser.formula HESLexer.main lexbuf)
  with
  | HESParser.Error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error" (get_position_string lexbuf))
  | HESLexer.SyntaxError error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s" (get_position_string lexbuf) error)

let muclp_from_file ~print =
  In_channel.create >> Lexing.from_channel >> parse_muclp_from_lexbuf ~print

let muclp_from_string ~print =
  Lexing.from_string >> parse_muclp_from_lexbuf ~print

let query_from_string ~print =
  Lexing.from_string >> parse_query_from_lexbuf ~print
