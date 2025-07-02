open Core
open Common.Util
open Common.Combinator

let parse_from_lexbuf lexbuf =
  try Ok (Problem.typeinf @@ T2Parser.main T2Lexer.token lexbuf) with
  | T2Parser.Error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error"
              (LexingHelper.get_position_string lexbuf))
  | T2Lexer.SyntaxError error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error)

let from_file = In_channel.create >> Lexing.from_channel >> parse_from_lexbuf
let from_string = Lexing.from_string >> parse_from_lexbuf
