open Core
open Common.Util
open Common.Combinator

let parse_from_lexbuf ~bv_mode lexbuf =
  Problem.bv_mode := bv_mode;
  try Ok (Problem.typeinf ~bv_mode @@ T2Parser.main T2Lexer.token lexbuf) with
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

let from_file ~bv_mode =
  In_channel.create >> Lexing.from_channel >> parse_from_lexbuf ~bv_mode

let from_string ~bv_mode = Lexing.from_string >> parse_from_lexbuf ~bv_mode
