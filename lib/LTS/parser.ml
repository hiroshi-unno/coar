open Core

let get_position_string (lexbuf: Lexing.lexbuf) =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%d:%d"
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_from_lexbuf lexbuf =
  try
    lexbuf
    |> T2Parser.main T2Lexer.token
    |> fun lts -> Ok lts
  with
  | T2Parser.Error ->
    Result.fail @@ Error.of_string (Printf.sprintf "%s: syntax error" (get_position_string lexbuf))
  (*| T2Lexer.SyntaxError error ->
    Result.fail @@ Error.of_string (Printf.sprintf "%s: syntax error: %s" (get_position_string lexbuf) error)*)

let from_file file =
  file
  |> In_channel.create
  |> Lexing.from_channel
  |> parse_from_lexbuf

let from_string str =
  str
  |> Lexing.from_string
  |> parse_from_lexbuf
