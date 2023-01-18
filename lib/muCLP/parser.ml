open Core

let typing muclp = muclp (* TODO *)

let get_position_string (lexbuf: Lexing.lexbuf) =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%d:%d"
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_from_lexbuf lexbuf =
  try
    lexbuf
    |> HESParser.toplevel HESLexer.main
    |> typing
    |> fun muclp -> Ok muclp
  with
  | HESParser.Error ->
    print_endline @@ Printf.sprintf "%s: syntax error" (get_position_string lexbuf);
    Result.fail @@ Error.of_string (Printf.sprintf "%s: syntax error" (get_position_string lexbuf))
  | HESLexer.SyntaxError error ->
    print_endline @@ Printf.sprintf "%s: syntax error" (get_position_string lexbuf);
    Result.fail @@ Error.of_string (Printf.sprintf "%s: syntax error: %s" (get_position_string lexbuf) error)

let parse_formula_from_lexbuf lexbuf =
  try
    lexbuf
    |> HESParser.formula HESLexer.main
    |> typing
    |> fun muclp -> Ok muclp
  with
  | HESParser.Error ->
    Result.fail @@ Error.of_string (Printf.sprintf "%s: syntax error" (get_position_string lexbuf))
  | HESLexer.SyntaxError error ->
    Result.fail @@ Error.of_string (Printf.sprintf "%s: syntax error: %s" (get_position_string lexbuf) error)

let from_file file =
  file
  |> In_channel.create
  |> Lexing.from_channel
  |> parse_from_lexbuf

let from_string str =
  str
  |> Lexing.from_string
  |> parse_from_lexbuf

let formula_from_string str =
  str
  |> Lexing.from_string
  |> parse_formula_from_lexbuf
