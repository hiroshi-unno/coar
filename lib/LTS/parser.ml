(* Reader for labelled transition systems in T2's input format.  [bv_mode]
   selects whether integer variables are read as bit-vectors; it is also
   stored in [Problem.bv_mode] for the code that runs after reading.
   [division] is how [/] is read in a file with a [BUCHI] line
   ([Problem.division]; a file without one is T2's, whose [/] truncates).  A
   syntax error becomes an [Error] carrying the source position. *)
open Core
open Common.Util
open Common.Combinator

let parse_from_lexbuf ?(division = Problem.Exact) ~bv_mode lexbuf =
  Problem.bv_mode := bv_mode;
  Problem.division := division;
  try Ok (Problem.typeinf ~bv_mode @@ T2Parser.main T2Lexer.token lexbuf) with
  | T2Parser.Error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error"
              (LexingHelper.get_position_string lexbuf))
  | Problem.Malformed error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: %s" (LexingHelper.get_position_string lexbuf) error)
  | T2Lexer.SyntaxError error ->
      Result.fail
      @@ Error.of_string
           (sprintf "%s: syntax error: %s"
              (LexingHelper.get_position_string lexbuf)
              error)

let from_file ?division ~bv_mode filename =
  In_channel.with_file filename ~f:(fun channel ->
      parse_from_lexbuf ?division ~bv_mode (Lexing.from_channel channel))

let from_string ?division ~bv_mode =
  Lexing.from_string >> parse_from_lexbuf ?division ~bv_mode
