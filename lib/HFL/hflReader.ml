(* Reading an HES in one of the tools' dialects.

   [parse ~dialect text] reads [text] with the union grammar and then refuses
   every construct the dialect's own lexer or parser does not accept, naming
   it; so a file of dialect [d] is either read as tool [d] reads it or refused.
   The constructs each dialect lacks were read from the tools' sources
   (lexer.mll and parser.mly of ReTHFL at cca07d6cef, hflmc2 at 79e2095815 and
   MuHFL at 5fd3a1b6d9):
   - ReTHFL: no [exists], [not]/[!], [=>], [<=>], [/=], ASCII [=m]/[=u], and no
     ['] in identifiers;
   - hflmc2: in addition no [forall], no [%], and one variable per lambda;
   - MuHFL: no [%ENV] section and no [%] (its lexer has no rule for [%],
     although its parser has the token).
   The result is typed ([HflTyping.infer]): every invariant listed in
   [HflSyntax] holds of it.  Integer [/] and [%] are read as truncating
   division and remainder for every dialect (the tools leave the rounding
   unsettled between their evaluator and their SMT printer; the formats come
   from OCaml programs, whose [/] and [mod] truncate). *)

open Core
open HflSyntax

exception Refused of string

let lacks = function
  | Rethfl -> [ "exists"; "not"; "=>"; "<=>"; "/="; "=m"; "=u"; "'" ]
  | Hflmc2 ->
      [
        "forall";
        "exists";
        "%";
        "not";
        "=>";
        "<=>";
        "/=";
        "=m";
        "=u";
        "'";
        "multi-variable lambda";
      ]
  | Muhfl -> [ "%ENV"; "%" ]
  | Coar -> []

let parse_untyped ~dialect ?(filename = "") text =
  HflParseState.reset ();
  let lexbuf = Lexing.from_string text in
  Lexing.set_filename lexbuf filename;
  let pos () =
    let p = lexbuf.Lexing.lex_curr_p in
    sprintf "%s:%d:%d" filename p.pos_lnum (p.pos_cnum - p.pos_bol)
  in
  let eqns =
    try HflParser.main HflLexer.token lexbuf with
    | HflParser.Error -> raise (Refused (sprintf "%s: syntax error" (pos ())))
    | HflLexer.Error msg -> raise (Refused (sprintf "%s: %s" (pos ()) msg))
    | HflNeg.Refused msg -> raise (Refused (sprintf "%s: %s" (pos ()) msg))
  in
  let seen = !HflParseState.seen in
  (match
     List.filter (lacks dialect) ~f:(List.mem seen ~equal:String.equal)
   with
  | [] -> ()
  | constructs ->
      raise
        (Refused
           (sprintf "%s: the %s dialect has no %s" filename
              (string_of_dialect dialect)
              (String.concat ~sep:", " constructs))));
  {
    eqns;
    closure = [];
    env_ignored = List.mem seen "%ENV" ~equal:String.equal;
  }

let parse ~dialect ?filename text =
  let hes = parse_untyped ~dialect ?filename text in
  try HflTyping.infer hes
  with HflTyping.Error msg ->
    raise
      (Refused
         (sprintf "%s: %s" (Option.value filename ~default:"") msg))

let from_file ~dialect filename =
  parse ~dialect ~filename (In_channel.read_all filename)
