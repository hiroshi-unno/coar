{
  open Parser

  (* Keep a quoted identifier distinct from a literal or reserved token before
     the S-expression reader performs grammar dispatch and alpha substitution.
     Ordinary quoted/simple symbols still share their existing canonical name.
     The octal prefix is an existing reader extension, not SMT-LIB syntax. *)
  let quoted_atom str =
    let name = String.sub str 1 (String.length str - 2) in
    let starts_literal =
      String.length name > 0 &&
      ((name.[0] >= '0' && name.[0] <= '9') || name.[0] = '"' || name.[0] = ':' ||
       (String.length name >= 2 && name.[0] = '#' &&
        (name.[1] = 'x' || name.[1] = 'b' || name.[1] = 'o')))
    in
    let reserved =
      List.mem name
        [ "BINARY"; "DECIMAL"; "HEXADECIMAL"; "NUMERAL"; "STRING";
          "_"; "!"; "as"; "lambda"; "let"; "exists"; "forall"; "match"; "par";
          "assert"; "check-sat"; "check-sat-assuming"; "declare-const";
          "declare-datatype"; "declare-datatypes"; "declare-fun";
          "declare-sort"; "declare-sort-parameter"; "define-const";
          "define-fun"; "define-fun-rec"; "define-funs-rec"; "define-sort";
          "echo"; "exit"; "get-assertions"; "get-assignment"; "get-info";
          "get-model"; "get-option"; "get-proof"; "get-unsat-assumptions";
          "get-unsat-core"; "get-value"; "pop"; "push"; "reset";
          "reset-assertions"; "set-info"; "set-logic"; "set-option" ]
    in
    if starts_literal || reserved then str else name
}

let space = [' ' '\t']
let newline = '\r' | '\n' | "\r\n"

rule token = parse
| space+ { token lexbuf }
| newline { Lexing.new_line lexbuf; token lexbuf }
| ';' { line_comment lexbuf; token lexbuf }
| "#|" { block_comment lexbuf; token lexbuf }
| '|' ("\\|" | [^'|'])* '|' {
    let str = Lexing.lexeme lexbuf in
    ATOM(quoted_atom str)
  }
(*for chc-comp19/lia-lin-arr/arrqua_30.smt2 and arrqua_31.smt2*)
| "\\\\\\\\\\" ([^'\\'])* "\\\\\\\\\\" {
  let str = Lexing.lexeme lexbuf in
  ATOM(String.sub str 5 (String.length str - 10) )
}
(* SMT-LIB's only escape inside a string literal is a DOUBLED quotation mark,
   which denotes one quotation mark and does not end the literal.  Without the
   first alternative the literal ended at the first of the two, so a string
   containing a quote was split into pieces and `"a b""c d"` became two atoms.
   The backslash-quote alternative is not SMT-LIB and is kept because files here
   have used it. *)
| '"' ("\"\"" | "\\\"" | [^'"'])* '"' {
    ATOM(Lexing.lexeme lexbuf)
  }
| [^' ' '\t' '\r' '\n' '(' ')' ';']+ {
    ATOM(Lexing.lexeme lexbuf)
  }
| '(' { LPAREN }
| ')' { RPAREN }
| eof { EOF }
| _ {
  let st = Lexing.lexeme_start_p lexbuf in
  let en = Lexing.lexeme_end_p lexbuf in
  Format.printf
    "File \"%s\", line %d"
    st.Lexing.pos_fname
    st.Lexing.pos_lnum;
  Format.printf
    ", unknown token %s near characters %d-%d"
    (Lexing.lexeme lexbuf)
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
    (en.Lexing.pos_cnum - en.Lexing.pos_bol);
    failwith "lexical error"
    }

and line_comment = parse
  | newline { Lexing.new_line lexbuf }
  | eof { () }
  | _ { line_comment lexbuf }

and block_comment = parse
  | "|#" { () }
  | "#|" { block_comment lexbuf; block_comment lexbuf }
  | newline { Lexing.new_line lexbuf; block_comment lexbuf }
  | eof { () }
  | _ { block_comment lexbuf }
