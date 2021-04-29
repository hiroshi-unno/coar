{
  open Parser
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
    ATOM(String.sub str 1 (String.length str - 2) )
  }
(*for chc-comp19/lia-lin-arr/arrqua_30.smt2 and arrqua_31.smt2*)
| "\\\\\\\\\\" ([^'\\'])* "\\\\\\\\\\" {
  let str = Lexing.lexeme lexbuf in
  ATOM(String.sub str 5 (String.length str - 10) )
}
| '"' ("\\\"" | [^'"'])* '"' {
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