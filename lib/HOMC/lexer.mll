{
open Parser
}

let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']

rule token = parse
| space+
    { token lexbuf }
| '\n'
    { Lexing.new_line lexbuf;
      token lexbuf }
| "/*"
    { comment lexbuf; token lexbuf}
| "%BEGING"
    { BEGING }
| "%ENDG"
    { ENDG }
| "%BEGINA"
    { BEGINA }
| "%ENDA"
    { ENDA }
| "%BEGINR"
    { BEGINR }
| "%ENDR"
    { ENDR }
| "%BEGINATA"
    { BEGINATA }
| "%ENDATA"
    { ENDATA }
| "%BEGINT"
    { BEGINT }
| "%ENDT"
    { ENDT }
| "%BEGINX"
    (* A section of regular tree expression type definitions is not tokenised
       here: its text up to [%ENDX] is returned whole, with the position where
       it begins, for the type-definition reader, so that reader's errors
       name this file's lines and columns.  A [/* ... */] comment inside it is
       replaced by blanks of the same length (newlines kept), so the section
       takes this file's comments as well as the type language's [(* ... *)].
       The token's start position is reset to the [%BEGINX] keyword, which
       the sub-lexers below would otherwise have moved. *)
    { let start = Lexing.lexeme_start_p lexbuf in
      let body = lexbuf.Lexing.lex_curr_p in
      let buf = Buffer.create 1024 in
      xtypes buf lexbuf;
      lexbuf.Lexing.lex_start_p <- start;
      XTYPES (Buffer.contents buf, body) }
(*| "fail"
    { FAIL }*)
| "case"
    { CASE }
| "of"
    { OF }
| "|"
    { BAR }
| "coerce"
    { COERCE }
| "copy"
    { COPY }
| "gen"
    { GEN }
| "true"
    { TRUE }
| "false"
    { FALSE }
| "/\\"
    { AND }
| "\\/"
    { OR }
| (lower|'_'(digit|lower|upper|'_')) (digit|lower|upper|'_')* (''')*
    { LIDENT(Lexing.lexeme lexbuf) }
| upper (digit|lower|upper|'_')* (''')*
    { UIDENT(Lexing.lexeme lexbuf) }
| digit+ { let str = Lexing.lexeme lexbuf in
           INT (int_of_string str) }
| '.'
    { PERIOD }
| ','
    { COMMA }
| ':'
    { COLON }
| '='
    { EQUAL }
| "->"
    { MINUS_RANGLE }
| "=>"
    { EQUAL_RANGLE }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| eof
    { EOF }
| _
    { failwith ("unknown token: " ^ Lexing.lexeme lexbuf) }
and xtypes buf = parse
| "%ENDX"
    { () }
| '\n'
    { Lexing.new_line lexbuf;
      Buffer.add_char buf '\n';
      xtypes buf lexbuf }
| "/*"
    { Buffer.add_string buf "  ";
      xcomment buf lexbuf;
      xtypes buf lexbuf }
| eof
    { failwith "unterminated %BEGINX section (no %ENDX)" }
| _
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      xtypes buf lexbuf }
and xcomment buf = parse
| '\n'
    { Lexing.new_line lexbuf;
      Buffer.add_char buf '\n';
      xcomment buf lexbuf }
| "*/"
    { Buffer.add_string buf "  " }
| "/*"
    { Buffer.add_string buf "  ";
      xcomment buf lexbuf;
      xcomment buf lexbuf }
| eof
    { failwith "unterminated comment" }
| _
    { Buffer.add_char buf ' ';
      xcomment buf lexbuf }
and comment = parse
| '\n'
    { Lexing.new_line lexbuf;
      comment lexbuf }
| "*/"
    { () }
| "/*"
    { comment lexbuf; comment lexbuf }
| eof
    { failwith "unterminated comment" }
| _
    { comment lexbuf }
