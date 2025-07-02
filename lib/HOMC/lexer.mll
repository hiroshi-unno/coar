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
