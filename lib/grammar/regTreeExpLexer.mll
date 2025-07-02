{
open Core
open RegTreeExpParser
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
| "(*"
    { comment lexbuf; token lexbuf}
| "type"
    { TYPE }
| (lower|'_'(digit|lower|upper|'_')) (digit|lower|upper|'_')* (''')*
    { LIDENT (Lexing.lexeme lexbuf) }
| upper (digit|lower|upper|'_')* (''')*
    { UIDENT (Lexing.lexeme lexbuf) }
| '='
    { EQUAL }
| '|'
    { BAR }
| ','
    { COMMA }
| '*'
    { AST }
| '?'
    { QUESTION }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| '['
    { LBRACKET }
| ']'
    { RBRACKET }
| eof
    { EOF }
| _
    { failwith ("unknown token: " ^ Lexing.lexeme lexbuf) }
and comment = parse
| '\n'
    { Lexing.new_line lexbuf;
      comment lexbuf }
| "*)"
    { () }
| "(*"
    { comment lexbuf; comment lexbuf }
| eof
    { failwith "unterminated comment" }
| _
    { comment lexbuf }
