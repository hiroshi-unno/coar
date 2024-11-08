{
  open Common.Util
  open T2Parser

  exception SyntaxError of string

  let float_of_string_safe s =
    try Q.of_string s with _ -> raise (SyntaxError ("Invalid float: " ^ s))
}

let space = ' ' | '\t'
let newline = '\r' | '\n' | "\r\n"
let digit = ['0'-'9']
let alpha = ['A'-'Z' 'a'-'z']
(*let operator = '+' | '-' | '*' | '/' | '%'
let comp = "==" | ">=" | '<' | "<=" | '<'*)

rule token = parse
| "START" { START }
| "ERROR" { ERROR }
| "FROM" { FROM }
| "TO" { TO }
| "AT" { AT }
| "CUTPOINT" { CUTPOINT }
| "SHADOW" { SHADOW }
| ':' { COLON }
| ';' { SEMICOLON }
| ',' { COMMA }
| "skip" { SKIP }
| "assume" { ASSUME }

| "int2real" { INT_TO_REAL }
| "real2int" { REAL_TO_INT }

| "nondet" { NONDET }

| "shl" { SHL }
| "lshr" { LSHR }
| "ashr" { ASHR }
| "or" { BITOR }
| "and" { BITAND }

| "const_array" { CONST_ARRAY }
| "select_array" { SELECT_ARRAY }
| "store_array" { STORE_ARRAY }
| "select_tuple" { SELECT_TUPLE }
| "constr_tuple" { CONSTR_TUPLE }

| digit+ { INT (Lexing.lexeme lexbuf |> int_of_string) }
| (alpha | '_') (digit | alpha | '_' | '.')* ('!' digit+)? { VAR (Lexing.lexeme lexbuf) }

| '\'' ['a'-'z' 'A'-'Z' '0'-'9'] '\''
  { CHAR (Lexing.lexeme_char lexbuf 1) }
| '\'' '\\' 'n' '\''
  { CHAR '\n' }
| '\'' '\\' 't' '\''
  { CHAR '\t' }
| '\'' '\\' 'r' '\''
  { CHAR '\r' }
| '\'' '\\' '\\' '\''
  { CHAR '\\' }
| '\'' '\\' '\'' '\''
  { CHAR '\'' }
| '\'' '\\' '\"' '\''
  { CHAR '\"' }
| '\'' '\\' '0' '\''
  { CHAR '\000' } (* NULL *)
| '\'' '\\' 'x' ['0'-'9''a'-'f''A'-'F']+ '\''
  { CHAR (char_of_int (int_of_string ("0x" ^ Lexing.lexeme lexbuf))) }
| '\'' '\\' ['0'-'7']+ '\''
  { CHAR (char_of_int (int_of_string ("0" ^ Lexing.lexeme lexbuf))) }

| ['0'-'9']+ '.' ['0'-'9']* ('e' | 'E') ('+' | '-')? ['0'-'9']+
  { FLOAT (float_of_string_safe @@ Lexing.lexeme lexbuf) }
| ['0'-'9']+ '.' ['0'-'9']*
  { FLOAT (float_of_string_safe @@ Lexing.lexeme lexbuf) }
| '.' ['0'-'9']+ ('e' | 'E') ('+' | '-')? ['0'-'9']+
  { FLOAT (float_of_string_safe @@ Lexing.lexeme lexbuf) }
| ['0'-'9']+ ('e' | 'E') ('+' | '-')? ['0'-'9']+
  { FLOAT (float_of_string_safe @@ Lexing.lexeme lexbuf) }

| '"' [^'"']* '"' { STRING }
| ":=" { SUBST }
| '(' { LPAREN }
| ')' { RPAREN }
| space { token lexbuf }
| newline | "//" [^'\n']* newline { LexingHelper.update_loc lexbuf; token lexbuf }

| '+' { PLUS }
| '-' { MINUS }
| '*' { TIMES }
| '/' { DIV }
| '%' { MOD }
| "==" { EQ }
| "!=" { NEQ }
| '>' { GT }
| '<' { LT }
| ">=" { GEQ }
| "<=" { LEQ }
| "&&" | "/\\" { AND }
| "||" | "\\/" { OR }
| "!" { NOT }

| eof {  EOF }
| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
