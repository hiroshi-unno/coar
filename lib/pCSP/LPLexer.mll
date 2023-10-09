{
  open LPParser

  (** Logic Program Lexer *)
}

let space = [' ' '\t']
let newline = '\r' | '\n' | "\r\n"
let digit = ['0'-'9']
let lalpha = ['A'-'Z']
let salpha = ['a'-'z']
let alpha = lalpha | salpha
let operator = '\\' | '+' | '/'
let ident_char1 = salpha | '\'' | '_'
let ident_char2 = ident_char1 | digit
let ident_pvar1 = lalpha
let ident_pvar2 = ident_pvar1 | ident_char2

rule token = parse
| space+ { token lexbuf }
| newline { Lexing.new_line lexbuf; token lexbuf }

| digit+
  { let str = Lexing.lexeme lexbuf in
    INT (Z.of_string str) }
| ":=" { ASSUME }
| ":-" { DECLARE }
| "?-" { QUERY }
| '=' { EQ }
| "\\=" { NOTEQ }
| "<>" { NOTEQ }
| '!' { NOT }
| "and" { AND }
| "or" { OR }
| "not" { NOT }
| '>' { GT }
| '<' { LT }
| ">=" { GEQ }
| "<=" { LEQ }
| '.' { DOT }
| ',' { COMMA }
| ':' { COLON }
| "bot" { BOT }
| "top" { TOP }
| "false" { FALSE }
| "true" { TRUE }
| "bool" { BOOL }

(* Quantifiers *)
| "exists" { EXISTS }

| '+' { PLUS }
| '-' { MINUS }
| '*' { TIMES }
| '/' { DIV }
| '%' { MOD }

| '(' { LPAREN }
| ')' { RPAREN }

| ident_char1 ident_char2* { VAR(Lexing.lexeme lexbuf) }
| ident_pvar1 ident_pvar2* { PVAR(Lexing.lexeme lexbuf) }

| eof { EOF }

| "(*" { comment lexbuf; token lexbuf }
| "/*" { comment lexbuf; token lexbuf }
| "//" { line_comment lexbuf; token lexbuf }
| '%' { line_comment lexbuf; token lexbuf }

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
and comment = parse
  | '\n'
      { Lexing.new_line lexbuf;
        comment lexbuf }
  | "*)"
      { () }
  | "*/"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | "/*"
      { comment lexbuf; comment lexbuf }
  | eof
      { failwith "unterminated comment" }
  | _
      { comment lexbuf }

and line_comment = parse
  | '\n' { Lexing.new_line lexbuf }
  | eof { () }
  | _ { line_comment lexbuf }
