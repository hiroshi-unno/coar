{
  open Ast.LogicOld
  open Lexing

  exception SyntaxError of string

  let update_loc (lexbuf: Lexing.lexbuf) =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\t' '\r']+     { main lexbuf }
| '\n'
| "//"[^'\n']*?'\n' { update_loc lexbuf; main lexbuf }
| "/*" { comment (lexeme_start_p lexbuf) lexbuf; main lexbuf }

| "true" { HESParser.TRUE }
| "false" { HESParser.FALSE }
| "int" { HESParser.INT }
| "bool" { HESParser.BOOL }
| "real" { HESParser.REAL }
| "=mu" { HESParser.EQFIX Predicate.Mu }
| "=nu" { HESParser.EQFIX Predicate.Nu }
| "/\\" { HESParser.AND }
| "\\/" { HESParser.OR }
| "!" | "not" { HESParser.NOT }
| "and" { HESParser.AND }
| "or" { HESParser.OR }
| "<=>" { HESParser.IFF }
| "=>" { HESParser.IMPLY }
| "-" { HESParser.MINUS }
| "+" { HESParser.ADD }
| "*" { HESParser.MULT }
| "/" | "div" { HESParser.DIV }
| "%" { HESParser.MOD }
| ">=" { HESParser.PREDSYM T_int.Geq }
| ">" { HESParser.PREDSYM T_int.Gt }
| "<=" { HESParser.PREDSYM T_int.Leq }
| "<" { HESParser.PREDSYM T_int.Lt }
| "=" { HESParser.PREDSYM T_bool.Eq }
| "!=" { HESParser.PREDSYM T_bool.Neq }
| ":" { HESParser.CORON }
| ";" { HESParser.SEMI }
| "forall" { HESParser.BINDER Forall }
| "exists" { HESParser.BINDER Exists }
| "s.t." | "where" { HESParser.WHERE }
| "." { HESParser.DOT }
| "(" { HESParser.LPAREN }
| ")" { HESParser.RPAREN }

| ['a'-'z''A'-'Z''#''!''_']['a'-'z''A'-'Z''0'-'9'''''_''#''!']*
    {
      let str = Lexing.lexeme lexbuf in
      HESParser.ID str
    }

| (('0'|['1'-'9']['0'-'9']*)'.'['0'-'9']*)
    {
      let str = Lexing.lexeme lexbuf in
      HESParser.REALL str
    }

| ('0'|['1'-'9']['0'-'9']*)
    {
      let str = Lexing.lexeme lexbuf in
      HESParser.INTL (int_of_string str)
    }

| eof { HESParser.EOF }
| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment openingpos = parse
| '\n'
    { update_loc lexbuf; comment openingpos lexbuf }
| "*/"
    { () }
| eof {
    raise
      (SyntaxError
        (Printf.sprintf
          "%d:%d:syntax error: unterminated comment."
          openingpos.pos_lnum (openingpos.pos_cnum - openingpos.pos_bol + 1)
        )
      )
  }
| _ { comment openingpos lexbuf }
