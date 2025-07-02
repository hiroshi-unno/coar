{
  open Core
  open Ast.LogicOld

  exception SyntaxError of string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\t' '\r']+ { main lexbuf }
| '\n'
| "//"[^'\n']*?'\n' { Lexing.new_line lexbuf; main lexbuf }
| "/*" { comment (Lexing.lexeme_start_p lexbuf) lexbuf; main lexbuf }

| "true" { Parser.TRUE }
| "false" { Parser.FALSE }
| "int" { Parser.INT }
| "bool" { Parser.BOOL }
| "real" { Parser.REAL }
| "=mu" { Parser.EQFIX Predicate.Mu }
| "=nu" { Parser.EQFIX Predicate.Nu }
| "/\\" { Parser.AND }
| "\\/" { Parser.OR }
| "!" | "not" { Parser.NOT }
| "and" { Parser.AND }
| "or" { Parser.OR }
| "<=>" { Parser.IFF }
| "=>" { Parser.IMPLY }
| "-" { Parser.MINUS }
| "+" { Parser.ADD }
| "*" { Parser.MULT }
| "/" | "div" { Parser.DIV }
| "%" { Parser.MOD }
| "mod" { Parser.MOD }
| ">=" { Parser.PREDSYM (T_num.NGeq (Ast.Ident.mk_fresh_svar ())) }
| ">" { Parser.PREDSYM (T_num.NGt (Ast.Ident.mk_fresh_svar ())) }
| "<=" { Parser.PREDSYM (T_num.NLeq (Ast.Ident.mk_fresh_svar ())) }
| "<" { Parser.PREDSYM (T_num.NLt (Ast.Ident.mk_fresh_svar ())) }
| "=" { Parser.PREDSYM T_bool.Eq }
| "!=" { Parser.PREDSYM T_bool.Neq }
| ":" { Parser.COLON }
| ";" { Parser.SEMI }
| "forall" { Parser.BINDER Forall }
| "exists" { Parser.BINDER Exists }
| "s.t." | "where" { Parser.WHERE }
| "." { Parser.DOT }
| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }

| ['a'-'z''A'-'Z''#''!''_']['a'-'z''A'-'Z''0'-'9'''''_''#''!']*
    {
      let str = Lexing.lexeme lexbuf in
      Parser.ID str
    }

| (('0'|['1'-'9']['0'-'9']*)'.'['0'-'9']*)
    {
      let str = Lexing.lexeme lexbuf in
      Parser.REALL str
    }

| ('0'|['1'-'9']['0'-'9']*)
    {
      let str = Lexing.lexeme lexbuf in
      Parser.INTL (int_of_string str)
    }

| eof { Parser.EOF }
| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment openingpos = parse
| '\n'
    { Lexing.new_line lexbuf; comment openingpos lexbuf }
| "*/"
    { () }
| eof {
    raise
      (SyntaxError
        (sprintf
          "%d:%d:syntax error: unterminated comment."
          openingpos.pos_lnum (openingpos.pos_cnum - openingpos.pos_bol + 1)
        )
      )
  }
| _ { comment openingpos lexbuf }
