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

| "tt" { Parser.TT }
| "ff" { Parser.FF }
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
(* The real-specific spellings this format's own printer emits.  They must
   come before the bare forms only for readability: ocamllex takes the longest
   match, so ">=." wins over ">=" wherever both apply.  Without these a problem
   over reals could be printed and not read back, which for a format three
   solvers share is a broken contract rather than a missing feature. *)
| ">=." { Parser.PREDSYM T_real.RGeq }
| ">." { Parser.PREDSYM T_real.RGt }
| "<=." { Parser.PREDSYM T_real.RLeq }
| "<." { Parser.PREDSYM T_real.RLt }
| "+." { Parser.RADD }
| "-." { Parser.RMINUS }
| "*." { Parser.RMULT }
| "/." { Parser.RDIV }
| "abs." { Parser.RABS }
(* a real constant prints as `real(q)`, where q is what Zarith writes for a
   rational: an optional sign, digits, and optionally `/` and more digits.
   Lexed whole so that the sort keyword `real` needs no grammar change *)
| "real" '(' ('-'? ['0'-'9']+ ('/' ['0'-'9']+)?) ')'
    {
      let s = Lexing.lexeme lexbuf in
      Parser.REALL (String.sub s ~pos:5 ~len:(String.length s - 6))
    }
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

(* '!' is the negation token, not an identifier character: with it in this
   class, [x!=y] lexed as the identifier [x!] followed by [=] *)
(* An identifier may be spelled like a name this process draws itself
   ([#tvar] followed by digits), since '#' is an identifier character here.
   Contract: once an identifier is lexed, [Ident.mk_fresh_tvar] never returns
   it.  Every identifier steps the fresh-name counter past itself as it is
   read, as the SMT-LIB reader does for every atom of its input; the
   grammar's actions draw no term variable, so the whole input has stepped
   the counter before the first name is drawn after parsing (type inference,
   the optimizer, the reductions).  Without this, a binder of the input
   spelled [#tvar<n>] and a copy or flag a reduction draws later as
   [#tvar<n>] would be one variable, and a substitution that relies on its
   own names being fresh would capture.  On an input spelling no such name
   the counter is untouched. *)
| ['a'-'z''A'-'Z''#''_']['a'-'z''A'-'Z''0'-'9'''''_''#']*
    {
      let str = Lexing.lexeme lexbuf in
      Ast.Ident.avoid_tvar (Ast.Ident.Tvar str);
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
