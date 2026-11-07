{
  open Core
  open Ast.LogicOld

  exception SyntaxError of string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\t' '\r']+ { main lexbuf }
| '\n' { Lexing.new_line lexbuf; main lexbuf }
(* a line comment ends before its newline, which the rule above counts, or at
   the end of the input: a file whose last line is a comment without a final
   newline was refused when the comment had to end in one *)
| "//"[^'\n']* { main lexbuf }
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
(* Integer division and remainder are SMT-LIB's: [/], [div], [%] and [mod]
   are the Euclidean pair (the remainder is never negative, and
   [a = b * (a div b) + a mod b]), as Z3 and every SMT-LIB reader take them.
   Both members change together, so a file's quotient and remainder stay one
   consistent pair.  The other rounding modes have spellings of their own,
   which are what this format's printer writes for a term a frontend built
   with them (a C or T2 program's [/] and [%] are truncated): [tdiv]/[rem]
   (also [trem]) truncated, [fdiv]/[frem] flooring, [cdiv]/[crem] ceiling,
   and [ediv]/[erem] the printer's own spelling of the Euclidean pair.  So
   the printed form of every integer division reads back as the same
   operation. *)
| "/" | "div" | "ediv" { Parser.DIV Ast.Value.Euclidean }
| "%" | "mod" | "erem" { Parser.MOD Ast.Value.Euclidean }
| "tdiv" { Parser.DIV Ast.Value.Truncated }
| "rem" | "trem" { Parser.MOD Ast.Value.Truncated }
| "fdiv" { Parser.DIV Ast.Value.Flooring }
| "frem" { Parser.MOD Ast.Value.Flooring }
| "cdiv" { Parser.DIV Ast.Value.Ceiling }
| "crem" { Parser.MOD Ast.Value.Ceiling }
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
(* '@' may follow the first character: the transition-system translation
   names a location's predicate [state_<function>@<label>], and the printer
   writes that name back as it is, so a printed problem reads again only if
   the reader takes it.  '@' is no token of this grammar. *)
| ['a'-'z''A'-'Z''#''_']['a'-'z''A'-'Z''0'-'9'''''_''#''@']*
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

(* an integer literal is unbounded, as in SMT-LIB: it is passed on as its
   digits and read by Zarith, since a native [int] overflows past 2^62 *)
| ('0'|['1'-'9']['0'-'9']*)
    {
      let str = Lexing.lexeme lexbuf in
      Parser.INTL str
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
