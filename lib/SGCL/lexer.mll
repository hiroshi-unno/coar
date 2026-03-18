{
  open Core
  open Ast.LogicOld

  exception SyntaxError of string
  exception ErrorFormatted of string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\t' '\r'';']+ { main lexbuf }
| "#=" { comment (Lexing.lexeme_start_p lexbuf) lexbuf}
| '\n'
| "//"[^'\n']*?'\n' 
| "#"[^'\n']*?'\n' { Lexing.new_line lexbuf; main lexbuf }

(* keywords for instruction*)
| "while" { Parser.WHILE }
| "if" { Parser.IF }
| "else" { Parser.ELSE }
| "flip" { Parser.FLIP }
| "observe" { Parser.OBSERVE }
| "return" { Parser.RETURN }
| "fail" { Parser.FAIL }

(* keywords for rvalue *)
| "~" {Parser.SAMPLE}
| "UniformDisc" { Parser.UNIFORMDISC }
| "Geometric" { Parser.GEOMETRIC }
| "Bernoulli" { Parser.BERNOULLI }
| "Categorical" { Parser.CATEGORICAL }

(* keywords for expressions and formulas *)
| ":=" { Parser.ASSIGN }
| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| "[" { Parser.LBRACKET }
| "]" { Parser.RBRACKET }
| "{" { Parser.LBRACE }
| "}" { Parser.RBRACE }
| "," { Parser.COMMA }
| "||" 
| "or" { Parser.OR }
| "and" { Parser.AND }
| "+=" { Parser.PLUSASSIGN }
| "-=" { Parser.MINUSASSIGN }
| "in" { Parser.IN }

| ">=" { Parser.PREDSYM (T_num.NGeq (Ast.Ident.mk_fresh_svar ())) }
| ">" { Parser.PREDSYM (T_num.NGt (Ast.Ident.mk_fresh_svar ())) }
| "<=" { Parser.PREDSYM (T_num.NLeq (Ast.Ident.mk_fresh_svar ())) }
| "<" { Parser.PREDSYM (T_num.NLt (Ast.Ident.mk_fresh_svar ())) }
| "=" { Parser.PREDSYM T_bool.Eq }
| "!=" { Parser.PREDSYM T_bool.Neq }

| "+" { Parser.PLUS }
| "-" { Parser.MINUS }
| "/" { Parser.DIV }
| "!"
| "not" { Parser.NOT }

| ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9''_']*
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
      Parser.NATL (int_of_string str)
    }

| eof { Parser.EOF }
| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment openingpos = parse
| '\n'
    { Lexing.new_line lexbuf; comment openingpos lexbuf }
| "=#"
    { main lexbuf }
| eof {
    raise
      (ErrorFormatted
        (sprintf
          "%d:%d:syntax error: unterminated comment."
          openingpos.pos_lnum (openingpos.pos_cnum - openingpos.pos_bol + 1)
        )
      )
  }
| _ { comment openingpos lexbuf }