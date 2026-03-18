{
  open Core
  open Ast.LogicOld

  exception SyntaxError of string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\t' '\r'';']+ { main lexbuf }
| '\n'
| "//"[^'\n']*?'\n' 
| "#"[^'\n']*?'\n' { Lexing.new_line lexbuf; main lexbuf }

(* keywords for declaration *)
| "bool" { Parser.BOOL }
| "nat" { Parser.NAT }
| "real" { Parser.REAL }
| "const" { Parser.CONST }
| "rparam" { Parser.RPARAM }
| "nparam" { Parser.NPARAM }

(* keywords for instruction*)
| "skip" { Parser.SKIP }
| "while" { Parser.WHILE }
| "if" { Parser.IF }
| "else" { Parser.ELSE }
| "tick" { Parser.TICK }
| "observe" { Parser.OBSERVE }
| "loop" { Parser.LOOP }

(* keywords for query *)
| "?Ex" { Parser.EXPECTATION }
| "?Pr" { Parser.PRQUERY }
| "!Print" { Parser.PRINT }
| "!Plot" { Parser.PLOT }
| "?Opt" { Parser.OPTIMIZE }

(* keywords for rvalue *)
| "unif_d" 
| "unif" { Parser.DUNIFORM }
| "unif_c" { Parser.CUNIFORM }
| "geometric" { Parser.GEOMETRIC }
| "poisson" { Parser.POISSON }
| "logdist" { Parser.LOGDIST }
| "binomial" { Parser.BINOMIAL }
| "bernoulli" { Parser.BERNOULLI }
| "iid" { Parser.IID }

(* keywords for literal *)
| "true" { Parser.TRUE }
| "false" { Parser.FALSE }
| "∞" 
| "\\infty" { Parser.INFINITY }

(* keywords for expressions and formulas *)
| ":=" { Parser.ASSIGN }
| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| "[" { Parser.LBRACKET }
| "]" { Parser.RBRACKET }
| "{" { Parser.LBRACE }
| "}" { Parser.RBRACE }
| "," { Parser.COMMA }
| "||" { Parser.OR }
| "&" { Parser.AND }

| ">=" { Parser.PREDSYM (T_num.NGeq (Ast.Ident.mk_fresh_svar ())) }
| ">" { Parser.PREDSYM (T_num.NGt (Ast.Ident.mk_fresh_svar ())) }
| "<=" { Parser.PREDSYM (T_num.NLeq (Ast.Ident.mk_fresh_svar ())) }
| "<" { Parser.PREDSYM (T_num.NLt (Ast.Ident.mk_fresh_svar ())) }
| "=" { Parser.EQUAL }

| ":" { Parser.COLON }
| "+" { Parser.PLUS }
| "-" { Parser.MINUS }
| "*" { Parser.MULT }
| "/"  { Parser.DIV }
| "%" { Parser.MOD }
| "^" { Parser.POW }
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

