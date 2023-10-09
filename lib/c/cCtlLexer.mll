{
  open Core
  open Lexing
  open Common.Util.LexingHelper
  open Ast.LogicOld

  exception SyntaxError of string
  exception ErrorFormatted of string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012']+ { main lexbuf }
| '\n'
| "//"[^'\n']*?'\n' { update_loc lexbuf; main lexbuf }
| "/*" { comment (lexeme_start_p lexbuf) lexbuf; main lexbuf }

| "if" { CCtlParser.IF }
| "else" { CCtlParser.ELSE }
| "while" { CCtlParser.WHILE }
| "break" { CCtlParser.BREAK }
| "return" { CCtlParser.RETURN }
| "assume" { CCtlParser.ASSUME }
| "(" { CCtlParser.LPAREN }
| ")" { CCtlParser.RPAREN }
| "{" { CCtlParser.LBLOCK }
| "}" { CCtlParser.RBLOCK }
| "=" { CCtlParser.EQUAL }
| "," { CCtlParser.COMMA }
| ":" { CCtlParser.CORON }
| ";" { CCtlParser.SEMI }
| "unsigned" { CCtlParser.UNSIGNED }
| "int" { CCtlParser.INT }
| "void" { CCtlParser.VOID }

(* Formula *)
| "&&" { CCtlParser.AND }
| "||" { CCtlParser.OR }
| "!" { CCtlParser.NOT }
| "--" { CCtlParser.MINUSMINUS }
| "++" { CCtlParser.PLUSPLUS }
| "-" { CCtlParser.MINUS }
| "+" { CCtlParser.ADD }
| "*" { CCtlParser.ASTERISK }
| "/" { CCtlParser.DIV }
| "%" { CCtlParser.MOD }
| ">=" { CCtlParser.PREDSYM T_int.Geq }
| ">" { CCtlParser.PREDSYM T_int.Gt }
| "<=" { CCtlParser.PREDSYM T_int.Leq }
| "<" { CCtlParser.PREDSYM T_int.Lt }
| "==" { CCtlParser.PREDSYM T_bool.Eq }
| "!=" { CCtlParser.PREDSYM T_bool.Neq }

(* #include "../ctl.h" *)
| "#include" { CCtlParser.SHARPINCLUDE }
| '\"'[^'\"']*'\"'
    {
      let str = Lexing.lexeme lexbuf in
      let str = Stdlib.String.sub str 1 (String.length str - 2) in
      CCtlParser.STRING str
    }

(* #define *)
| "#define" { CCtlParser.SHARPDEFINE }

(* functions *)
| "__phi" { CCtlParser.PHI }
| "init" { CCtlParser.INIT }
| "body" { CCtlParser.BODY }
| "main" { CCtlParser.MAIN }

(* CTL *)
| "CAF" { CCtlParser.CAF }
| "CEF" { CCtlParser.CEF }
| "CAG" { CCtlParser.CAG }
| "CEG" { CCtlParser.CEG }
| "CAND" { CCtlParser.CAND }
| "COR" { CCtlParser.COR }
| "CIMP" { CCtlParser.CIMP }
| "CAP" { CCtlParser.CAP }

(* non-deterministic *)
| "nondet" { CCtlParser.NONDET }
| "NONDET" { CCtlParser.LNONDET }

(* docheck *)
| "DOCHECK" { CCtlParser.DOCHECK }

| ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9'''''_']*
    {
      let str = Lexing.lexeme lexbuf in
      CCtlParser.ID str
    }
| ('0'|('+'|'-')?['1'-'9']['0'-'9']*)
    {
      let str = Lexing.lexeme lexbuf in
      CCtlParser.INTL (int_of_string str)
    }

| eof { CCtlParser.EOF }
| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment openingpos = parse
| '\n'
    { update_loc lexbuf; comment openingpos lexbuf }
| "*/"
    { () }
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
