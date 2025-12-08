{
  open Core
  open Ast.LogicOld

  exception SyntaxError of string
  exception ErrorFormatted of string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012']+ { main lexbuf }
| '\n'
| "//"[^'\n']*?'\n' { Lexing.new_line lexbuf; main lexbuf }
(* comments *)
| "/*" { comment (Lexing.lexeme_start_p lexbuf) lexbuf; main lexbuf }
(* string *)
| '"'[^'"']*'"'
    {
      let str = Lexing.lexeme lexbuf in
      CCtlParser.STRINGL (Stdlib.String.sub str 1 (String.length str - 2))
    }

(* for CTL *)
| "CAF" { CCtlParser.CAF }
| "CEF" { CCtlParser.CEF }
| "CAG" { CCtlParser.CAG }
| "CEG" { CCtlParser.CEG }
| "CAND" { CCtlParser.CAND }
| "COR" { CCtlParser.COR }
| "CIMP" { CCtlParser.CIMP }
| "CAP" { CCtlParser.CAP }

| "if" { CCtlParser.IF }
| "else" { CCtlParser.ELSE }
| "while" { CCtlParser.WHILE }
| "do" { CCtlParser.DO }
| "for" { CCtlParser.FOR }
| "break" { CCtlParser.BREAK }
| "return" { CCtlParser.RETURN }
| "goto" { CCtlParser.GOTO }
| "__VERIFIER_assume" { CCtlParser.ASSUME }
| "assume" { CCtlParser.ASSUME }
| "__VERIFIER_error" { CCtlParser.ERROR }
| "abort" { CCtlParser.ABORT }
| "__assert_fail" { CCtlParser.ASSERT_FAIL }
| "__attribute__" { CCtlParser.ATTRIBUTE }
| "__noreturn__" { CCtlParser.NORETURN }
| "__nothrow__" { CCtlParser.NOTHROW }
| "__leaf__" { CCtlParser.LEAF }
(* symbols *)
| "(" { CCtlParser.LPAREN }
| ")" { CCtlParser.RPAREN }
| "{" { CCtlParser.LBLOCK }
| "}" { CCtlParser.RBLOCK }
| "=" { CCtlParser.EQUAL }
| "," { CCtlParser.COMMA }
| ":" { CCtlParser.COLON }
| ";" { CCtlParser.SEMI }
| "extern" { CCtlParser.EXTERN }
| "unsigned" { CCtlParser.UNSIGNED }
| "char" { CCtlParser.CHAR }
| "short" { CCtlParser.SHORT }
| "int" { CCtlParser.INT }
| "long" { CCtlParser.LONG }
| "void" { CCtlParser.VOID }
| "const" { CCtlParser.CONST }
| "static" { CCtlParser.STATIC }
| "volatile" { CCtlParser.VOLATILE }
| "sizeof" { CCtlParser.SIZEOF }

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

(* conflicts *)
| "&" { CCtlParser.ADDR }

(* #include "../ctl.h" *)
| "#include" { CCtlParser.SHARPINCLUDE }

(* #define *)
| "#define" { CCtlParser.SHARPDEFINE }

(* functions *)
| "__phi" { CCtlParser.PHI }
| "init" { CCtlParser.INIT }
| "body" { CCtlParser.BODY }
| "main" { CCtlParser.MAIN }

(* non-deterministic *)
| "nondet" { CCtlParser.NONDET }
| "NONDET" { CCtlParser.LNONDET }
| "__VERIFIER_nondet_bool" { CCtlParser.NONDET_BOOL }
| "__VERIFIER_nondet_char" { CCtlParser.NONDET_CHAR }
| "__VERIFIER_nondet_uchar" { CCtlParser.NONDET_UCHAR }
| "__VERIFIER_nondet_short" { CCtlParser.NONDET_SHORT }
| "__VERIFIER_nondet_ushort" { CCtlParser.NONDET_USHORT }
| "__VERIFIER_nondet_int" { CCtlParser.NONDET_INT }
| "__VERIFIER_nondet_uint" { CCtlParser.NONDET_UINT }
| "__VERIFIER_nondet_long" { CCtlParser.NONDET_LONG }
| "__VERIFIER_nondet_ulong" { CCtlParser.NONDET_ULONG }

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
    { Lexing.new_line lexbuf; comment openingpos lexbuf }
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
