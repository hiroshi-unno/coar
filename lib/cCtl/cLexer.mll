{
  exception SyntaxError of string
  exception ErrorFormatted of string
  open Lexing
  open Ast.LogicOld

  let update_loc (lexbuf: Lexing.lexbuf) =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012']+ { main lexbuf }
| '\n'
| "//"[^'\n']*?'\n' { update_loc lexbuf; main lexbuf }
| "/*" { comment (lexeme_start_p lexbuf) lexbuf; main lexbuf }

| "if" { CParser.IF }
| "else" { CParser.ELSE }
| "while" { CParser.WHILE }
| "break" { CParser.BREAK }
| "return" { CParser.RETURN }
| "assume" { CParser.ASSUME }
| "(" { CParser.LPAREN }
| ")" { CParser.RPAREN }
| "{" { CParser.LBLOCK }
| "}" { CParser.RBLOCK }
| "=" { CParser.EQUAL }
| "," { CParser.COMMA }
| ":" { CParser.CORON }
| ";" { CParser.SEMI }
| "unsigned" { CParser.UNSIGNED }
| "int" { CParser.INT }
| "void" { CParser.VOID }

(* Formula *)
| "&&" { CParser.AND }
| "||" { CParser.OR }
| "!" { CParser.NOT }
| "--" { CParser.MINUSMINUS }
| "++" { CParser.PLUSPLUS }
| "-" { CParser.MINUS }
| "+" { CParser.ADD }
| "*" { CParser.ASTERISK }
| "/" { CParser.DIV }
| "%" { CParser.MOD }
| ">=" { CParser.PREDSYM T_int.Geq }
| ">" { CParser.PREDSYM T_int.Gt }
| "<=" { CParser.PREDSYM T_int.Leq }
| "<" { CParser.PREDSYM T_int.Lt }
| "==" { CParser.PREDSYM T_bool.Eq }
| "!=" { CParser.PREDSYM T_bool.Neq }

(* #include "../ctl.h" *)
| "#include" { CParser.SHARPINCLUDE }
| '\"'[^'\"']*'\"'
    {
      let str = Lexing.lexeme lexbuf in
      let str = String.sub str 1 (String.length str - 2) in
      CParser.STRING str
    }

(* #define *)
| "#define" { CParser.SHARPDEFINE }

(* functions *)
| "__phi" { CParser.PHI }
| "init" { CParser.INIT }
| "body" { CParser.BODY }
| "main" { CParser.MAIN }

(* CTL *)
| "CAF" { CParser.CAF }
| "CEF" { CParser.CEF }
| "CAG" { CParser.CAG }
| "CEG" { CParser.CEG }
| "CAND" { CParser.CAND }
| "COR" { CParser.COR }
| "CIMP" { CParser.CIMP }
| "CAP" { CParser.CAP }

(* non-deterministic *)
| "nondet" { CParser.NONDET }
| "NONDET" { CParser.LNONDET }

(* docheck *)
| "DOCHECK" { CParser.DOCHECK }

| ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9'''''_']*
    {
      let str = Lexing.lexeme lexbuf in
      CParser.ID str
    }
| ('0'|('+'|'-')?['1'-'9']['0'-'9']*)
    {
      let str = Lexing.lexeme lexbuf in
      CParser.INTL (int_of_string str)
    }

| eof { CParser.EOF }
| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment openingpos = parse
| '\n'
    { update_loc lexbuf; comment openingpos lexbuf }
| "*/"
    { () }
| eof {
    raise
      (ErrorFormatted
        (Printf.sprintf
          "%d:%d:syntax error: unterminated comment."
          openingpos.pos_lnum (openingpos.pos_cnum - openingpos.pos_bol + 1)
        )
      )
  }
| _ { comment openingpos lexbuf }
