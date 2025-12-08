{
  open Ast.LogicOld

  exception SyntaxError of string
  exception ErrorFormatted of string

  let intl_reg = Str.regexp "\\(0\\|[1-9][0-9]*\\)L?"
}

rule main = parse
 "//@" " "* "ltl invariant " (['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9'''''_']* as label) ":"
    { CLtlParser.LTLDECLARE label }
  (* ignore spacing and newline characters *)
| [' ' '\009' '\012' '\r']+ { main lexbuf }
| '\n'
| "//"'\n' { Lexing.new_line lexbuf; main lexbuf }
(* Safe/Unsafe *)
| "//"[^'@''\n'][^'\n']* { main lexbuf }
(* comments *)
| "/*" { comment (Lexing.lexeme_start_p lexbuf) lexbuf; main lexbuf }
(* string *)
| '"'[^'"']*'"'
    {
      let str = Lexing.lexeme lexbuf in
      CLtlParser.STRINGL (Stdlib.String.sub str 1 (String.length str - 2))
    }

(* for LTL *)
| "<>" { CLtlParser.DIAMOND }
| "[]" { CLtlParser.BOX }
| "AP" { CLtlParser.AP }
| "X" { CLtlParser.X }
| "U" { CLtlParser.U }
| "R" { CLtlParser.R }
| "WU" { CLtlParser.WU }
| "==>" { CLtlParser.IMPLY }

| "while"[' ' '\009' '\012' '\r']*"(true)"
| "while"[' ' '\009' '\012' '\r']*"(1)" { CLtlParser.WHILE_TRUE }

| "if" { CLtlParser.IF }
| "else" { CLtlParser.ELSE }
| "while" { CLtlParser.WHILE }
| "do" { CLtlParser.DO }
| "for" { CLtlParser.FOR }
| "break" { CLtlParser.BREAK }
| "return" { CLtlParser.RETURN }
| "goto" { CLtlParser.GOTO }
| "__VERIFIER_assume" { CLtlParser.ASSUME }
| "assume" { CLtlParser.ASSUME }
| "__VERIFIER_error" { CLtlParser.ERROR }
| "abort" { CLtlParser.ABORT }
| "__assert_fail" { CLtlParser.ASSERT_FAIL }
| "__attribute__" { CLtlParser.ATTRIBUTE }
| "__noreturn__" { CLtlParser.NORETURN }
| "__nothrow__" { CLtlParser.NOTHROW }
| "__leaf__" { CLtlParser.LEAF }
(* symbols *)
| "(" { CLtlParser.LPAREN }
| ")" { CLtlParser.RPAREN }
| "{" { CLtlParser.LBLOCK }
| "}" { CLtlParser.RBLOCK }
| "=" { CLtlParser.EQUAL }
| "," { CLtlParser.COMMA }
| ":" { CLtlParser.COLON }
| ";" { CLtlParser.SEMI }
| "extern" { CLtlParser.EXTERN }
| "unsigned" { CLtlParser.UNSIGNED }
| "char" { CLtlParser.CHAR }
| "short" { CLtlParser.SHORT }
| "int" { CLtlParser.INT }
| "long" { CLtlParser.LONG }
| "void" { CLtlParser.VOID }
| "const" { CLtlParser.CONST }
| "static" { CLtlParser.STATIC }
| "volatile" { CLtlParser.VOLATILE }
| "sizeof" { CLtlParser.SIZEOF }

(* Formula *)
| "&&" { CLtlParser.AND }
| "||" { CLtlParser.OR }
| "!" { CLtlParser.NOT }
| "--" { CLtlParser.MINUSMINUS }
| "++" { CLtlParser.PLUSPLUS }
| "-" { CLtlParser.MINUS }
| "+" { CLtlParser.ADD }
| "*" { CLtlParser.ASTERISK }
| "/" { CLtlParser.DIV }
| "%" { CLtlParser.MOD }
| ">=" { CLtlParser.PREDSYM T_int.Geq }
| ">" { CLtlParser.PREDSYM T_int.Gt }
| "<=" { CLtlParser.PREDSYM T_int.Leq }
| "<" { CLtlParser.PREDSYM T_int.Lt }
| "==" { CLtlParser.PREDSYM T_bool.Eq }
| "!=" { CLtlParser.PREDSYM T_bool.Neq }

(* conflicts *)
| "&" { CLtlParser.ADDR }

(* functions *)
| "main" { CLtlParser.MAIN }

(* non-deterministic *)
| "__VERIFIER_nondet_bool" { CLtlParser.NONDET_BOOL }
| "__VERIFIER_nondet_char" { CLtlParser.NONDET_CHAR }
| "__VERIFIER_nondet_uchar" { CLtlParser.NONDET_UCHAR }
| "__VERIFIER_nondet_short" { CLtlParser.NONDET_SHORT }
| "__VERIFIER_nondet_ushort" { CLtlParser.NONDET_USHORT }
| "__VERIFIER_nondet_int" { CLtlParser.NONDET_INT }
| "__VERIFIER_nondet_uint" { CLtlParser.NONDET_UINT }
| "__VERIFIER_nondet_long" { CLtlParser.NONDET_LONG }
| "__VERIFIER_nondet_ulong" { CLtlParser.NONDET_ULONG }

| ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9'''''_']*
    {
      let str = Lexing.lexeme lexbuf in
      CLtlParser.ID str
    }
| ('0'|['1'-'9']['0'-'9']*)'L'?
    {
      let str = Lexing.lexeme lexbuf in
      assert (Str.string_match intl_reg str 0);
      let str = Str.matched_group 1 str in
      CLtlParser.INTL (int_of_string str)
    }
| "0x"['a'-'z''0'-'9']+
    {
      let str = Lexing.lexeme lexbuf in
      let str = Stdlib.String.sub str 2 (String.length str - 2) in
      let n = Seq.fold_left
        (fun res c ->
          let c = int_of_char c in
          let digit =
            if int_of_char 'a' <= c && c <= int_of_char 'f' then
              c - (int_of_char 'a') + 10
            else
              c - (int_of_char '0')
          in
          res * 16 + digit
        )
        0
        (Stdlib.String.to_seq str)
      in
      CLtlParser.INTL n
    }

| "//"eof
| eof { CLtlParser.EOF }
| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment openingpos = parse
| '\n'
    { Lexing.new_line lexbuf; comment openingpos lexbuf }
| "*/"
    { () }
| eof {
    raise
      (ErrorFormatted
        (Core.sprintf
          "%d:%d:syntax error: unterminated comment."
          openingpos.pos_lnum (openingpos.pos_cnum - openingpos.pos_bol + 1)
        )
      )
  }
| _ { comment openingpos lexbuf }

and include_file openingpos = parse
| '<' [^'>']+ '>' { () }
| '"' [^'"']+ '"' { () }
| eof {
    let open Lexing in
    raise
      (ErrorFormatted
        (Core.sprintf
          "%d:%d:syntax error: unterminated include."
          openingpos.pos_lnum (openingpos.pos_cnum - openingpos.pos_bol + 1)
        )
      )
  }
