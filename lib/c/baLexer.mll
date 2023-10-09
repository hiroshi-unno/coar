{
  open Core
  open Lexing
  open Common.Util.LexingHelper

  exception SyntaxError of string
  exception ErrorFormatted of string
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012']+ { main lexbuf }
| '\n'
| "//"[' ''#'][^'\n']*?'\n' { update_loc lexbuf; main lexbuf }
| "/*" { comment (lexeme_start_p lexbuf) lexbuf; main lexbuf }

| "never" { BaParsing.NEVER }
| "(" { BaParsing.LPAREN }
| ")" { BaParsing.RPAREN }
| "{" { BaParsing.LBLOCK }
| "}" { BaParsing.RBLOCK }

| "::" { BaParsing.CORONCORON }
| ":" { BaParsing.CORON }
| ";" { BaParsing.SEMI }

| "->" { BaParsing.ARROW }
| "goto" { BaParsing.GOTO }
| "if" { BaParsing.IF }
| "fi" { BaParsing.FI }
| "skip" { BaParsing.SKIP }
| "1" { BaParsing.TRUE }
| "false" { BaParsing.FALSE }

| "!" { BaParsing.NOT }
| "&&" { BaParsing.AND }
| "||" { BaParsing.OR }

| ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9'''''_']*
    {
      let str = Lexing.lexeme lexbuf in
      BaParsing.ID str
    }

| eof { BaParsing.EOF }
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
