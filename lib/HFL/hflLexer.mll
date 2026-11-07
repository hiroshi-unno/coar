(* The lexer of the union of the HES dialects of ReTHFL, hflmc2 (PaHFL), MuHFL
   and MoCHi's [-trans HFLz] output.  Every token any of the tools' lexers
   accepts is accepted, with the tools' longest-match reading of operator
   runs ([=v] is the greatest-fixpoint marker even where [x =v] was meant).
   Each token that only some dialects have is recorded in
   [HflParseState.seen] under the name the refusal will give it, so that the
   reader can refuse a construct the requested dialect does not have.
   [%LTS] and [%ENV] end the HES: the rest of the file is skipped ([%ENV]
   gives abstraction types that only guide predicate abstraction, and its
   presence is recorded). *)
{
  open HflParser
  exception Error of string
  let saw = HflParseState.saw
}

let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z' '_']
let upper = ['A'-'Z']
let alphanum = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '\'']
let ope_symbols = [ '=' '<' '>' '+' '-' '*' '&' '|' '\\' '/' '!' '%']

rule token = parse
| "\n"                     { Lexing.new_line lexbuf; token lexbuf }
| space+                   { token lexbuf }
| "/*"                     { comment lexbuf; token lexbuf }
| "%LTS"                   { saw "%LTS"; skip_all lexbuf; EOF }
| "%ENV"                   { saw "%ENV"; skip_all lexbuf; EOF }
| eof                      { EOF }
| "%HES"                   { START_HES }
| "("                      { LPAREN }
| ")"                      { RPAREN }
| "true"                   { TRUE }
| "false"                  { FALSE }
| "not"                    { saw "not"; NOT }
| ("\\"|"λ")               { LAMBDA }
| ("=v"|"=ν")              { DEF_G }
| "=μ"                     { DEF_L }
| "=m"                     { saw "=m"; DEF_L }
| "=u"                     { saw "=u"; DEF_L }
| "."                      { DOT }
| "∀"                      { saw "forall"; FORALL }
| "∃"                      { saw "exists"; EXISTS }
| digit+                   { INT (int_of_string (Lexing.lexeme lexbuf)) }
| upper alphanum*          { let s = Lexing.lexeme lexbuf in
                             if String.contains s '\'' then saw "'";
                             UIDENT s }
| lower alphanum*          { let s = Lexing.lexeme lexbuf in
                             if String.contains s '\'' then saw "'";
                             LIDENT s }
| ope_symbols+             { match Lexing.lexeme lexbuf with
                             | "+" -> PLUS
                             | "-" -> MINUS
                             | "*" -> STAR
                             | "/" -> SLASH
                             | "%" -> saw "%"; PERCENT
                             | "=" -> EQ
                             | "!=" -> saw "!="; NEQ
                             | "<>" -> NEQ
                             | "/=" -> saw "/="; NEQ
                             | "<=" -> LE
                             | ">=" -> GE
                             | "<" -> LT
                             | ">" -> GT
                             | "&&" | "/\\" -> AND
                             | "||" | "\\/" -> OR
                             | "!" -> saw "not"; NOT
                             | "=>" -> saw "=>"; IMPLY
                             | "<=>" -> saw "<=>"; IFF
                             | s -> raise (Error ("unknown operator " ^ s)) }
| _                        { raise (Error ("unexpected character "
                                           ^ Lexing.lexeme lexbuf)) }

and comment = parse
| "*/"                     { () }
| "/*"                     { comment lexbuf; comment lexbuf }
| "\n"                     { Lexing.new_line lexbuf; comment lexbuf }
| eof                      { raise (Error "unterminated comment") }
| _                        { comment lexbuf }

and skip_all = parse
| eof                      { () }
| _                        { skip_all lexbuf }
