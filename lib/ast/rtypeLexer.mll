{
  open RtypeParser
}

let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lalpha = ['A'-'Z']
let salpha = ['a'-'z']
let lsnum = digit | lalpha | salpha | '\'' | '_'

rule token = parse
  | '.' { DOT }
  | ',' { COMMA }
  | ':' { COLON }
  | ';' { SEMICOLON }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '{' { LBRA }
  | '}' { RBRA }
  (*| '[' { LBRACKET }
  | ']' { RBRACKET }
  | "[|" { LABRA }
  | "|]" { RABRA }

  | "//" { SLASLA }*)

  | '&' { AMP }
  | '|' { VERT }
  | '!' { EXC }
  | '?' { QUESTION }
  | '$' { APPLY }

  (*| "mu" { MU }
  | "nu" { NU }*)
  | "_forall" { FORALL }
  | "_exists" { EXISTS }
  | "not" { NOT }
  | "&&" { AND }
  | "||" { OR }
  | "=>" { IMP }
  | "<=>" { IFF }
  | '=' { EQUAL }
  | "<>" { NOTEQUAL }
  (*| "==" { EQEQ }*)

  | '<' { LT }
  | '>' { GT }
  | "<=" { LEQ }
  | ">=" { GEQ }

  | '+' { ADD }
  | '-' { SUB }
  | '*' { AST }
  | '/' { DIV }
  | "+." { FADD }
  | "-." { FSUB }
  | "*." { FMUL }
  | "/." { FDIV }
  | "mod" { MOD }
  | "::" { COLCOL }
  | "[]" | lalpha lsnum* { CONST (Lexing.lexeme lexbuf) }

  | "eps" { EPSILON }
  | "ev" { EVENT }
  | "++" { PLUSPLUS }

  (*| "^" { SCOMP }
  | "(=" { SUBSET }
  | "**" { SINTERSECT }
  | "--" { SDIFF }*)
  | "{}" { SEMPTY }
  | "|>" { RTRI }
  | "_" { WILDCARD }

  | "_is_" lalpha lsnum* | "_is_[]" | "_is_::" {
    let str = Lexing.lexeme lexbuf in
    RECOGNIZER (String.sub str 4 (String.length str - 4))
  }

  | "_get_" lalpha lsnum*  "_" digit+ | "_get_::_" digit+ {
    let str = Lexing.lexeme lexbuf in
    let sn = String.length str in
    let mn = String.rindex str '_' in
    let id = String.sub str 5 (mn - 5) in
    let n = String.sub str (mn + 1) (sn - mn -1) in
    ACCESSOR (id,int_of_string n)
  }

  (*| "_size_" lsnum+ "_" lsnum* {
    let str = Lexing.lexeme lexbuf in
    let sn = String.length str in
    let mn = String.rindex str '_' in
    let size_id = String.sub str 6 (mn - 6) in
    let adt_id = String.sub str (mn + 1) (sn - mn -1) in
    SIZE (size_id, adt_id)
  }

  | "size_" lsnum* {
    let str = Lexing.lexeme lexbuf in
    let adt_id = String.sub str 5 (String.length str - 5) in
    SIZE ("size", adt_id)
  }*)

  | "true" { BOOL true }
  | "false" { BOOL false }
  | "tt" { TRUE }
  | "ff" { FALSE }
  | "$proj" { PROJ }
  | "abs" { ABS }
  | "int_of_float" { ToInt }
  | "float_of_int" { ToReal }
  | "sqrt" { SQRT }

  | digit+ {
    let str = Lexing.lexeme lexbuf in
    INT (int_of_string str)
  }

  | digit+ '.' digit* (['e''E'] ['+''-']? ['0'-'9']+)? {
    let str = Lexing.lexeme lexbuf in
    FLOAT (float_of_string str)
  }

  (*| "?" lsnum* { UNKNOWN (Lexing.lexeme lexbuf) }*)

  (*| "let" { LET }
  | "in" { IN }
  | "<-" { LARROW }
  | ":=" { COLEQ }

  | ":-" { COLMIN }
  | "?-" { QMIN }

  | "|-" { TURNSTILE }*)
  | "<:" { SUBTYPE }
  | "->" { ARROW }

  (*| "template" { TEMPLATE }*)
  | "max" { MAXIMIZE }
  | "min" { MINIMIZE }
  (*| "prioritize" { PRIORITIZE }*)

  | "typeof" | "type_of" { TYPEOF }
  | "fineffectof" | "fin_effect_of" { FINEFFECTOF }
  | "infeffectof" | "inf_effect_of" { INFEFFECTOF }

  | salpha lsnum* { IDENT (Lexing.lexeme lexbuf) }
  | salpha lsnum* ('['':' digit+ ']')* { IDENT_T (Lexing.lexeme lexbuf) }

  | eof { EOF }

  | space+ { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }

  | "(*" { comment lexbuf; token lexbuf}

  | _ { failwith "Lexical error" }
and comment = parse
  | '\n' { Lexing.new_line lexbuf; comment lexbuf }
  | "*)" { () }
  | "(*" { comment lexbuf; comment lexbuf }
  | eof { failwith "unterminated comment" }
  | _ { comment lexbuf }
