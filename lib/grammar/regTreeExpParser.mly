%{
let print_error_information () =
  let st = Parsing.symbol_start_pos () in
  let en = Parsing.symbol_end_pos () in
  print_string ("File \"" ^ st.Lexing.pos_fname);
  Format.printf "\", line %d" st.Lexing.pos_lnum;
  Format.printf ", characters %d-%d:\n"
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
    (en.Lexing.pos_cnum - en.Lexing.pos_bol)
%}

%token TYPE
%token <string> LIDENT
%token <string> UIDENT
%token EQUAL
%token BAR
%token COMMA
%token AST
%token QUESTION
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token EOF

%right BAR
%right COMMA
%left AST
%left QUESTION

%type <(string * (string, string) RegTreeExp.t) list> regtreeexpdefs
%start regtreeexpdefs

%%

regtreeexpdefs:
  /* empty */
    { [] }
| regtreeexpdef regtreeexpdefs EOF
    { $1::$2 }
| error
    { print_error_information ();
      raise (Failure "Syntax error") }

regtreeexpdef:
  TYPE UIDENT EQUAL regtreeexp
    { $2, $4 }

regtreeexp:
  LPAREN RPAREN
    { RegTreeExp.Nil }
| UIDENT
    { RegTreeExp.Symbol $1 }
| regtreeexp COMMA regtreeexp
    { RegTreeExp.Concat ($1, $3) }
| LIDENT LBRACKET RBRACKET
    { RegTreeExp.Label ($1, RegTreeExp.Nil) }
| LIDENT LBRACKET regtreeexp RBRACKET
    { RegTreeExp.Label ($1, $3) }
| regtreeexp BAR regtreeexp
    { RegTreeExp.Alter ($1, $3) }
| regtreeexp AST
    { RegTreeExp.Kleene $1 }
| regtreeexp QUESTION
    { RegTreeExp.Option $1 }
| LPAREN regtreeexp RPAREN
    { $2 }
