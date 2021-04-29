%{

%}

%token LPAREN RPAREN
%token <string>ATOM
%token EOF

%type <Ppx_sexp_conv_lib.Sexp.t list > program
%start program

%%

program: list(sexp) EOF { $1 }

sexp:
  | LPAREN list(sexp) RPAREN { Ppx_sexp_conv_lib.Sexp.List ($2) }
  | atom { $1 }

atom: ATOM { Ppx_sexp_conv_lib.Sexp.Atom ($1) }