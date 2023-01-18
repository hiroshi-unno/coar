%{
  open Core
  open Ast
  open Ast.LogicOld

let nondet_count = ref 0
let mk_nondet () =
  incr nondet_count;
  Ident.Tvar (Problem.nondet_prefix ^ string_of_int !nondet_count)
%}

%token START ERROR CUTPOINT FROM TO AT SHADOW
%token COLON SEMICOLON COMMA
%token SKIP ASSUME NONDET SUBST
%token LPAREN RPAREN
%token <string> VAR
%token <int> INT
%token STRING
%token PLUS MINUS
%token TIMES DIV MOD
%token EQ NEQ GEQ GT LEQ LT
%token AND OR NOT
%token EOF

%left OR
%left AND
%nonassoc NOT
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc UMINUS

%type <Problem.lts> main
%start main

%%

main:
  | start_opt error_opt cutpoint_opt list(transition) EOF
    { ($1, $2, $3, List.filter_map ~f:Fn.id $4) }

start_opt:
    { None }
  | START COLON state SEMICOLON { Some $3 }

error_opt:
    { None }
  | ERROR COLON state SEMICOLON { Some $3 }

cutpoint_opt:
    { None }
  | CUTPOINT COLON state SEMICOLON { Some $3 }

transition:
  | from list(command) to_ { Some ($1, Problem.seq $2, $3) }
  | SHADOW LPAREN VAR COMMA VAR RPAREN SEMICOLON { None }

from:
  | FROM COLON state SEMICOLON { $3 }

to_:
  | TO COLON state SEMICOLON { $3 }

state:
  | INT { string_of_int $1 }
  | VAR { $1 }

at:
  | AT LPAREN INT COMMA STRING RPAREN { () }

command:
  | at command_body { $2 }
  | command_body { $1 }
command_body:
  | VAR SUBST expr SEMICOLON { Problem.Subst ((Ident.Tvar $1, T_int.SInt), $3) }
  | ASSUME LPAREN cond RPAREN SEMICOLON { Problem.Assume $3 }
  | SKIP SEMICOLON { Problem.Skip }

expr:
  | MINUS expr %prec UMINUS {
    if T_int.is_int $2 then T_int.mk_int (Z.neg @@ T_int.let_int $2) else T_int.mk_neg $2
  }
  | expr PLUS expr { T_int.mk_add $1 $3 }
  | expr MINUS expr { T_int.mk_sub $1 $3 }
  | expr TIMES expr { T_int.mk_mult $1 $3 }
  | expr DIV expr { T_int.mk_div $1 $3 }
  | expr MOD expr { T_int.mk_mod $1 $3 }
  | LPAREN expr RPAREN { $2 }
  | INT { T_int.mk_int (Z.of_int $1) }
  | VAR { Term.mk_var (Ident.Tvar $1) T_int.SInt }
  | NONDET LPAREN RPAREN { Term.mk_var (mk_nondet ()) T_int.SInt}

cond:
  | LPAREN cond RPAREN { $2 }
  | cond AND cond { Formula.mk_and $1 $3 }
  | cond OR cond { Formula.mk_or $1 $3 }
  | NOT cond { Formula.mk_neg $2 }
  | atom { Formula.mk_atom $1 }

atom:
  | expr EQ expr { T_bool.mk_eq $1 $3 }
  | expr NEQ expr { T_bool.mk_neq $1 $3 }
  | expr GEQ expr { T_int.mk_geq $1 $3 }
  | expr GT expr { T_int.mk_gt $1 $3 }
  | expr LEQ expr { T_int.mk_leq $1 $3 }
  | expr LT expr { T_int.mk_lt $1 $3 }
