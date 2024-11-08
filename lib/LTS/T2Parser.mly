%{
  open Core
  open Ast
  open Ast.LogicOld
%}

%token START ERROR CUTPOINT FROM TO AT SHADOW
%token COLON SEMICOLON COMMA
%token SKIP ASSUME SUBST
%token INT_TO_REAL REAL_TO_INT
%token NONDET
%token CONST_ARRAY SELECT_ARRAY STORE_ARRAY SELECT_TUPLE CONSTR_TUPLE
%token LPAREN RPAREN
%token <string> VAR
%token <int> INT
%token <char> CHAR
%token <Q.t> FLOAT
%token STRING
%token PLUS MINUS
%token TIMES DIV MOD
%token EQ NEQ GEQ GT LEQ LT
%token AND OR NOT
%token SHL LSHR ASHR BITOR BITAND
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
  | VAR SUBST expr SEMICOLON { Problem.Subst ((Ident.Tvar $1, Term.sort_of $3), $3) }
  | ASSUME LPAREN cond RPAREN SEMICOLON { Problem.Assume $3 }
  | SKIP SEMICOLON { Problem.Skip }

expr:
  | MINUS expr %prec UMINUS {
    if T_num.is_value $2 then T_num.mk_neg_value @@ fst @@ T_num.let_value $2 else T_num.mk_nneg $2
  }
  | expr PLUS expr { T_num.mk_nadd $1 $3 }
  | expr MINUS expr { T_num.mk_nsub $1 $3 }
  | expr TIMES expr { T_num.mk_nmult $1 $3 }
  | expr DIV expr { T_num.mk_ndiv $1 $3 }
  | expr MOD expr { T_num.mk_nmod $1 $3 }
  | SHL LPAREN expr COMMA expr RPAREN { T_bv.mk_bvshl ~size:None $3 $5 }
  | LSHR LPAREN expr COMMA expr RPAREN { T_bv.mk_bvlshr ~size:None $3 $5 }
  | ASHR LPAREN expr COMMA expr RPAREN { T_bv.mk_bvashr ~size:None $3 $5 }
  | BITOR LPAREN expr COMMA expr RPAREN { T_bv.mk_bvor ~size:None $3 $5 }
  | BITAND LPAREN expr COMMA expr RPAREN { T_bv.mk_bvand ~size:None $3 $5 }
  | CONST_ARRAY LPAREN expr RPAREN { T_array.mk_const_array T_int.SInt (Term.sort_of $3) $3 }
  | SELECT_ARRAY LPAREN expr COMMA expr RPAREN { T_array.mk_select T_int.SInt (Sort.mk_fresh_svar ()) $3 $5 }
  | STORE_ARRAY LPAREN expr COMMA expr COMMA expr RPAREN { T_array.mk_store T_int.SInt (Term.sort_of $7) $3 $5 $7 }
  | SELECT_TUPLE LPAREN expr COMMA INT COMMA INT RPAREN { T_tuple.mk_tuple_sel (List.init $7 ~f:(fun _ -> Sort.mk_fresh_svar ())) $3 $5 }
  | CONSTR_TUPLE LPAREN exprs RPAREN { T_tuple.mk_tuple_cons (List.map $3 ~f:Term.sort_of) $3 }
  | LPAREN expr RPAREN { $2 }
  | INT { T_num.mk_value (string_of_int $1) }
  | CHAR { T_num.mk_value (string_of_int (int_of_char $1)) }
  | FLOAT { T_real.mk_real $1 }
  | VAR { Term.mk_var (Ident.Tvar $1) (Sort.mk_fresh_svar ()) }
  | INT_TO_REAL LPAREN expr RPAREN { T_irb.mk_int_to_real $3 }
  | REAL_TO_INT LPAREN expr RPAREN { T_irb.mk_real_to_int $3 }
  | NONDET LPAREN RPAREN { Term.mk_var (Problem.mk_nondet ()) (Sort.mk_fresh_svar ()) }

exprs:
  | expr { [ $1 ] }
  | expr COMMA exprs { $1 :: $3 }

cond:
  | LPAREN cond RPAREN { $2 }
  | cond AND cond { Formula.mk_and $1 $3 }
  | cond OR cond { Formula.mk_or $1 $3 }
  | NOT cond { Formula.mk_neg $2 }
  | atom { Formula.mk_atom $1 }

atom:
  | expr EQ expr { T_bool.mk_eq $1 $3 }
  | expr NEQ expr { T_bool.mk_neq $1 $3 }
  | expr GEQ expr { T_num.mk_ngeq $1 $3 }
  | expr GT expr { T_num.mk_ngt $1 $3 }
  | expr LEQ expr { T_num.mk_nleq $1 $3 }
  | expr LT expr { T_num.mk_nlt $1 $3 }
