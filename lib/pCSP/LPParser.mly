%{
  open Ast
  open Ast.LogicOld

  (* Logic Program Parser *)
%}

%token FALSE TRUE
%token <Z.t> INT
%token <string> VAR
%token <string> PVAR
%token NOT AND OR
%token PLUS MINUS TIMES DIV MOD
%token EQ NOTEQ GT LT GEQ LEQ COMMA COLON
%token LPAREN RPAREN
%token ASSUME DECLARE QUERY
%token BOT TOP BOOL
%token DOT EOF
/* %token FORALL */
%token EXISTS

%left OR
%left AND
%nonassoc NOT
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc UMINUS

%start parser_main_logic_program
%type <(LogicOld.Formula.t * LogicOld.Formula.t) list > parser_main_logic_program
%%

parser_main_logic_program: clauses EOF { $1 }

clauses: list(clause) { $1 }

clause:
  | head DOT { $1, Formula.mk_true () }
  | head ASSUME body DOT { $1, $3 }
  | head DECLARE body DOT { $1, $3 }
  | QUERY body DOT { Formula.mk_false (), $2 }
  | error {
        let message = Printf.sprintf "clause parse error near characters %d-%d"
                                     (Parsing.symbol_start ())
                                     (Parsing.symbol_end ())
        in failwith message
      }

atoms: separated_list(COMMA, atom) { $1 }

head:
 | atoms { Formula.or_of $1 }
 | EXISTS vars DOT atoms { Formula.mk_exists $2 (Formula.or_of $4) }

body: atoms { Formula.and_of $1 }

atom:
  | LPAREN atom RPAREN { $2 }
  | NOT atom { Formula.mk_neg $2 }
  | atom AND atom { Formula.mk_and $1 $3 }
  | atom OR atom { Formula.mk_or $1 $3 }
  | term EQ term { Formula.eq $1 $3 }
  | term NOTEQ term { Formula.mk_atom (T_bool.mk_neq $1 $3) }
  | term GT term { Formula.mk_atom (T_int.mk_gt $1 $3) }
  | term LT term { Formula.mk_atom (T_int.mk_lt $1 $3) }
  | term GEQ term { Formula.mk_atom (T_int.mk_geq $1 $3) }
  | term LEQ term { Formula.mk_atom (T_int.mk_leq $1 $3) }
  | TOP { Formula.mk_true () }
  | BOT { Formula.mk_false () }
  | VAR { Formula.mk_atom (Atom.of_bool_var (Ident.Tvar $1) )}
  | PVAR LPAREN terms RPAREN {
   let pred = Predicate.Var (Ident.Pvar $1, List.map Term.sort_of $3) in
   Formula.mk_atom (Atom.mk_app pred $3)
   }
  | error {
       let message = Printf.sprintf "atom parse error near characters %d-%d"
                                    (Parsing.symbol_start ())
                                    (Parsing.symbol_end ())
       in failwith message
  }
(*
   let sorts = List.map (Logic.AstUtil.sort_of_term []) $3 in (* BUG *)
*)

term:
 | LPAREN term RPAREN { $2 }
 | VAR { Term.mk_var (Ident.Tvar $1) T_int.SInt (* ToDo: assume sort is int *) }
 | VAR COLON BOOL { Term.mk_var (Ident.Tvar $1) T_bool.SBool }
 | FALSE { T_bool.mk_false () }
 | TRUE { T_bool.mk_true () }
 | INT { T_int.mk_int $1 }
 | MINUS term %prec UMINUS { T_int.mk_neg $2 }
 | term PLUS term { T_int.mk_add $1 $3 }
 | term TIMES term { T_int.mk_mult $1 $3 }
 | term MINUS term { T_int.mk_sub $1 $3 }
 | term DIV term { T_int.mk_div $1 $3 }
 | term MOD term { T_int.mk_mod $1 $3 }

terms : separated_list(COMMA, term) { $1 }

vars : separated_list(COMMA, VAR) { List.map (fun x -> Ident.Tvar x, T_int.SInt) $1 }

