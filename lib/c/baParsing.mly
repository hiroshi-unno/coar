%{
  open Ast
  open Ast.LogicOld
%}

%token NEVER LBLOCK RBLOCK EOF
%token LPAREN RPAREN
%token CORON CORONCORON SEMI
%token ARROW GOTO IF FI SKIP TRUE FALSE
%token NOT AND OR
%token <string> ID

%start toplevel
%type <(string * string * Ast.LogicOld.Formula.t) list> toplevel
%%

toplevel:
    NEVER LBLOCK t=states RBLOCK EOF { t }

states:
    t=state { t }
  | t1=state t2=states { t1 @ t2 }

state:
    id=ID CORON SKIP { [id, id, Formula.mk_atom (Atom.mk_true () ~info:Dummy) ~info:Dummy] }
  | id=ID CORON toes=transition SEMI {
    List.map (fun (to_id, fml) -> id, to_id, fml) toes
  }

transition:
    FALSE { [] }
  | IF toes=conds FI { toes }

conds:
    c=cond { [c] }
  | c=cond toes=conds { c :: toes }

cond:
    CORONCORON fml=formula ARROW GOTO id=ID { (id, fml) }

formula:
    fml=formula_or { fml }

formula_or:
    fml=formula_and { fml }
  | fml1=formula_and OR fml2=formula_or { Formula.mk_or fml1 fml2 ~info:Dummy }

formula_and:
    fml=formula_unary { fml }
  | fml1=formula_unary AND fml2=formula_and { Formula.mk_and fml1 fml2 ~info:Dummy }

formula_unary:
    fml=formula_atom { fml }
  | NOT fml=formula_unary { Formula.mk_neg fml ~info:Dummy }

formula_atom:
    id=ID { Formula.mk_atom (Atom.mk_app (Predicate.Var (Ident.Pvar id, [])) [] ~info:Dummy) ~info:Dummy }
  | TRUE { Formula.mk_atom (Atom.mk_true () ~info:Dummy) ~info:Dummy }
  | LPAREN fml=formula RPAREN { fml }
