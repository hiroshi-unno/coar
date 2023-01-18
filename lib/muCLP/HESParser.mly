%{
  open Ast
  open Ast.LogicOld
%}

%token CORON INT BOOL REAL
%token LPAREN RPAREN EOF
%token <Ast.LogicOld.Predicate.fixpoint> EQFIX
%token <Ast.LogicOld.Formula.binder> BINDER
%token DOT SEMI
%token NOT
%token AND OR IMPLY IFF
%token MINUS ADD MULT DIV MOD
%token <Ast.LogicOld.pred_sym> PREDSYM
%token <int> INTL
%token <string> REALL
%token TRUE FALSE
%token WHERE
%token <string> ID

%start toplevel
%type <Problem.t> toplevel
%start formula
%type <Ast.LogicOld.Formula.t> formula
%%

/*
;; forall x. F1 x
;; s.t.
;; F1 (x: int): bool =nu G1 x /\ (x <= 5 => F2 x) /\ (x <= 5 => F1 (x + 1)) /\ (x > 5 => F1 (x + 1));
;; F2 (x: int): bool =nu G2 x /\ (x <= 2 => F1 x) /\ (x > 2 => F2 (x-1));
;; G1 (x: int): bool =mu x >= 1 \/ (x <= 5 /\ G2 x) \/ (x <= 5 => G1 (x + 1)) /\ (x > 5 => G1 (x + 1));
;; G2 (x: int): bool =mu x >= 1 \/ (x <= 2 => G1 x) /\ (x > 2 => G2 (x-1));
*/

toplevel:
    query=Formula WHERE preds=Funs EOF { Problem.make preds query }

formula:
    fml=Formula EOF { fml }

Funs:
    f=Fun SEMI preds=Funs { f :: preds }
  | f=Fun SEMI { [f] }

Fun:
    funname=ID bounds=Bounds CORON BOOL fix=EQFIX body=Formula {
      Pred.make fix (Ident.Pvar funname) bounds body
    }

/* Ast.LogicOld.Formula.t */
/* not including LetRec */
Formula:
    fml=FormulaBinder { fml }

FormulaBinder:
    binder=BINDER bounds=Bounds DOT body=Formula { Formula.mk_bind binder bounds body }
  | fml=FormulaIff { fml }

FormulaIff:
    left=FormulaImply IFF right=FormulaImply { Formula.mk_iff left right }
  | fml=FormulaImply { fml }

FormulaImply:
    left=FormulaOr IMPLY right=FormulaImply { Formula.mk_imply left right }
  | fml=FormulaOr { fml }

FormulaOr:
    left=FormulaAnd OR right=FormulaOr { Formula.mk_or left right }
  | fml=FormulaAnd { fml }

FormulaAnd:
    left=FormulaNeg AND right=FormulaAnd { Formula.mk_and left right }
  | fml=FormulaNeg { fml }

FormulaNeg:
    NOT fml=FormulaNegParen { Formula.mk_neg fml }
  | fml=FormulaAtom { fml }

FormulaNegParen:
    NOT fml=FormulaNegParen { Formula.mk_neg fml }
  | LPAREN fml=Formula RPAREN { fml }

FormulaAtom:
    atom=Atom { Formula.mk_atom atom }
  | LPAREN fml=Formula RPAREN { fml }


/* Ast.LogicOld.Atom.t */
Atom:
    funname=ID args=AtomAppArgs { Atom.mk_app (Predicate.mk_var (Ident.Pvar funname) []) args }
  | atom=T_bool { atom }
  | TRUE { Atom.True Dummy }
  | FALSE { Atom.False Dummy }

AtomAppArgs:
    { [] }
  | arg=T_intAtom args=AtomAppArgs { arg :: args }


/* Ast.LogicOld.Term.t */
/* Ast.LogicOld.T_int */
/* Term:
    t=T_int { t } */

T_int:
    t=T_intAddSub { t }

T_intAddSub:
    t=T_intMultDivMod { t }
  | t1=T_intMultDivMod ADD t2=T_intAddSub { T_int.mk_add t1 t2 }
  | t1=T_intMultDivMod MINUS t2=T_intAddSub { T_int.mk_sub t1 t2 }

T_intMultDivMod:
    t=T_intNeg { t }
  | t1=T_intNeg MULT t2=T_intMultDivMod { T_int.mk_mult t1 t2 }
  | t1=T_intNeg DIV t2=T_intMultDivMod { T_int.mk_div t1 t2 }
  | t1=T_intNeg MOD t2=T_intMultDivMod { T_int.mk_mod t1 t2 }

T_intNeg:
    t=T_intAtom { t }
  | MINUS t=T_intNeg { T_int.mk_neg t }

T_intAtom:
    LPAREN t=T_int RPAREN { t }
  | n=INTL { T_int.mk_int (Z.of_int n) }
  | n=REALL { T_real.mk_real (Q.of_string n) }
  | varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SInt }

/* Ast.LogicOld.T_bool */
T_bool:
    t1=T_int op=PREDSYM t2=T_int { Atom.mk_app (Predicate.mk_psym op) [t1; t2] }

/* Ast.LogicOld.Predicate.t */
/* not including Fixpoint */
/* Predicate.Psym is dealt with by T_bool */
/* Predicate:
    varname=ID { Predicate.mk_var (Ident.Pvar varname) [] } */


/* Ast.LogicOld.Sort.t */
Sort:
    INT { T_int.SInt }
  | BOOL { T_bool.SBool }
  | REAL { T_real.SReal }

/* Bounds */
Bounds:
    { [] }
  | LPAREN varname=ID CORON sort=Sort RPAREN bounds=Bounds {
    (Ident.Tvar varname, sort) :: bounds
  }
