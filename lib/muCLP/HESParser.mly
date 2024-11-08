%{
  open Core
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
    funname=ID args=AtomAppArgs {
      Atom.mk_pvar_app (Ident.Pvar funname) (List.map args ~f:Term.sort_of) args
    }
  | atom=T_bool { atom }
  | TRUE { Atom.True Dummy }
  | FALSE { Atom.False Dummy }

AtomAppArgs:
    { [] }
  | arg=T_numAtom args=AtomAppArgs { arg :: args }


/* Ast.LogicOld.Term.t */
/* Ast.LogicOld.T_num */
/* Term:
    t=T_num { t } */

T_num:
    t=T_numAddSub { t }

T_numAddSub:
    t=T_numMultDivMod { t }
  | t1=T_numAddSub ADD t2=T_numMultDivMod { T_num.mk_nadd t1 t2 }
  | t1=T_numAddSub MINUS t2=T_numMultDivMod { T_num.mk_nsub t1 t2 }

T_numMultDivMod:
    t=T_numNeg { t }
  | t1=T_numMultDivMod MULT t2=T_numNeg { T_num.mk_nmult t1 t2 }
  | t1=T_numMultDivMod DIV t2=T_numNeg { T_num.mk_ndiv t1 t2 }
  | t1=T_numMultDivMod MOD t2=T_numNeg { T_int.mk_mod(*ToDo*) t1 t2 }

T_numNeg:
    t=T_numAtom { t }
  | MINUS t=T_numNeg { T_num.mk_nneg t }

T_numAtom:
    LPAREN t=T_num RPAREN { t }
  | n=INTL { T_int.from_int n }
  | n=REALL { T_real.mk_real (Q.of_string n) }
  | varname=ID { Term.mk_var (Ident.Tvar varname) @@ Sort.mk_fresh_svar () }

/* Ast.LogicOld.T_bool */
T_bool:
    t1=T_num op=PREDSYM t2=T_num { Atom.mk_app (Predicate.mk_psym op) [t1; t2] }

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
