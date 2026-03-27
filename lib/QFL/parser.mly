%{
  open Core
  open Ast
  open Ast.LogicOld

let query_of params left right =
  if Formula.is_atom right then
    let atm, _ = Formula.let_atom right in
    if Atom.is_psym_app atm then
      let op, args, _ = Atom.let_psym_app atm in
      let left =
      match left with
      | None -> None
      | Some fml ->
        Option.return @@
          Typeinf.typeinf_formula ~print:(fun _ -> ()) ~default:(Some T_real.SReal)
            ~senv:(Map.Poly.of_alist_exn params) fml
      in
      match op, args with
        | T_num.NLeq _, [Var (name, _, _); bound] ->
          Problem.Check ({ params; left; kind = Problem.UB; name; args = []; bound; strict = false })
        | T_num.NLt _, [Var (name, _, _); bound] ->
          Problem.Check ({ params; left; kind = Problem.UB; name; args = []; bound; strict = true })
        | T_num.NLeq _, [FunApp (FVar (name, _, _), args, _); bound] ->
          Problem.Check ({ params; left; kind = Problem.UB; name; args; bound; strict = false })
        | T_num.NLt _, [FunApp (FVar (name, _, _), args, _); bound] ->
          Problem.Check ({ params; left; kind = Problem.UB; name; args; bound; strict = true })
        | T_num.NGeq _, [Var (name, _, _); bound] ->
          Problem.Check ({ params; left; kind = Problem.LB; name; args = []; bound; strict = false })
        | T_num.NGt _, [Var (name, _, _); bound] ->
          Problem.Check ({ params; left; kind = Problem.LB; name; args = []; bound; strict = true })
        | T_num.NGeq _, [FunApp (FVar (name, _, _), args, _);  bound] ->
          Problem.Check ({ params; left; kind = Problem.LB; name; args; bound; strict = false })
        | T_num.NGt _, [FunApp (FVar (name, _, _), args, _);  bound] ->
          Problem.Check ({ params; left; kind = Problem.LB; name; args; bound; strict = true })
        | _ -> failwith @@ Printf.sprintf "Unexpected predicate %s" (Atom.str_of atm)
    else assert false
  else assert false
%}

%token INT BOOL REAL
%token LPAREN RPAREN LBRACKET RBRACKET EOF
%token <Ast.LogicOld.Predicate.fixpoint> EQFIX
%token <Ast.LogicOld.Formula.binder> BINDER
%token COLON SEMI PERIOD COMMA BAR ARROW
%token NOT
%token AND OR IMPLY IFF
%token MINUS ADD MULT DIV MOD MAX MIN
%token <Ast.LogicOld.pred_sym> PREDSYM
%token <int> INTL
%token <string> REALL
%token TRUE FALSE
%token WHERE
%token <string> ID
%token ASAT DIST ENSURES
%token IF THEN ELSE

%start toplevel
%type <Problem.t> toplevel
%start query
%type <Problem.query> query
%%

toplevel:
    query=Query WHERE preds=Funs EOF { Problem.make preds query }

query:
    query=Query EOF { query }

Query:
    fml=Formula {
      if Formula.is_atom fml then
        query_of [] None fml
      else if Formula.is_bind fml then
        let binder, bounds, body, _ = Formula.let_bind fml in
        assert Stdlib.(Formula.Forall = binder);
        if Formula.is_imply body then
          let left, right, _ = Formula.let_imply body in
          query_of bounds (Some left) right
        else assert false
      else assert false
    }
  | ASAT bounds=Bounds {
      ASAT (None, bounds, Formula.mk_true ())
    }
  | ASAT LPAREN name=ID args=FvarAppArgs RPAREN bounds=Bounds {
      ASAT (Some (Ident.Tvar name, args), bounds, Formula.mk_true ())
    }
  | ASAT bounds=Bounds BAR fml=Formula {
      ASAT (None, bounds, fml)
    }
  | ASAT LPAREN name=ID args=FvarAppArgs RPAREN bounds=Bounds BAR fml=Formula {
      ASAT (Some (Ident.Tvar name, args), bounds, fml)
    }
  | DIST LPAREN name=ID args=FvarAppArgs RPAREN ENSURES params=Bounds ARROW LPAREN bound=Formula RPAREN {
      DistCheck { name = Ident.Tvar name; args; params; bound }
    }

Funs:
    f=Fun SEMI preds=Funs { f :: preds }
  | f=Fun SEMI { [f] }

Fun:
    funname=ID bounds=Bounds COLON REAL fix=EQFIX body=T_num {
      Pred.make fix (Ident.Tvar funname) bounds body
    }
  | funname=ID bounds=Bounds COLON REAL BAR fmls=Formulas fix=EQFIX body=T_num {
      Pred.make fix (Ident.Tvar funname) bounds body ~annots:fmls
    }

Formulas:
    fml=Formula { [fml] }
  | fml=Formula COMMA fmls=Formulas { fml :: fmls }

/* Ast.LogicOld.Formula.t */
/* not including LetRec */
Formula:
    fml=FormulaBinder { fml }

FormulaBinder:
    binder=BINDER bounds=Bounds PERIOD body=Formula { Formula.mk_bind binder bounds body }
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
    atom=T_bool { atom }
  | TRUE { Atom.True Dummy }
  | FALSE { Atom.False Dummy }

/*AtomAppArgs:
    { [] }
  | arg=T_numAtom args=AtomAppArgs { arg :: args }*/


/* Ast.LogicOld.Term.t */
/* Ast.LogicOld.T_num */
/* Term:
    t=T_num { t } */

T_num:
    t=T_numAddSub { t }
  | IF cond=Formula THEN t1=T_num ELSE t2=T_num {
      T_bool.mk_if_then_else (T_bool.of_formula cond) t1 t2
    }

T_numAddSub:
    t=T_numMulDivMod { t }
  | t1=T_numAddSub ADD t2=T_numMulDivMod { T_num.mk_nadd t1 t2 }
  | t1=T_numAddSub MINUS t2=T_numMulDivMod { T_num.mk_nsub t1 t2 }

T_numMulDivMod:
    t=T_numNeg { t }
  | t1=T_numMulDivMod MULT t2=T_numNeg { T_num.mk_nmul t1 t2 }
  | t1=T_numMulDivMod DIV t2=T_numNeg { T_num.mk_ndiv Value.Truncated t1 t2 }
  | t1=T_numMulDivMod MOD t2=T_numNeg { T_num.mk_nrem Value.Truncated t1 t2 }

T_numNeg:
    t=T_numAtom { t }
  | MINUS t=T_numNeg { T_num.mk_nneg t }
  | MAX args=FvarAppArgs {
    Term.mk_fvar_app (Ident.Tvar "max") (List.map args ~f:(fun _ -> T_real.SReal)) T_real.SReal args }
  | MIN args=FvarAppArgs {
    Term.mk_fvar_app (Ident.Tvar "min") (List.map args ~f:(fun _ -> T_real.SReal)) T_real.SReal args }
  | funname=ID args=FvarAppArgs {
      Term.mk_fvar_app (Ident.Tvar funname)
        (List.map args ~f:(fun t -> if T_tuple.is_stuple t then T_real.SReal else Term.sort_of t))
        T_real.SReal args
    }

T_numAtom:
    LPAREN t=T_num RPAREN { t }
  | LBRACKET ts=T_nums RBRACKET { T_tuple.mk_tuple_cons (List.map ts ~f:Term.sort_of) ts }
  | n=INTL { T_int.from_int n }
  | n=REALL { T_real.mk_real (Q.of_string n) }
  | varname=ID { Term.mk_var (Ident.Tvar varname) @@ Sort.mk_fresh_svar () }

FvarAppArgs:
    { [] }
  | arg=T_numAtom args=FvarAppArgs { arg :: args }

/* Ast.LogicOld.T_bool */
T_bool:
    t1=T_num op=PREDSYM t2=T_num { Atom.mk_app (Predicate.mk_psym op) [t1; t2] }

/* Ast.LogicOld.Predicate.t */
/* not including Fixpoint */
/* Predicate.Psym is dealt with by T_bool */
/* Predicate:
    varname=ID { Predicate.mk_var (Ident.Tvar varname) [] } */


/* Ast.LogicOld.Sort.t */
Sort:
    INT { T_int.SInt }
  | BOOL { T_bool.SBool }
  | REAL { T_real.SReal }

/* Bounds */
Bounds:
    { [] }
  | LPAREN varname=ID COLON sort=Sort RPAREN bounds=Bounds {
    (Ident.Tvar varname, sort) :: bounds
  }

/* T_nums */
T_nums:
    t = T_num { [t] }
  | t = T_num SEMI ts = T_nums { t :: ts }
