%{
  open Ast
  open Ast.LogicOld
  open CSyntax

  let rec stmt_of_statements = function
      [] -> Statement.mk_nop ()
    | stmt :: [] -> stmt
    | stmt :: tail -> Statement.mk_compound stmt (stmt_of_statements tail)

  let mk_fun_nondet funname params =
    FunDecl.mk_fun_nondet funname params
    (* FunDecl.mk_fun_int funname params (Statement.mk_return_nondet ()) *)
%}

%token IF ELSE WHILE BREAK RETURN
%token LPAREN RPAREN LBLOCK RBLOCK EOF
%token EQUAL
%token NOT AND OR
%token CORON SEMI COMMA
%token UNSIGNED VOID INT
%token SHARPINCLUDE SHARPDEFINE
%token PHI INIT BODY MAIN
%token CAF CEF CAG CEG CAP CAND COR CIMP
%token NONDET LNONDET
%token ADD MINUS ASTERISK DIV MOD
%token PLUSPLUS MINUSMINUS
%token <Ast.LogicOld.pred_sym> PREDSYM
%token <int> INTL
%token <string> ID STRING
%token ASSUME DOCHECK

%start toplevel
%type <CSyntax.cctl * CSyntax.Define.t list * CSyntax.FunDecl.t list> toplevel
%%

toplevel:
    d=Decls EOF {
      match d with
        None, _, _, _, _, _ -> raise (SemanticError "function __phi is not declared")
        | _, _, None, _, _, _ -> raise (SemanticError "function init is not declared")
        | _, _, _, None, _, _ -> raise (SemanticError "function body is not declared")
        | Some phi, decls, Some init, Some body, defs, fundecls ->
          (phi, decls, init, body), defs, fundecls
    }

/* Functions and Variables Declarations */
Decls:
    { None, [], None, None, [], [] }
  | d1=Decl d2=Decls {
    match d1, d2 with
    | (Some _, _, _, _, _, _), (Some _, _, _, _, _, _) -> raise (SemanticError "function __phi is declared multiple times")
    | (_, _, Some _, _, _, _), (_, _, Some _, _, _, _) -> raise (SemanticError "function init is declared multiple times")
    | (_, _, _, Some _, _, _), (_, _, _, Some _, _, _) -> raise (SemanticError "function body is declared multiple times")
    | (phi1, decls1, init1, body1, defs1, fundecls1), (phi2, decls2, init2, body2, defs2, fundecls2) ->
      let merge a b = match a, b with Some x, _ | _, Some x -> Some x | _ -> None in
      let phi = merge phi1 phi2 in
      let decls = decls1 @ decls2 in
      let init = merge init1 init2 in
      let body = merge body1 body2 in
      let defs = defs1 @ defs2 in
      let fundecls = fundecls1 @ fundecls2 in
      phi, decls, init, body, defs, fundecls
  }

Decl:
  /* int a, b, c; */
    decls=VarDecl { None, decls, None, None, [], [] }
  /* int __phi() { return CAG( CAP(x > 1) ); } */
  | INT PHI LPAREN RPAREN LBLOCK RETURN phi=Phi SEMI RBLOCK { Some phi, [], None, None, [], [] }
  /* void init() { p = 0; start = 0; } */
  | VOID INIT LPAREN RPAREN LBLOCK inits=Init RBLOCK { None, [], Some inits, None, [], [] }
  | INT INIT LPAREN RPAREN LBLOCK inits=Init RBLOCK { None, [], Some inits, None, [], [] }
  | VOID BODY LPAREN RPAREN LBLOCK stmts=Statements RBLOCK { None, [], None, Some (stmt_of_statements stmts), [], [] }
  | INT BODY LPAREN RPAREN LBLOCK stmts=Statements RBLOCK { None, [], None, Some (stmt_of_statements stmts), [], [] }
  /* int main() {} */
  | INT MAIN LPAREN RPAREN LBLOCK RBLOCK { None, [], None, None, [], [] }
  /* #include "../ctl.h" */
  | SHARPINCLUDE s=STRING {
    if s = "../ctl.h" then
      None, [], None, None, [], []
    else
      raise (SyntaxError "#include is not implemented")
  }
  /* #define XX 12 */
  | SHARPDEFINE id=ID value=INTL {
    None, [], None, None, [Define.mk_def id value], []
  }
  /* int f(int a, int *b) { return nondet(); } */
  | INT funname=ID LPAREN params=Parameters RPAREN LBLOCK RETURN NONDET LPAREN RPAREN SEMI RBLOCK {
    None, [], None, None, [], [mk_fun_nondet funname params]
  }
  /* TODO */
  /* int f(int a, int *b) { x = nondet(); return x; } */
  | INT funname=ID LPAREN params=Parameters RPAREN LBLOCK varname1=ID EQUAL NONDET LPAREN RPAREN SEMI RETURN varname2=ID SEMI RBLOCK {
    assert (varname1 = varname2);
    None, [], None, None, [], [mk_fun_nondet funname params]
  }
  /* void f(int a, int *b) { ... } */
  | VOID funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], None, None, [], [FunDecl.mk_fun_void funname params (stmt_of_statements stmts)]
  }
  /* #define hoge() nondet() */
  | SHARPDEFINE funname=ID LPAREN RPAREN NONDET LPAREN RPAREN {
    None, [], None, None, [], [mk_fun_nondet funname []]
  }

/* int a, b, c; */
VarDecl:
    UNSIGNED INT varnames=Variables SEMI | INT varnames=Variables SEMI {
      List.map (fun varname -> Declare.mk_int varname) varnames
    }

/* a, b, c */
Variables:
    varnames=Variable { varnames }
  | varnames1=Variable COMMA varnames=Variables { varnames1 @ varnames }

Variable:
    varname=ID { [varname] }
  | LNONDET { [] }

/* int a, int* b */
Parameters:
    { [] }
  | params=ParametersOneOrMore { params }

ParametersOneOrMore:
    param=Parameter { [param] }
  | param=Parameter COMMA params=ParametersOneOrMore { param :: params }

Parameter:
    sort=Type varname=ID { varname, sort }

/* a, 3+5, b */
Arguements:
    { [] }
  | args=ArguementsOneOrMore { args }

ArguementsOneOrMore:
    t=Term { [t] }
  | t=Term COMMA args=ArguementsOneOrMore { t :: args }

Type:
    INT { T_int.SInt }
  | INT ASTERISK { T_int.SRefInt }

/* CAG( CAP(x > 1) ) */
Phi:
    CAF LPAREN phi=Phi RPAREN { Ctl.mk_af phi }
  | CEF LPAREN phi=Phi RPAREN { Ctl.mk_ef phi }
  | CAG LPAREN phi=Phi RPAREN { Ctl.mk_ag phi }
  | CEG LPAREN phi=Phi RPAREN { Ctl.mk_eg phi }
  | CAND LPAREN phi1=Phi COMMA phi2=Phi RPAREN { Ctl.mk_and phi1 phi2 }
  | COR LPAREN phi1=Phi COMMA phi2=Phi RPAREN { Ctl.mk_or phi1 phi2 }
  | CIMP LPAREN phi1=Phi COMMA phi2=Phi RPAREN { Ctl.mk_imp phi1 phi2 }
  | CAP LPAREN fml=Formula RPAREN { Ctl.mk_ap fml }

/* Init */
Init:
    { [] }
  | data=MultipleAssignInit inits=Init {
    let varnames, term = data in
    List.fold_left
      (fun inits varname -> Init.mk_assign varname term :: inits)
      inits
      varnames
  }
  | MultipleNondetAssignInit inits=Init { inits }
  | ASSUME LPAREN fml=Formula RPAREN SEMI inits=Init { Init.mk_assume fml :: inits }

/* a = b = c = 10; */
MultipleAssignInit:
    varname=ID EQUAL term=Term SEMI { [varname], term }
  | varname=ID EQUAL tail=MultipleAssignInit {
    let varnames, term = tail in
    varname :: varnames, term
  }

/* a = b = c = nondet(); */
MultipleNondetAssignInit:
    ID EQUAL NONDET LPAREN RPAREN SEMI {}
  | ID EQUAL LNONDET SEMI {}
  | ID EQUAL MultipleNondetAssignInit {}

/* a = 3; if (x > 0) { y = 10; } */
Statements:
    { [] }
  | stmt=Statement stmts=Statements { stmt :: stmts }

Statement:
    stmt=StatementGeneral { stmt }
  | IF LPAREN cond_fml=Formula RPAREN t_stmt=Statement { Statement.mk_if cond_fml t_stmt (Statement.mk_nop ()) }
  | IF LPAREN LNONDET RPAREN stmt=Statement { Statement.mk_nondet stmt (Statement.mk_nop ()) }
  | IF LPAREN cond_fml=Formula RPAREN t_stmt=StatementIfT ELSE f_stmt=Statement { Statement.mk_if cond_fml t_stmt f_stmt }
  | IF LPAREN LNONDET RPAREN stmt1=StatementIfT ELSE stmt2=Statement { Statement.mk_nondet stmt1 stmt2 }
  | WHILE LPAREN cond_n=INTL RPAREN stmt=Statement {
      if cond_n = 0 then
        Statement.mk_nop ()
      else
        Statement.mk_loop stmt
    }

StatementIfT:
    stmt=StatementGeneral { stmt }
  | IF LPAREN cond_fml=Formula RPAREN t_stmt=StatementIfT ELSE f_stmt=StatementIfT { Statement.mk_if cond_fml t_stmt f_stmt }
  | IF LPAREN LNONDET RPAREN stmt1=StatementIfT ELSE stmt2=StatementIfT { Statement.mk_nondet stmt1 stmt2 }
  | WHILE LPAREN cond_n=INTL RPAREN stmt=StatementIfT {
      if cond_n = 0 then
        Statement.mk_nop ()
      else
        Statement.mk_loop stmt
    }

StatementGeneral:
    varname=ID EQUAL term=Term SEMI { Statement.mk_assign varname term }
  | varname=ID EQUAL NONDET LPAREN RPAREN SEMI { Statement.mk_nondet_assign varname }
  | varname=ID EQUAL LNONDET SEMI { Statement.mk_nondet_assign varname }
  | BREAK SEMI { Statement.mk_break () }
  | RETURN INTL SEMI { Statement.mk_exit () }
  | RETURN SEMI { Statement.mk_exit () }
  | LBLOCK stmts=Statements RBLOCK { stmt_of_statements stmts }
  /* label */
  | ID CORON { Statement.mk_nop () }
  | DOCHECK LPAREN RPAREN SEMI { Statement.mk_assign "check" (T_int.mk_int Z.one) }
  | ASSUME LPAREN fml=Formula RPAREN SEMI { Statement.mk_assume fml }
  /* a++; b--; */
  | varname=ID PLUSPLUS SEMI {
    let tvar = Ident.Tvar varname in
    Statement.mk_assign varname
      (T_int.mk_add
        (Term.mk_var tvar T_int.SInt)
        (T_int.mk_int Z.one))
  }
  | varname=ID MINUSMINUS SEMI {
    let tvar = Ident.Tvar varname in
    Statement.mk_assign varname
      (T_int.mk_sub
        (Term.mk_var tvar T_int.SInt)
        (T_int.mk_int Z.one))
  }
  | funname=ID LPAREN args=Arguements RPAREN SEMI {
    Statement.mk_call_voidfun funname args
  }
  | varname=ID EQUAL funname=ID LPAREN args=Arguements RPAREN SEMI {
    Statement.mk_call_assign varname funname args
  }
  /* nops */
  | INTL SEMI { Statement.mk_nop () }

/* Ast.LogicOld.Formula.t */
/* not including LetRec */
Formula:
    fml=FormulaAnd { fml }

FormulaAnd:
    left=FormulaOr AND right=FormulaAnd { Formula.mk_and left right }
  | fml=FormulaOr { fml }

FormulaOr:
    left=FormulaNeg OR right=FormulaOr { Formula.mk_or left right }
  | fml=FormulaNeg { fml }

FormulaNeg:
    NOT fml=FormulaNeg { Formula.mk_neg fml }
  | fml=FormulaAtom { fml }

FormulaAtom:
    atom=Atom { Formula.mk_atom atom }
  | LPAREN fml=Formula RPAREN { fml }


/* Ast.LogicOld.Atom.t */
Atom:
    atom=T_bool { atom }


/* Ast.LogicOld.Term.t */
/* Ast.LogicOld.T_int */
Term:
    t=T_int { t }

T_int:
    t=T_intAddSub { t }

T_intAddSub:
    t=T_intMultDivMod { t }
  | t1=T_intAddSub ADD t2=T_intMultDivMod { T_int.mk_add t1 t2 }
  | t1=T_intAddSub MINUS t2=T_intMultDivMod { T_int.mk_sub t1 t2 }

T_intMultDivMod:
    t=T_intNeg { t }
  | t1=T_intMultDivMod ASTERISK t2=T_intNeg { T_int.mk_mult t1 t2 }
  | t1=T_intMultDivMod DIV t2=T_intNeg { T_int.mk_div t1 t2 }
  | t1=T_intMultDivMod MOD t2=T_intNeg { T_int.mk_mod t1 t2 }

T_intNeg:
    t=T_intAtom { t }
  | MINUS t=T_intNeg { T_int.mk_neg t }

T_intAtom:
    LPAREN t=T_int RPAREN { t }
  | n=INTL { T_int.from_int n }
  | varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SInt }

/* Ast.LogicOld.T_bool */
T_bool:
    t1=T_int op=PREDSYM t2=T_int { Atom.mk_app (Predicate.mk_psym op) [t1; t2] }
