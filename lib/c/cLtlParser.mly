%{
  open Core
  open Ast
  open Ast.LogicOld
  open CSyntax

  let funname_nondet = "__VERIFIER_nondet_int"
  let stmt_of_statements = Statement.of_statements
  let formula_of_term term = Formula.mk_atom (T_bool.mk_neq term (T_int.mk_int Z.zero ~info:Dummy) ~info:Dummy) ~info:Dummy
  let term_of_string str = let varname = sprintf "\"%s\"" str in Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy
  let is_nondet term =
    if Term.is_funcall term then
      let funname, _, _ = Term.let_funcall term in
      Stdlib.(funname = funname_nondet)
    else false
%}

%token IF ELSE DO WHILE WHILE_TRUE FOR BREAK RETURN GOTO
%token LPAREN RPAREN LBLOCK RBLOCK EOF
%token EQUAL
%token NOT AND OR IMPLY
%token CORON SEMI COMMA
%token UNSIGNED VOID INT EXTERN CONST STATIC VOLATILE SIZEOF
%token MAIN
%token NONDET ASSUME ERROR ATTRIBUTE NORETURN LTLDECLARE
%token ADD MINUS ASTERISK DIV MOD ADDR
%token PLUSPLUS MINUSMINUS
%token <Ast.LogicOld.pred_sym> PREDSYM
%token BOX DIAMOND X AP U R WU
%token <int> INTL
%token <string> ID
%token <string> STRINGL

%start toplevel
%type <CSyntax.cltl * CSyntax.Define.t list * CSyntax.FunDecl.t list> toplevel
%%

toplevel:
    d=Decls EOF {
      match d with
        None, _, _, _, _, _ -> raise (SemanticError "function ltl formula is not declared")
        | _, _, _, None, _, _ -> raise (SemanticError "function main is not declared")
        | Some phi, decls, init, Some body, defs, fundecls ->
          (phi, decls, init, body), defs, fundecls
    }

/* Functions and Variables Declarations */
Decls:
    { None, [], [], None, [], [] }
  | d1=Decl d2=Decls {
    match d1, d2 with
    | (Some _, _, _, _, _, _), (Some _, _, _, _, _, _) -> raise (SemanticError "ltl formula is declared multiple times")
    | (_, _, _, Some _, _, _), (_, _, _, Some _, _, _) -> raise (SemanticError "function main is declared multiple times")
    | (phi1, decls1, init1, body1, defs1, fundecls1), (phi2, decls2, init2, body2, defs2, fundecls2) ->
      let merge a b = match a, b with Some x, _ | _, Some x -> Some x | _ -> None in
      let phi = merge phi1 phi2 in
      let decls = decls1 @ decls2 in
      let init = init1 @ init2 in
      let body = merge body1 body2 in
      let defs = defs1 @ defs2 in
      let fundecls = fundecls1 @ fundecls2 in
      phi, decls, init, body, defs, fundecls
  }

Decl:
  /* ignore: extern void __VERIFIER_error() __attribute__ ((__noreturn__)); */
    EXTERN VOID ERROR LPAREN RPAREN ATTRIBUTE LPAREN LPAREN NORETURN RPAREN RPAREN SEMI { None, [], [], None, [], [] }
  /* ignore: extern void __VERIFIER_assume(); */
  | EXTERN VOID ASSUME LPAREN RPAREN SEMI { None, [], [], None, [], [] }
  /* ignore: extern void __VERIFIER_assume() __attribute__ ((__noreturn__)); */
  | EXTERN VOID ASSUME LPAREN RPAREN ATTRIBUTE LPAREN LPAREN NORETURN RPAREN RPAREN SEMI { None, [], [], None, [], [] }
  /* ignore: extern int __VERIFIER_nondet_int(); */
  | EXTERN INT NONDET LPAREN RPAREN SEMI { None, [], [], None, [], [] }
  /* ignore: extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__)); */
  | EXTERN INT NONDET LPAREN RPAREN ATTRIBUTE LPAREN LPAREN NORETURN RPAREN RPAREN SEMI { None, [], [], None, [], [] }
  /* int a, b, c; */
  | decls=VarDecl {
      let decls, inits = decls in
      None, decls, inits, None, [], []
    }
  /* //@ ltl invariant positive: <>[]AP(x==1); */
  | LTLDECLARE phi=Phi SEMI { Some phi, [], [], None, [], [] }
  /* p = 0; */
  | inits=Init { None, [], inits, None, [], [] }
  /* void main() { ... } */
  | VOID MAIN LPAREN RPAREN LBLOCK stmts=Statements RBLOCK { None, [], [], Some (stmt_of_statements stmts), [], [] }
  | INT MAIN LPAREN RPAREN LBLOCK stmts=Statements RBLOCK { None, [], [], Some (stmt_of_statements stmts), [], [] }
  /* int f(int a, int *b) { ... } */
  | INT funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK
  | VOID ASTERISK funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], [], None, [], [FunDecl.mk_fun_int funname params (stmt_of_statements stmts)]
  }
  /* void f(int a, int *b) { ... } */
  | VOID funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], [], None, [], [FunDecl.mk_fun_void funname params (stmt_of_statements stmts)]
  }

/* int a, b, c = 0; */
VarDecl:
    INT decls=IntVarDecls SEMI
    | VOID decls=IntVarDecls SEMI
    | VarDeclIntType decls=IntVarDecls SEMI {
      let varnames, stmts = decls in
      List.map ~f:(fun varname -> Declare.mk_int varname) varnames,
      match stmts with
        [] -> []
      | stmts -> stmt_of_statements stmts |> Init.of_stmt_exn []
    }

VarDeclIntType:
    UNSIGNED INT
  | CONST INT
  | STATIC INT
  | STATIC CONST INT
  | STATIC VOLATILE INT
  | STATIC VOID { () }

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
  phi=PhiUntil { phi }

PhiUntil:
    phi1=PhiImp U phi2=PhiUntil { Ltl.mk_u phi1 phi2 }
  | phi1=PhiImp R phi2=PhiUntil { Ltl.mk_r phi1 phi2 }
  | phi1=PhiImp WU phi2=PhiUntil { Ltl.mk_wu phi1 phi2 }
  | phi=PhiImp { phi }

PhiImp:
    phi1=PhiOr IMPLY phi2=PhiImp { Ltl.mk_or (Ltl.mk_neg phi1) phi2 }
  | phi=PhiOr { phi }

PhiOr:
    phi1=PhiAnd OR phi2=PhiOr { Ltl.mk_or phi1 phi2 }
  | phi=PhiAnd { phi }

PhiAnd:
    phi1=PhiUnary AND phi2=PhiAnd { Ltl.mk_and phi1 phi2 }
  | phi=PhiUnary { phi }

PhiUnary:
    phi=PhiAtom { phi }
  | BOX phi=PhiUnary { Ltl.mk_g phi }
  | DIAMOND phi=PhiUnary { Ltl.mk_f phi }
  | X phi=PhiUnary { Ltl.mk_x phi }
  | NOT phi=PhiUnary { Ltl.mk_neg phi }

PhiAtom:
    AP LPAREN fml=Formula RPAREN { Ltl.mk_p fml }
  | LPAREN phi=Phi RPAREN { phi }

/* Init */
Init:
    init=InitOne SEMI { init }
  | init=InitOne COMMA inits=Init { init @ inits }

InitOne:
  | data=MultipleAssignInit {
    let varnames, term = data in
    if is_nondet term then begin
      assert (List.length varnames <= 1);
      List.map ~f:(fun varname -> Init.mk_nondet_assign varname) varnames
    end else
      List.map ~f:(fun varname -> Init.mk_assign varname term) varnames
  }
  /* | ASSUME LPAREN fml=Formula RPAREN SEMI inits=Init { Init.mk_assume fml :: inits } */

/* a = b = c = 10 */
MultipleAssignInit:
    varname=ID EQUAL term=Term { [varname], term }
  | varname=ID EQUAL tail=MultipleAssignInit {
    let varnames, term = tail in
    varname :: varnames, term
  }

/* a = 3; if (x > 0) { y = 10; } */
Statements:
    { [] }
  | stmt=Statement stmts=Statements { stmt :: stmts }

Statement:
    stmt=StatementGeneral { stmt }
  | IF LPAREN cond_fml=Formula RPAREN t_stmt=Statement { Statement.mk_if cond_fml t_stmt (Statement.mk_nop ()) }
  | IF LPAREN cond_assign_stmt=FormulaAssignOne RPAREN t_stmt=StatementIfT {
      let varname = Statement.varname_of_assign cond_assign_stmt in
      let tvar = Ident.Tvar varname in
      let term = Term.mk_var tvar T_int.SInt ~info:Dummy in
      let cond_fml = Formula.mk_atom (T_bool.mk_neq term (T_int.mk_int Z.zero ~info:Dummy) ~info:Dummy) ~info:Dummy in
      stmt_of_statements [
        cond_assign_stmt;
        Statement.mk_if cond_fml t_stmt (Statement.mk_nop ())
      ]
    }
  | mk_ifelse=IfElse f_stmt=Statement { mk_ifelse f_stmt }
  | mk_while=While stmt=Statement { mk_while stmt }
  | mk_for=For stmt=Statement { mk_for stmt }

StatementIfT:
    stmt=StatementGeneral { stmt }
  | mk_ifelse=IfElse f_stmt=StatementIfT { mk_ifelse f_stmt }
  | mk_while=While stmt=StatementIfT { mk_while stmt }
  | mk_for=For stmt=StatementIfT { mk_for stmt }

IfElse:
    IF LPAREN cond_fml=Formula RPAREN t_stmt=StatementIfT ELSE { fun f_stmt -> Statement.mk_if cond_fml t_stmt f_stmt }
  | IF LPAREN cond_assign_stmt=FormulaAssignOne RPAREN t_stmt=StatementIfT ELSE {
      let varname = Statement.varname_of_assign cond_assign_stmt in
      let tvar = Ident.Tvar varname in
      let term = Term.mk_var tvar T_int.SInt ~info:Dummy in
      let cond_fml = Formula.mk_atom (T_bool.mk_neq term (T_int.mk_int Z.zero ~info:Dummy) ~info:Dummy) ~info:Dummy in
      fun f_stmt ->
        stmt_of_statements [
          cond_assign_stmt;
          Statement.mk_if cond_fml t_stmt f_stmt
        ]
    }

FormulaAssignOne:
    stmt=ForInitOne { stmt }
  | LPAREN stmt=FormulaAssignOne RPAREN { stmt }

While:
    WHILE_TRUE { Statement.mk_loop }
  | WHILE LPAREN cond_fml=Formula RPAREN {
      fun stmt ->
        Statement.mk_if cond_fml stmt (Statement.mk_break ())
        |> Statement.mk_loop
    }

/* do { ... } while (...); */
DoWhile:
    DO LBLOCK stmts=Statements RBLOCK WHILE LPAREN cond_fml=Formula RPAREN SEMI {
      stmt_of_statements [
        stmt_of_statements stmts;
        Statement.mk_if cond_fml (Statement.mk_nop ()) (Statement.mk_break ())
      ]
      |> Statement.mk_loop
    }

For:
    /* TODO */
    FOR LPAREN init_stmt=ForInit SEMI cond_fml=ForCond SEMI step_var=ID PLUSPLUS RPAREN {
      fun stmt ->
        stmt_of_statements [
          init_stmt;
          Statement.mk_if cond_fml
            (stmt_of_statements [
              stmt;
              let tvar = Ident.Tvar step_var in
              Statement.mk_assign step_var
                (T_int.mk_add
                  (Term.mk_var tvar T_int.SInt ~info:Dummy)
                  (T_int.mk_int Z.one ~info:Dummy)
                  ~info:Dummy)
            ])
            (Statement.mk_break ())
          |> Statement.mk_loop
        ]
    }
  | FOR LPAREN init_stmt=ForInit SEMI cond_fml=ForCond SEMI RPAREN {
      fun stmt ->
        stmt_of_statements [
          init_stmt;
          Statement.mk_if cond_fml stmt (Statement.mk_break ())
          |> Statement.mk_loop
        ]
  }

ForCond:
    fml=Formula { fml }
  | { Formula.mk_atom (Atom.mk_true () ~info:Dummy) ~info:Dummy }

/* a = b, c = d */
ForInitOne:
  varname=ID EQUAL term=Term { Statement.mk_assign varname term }

ForInits:
    stmt=ForInitOne { [stmt] }
  | stmt=ForInitOne COMMA stmts=ForInits { stmt :: stmts }

ForInit:
    { Statement.mk_nop () }
  | stmts=ForInits { stmt_of_statements stmts }

IntVarDeclOne:
    varname=ID {
        varname, Some (Statement.mk_assign varname (*ToDo*)(T_int.zero ()))
    }
  | ASTERISK varname=ID { varname, (*ToDo*)None }
  | varname=ID EQUAL term=Term {
      if is_nondet term then
        varname, None
      else
        varname, Some (Statement.mk_assign varname term)
    }

IntVarDecls:
    decl=IntVarDeclOne {
      let varname, stmt = decl in
      [varname],
      match stmt with
        None -> []
      | Some stmt -> [stmt]
    }
  | decl=IntVarDeclOne COMMA decls=IntVarDecls {
      let varname, stmt = decl in
      let varnames, stmts = decls in
      let varnames = varname :: varnames in
      let stmts = match stmt with
          None -> stmts
        | Some stmt -> stmt :: stmts
      in
      varnames, stmts
    }

StatementGeneral:
    varname=ID EQUAL term=Term SEMI {
      if is_nondet term then
        Statement.mk_nondet_assign varname
      else
        Statement.mk_assign varname term
    }
  /* TODO */
  | varname1=ID EQUAL varname2=ID EQUAL term=Term SEMI { Statement.mk_compound (Statement.mk_assign varname1 term) (Statement.mk_assign varname2 term) }
  | LPAREN ASTERISK varname=ID RPAREN EQUAL term=Term SEMI { Statement.mk_unref_assign varname term }
  | stmt=DoWhile { stmt }
  /* int a = 3, b = 2; */
  | INT decls=IntVarDecls SEMI | CONST INT decls=IntVarDecls SEMI
  | VOID decls=IntVarDecls SEMI
  | CONST VOID decls=IntVarDecls SEMI {
      let varnames, stmts = decls in
      List.map ~f:(fun varname -> Statement.mk_vardecl varname T_int.SInt) varnames
      @ stmts
      |> stmt_of_statements
    }
  | BREAK SEMI { Statement.mk_break () }
  | RETURN term=Term SEMI {
      if is_nondet term then
        Statement.mk_return_nondet ()
      else
        Statement.mk_return_int term
    }
  | RETURN SEMI { Statement.mk_return_void () }
  | LBLOCK stmts=Statements RBLOCK { stmt_of_statements stmts }
  /* goto */
  | GOTO label_name=ID SEMI { Statement.mk_goto label_name }
  /* label */
  | label_name=ID CORON { Statement.mk_label label_name }
  | ASSUME LPAREN fml=Formula RPAREN SEMI { Statement.mk_assume fml }
  /* nops */
  | t=Term SEMI {
    if Term.is_funcall t then
      let funname, args, _ = Term.let_funcall t in
      Statement.mk_call_voidfun funname args
    else
      Statement.mk_assign "#_" t
  }
  | SEMI { Statement.mk_nop () }

/* Ast.LogicOld.Formula.t */
/* not including LetRec */
Formula:
    fml=FormulaOr { fml }

FormulaOr:
    left=FormulaAnd OR right=FormulaOr { Formula.mk_or left right ~info:Dummy }
  | fml=FormulaAnd { fml }

FormulaAnd:
    left=FormulaNeg AND right=FormulaAnd { Formula.mk_and left right ~info:Dummy }
  | fml=FormulaNeg { fml }

FormulaNeg:
    NOT fml=FormulaNeg { Formula.mk_neg fml ~info:Dummy }
  | fml=FormulaAtom { fml }

FormulaAtom:
    atom=Atom { Formula.mk_atom atom ~info:Dummy }
  | LPAREN fml=Formula RPAREN { fml }
  | term=T_intAtom { formula_of_term term }
  /* | n=INTL { T_int.from_int n ~info:Dummy |> formula_of_term }
  | varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy |> formula_of_term } */

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
  | t1=T_intAddSub ADD t2=T_intMultDivMod { T_int.mk_add t1 t2 ~info:Dummy }
  | t1=T_intAddSub MINUS t2=T_intMultDivMod { T_int.mk_sub t1 t2 ~info:Dummy }

T_intMultDivMod:
    t=T_intUnary { t }
  | t1=T_intMultDivMod ASTERISK t2=T_intUnary { T_int.mk_mult t1 t2 ~info:Dummy }
  | t1=T_intMultDivMod DIV t2=T_intUnary { T_int.mk_div t1 t2 ~info:Dummy }
  | t1=T_intMultDivMod MOD t2=T_intUnary { T_int.mk_mod t1 t2 ~info:Dummy }

T_intUnary:
    t=T_intParen { t }
  | Cast t=T_intUnary { t }
  | MINUS t=T_intUnary { T_int.mk_neg t ~info:Dummy }

T_intParen:
    t=T_intAtom { t }
  | LPAREN t=T_int RPAREN { t }

T_intAtom:
    n=INTL { T_int.from_int n ~info:Dummy }
  | varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy }
  | funname=ID LPAREN args=Arguements RPAREN {
    Term.mk_fsym_app (FunCall funname) args ~info:Dummy
  }
  | ADDR varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy }
  | ASTERISK varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SUnrefInt ~info:Dummy }
  /* sizeof(int) -> 4 */
  | SIZEOF LPAREN INT RPAREN { T_int.from_int 4 ~info:Dummy }
  /* --x, ++x */
  | MINUSMINUS varname=ID { Term.mk_fsym_app (FunCall "#dec") [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy }
  | PLUSPLUS varname=ID { Term.mk_fsym_app (FunCall "#inc") [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy }
  /* x--, x++ */
  | varname=ID MINUSMINUS { T_int.mk_add (Term.mk_fsym_app (FunCall "#dec") [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy) (T_int.mk_int Z.one ~info:Dummy) ~info:Dummy }
  | varname=ID PLUSPLUS { T_int.mk_sub (Term.mk_fsym_app (FunCall "#inc") [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy) (T_int.mk_int Z.one ~info:Dummy) ~info:Dummy }
  /* "hoge" */
  | str=STRINGL { term_of_string str }
  /* "hoge" "fuga" */
  | str1=STRINGL str2=STRINGL { term_of_string (str1 ^ str2) }
  /* nondet() */
  | NONDET LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet) [] ~info:Dummy }

Cast:
    LPAREN UNSIGNED INT RPAREN
  | LPAREN VOID RPAREN { () }

/* Ast.LogicOld.T_bool */
T_bool:
    t1=T_int op=PREDSYM t2=T_int { Atom.mk_app (Predicate.mk_psym op) [t1; t2] ~info:Dummy }
