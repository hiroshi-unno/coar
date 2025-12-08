%{
  open Core
  open Ast
  open Ast.LogicOld
  open CSyntax
%}

%token IF ELSE DO WHILE FOR BREAK RETURN GOTO
%token LPAREN RPAREN LBLOCK RBLOCK EOF
%token EQUAL
%token NOT AND OR
%token COLON SEMI COMMA
%token UNSIGNED VOID CHAR SHORT INT LONG EXTERN CONST STATIC VOLATILE SIZEOF
%token SHARPINCLUDE SHARPDEFINE
%token PHI INIT BODY
%token CAF CEF CAG CEG CAP CAND COR CIMP
%token MAIN
%token NONDET_BOOL NONDET_CHAR NONDET_UCHAR NONDET_SHORT NONDET_USHORT NONDET_INT NONDET_UINT NONDET_LONG NONDET_ULONG NONDET LNONDET
%token ASSUME ERROR ABORT ASSERT_FAIL DOCHECK
%token ATTRIBUTE NORETURN NOTHROW LEAF
%token ADD MINUS ASTERISK DIV MOD ADDR
%token PLUSPLUS MINUSMINUS

%token <Ast.LogicOld.pred_sym> PREDSYM
%token <int> INTL
%token <string> ID
%token <string> STRINGL

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
  /* ignore: extern void __VERIFIER_error(); */
    EXTERN VOID ERROR LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern void __VERIFIER_assume(); */
  | EXTERN VOID ASSUME LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern int __VERIFIER_nondet_bool(); */
  | EXTERN INT NONDET_BOOL LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern char __VERIFIER_nondet_char(); */
  | EXTERN CHAR NONDET_CHAR LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern unsigned char __VERIFIER_nondet_uchar(); */
  | EXTERN UNSIGNED CHAR NONDET_UCHAR LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern short __VERIFIER_nondet_short(); */
  | EXTERN SHORT NONDET_SHORT LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern unsigned short __VERIFIER_nondet_ushort(); */
  | EXTERN UNSIGNED SHORT NONDET_USHORT LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern int __VERIFIER_nondet_int(); */
  | EXTERN INT NONDET_INT LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern unsigned int __VERIFIER_nondet_uint(); */
  | EXTERN UNSIGNED INT NONDET_UINT LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern long __VERIFIER_nondet_long(); */
  | EXTERN LONG NONDET_LONG LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern unsigned long __VERIFIER_nondet_ulong(); */
  | EXTERN UNSIGNED LONG NONDET_ULONG LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern void abort(); */
  | EXTERN VOID ABORT LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern int abort(); */
  | EXTERN INT ABORT LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern void __assert_fail(const char *, const char *, unsigned int, const char *); */
  | EXTERN VOID ASSERT_FAIL LPAREN CONST CHAR ASTERISK COMMA CONST CHAR ASTERISK COMMA UNSIGNED INT COMMA CONST CHAR ASTERISK RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* int __phi() { return CAG( CAP(x > 1) ); } */
  | INT PHI LPAREN RPAREN LBLOCK RETURN phi=Phi SEMI RBLOCK { Some phi, [], None, None, [], [] }
  /* void init() { p = 0; start = 0; } */
  | VOID INIT LPAREN RPAREN LBLOCK inits=Init RBLOCK { None, [], Some inits, None, [], [] }
  | INT INIT LPAREN RPAREN LBLOCK inits=Init RBLOCK { None, [], Some inits, None, [], [] }
  | VOID BODY LPAREN RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], None, Some (Statement.of_statements stmts), [], []
  }
  | INT BODY LPAREN RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], None, Some (Statement.of_statements stmts), [], []
  }
  /* #include "../ctl.h" */
  | SHARPINCLUDE s=STRINGL {
    if String.(s = "../ctl.h") then
      None, [], None, None, [], []
    else
      raise (SyntaxError "#include is not implemented")
  }
  /* #define XX 12 */
  | SHARPDEFINE id=ID value=INTL {
    None, [], None, None, [Define.mk_def id value], []
  }
  /* #define hoge() nondet() */
  | SHARPDEFINE funname=ID LPAREN RPAREN NONDET LPAREN RPAREN {
    None, [], None, None, [], [FunDecl.mk_fun_nondet funname []]
  }

  /* int a, b, c; */
  | decls=VarDecl { None, decls, None, None, [], [] }

  /* void main() { ... } */
  | VOID MAIN LPAREN VOID? RPAREN LBLOCK stmts=Statements RBLOCK
  /* int main() { ... } */
  | Int MAIN LPAREN VOID? RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], None, Some (Statement.of_statements stmts), [], []
  }
  /* void main() {} */
  | VOID MAIN LPAREN VOID? RPAREN LBLOCK RBLOCK {
    None, [], None, None, [], []
  }
  /* int main() {} */
  | Int MAIN LPAREN VOID? RPAREN LBLOCK RBLOCK {
    None, [], None, None, [], []
  }
  /* void f(int a, int *b) { ... } */
  | VOID funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], None, None, [], [FunDecl.mk_fun_void funname params (Statement.of_statements stmts)]
  }
  /* int f(int a, int *b) { ... } */
  | Int funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], None, None, [], [FunDecl.mk_fun_int funname params (Statement.of_statements stmts)]
  }
  /* TODO */ /* int f(int a, int *b) { return nondet(); } */
  | Int funname=ID LPAREN params=Parameters RPAREN LBLOCK RETURN NONDET LPAREN RPAREN SEMI RBLOCK {
    None, [], None, None, [], [FunDecl.mk_fun_nondet funname params]
  }
  /* TODO */ /* int f(int a, int *b) { x = nondet(); return x; } */
  | Int funname=ID LPAREN params=Parameters RPAREN LBLOCK varname1=ID EQUAL NONDET LPAREN RPAREN SEMI RETURN varname2=ID SEMI RBLOCK {
    assert String.(varname1 = varname2);
    None, [], None, None, [], [FunDecl.mk_fun_nondet funname params]
  }

Int: CHAR | SHORT | INT | LONG | LONG LONG { () }

/* int a, b, c; */
VarDecl:
    VOID varnames=Variables SEMI
  | Int varnames=Variables SEMI
  | VarDeclIntType varnames=Variables SEMI {
    List.map varnames ~f:(fun varname -> Declare.mk_int varname)
  }

VarDeclIntType:
    UNSIGNED Int
  | CONST Int
  | STATIC Int
  | STATIC CONST Int
  | STATIC VOLATILE Int
  | STATIC VOID { () }

/* a, b, c */
Variables:
    varnames=Variable { varnames }
  | varnames1=Variable COMMA varnames=Variables { varnames1 @ varnames }

Variable:
    varname=ID { [varname] }
  | LNONDET { [] }

Attributes:
    { () }
  /* ignore: __attribute__ ((__noreturn__)) */
  | ATTRIBUTE LPAREN LPAREN NORETURN RPAREN RPAREN Attributes { () }
  /* ignore: __attribute__ ((__nothrow__ , __leaf__)) */
  | ATTRIBUTE LPAREN LPAREN NOTHROW COMMA LEAF RPAREN RPAREN Attributes { () }

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
    Int { T_int.SInt }
  | Int ASTERISK { T_int.SRefInt }

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
    List.fold_left ~init:inits
      ~f:(fun inits varname -> Init.mk_assign varname term :: inits)
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
  | LBLOCK stmts=Statements RBLOCK { Statement.of_statements stmts }
  /* label */
  | ID COLON { Statement.mk_nop () }
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
  /* abort */
  | ERROR LPAREN RPAREN SEMI { Statement.mk_nop ()(*ToDo*) }
  | ABORT LPAREN RPAREN SEMI { Statement.mk_nop ()(*ToDo*) }
  | ASSERT_FAIL LPAREN args=Arguements RPAREN SEMI { ignore args; Statement.mk_nop ()(*ToDo*) }
  /* nops */
  | t=Term SEMI {
    if Term.is_funcall t then
      let funname, args, _ = Term.let_funcall t in
      Statement.mk_call_voidfun funname args
    else
      Statement.mk_assign "#_" t
  }
  | SEMI { Statement.mk_nop () }
  /*| INTL SEMI { Statement.mk_nop () }*/

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
    t=T_intMulDivMod { t }
  | t1=T_intAddSub ADD t2=T_intMulDivMod { T_int.mk_add t1 t2 ~info:Dummy }
  | t1=T_intAddSub MINUS t2=T_intMulDivMod { T_int.mk_sub t1 t2 ~info:Dummy }

T_intMulDivMod:
    t=T_intUnary { t }
  | t1=T_intMulDivMod ASTERISK t2=T_intUnary { T_int.mk_mul t1 t2 ~info:Dummy }
  | t1=T_intMulDivMod DIV t2=T_intUnary { T_int.mk_div Value.Truncated t1 t2 ~info:Dummy }
  | t1=T_intMulDivMod MOD t2=T_intUnary { T_int.mk_rem Value.Truncated t1 t2 ~info:Dummy }

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
  | funname=ID LPAREN t1=T_int op=PREDSYM t2=T_int RPAREN { (* ToDo *)
    let cond = Formula.mk_atom @@ Atom.mk_app (Predicate.mk_psym op) [t1; t2] ~info:Dummy in
    Term.mk_fsym_app (FunCall funname) [T_bool.ifte cond (T_int.one ()) (T_int.zero ()) ~info:Dummy] ~info:Dummy
  }
  | ADDR varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy }
  | ASTERISK varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SUnrefInt ~info:Dummy }
  /* sizeof(char) -> 1 */
  | SIZEOF LPAREN CHAR RPAREN { T_int.from_int 1 ~info:Dummy }
  /* sizeof(short) -> 2 */
  | SIZEOF LPAREN SHORT RPAREN { T_int.from_int 2 ~info:Dummy }
  /* sizeof(int) -> 4 */
  | SIZEOF LPAREN INT RPAREN { T_int.from_int 4 ~info:Dummy }
  /* sizeof(long) -> 8 */
  | SIZEOF LPAREN LONG RPAREN { T_int.from_int 8 ~info:Dummy }
  /* "hoge" */
  | str=STRINGL { term_of_string str }
  /* "hoge" "fuga" */
  | str1=STRINGL str2=STRINGL { term_of_string (str1 ^ str2) }
  /* nondet() */
  | NONDET_BOOL LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_bool) [] ~info:Dummy }
  | NONDET_CHAR LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_char) [] ~info:Dummy }
  | NONDET_UCHAR LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_uchar) [] ~info:Dummy }
  | NONDET_SHORT LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_short) [] ~info:Dummy }
  | NONDET_USHORT LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_ushort) [] ~info:Dummy }
  | NONDET_INT LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_int) [] ~info:Dummy }
  | NONDET_UINT LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_uint) [] ~info:Dummy }
  | NONDET_LONG LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_long) [] ~info:Dummy }
  | NONDET_ULONG LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_ulong) [] ~info:Dummy }

Cast:
    LPAREN Int RPAREN
  | LPAREN UNSIGNED Int RPAREN
  | LPAREN VOID RPAREN { () }

/* Ast.LogicOld.T_bool */
T_bool:
    t1=T_int op=PREDSYM t2=T_int { Atom.mk_app (Predicate.mk_psym op) [t1; t2] ~info:Dummy }
