%{
  open Core
  open Ast
  open Ast.LogicOld
  open CSyntax

  (* a loop body whose [continue]s jump to its end, the loop's next iteration;
     [continue] used to be read as an expression statement naming a variable,
     a no-op, so the rest of the body ran *)
  let loop_body body =
    let body, cont = Statement.close_continue body in
    Statement.of_statements (body :: Option.to_list cont)
%}

%token IF ELSE DO WHILE FOR BREAK CONTINUE RETURN GOTO
%token LPAREN RPAREN LBLOCK RBLOCK EOF
%token EQUAL
%token NOT AND OR
%token COLON SEMI COMMA
%token UNSIGNED VOID CHAR SHORT INT LONG FLOAT DOUBLE
%token EXTERN CONST STATIC VOLATILE SIZEOF
%token SHARPINCLUDE SHARPDEFINE
%token PHI INIT BODY
%token CAF CEF CAG CEG CAP CAND COR CIMP
%token MAIN
%token NONDET_BOOL NONDET_CHAR NONDET_UCHAR NONDET_SHORT NONDET_USHORT NONDET_INT NONDET_UINT NONDET_LONG NONDET_ULONG NONDET_FLOAT NONDET_DOUBLE NONDET LNONDET
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
  | d=Decls EOF {
      match d with
        None, _, _, _, _, _ -> raise (SemanticError "function __phi is not declared")
        | _, _, None, _, _, _ -> raise (SemanticError "function init is not declared")
        | _, _, _, None, _, _ -> raise (SemanticError "function body is not declared")
        | Some phi, decls, Some init, Some body, defs, fundecls ->
          (phi, decls, init, body), defs, fundecls
    }

/* Functions and Variables Declarations */
Decls:
  | { None, [], None, None, [], [] }
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
  | EXTERN VOID ERROR LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern void __VERIFIER_assume(); and its prototype form extern void __VERIFIER_assume(int);
     (the SV-COMP declaration, with or without a parameter name).  The declaration is ignored either way:
     a call of __VERIFIER_assume is recognised by its name, so the parameter list carries nothing. */
  | EXTERN VOID ASSUME LPAREN AssumeParameter RPAREN Attributes SEMI { None, [], None, None, [], [] }
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
  /* ignore: extern float __VERIFIER_nondet_float(); */
  | EXTERN FLOAT NONDET_FLOAT LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
  /* ignore: extern double __VERIFIER_nondet_double(); */
  | EXTERN DOUBLE NONDET_DOUBLE LPAREN RPAREN Attributes SEMI { None, [], None, None, [], [] }
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
  /* #define XX -12 (a literal carries no sign: x-1 is a subtraction) */
  | SHARPDEFINE id=ID MINUS value=INTL {
    None, [], None, None, [Define.mk_def id (- value)], []
  }
  /* #define hoge() nondet() */
  | SHARPDEFINE funname=ID LPAREN RPAREN NONDET LPAREN RPAREN {
    None, [], None, None, [], [FunDecl.mk_fun_nondet_int(*ToDo*) funname []]
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
    None, [], None, None, [], [FunDecl.mk_fun_nondet_int funname params]
  }
  /* TODO */ /* int f(int a, int *b) { x = nondet(); return x; } */
  | Int funname=ID LPAREN params=Parameters RPAREN LBLOCK varname1=ID EQUAL NONDET LPAREN RPAREN SEMI RETURN varname2=ID SEMI RBLOCK {
    assert String.(varname1 = varname2);
    None, [], None, None, [], [FunDecl.mk_fun_nondet_int funname params]
  }

/* the width of a narrow integer type; [None] for the int-ranked ones */
IntWidth:
  | CHAR { Some 8 }
  | SHORT { Some 16 }
  | INT | LONG | LONG LONG { None }

/* the type of a declaration, a parameter or a function's result */
Int: n=IntWidth { refuse_narrow_decl n }

/* int a, b, c; */
VarDecl:
  | VOID varnames=Variables SEMI
  | Int varnames=Variables SEMI
  | VarDeclIntType varnames=Variables SEMI {
    List.map varnames ~f:(fun varname -> Declare.mk_int varname)
  }

VarDeclIntType:
  | UNSIGNED Int { unsigned_seen := true }
  | CONST Int
  | STATIC Int
  | STATIC CONST Int
  | STATIC VOLATILE Int
  | STATIC VOID { () }

/* a, b, c */
Variables:
  | varnames=Variable { varnames }
  | varnames1=Variable COMMA varnames=Variables { varnames1 @ varnames }

Variable:
  | varname=ID { [varname] }
  | LNONDET { [] }

/* The parameter list of an ignored __VERIFIER_assume declaration: empty, int, or int with a name. */
AssumeParameter:
  | { () }
  | INT ID? { () }

Attributes:
  | { () }
  /* ignore: __attribute__ ((__noreturn__)) */
  | ATTRIBUTE LPAREN LPAREN NORETURN RPAREN RPAREN Attributes { () }
  /* ignore: __attribute__ ((__nothrow__ , __leaf__)) */
  | ATTRIBUTE LPAREN LPAREN NOTHROW COMMA LEAF RPAREN RPAREN Attributes { () }

/* int a, int* b */
Parameters:
  | { [] }
  | params=ParametersOneOrMore { params }

ParametersOneOrMore:
  | param=Parameter { [param] }
  | param=Parameter COMMA params=ParametersOneOrMore { param :: params }

Parameter:
  | sort=Type varname=ID { varname, sort }

/* a, 3+5, b */
Arguements:
  | { [] }
  | args=ArguementsOneOrMore { args }

ArguementsOneOrMore:
  | t=Term { [t] }
  | t=Term COMMA args=ArguementsOneOrMore { t :: args }

Type:
  | Int { T_int.SInt }
  | Int ASTERISK { T_int.SRefInt }

/* CAG( CAP(x > 1) ) */
Phi:
  | CAF LPAREN phi=Phi RPAREN { Ctl.mk_af phi }
  | CEF LPAREN phi=Phi RPAREN { Ctl.mk_ef phi }
  | CAG LPAREN phi=Phi RPAREN { Ctl.mk_ag phi }
  | CEG LPAREN phi=Phi RPAREN { Ctl.mk_eg phi }
  | CAND LPAREN phi1=Phi COMMA phi2=Phi RPAREN { Ctl.mk_and phi1 phi2 }
  | COR LPAREN phi1=Phi COMMA phi2=Phi RPAREN { Ctl.mk_or phi1 phi2 }
  | CIMP LPAREN phi1=Phi COMMA phi2=Phi RPAREN { Ctl.mk_imp phi1 phi2 }
  | CAP LPAREN fml=Formula RPAREN { Ctl.mk_ap fml }

/* Init */
Init:
  | { [] }
  | data=MultipleAssignInit inits=Init {
    let varnames, term = data in
    List.fold_left ~init:inits varnames
      ~f:(fun inits varname -> Init.mk_assign varname term :: inits)
  }
  | varnames=MultipleNondetAssignInit inits=Init {
    List.map varnames ~f:Init.mk_nondet_int_assign @ inits
  }
  | ASSUME LPAREN fml=Formula RPAREN SEMI inits=Init { Init.mk_assume fml :: inits }

/* a = b = c = 10; */
MultipleAssignInit:
  | varname=ID EQUAL term=Term SEMI { [varname], term }
  | varname=ID EQUAL tail=MultipleAssignInit {
    let varnames, term = tail in
    varname :: varnames, term
  }

/* a = b = c = nondet(); -- a draw each, kept so that one overwrites an
   earlier assignment in init */
MultipleNondetAssignInit:
  | varname=ID EQUAL NONDET LPAREN RPAREN SEMI { [varname] }
  | varname=ID EQUAL LNONDET SEMI { [varname] }
  | varname=ID EQUAL varnames=MultipleNondetAssignInit { varname :: varnames }

/* a = 3; if (x > 0) { y = 10; } */
Statements:
  | { [] }
  | stmt=Statement stmts=Statements { stmt :: stmts }

Statement:
  | stmt=StatementGeneral { stmt }
  | IF LPAREN cond_fml=Formula RPAREN t_stmt=Statement { Statement.mk_if cond_fml t_stmt (Statement.mk_nop ()) }
  | IF LPAREN LNONDET RPAREN stmt=Statement { Statement.mk_nondet stmt (Statement.mk_nop ()) }
  | IF LPAREN cond_fml=Formula RPAREN t_stmt=StatementIfT ELSE f_stmt=Statement { Statement.mk_if cond_fml t_stmt f_stmt }
  | IF LPAREN LNONDET RPAREN stmt1=StatementIfT ELSE stmt2=Statement { Statement.mk_nondet stmt1 stmt2 }
  | WHILE LPAREN cond_n=INTL RPAREN stmt=Statement {
      if cond_n = 0 then
        Statement.mk_nop ()
      else
        Statement.mk_loop (loop_body stmt)
    }

StatementIfT:
  | stmt=StatementGeneral { stmt }
  | IF LPAREN cond_fml=Formula RPAREN t_stmt=StatementIfT ELSE f_stmt=StatementIfT { Statement.mk_if cond_fml t_stmt f_stmt }
  | IF LPAREN LNONDET RPAREN stmt1=StatementIfT ELSE stmt2=StatementIfT { Statement.mk_nondet stmt1 stmt2 }
  | WHILE LPAREN cond_n=INTL RPAREN stmt=StatementIfT {
      if cond_n = 0 then
        Statement.mk_nop ()
      else
        Statement.mk_loop (loop_body stmt)
    }

StatementGeneral:
  | varname=ID EQUAL term=Term SEMI { Statement.mk_assign varname term }
  | varname=ID EQUAL NONDET LPAREN RPAREN SEMI { Statement.mk_nondet_int_assign varname }
  | varname=ID EQUAL LNONDET SEMI { Statement.mk_nondet_int_assign varname }
  | BREAK SEMI { Statement.mk_break () }
  | CONTINUE SEMI { Statement.mk_continue () }
  /* A return leaves the function it is in: inlining turns a helper's into a
     jump to its call site, and those left in body or main end the run.
     Reading every return as the end of the run let a helper's return 1;
     stop the program at its call. */
  | RETURN t=Term SEMI { Statement.mk_return_int t }
  | RETURN SEMI { Statement.mk_return_void () }
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
  /* abort(), __VERIFIER_error() and __assert_fail(...) do not return: the run
     ends there, as it does at a return from main.  Reading them as a no-op let
     the statements after them run and decide the property. */
  | ERROR LPAREN RPAREN SEMI { Statement.mk_exit () }
  | ABORT LPAREN RPAREN SEMI { Statement.mk_exit () }
  | ASSERT_FAIL LPAREN args=Arguements RPAREN SEMI { ignore args; Statement.mk_exit () }
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
  | fml=FormulaOr { fml }

FormulaOr:
  | left=FormulaAnd OR right=FormulaOr { Formula.mk_or left right ~info:Dummy }
  | fml=FormulaAnd { fml }

FormulaAnd:
  | left=FormulaNeg AND right=FormulaAnd { Formula.mk_and left right ~info:Dummy }
  | fml=FormulaNeg { fml }

/* C's ! binds tighter than a comparison: !x > 0 is (!x) > 0, which is x == 0,
   not !(x > 0).  So a negated formula is a parenthesised formula, another
   negation or a bare term; a ! that a comparison follows is the term
   operator of T_intUnary. */
FormulaNeg:
  | NOT fml=FormulaNegOperand { Formula.mk_neg fml ~info:Dummy }
  | fml=FormulaAtom { fml }

FormulaNegOperand:
  | NOT fml=FormulaNegOperand { Formula.mk_neg fml ~info:Dummy }
  | LPAREN fml=Formula RPAREN { fml }
  | term=T_intAtom { formula_of_term term }

FormulaAtom:
  | atom=Atom { Formula.mk_atom atom ~info:Dummy }
  | LPAREN fml=Formula RPAREN { fml }
  | term=T_intAtom { formula_of_term term }

/* Ast.LogicOld.Atom.t */
Atom:
  | atom=T_bool { atom }


/* Ast.LogicOld.Term.t */
/* Ast.LogicOld.T_int */
Term:
  | t=T_int { t }

T_int:
  | t=T_intAddSub { t }

T_intAddSub:
  | t=T_intMulDivMod { t }
  | t1=T_intAddSub ADD t2=T_intMulDivMod { T_int.mk_add t1 t2 ~info:Dummy }
  | t1=T_intAddSub MINUS t2=T_intMulDivMod { T_int.mk_sub t1 t2 ~info:Dummy }

T_intMulDivMod:
  | t=T_intUnary { t }
  | t1=T_intMulDivMod ASTERISK t2=T_intUnary { T_int.mk_mul t1 t2 ~info:Dummy }
  | t1=T_intMulDivMod DIV t2=T_intUnary { T_int.mk_div Value.Truncated t1 t2 ~info:Dummy }
  | t1=T_intMulDivMod MOD t2=T_intUnary { T_int.mk_rem Value.Truncated t1 t2 ~info:Dummy }

T_intUnary:
  | t=T_intParen { t }
  /* a cast to char or short converts modulo 2^bits; one to an int-ranked
     type is the identity, these types being mathematical integers here */
  | c=Cast t=T_intUnary {
    match c with
    | None -> t
    | Some (bits, signed) -> convert_to_narrow bits signed t }
  | MINUS t=T_intUnary { T_int.mk_neg t ~info:Dummy }
  /* !e as a value: 1 when e is 0, else 0 */
  | NOT t=T_intUnary {
    T_bool.ifte (Formula.eq t (T_int.zero ())) (T_int.one ()) (T_int.zero ()) ~info:Dummy
  }

T_intParen:
  | t=T_intAtom { t }
  | LPAREN t=T_int RPAREN { t }

T_intAtom:
  | n=INTL { T_int.from_int n ~info:Dummy }
  | varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy }
  | funname=ID LPAREN args=Arguements RPAREN {
    Term.mk_fsym_app (FunCall funname) args ~info:Dummy
  }
  | funname=ID LPAREN t1=T_int op=PREDSYM t2=T_int RPAREN { (* ToDo *)
    let cond = Formula.mk_atom @@ Atom.mk_psym_app op [t1; t2] ~info:Dummy in
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
  | NONDET_FLOAT LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_float) [] ~info:Dummy }
  | NONDET_DOUBLE LPAREN RPAREN { Term.mk_fsym_app (FunCall funname_nondet_double) [] ~info:Dummy }

Cast:
  | LPAREN UNSIGNED n=IntWidth RPAREN {
    match n with
    | None -> unsigned_seen := true; None
    | Some bits -> Some (bits, false) }
  | LPAREN n=IntWidth RPAREN { Option.map n ~f:(fun bits -> (bits, true)) }
  | LPAREN VOID RPAREN { None }

/* Ast.LogicOld.T_bool */
T_bool:
  | t1=T_int op=PREDSYM t2=T_int { Atom.mk_app (Predicate.mk_psym op) [t1; t2] ~info:Dummy }
