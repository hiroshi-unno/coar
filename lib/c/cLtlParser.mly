%{
  open Core
  open Ast
  open Ast.LogicOld
  open CSyntax
%}

%token IF ELSE DO WHILE WHILE_TRUE FOR BREAK RETURN GOTO
%token LPAREN RPAREN LBLOCK RBLOCK EOF
%token EQUAL
%token NOT AND OR IMPLY
%token COLON SEMI COMMA
%token UNSIGNED VOID CHAR SHORT INT LONG EXTERN CONST STATIC VOLATILE SIZEOF
%token BOX DIAMOND X AP U R WU
%token MAIN
%token NONDET_BOOL NONDET_CHAR NONDET_UCHAR NONDET_SHORT NONDET_USHORT NONDET_INT NONDET_UINT NONDET_LONG NONDET_ULONG
%token ASSUME ERROR ABORT ASSERT_FAIL
%token ATTRIBUTE NORETURN NOTHROW LEAF
%token ADD MINUS ASTERISK DIV MOD ADDR
%token PLUSPLUS MINUSMINUS

%token <string> LTLDECLARE
%token <Ast.LogicOld.pred_sym> PREDSYM
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
  /* ignore: extern void __VERIFIER_error(); */
    EXTERN VOID ERROR LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern void __VERIFIER_assume(); */
  | EXTERN VOID ASSUME LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern int __VERIFIER_nondet_bool(); */
  | EXTERN INT NONDET_BOOL LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern char __VERIFIER_nondet_char(); */
  | EXTERN CHAR NONDET_CHAR LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern unsigned char __VERIFIER_nondet_uchar(); */
  | EXTERN UNSIGNED CHAR NONDET_UCHAR LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern short __VERIFIER_nondet_short(); */
  | EXTERN SHORT NONDET_SHORT LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern unsigned short __VERIFIER_nondet_ushort(); */
  | EXTERN UNSIGNED SHORT NONDET_USHORT LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern int __VERIFIER_nondet_int(); */
  | EXTERN INT NONDET_INT LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern unsigned int __VERIFIER_nondet_uint(); */
  | EXTERN UNSIGNED INT NONDET_UINT LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern long __VERIFIER_nondet_long(); */
  | EXTERN LONG NONDET_LONG LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern unsigned long __VERIFIER_nondet_ulong(); */
  | EXTERN UNSIGNED LONG NONDET_ULONG LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern void abort(); */
  | EXTERN VOID ABORT LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern int abort(); */
  | EXTERN INT ABORT LPAREN RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* ignore: extern void __assert_fail(const char *, const char *, unsigned int, const char *); */
  | EXTERN VOID ASSERT_FAIL LPAREN CONST CHAR ASTERISK COMMA CONST CHAR ASTERISK COMMA UNSIGNED INT COMMA CONST CHAR ASTERISK RPAREN Attributes SEMI { None, [], [], None, [], [] }
  /* //@ ltl invariant <name>: <>[]AP(x==1); */
  | label=LTLDECLARE phi=Phi SEMI { ignore label; Some phi, [], [], None, [], [] }

  /* int a, b, c; */
  | decls=VarDecl {
      let decls, inits = decls in
      None, decls, inits, None, [], []
    }
  /* p = 0; */
  | inits=Init { None, [], inits, None, [], [] }
  /* void main() { ... } */
  | VOID MAIN LPAREN VOID? RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], [], Some (Statement.of_statements stmts), [], []
  }
  /* int main() { ... } */
  | Int MAIN LPAREN VOID? RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], [], Some (Statement.of_statements stmts), [], []
  }
  /* void f(int a, int *b) { ... } */
  | VOID funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], [], None, [], [FunDecl.mk_fun_void funname params (Statement.of_statements stmts)]
  }
  /* int f(int a, int *b) { ... } */
  | Int funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK
  | VOID ASTERISK funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    None, [], [], None, [], [FunDecl.mk_fun_int funname params (Statement.of_statements stmts)]
  }

Int: CHAR | SHORT | INT | LONG | LONG LONG { () }

/* int a, b, c = 0; */
VarDecl:
    VOID decls=IntVarDecls SEMI
  | Int decls=IntVarDecls SEMI
  | VarDeclIntType decls=IntVarDecls SEMI {
    let varnames, stmts = decls in
    List.map varnames ~f:(fun varname -> Declare.mk_int varname),
    match stmts with
      [] -> []
    | stmts -> Statement.of_statements stmts |> Init.of_stmt_exn []
  }

VarDeclIntType:
    UNSIGNED Int
  | CONST Int
  | STATIC Int
  | STATIC CONST Int
  | STATIC VOLATILE Int
  | STATIC VOID { () }

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
    match type_of_nondet term with
    | Some (32, true) ->
      assert (List.length varnames <= 1);
      List.map ~f:(fun varname -> Init.mk_nondet_assign varname) varnames
    | None -> List.map ~f:(fun varname -> Init.mk_assign varname term) varnames
    | _ -> failwith "only nondet_int supported in init"
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
      let cond_fml = Formula.neq term (T_int.zero ()) in
      Statement.of_statements [
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
      let cond_fml = Formula.neq term (T_int.zero ()) in
      fun f_stmt ->
        Statement.of_statements [
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
      Statement.of_statements [
        Statement.of_statements stmts;
        Statement.mk_if cond_fml (Statement.mk_nop ()) (Statement.mk_break ())
      ]
      |> Statement.mk_loop
    }

For:
    /* TODO */
    FOR LPAREN init_stmt=ForInit SEMI cond_fml=ForCond SEMI step_var=ID PLUSPLUS RPAREN {
      fun stmt ->
        Statement.of_statements [
          init_stmt;
          Statement.mk_if cond_fml
            (Statement.of_statements [
              stmt;
              let tvar = Ident.Tvar step_var in
              Statement.mk_assign step_var
                (T_int.mk_add
                  (Term.mk_var tvar T_int.SInt ~info:Dummy)
                  (T_int.one ())
                  ~info:Dummy)
            ])
            (Statement.mk_break ())
          |> Statement.mk_loop
        ]
    }
  | FOR LPAREN init_stmt=ForInit SEMI cond_fml=ForCond SEMI RPAREN {
      fun stmt ->
        Statement.of_statements [
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
  | stmts=ForInits { Statement.of_statements stmts }

IntVarDeclOne:
    varname=ID {
        varname, Some (Statement.mk_assign varname (*ToDo*)(T_int.zero ()))
    }
  | ASTERISK varname=ID { varname, (*ToDo*)None }
  | varname=ID EQUAL term=Term {
      match type_of_nondet term with
      | Some (1, false) ->
        let x = Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy in
        varname,
        Some (Statement.mk_assume (Formula.or_of [Formula.eq x (T_int.zero ()); Formula.eq x (T_int.one ())]))
      | Some (32, true) -> varname, None (*ToDo*)
      | None -> varname, Some (Statement.mk_assign varname term)
      | _ -> failwith "only nondet_int and nondet_bool supported in var decl"
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
      match type_of_nondet term with
      | Some (1, false) ->
        let x = Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy in
        Statement.mk_compound
          (Statement.mk_nondet_assign varname)
          (Statement.mk_assume (Formula.or_of [Formula.eq x (T_int.zero ()); Formula.eq x (T_int.one ())]))
      | Some (_(*16*), false) ->
        let x = Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy in
        Statement.mk_compound
          (Statement.mk_nondet_assign varname)
          (Statement.mk_assume (Formula.geq x (T_int.zero ()))) (*ToDo*)
      | Some (_(*32*), true) -> Statement.mk_nondet_assign varname (*ToDo*)
      | None -> Statement.mk_assign varname term
    }
  /*| varname=ID EQUAL fml=Formula SEMI {
      Statement.mk_assign varname (T_bool.ifte fml (T_int.one ()) (T_int.zero ()) ~info:Dummy)
    }*/
  /* TODO */
  | varname1=ID EQUAL varname2=ID EQUAL term=Term SEMI {
      Statement.mk_compound (Statement.mk_assign varname1 term) (Statement.mk_assign varname2 term)
    }
  | LPAREN ASTERISK varname=ID RPAREN EQUAL term=Term SEMI {
      Statement.mk_unref_assign varname term
    }
  | stmt=DoWhile { stmt }
  /* int a = 3, b = 2; */
  | Int decls=IntVarDecls SEMI | CONST Int decls=IntVarDecls SEMI
  | VOID decls=IntVarDecls SEMI
  | CONST VOID decls=IntVarDecls SEMI {
      let varnames, stmts = decls in
      List.map ~f:(fun varname -> Statement.mk_vardecl varname T_int.SInt) varnames
      @ stmts
      |> Statement.of_statements
    }
  | BREAK SEMI { Statement.mk_break () }
  | RETURN term=Term SEMI {
      match type_of_nondet term with
      | Some (32, true) -> Statement.mk_return_nondet () (*ToDo*)
      | None -> Statement.mk_return_int term
      | _ -> failwith "only nondet_int supported in return"
    }
  | RETURN SEMI { Statement.mk_return_void () }
  | LBLOCK stmts=Statements RBLOCK { Statement.of_statements stmts }
  /* goto */
  | GOTO label_name=ID SEMI { Statement.mk_goto label_name }
  /* label */
  | label_name=ID COLON { Statement.mk_label label_name }
  | ASSUME LPAREN fml=Formula RPAREN SEMI { Statement.mk_assume fml }
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
  /* --x, ++x */
  | MINUSMINUS varname=ID {
    Term.mk_fsym_app (FunCall "#dec") [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy
  }
  | PLUSPLUS varname=ID {
    Term.mk_fsym_app (FunCall "#inc") [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy
  }
  /* x--, x++ */
  | varname=ID MINUSMINUS {
    T_int.mk_add (Term.mk_fsym_app (FunCall "#dec") [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy) (T_int.one ()) ~info:Dummy
  }
  | varname=ID PLUSPLUS {
    T_int.mk_sub (Term.mk_fsym_app (FunCall "#inc") [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy) (T_int.one ()) ~info:Dummy
  }
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
