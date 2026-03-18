%{
  open Core
  open Ast
  open Ast.LogicOld
  open Common.Ext
  open CSyntax
%}

%token IF ELSE DO WHILE WHILE_TRUE FOR BREAK RETURN GOTO
%token LPAREN RPAREN LBLOCK RBLOCK EOF
%token EQUAL
%token NOT AND OR IMPLY
%token COLON SEMI COMMA
%token UNSIGNED VOID CHAR SHORT INT LONG FLOAT DOUBLE
%token EXTERN CONST STATIC VOLATILE SIZEOF
%token BOX DIAMOND X AP U R WU
%token MAIN
%token NONDET_BOOL NONDET_CHAR NONDET_UCHAR NONDET_SHORT NONDET_USHORT NONDET_INT NONDET_UINT NONDET_LONG NONDET_ULONG NONDET_FLOAT NONDET_DOUBLE
%token ASSUME ERROR ABORT ASSERT_FAIL
%token ATTRIBUTE NORETURN NOTHROW LEAF
%token ADD MINUS ASTERISK DIV MOD ADDR
%token PLUSPLUS MINUSMINUS

%token <string> LTLDECLARE
%token <Ast.LogicOld.Sort.t -> Ast.LogicOld.pred_sym> PREDSYM
%token <int> INTL
%token <float> FLOATL
%token <string> ID
%token <string> STRINGL

%start toplevel
%type <CSyntax.cltl * CSyntax.Define.t list * CSyntax.FunDecl.t list> toplevel
%%

toplevel:
  | d=Decls EOF {
    match d Map.Poly.empty(*ToDo*) with
    | _, (None, _, _, _, _, _) -> raise (SemanticError "function ltl formula is not declared")
    | _, (_, _, _, None, _, _) -> raise (SemanticError "function main is not declared")
    | senv, (Some phi, decls, init, Some body, defs, fundecls) ->
      (phi senv, decls, init, body), defs, fundecls
  }

/* Functions and Variables Declarations */
Decls:
  | { fun senv -> senv, (None, [], [], None, [], []) }
  | d1=Decl d2=Decls { fun senv ->
    let senv, d1 = d1 senv in
    let senv, d2 = d2 senv in
    senv,
    match d1, d2 with
    | (Some _, _, _, _, _, _), (Some _, _, _, _, _, _) ->
      raise (SemanticError "ltl formula is declared multiple times")
    | (_, _, _, Some _, _, _), (_, _, _, Some _, _, _) ->
      raise (SemanticError "function main is declared multiple times")
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
  | EXTERN VOID ERROR LPAREN RPAREN Attributes SEMI
  /* ignore: extern void __VERIFIER_assume(); */
  | EXTERN VOID ASSUME LPAREN RPAREN Attributes SEMI
  /* ignore: extern int __VERIFIER_nondet_bool(); */
  | EXTERN INT NONDET_BOOL LPAREN RPAREN Attributes SEMI
  /* ignore: extern char __VERIFIER_nondet_char(); */
  | EXTERN CHAR NONDET_CHAR LPAREN RPAREN Attributes SEMI
  /* ignore: extern unsigned char __VERIFIER_nondet_uchar(); */
  | EXTERN UNSIGNED CHAR NONDET_UCHAR LPAREN RPAREN Attributes SEMI
  /* ignore: extern short __VERIFIER_nondet_short(); */
  | EXTERN SHORT NONDET_SHORT LPAREN RPAREN Attributes SEMI
  /* ignore: extern unsigned short __VERIFIER_nondet_ushort(); */
  | EXTERN UNSIGNED SHORT NONDET_USHORT LPAREN RPAREN Attributes SEMI
  /* ignore: extern int __VERIFIER_nondet_int(); */
  | EXTERN INT NONDET_INT LPAREN RPAREN Attributes SEMI
  /* ignore: extern unsigned int __VERIFIER_nondet_uint(); */
  | EXTERN UNSIGNED INT NONDET_UINT LPAREN RPAREN Attributes SEMI
  /* ignore: extern long __VERIFIER_nondet_long(); */
  | EXTERN LONG NONDET_LONG LPAREN RPAREN Attributes SEMI
  /* ignore: extern unsigned long __VERIFIER_nondet_ulong(); */
  | EXTERN UNSIGNED LONG NONDET_ULONG LPAREN RPAREN Attributes SEMI
  /* ignore: extern float __VERIFIER_nondet_float(); */
  | EXTERN FLOAT NONDET_FLOAT LPAREN RPAREN Attributes SEMI
  /* ignore: extern double __VERIFIER_nondet_double(); */
  | EXTERN DOUBLE NONDET_DOUBLE LPAREN RPAREN Attributes SEMI
  /* ignore: extern void abort(); */
  | EXTERN VOID ABORT LPAREN RPAREN Attributes SEMI
  /* ignore: extern int abort(); */
  | EXTERN INT ABORT LPAREN RPAREN Attributes SEMI
  /* ignore: extern void __assert_fail(const char *, const char *, unsigned int, const char *); */
  | EXTERN VOID ASSERT_FAIL LPAREN CONST CHAR ASTERISK COMMA CONST CHAR ASTERISK COMMA UNSIGNED INT COMMA CONST CHAR ASTERISK RPAREN Attributes SEMI { fun senv -> senv, (None, [], [], None, [], []) }
  /* //@ ltl invariant <name>: <>[]AP(x==1); */
  | label=LTLDECLARE phi=Phi SEMI { fun senv ->
    ignore label; senv, (Some (fun senv -> phi senv), [], [], None, [], []) }
  /* int a, b, c; */
  | decls=VarDecl { fun senv ->
    let decls, inits = decls senv in
    Map.force_merge senv
      (Map.Poly.of_alist_exn @@
       List.map decls ~f:(function Declare.INT s -> s, T_int.SInt | Declare.REAL s -> s, T_real.SReal)),
    (None, decls, inits, None, [], [])
  }
  /* p = 0; */
  | inits=Init { fun senv ->
    senv, (None, [], inits senv, None, [], []) }
  /* void main() { ... } */
  | VOID MAIN LPAREN VOID? RPAREN LBLOCK stmts=Statements RBLOCK { fun senv ->
    senv, (None, [], [], Some (Statement.of_statements (snd @@ stmts senv)), [], []) }
  /* int main() { ... } */
  | Int MAIN LPAREN VOID? RPAREN LBLOCK stmts=Statements RBLOCK { fun senv ->
    senv, (None, [], [], Some (Statement.of_statements (snd @@ stmts senv)), [], []) }
  /* void f(int a, int *b) { ... } */
  | VOID funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    fun senv ->
      senv,
      (None, [], [], None, [],
       [FunDecl.mk_fun_void funname params (Statement.of_statements (snd @@ stmts senv))])
  }
  /* int f(int a, int *b) { ... } */
  | Int funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK
  | VOID ASTERISK funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    fun senv ->
      senv,
      (None, [], [], None, [],
       [FunDecl.mk_fun_int funname params (Statement.of_statements (snd @@ stmts senv))])
  }
  /* float f(int a, int *b) { ... } */
  | FLOAT funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK
  | DOUBLE funname=ID LPAREN params=Parameters RPAREN LBLOCK stmts=Statements RBLOCK {
    fun senv ->
      senv,
      (None, [], [], None, [],
       [FunDecl.mk_fun_real funname params (Statement.of_statements (snd @@ stmts senv))])
  }

Int: CHAR | SHORT | INT | LONG | LONG LONG { () }

/* int a, b, c = 0; */
VarDecl:
  | VOID decls=IntVarDecls SEMI
  | Int decls=IntVarDecls SEMI
  | VarDeclIntType decls=IntVarDecls SEMI { fun senv ->
    let varnames, stmts = decls senv in
    List.map varnames ~f:Declare.mk_int,
    match stmts with
    | [] -> []
    | stmts -> Init.of_stmt_exn [] @@ Statement.of_statements stmts
  }
  | FLOAT decls=RealVarDecls SEMI
  | DOUBLE decls=RealVarDecls SEMI { fun senv ->
    let varnames, stmts = decls senv in
    List.map ~f:Declare.mk_real varnames,
    match stmts with
    | [] -> []
    | stmts -> Init.of_stmt_exn [] @@ Statement.of_statements stmts
  }

VarDeclIntType:
  | UNSIGNED Int
  | CONST Int
  | STATIC Int
  | STATIC CONST Int
  | STATIC VOLATILE Int
  | STATIC VOID { () }

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
  | { fun _ -> [] }
  | args=ArguementsOneOrMore { args }

ArguementsOneOrMore:
  | t=Term { fun senv -> [ t senv ] }
  | t=Term COMMA args=ArguementsOneOrMore { fun senv -> t senv :: args senv }

Type:
  | Int { T_int.SInt }
  | Int ASTERISK { T_int.SRefInt }
  | FLOAT | DOUBLE { T_real.SReal }
  | FLOAT ASTERISK | DOUBLE ASTERISK { failwith "pointer to float or double is not supported" }

/* CAG( CAP(x > 1) ) */
Phi:
  | phi=PhiUntil { phi }

PhiUntil:
  | phi1=PhiImp U phi2=PhiUntil { fun senv -> Ltl.mk_u (phi1 senv) (phi2 senv) }
  | phi1=PhiImp R phi2=PhiUntil { fun senv -> Ltl.mk_r (phi1 senv) (phi2 senv) }
  | phi1=PhiImp WU phi2=PhiUntil { fun senv -> Ltl.mk_wu (phi1 senv) (phi2 senv) }
  | phi=PhiImp { phi }

PhiImp:
  | phi1=PhiOr IMPLY phi2=PhiImp { fun senv -> Ltl.mk_or (Ltl.mk_neg (phi1 senv)) (phi2 senv) }
  | phi=PhiOr { phi }

PhiOr:
  | phi1=PhiAnd OR phi2=PhiOr { fun senv -> Ltl.mk_or (phi1 senv) (phi2 senv) }
  | phi=PhiAnd { phi }

PhiAnd:
  | phi1=PhiUnary AND phi2=PhiAnd { fun senv -> Ltl.mk_and (phi1 senv) (phi2 senv) }
  | phi=PhiUnary { phi }

PhiUnary:
  | phi=PhiAtom { phi }
  | BOX phi=PhiUnary { fun senv -> Ltl.mk_g (phi senv) }
  | DIAMOND phi=PhiUnary { fun senv -> Ltl.mk_f (phi senv) }
  | X phi=PhiUnary { fun senv -> Ltl.mk_x (phi senv) }
  | NOT phi=PhiUnary { fun senv -> Ltl.mk_neg (phi senv) }

PhiAtom:
  | AP LPAREN fml=Formula RPAREN { fun senv -> Ltl.mk_p (fml senv) }
  | LPAREN phi=Phi RPAREN { phi }

/* Init */
Init:
  | init=InitOne SEMI { init }
  | init=InitOne COMMA inits=Init { fun senv -> init senv @ inits senv }

InitOne:
  | data=MultipleAssignInit { fun senv ->
    let varnames, term = data senv in
    match type_of_nondet term with
    | Some (T_int.SInt, _(*32*), _(*true*)) ->
      assert (List.length varnames <= 1);
      List.map varnames ~f:Init.mk_nondet_int_assign(*ToDo*)
    | Some (T_real.SReal, _(*32*), _(*true*)) ->
      assert (List.length varnames <= 1);
      List.map varnames ~f:Init.mk_nondet_real_assign
    | Some (s, _, _) -> failwith (sprintf "%s not supported in init" (Term.str_of_sort s))
    | None -> List.map varnames ~f:(Fn.flip Init.mk_assign term)
  }
  /* | ASSUME LPAREN fml=Formula RPAREN SEMI inits=Init { Init.mk_assume fml :: inits } */

/* a = b = c = 10 */
MultipleAssignInit:
  | varname=ID EQUAL term=Term { fun senv -> [varname], term senv }
  | varname=ID EQUAL tail=MultipleAssignInit { fun senv ->
    let varnames, term = tail senv in
    varname :: varnames, term
  }

/* a = 3; if (x > 0) { y = 10; } */
Statements:
  | { fun senv -> senv, [] }
  | stmt=Statement stmts=Statements { fun senv ->
    let senv, stmt = stmt senv in
    let senv, stmts = stmts senv in
    senv, stmt :: stmts }

Statement:
  | stmt=StatementGeneral { stmt }
  | IF LPAREN cond_fml=Formula RPAREN t_stmt=Statement { fun senv ->
    senv, Statement.mk_if (cond_fml senv) (snd @@ t_stmt senv) (Statement.mk_nop ()) }
  | IF LPAREN cond_assign_stmt=FormulaAssignOne RPAREN t_stmt=StatementIfT { fun senv ->
    let cond_assign_stmt = cond_assign_stmt senv in
    let varname, s = Statement.varname_of_assign cond_assign_stmt in
    let term = Term.mk_var (Ident.Tvar varname) s ~info:Dummy in
    let cond_fml = Formula.neq term (T_int.zero ()) in
    senv,
    Statement.of_statements [
      cond_assign_stmt;
      Statement.mk_if cond_fml (snd @@ t_stmt senv) (Statement.mk_nop ())
    ] }
  | mk_ifelse=IfElse f_stmt=Statement { fun senv -> senv, mk_ifelse senv f_stmt }
  | mk_while=While stmt=Statement { fun senv -> senv, mk_while senv stmt }
  | mk_for=For stmt=Statement { fun senv -> senv, mk_for senv stmt }

StatementIfT:
  | stmt=StatementGeneral { stmt }
  | mk_ifelse=IfElse f_stmt=StatementIfT { fun senv -> senv, mk_ifelse senv f_stmt }
  | mk_while=While stmt=StatementIfT { fun senv -> senv, mk_while senv stmt }
  | mk_for=For stmt=StatementIfT { fun senv -> senv, mk_for senv stmt }

IfElse:
  | IF LPAREN cond_fml=Formula RPAREN t_stmt=StatementIfT ELSE { fun senv f_stmt ->
    Statement.mk_if (cond_fml senv) (snd @@ t_stmt senv) (snd @@ f_stmt senv) }
  | IF LPAREN cond_assign_stmt=FormulaAssignOne RPAREN t_stmt=StatementIfT ELSE { fun senv ->
    let cond_assign_stmt = cond_assign_stmt senv in
    let varname, s = Statement.varname_of_assign cond_assign_stmt in
    let term = Term.mk_var (Ident.Tvar varname) s ~info:Dummy in
    let cond_fml = Formula.neq term (T_int.zero ()) in
    fun f_stmt ->
      Statement.of_statements [
        cond_assign_stmt;
        Statement.mk_if cond_fml (snd @@ t_stmt senv) (snd @@ f_stmt senv)
      ]
  }

FormulaAssignOne:
  | stmt=ForInitOne { stmt }
  | LPAREN stmt=FormulaAssignOne RPAREN { stmt }

While:
  | WHILE_TRUE { fun senv stmt -> Statement.mk_loop (snd @@ stmt senv) }
  | WHILE LPAREN cond_fml=Formula RPAREN { fun senv stmt ->
    Statement.mk_loop @@
    Statement.mk_if (cond_fml senv) (snd @@ stmt senv) (Statement.mk_break ())
  }

/* do { ... } while (...); */
DoWhile:
  | DO LBLOCK stmts=Statements RBLOCK WHILE LPAREN cond_fml=Formula RPAREN SEMI { fun senv ->
    senv,
    Statement.mk_loop @@
    Statement.of_statements [
      Statement.of_statements (snd @@ stmts senv);
      Statement.mk_if (cond_fml senv) (Statement.mk_nop ()) (Statement.mk_break ())
    ]
  }

For:
    /* TODO */
  | FOR LPAREN init_stmt=ForInit SEMI cond_fml=ForCond SEMI step_var=ID PLUSPLUS RPAREN {
    fun senv stmt ->
      Statement.of_statements [
        init_stmt senv;
        Statement.mk_loop @@
        Statement.mk_if (cond_fml senv)
          (Statement.of_statements [
            snd @@ stmt senv;
            Statement.mk_assign step_var
              (T_int.mk_add
                (Term.mk_var (Ident.Tvar step_var) T_int.SInt ~info:Dummy)
                (T_int.one ())
                ~info:Dummy)
          ])
          (Statement.mk_break ())
      ]
    }
  | FOR LPAREN init_stmt=ForInit SEMI cond_fml=ForCond SEMI RPAREN {
    fun senv stmt ->
      Statement.of_statements [
        init_stmt senv;
        Statement.mk_loop @@
        Statement.mk_if (cond_fml senv) (snd @@ stmt senv) (Statement.mk_break ())
      ]
  }

ForCond:
  | fml=Formula { fml }
  | { fun _ -> Formula.mk_true () ~info:Dummy }

/* a = b, c = d */
ForInitOne:
  | varname=ID EQUAL term=Term { fun senv -> Statement.mk_assign varname (term senv) }

ForInits:
  | stmt=ForInitOne { fun senv -> [ stmt senv ] }
  | stmt=ForInitOne COMMA stmts=ForInits { fun senv -> stmt senv :: stmts senv }

ForInit:
  | { fun _ -> Statement.mk_nop () }
  | stmts=ForInits { fun senv -> Statement.of_statements (stmts senv) }

IntVarDeclOne:
  | varname=ID { fun _ ->
    varname, Some (Statement.mk_assign varname (*ToDo*)(T_int.zero ()))
  }
  | ASTERISK varname=ID { fun _ -> varname, (*ToDo*)None }
  | varname=ID EQUAL term=Term { fun senv ->
    let term = term senv in
    match type_of_nondet term with
    | Some (T_int.SInt, 1, false) ->
      let x = Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy in
      varname,
      Some (Statement.mk_assume (Formula.or_of [Formula.eq x (T_int.zero ()); Formula.eq x (T_int.one ())]))
    | Some (T_int.SInt, _(*32*), _(*true*)) -> varname, None (*ToDo*)
    | Some (s, _, _) -> failwith (sprintf "%s not supported in int var decl" (Term.str_of_sort s))
    | None -> varname, Some (Statement.mk_assign varname term)
  }

IntVarDecls:
  | decl=IntVarDeclOne { fun senv ->
    let varname, stmt = decl senv in
    [varname], Option.to_list stmt
  }
  | decl=IntVarDeclOne COMMA decls=IntVarDecls { fun senv ->
    let varname, stmt = decl senv in
    let varnames, stmts = decls senv in
    varname :: varnames, Option.to_list stmt @ stmts
  }

RealVarDeclOne:
  | varname=ID { fun _ ->
    varname, Some (Statement.mk_assign varname (*ToDo*)(T_real.rzero ()))
  }
  | ASTERISK varname=ID { fun _ -> varname, (*ToDo*)None }
  | varname=ID EQUAL term=Term { fun senv ->
    let term = term senv in
    match type_of_nondet term with
    | Some (T_real.SReal, _(*32*), _(*true*)) -> varname, None (*ToDo*)
    | Some (s, _, _) -> failwith (sprintf "%s not supported in real var decl" (Term.str_of_sort s))
    | None -> varname, Some (Statement.mk_assign varname term)
  }

RealVarDecls:
  | decl=RealVarDeclOne { fun senv ->
    let varname, stmt = decl senv in
    [varname], Option.to_list stmt
  }
  | decl=RealVarDeclOne COMMA decls=RealVarDecls { fun senv ->
    let varname, stmt = decl senv in
    let varnames, stmts = decls senv in
    varname :: varnames, Option.to_list stmt @ stmts
  }

StatementGeneral:
  | varname=ID EQUAL term=Term SEMI { fun senv ->
    let term = term senv in
    senv,
    match type_of_nondet term with
    | Some (T_int.SInt, 1, false) ->
      let x = Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy in
      Statement.mk_compound
        (Statement.mk_nondet_int_assign varname)
        (Statement.mk_assume (Formula.or_of [Formula.eq x (T_int.zero ());
                                             Formula.eq x (T_int.one ())]))
    | Some (T_int.SInt, _(*32*), false) ->
      let x = Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy in
      Statement.mk_compound
        (Statement.mk_nondet_int_assign varname)
        (Statement.mk_assume (Formula.geq x (T_int.zero ()))) (*ToDo*)
    | Some (T_int.SInt, _(*32*), true) ->
      Statement.mk_nondet_int_assign varname (*ToDo*)
    | Some (T_real.SReal, _(*32*), _(*true*)) ->
      Statement.mk_nondet_real_assign varname (*ToDo*)
    | Some (s, _, _) -> failwith (sprintf "%s not supported in assign" (Term.str_of_sort s))
    | None -> Statement.mk_assign varname term
  }
  /* TODO */
  | varname1=ID EQUAL varname2=ID EQUAL term=Term SEMI { fun senv ->
    let term = term senv in
    senv,
    Statement.mk_compound
      (Statement.mk_assign varname1 term)
      (Statement.mk_assign varname2 term) }
  | LPAREN ASTERISK varname=ID RPAREN EQUAL term=Term SEMI { fun senv ->
    senv,
    Statement.mk_unref_assign varname (term senv) }
  /*| varname=ID EQUAL fml=Formula SEMI {
      Statement.mk_assign varname (T_bool.ifte fml (T_int.one ()) (T_int.zero ()) ~info:Dummy)
    }*/
  | stmt=DoWhile { stmt }
  /* int a = 3, b = 2; */
  | Int decls=IntVarDecls SEMI | CONST Int decls=IntVarDecls SEMI
  | VOID decls=IntVarDecls SEMI | CONST VOID decls=IntVarDecls SEMI { fun senv ->
    let varnames, stmts = decls senv in
    Map.force_merge senv (Map.Poly.of_alist_exn @@ List.map varnames ~f:(fun s -> s, T_int.SInt)),
    Statement.of_statements @@
    List.map varnames ~f:(Fn.flip Statement.mk_vardecl T_int.SInt) @ stmts }
  | FLOAT decls=RealVarDecls SEMI | DOUBLE decls=RealVarDecls SEMI { fun senv ->
    let varnames, stmts = decls senv in
    Map.force_merge senv (Map.Poly.of_alist_exn @@ List.map varnames ~f:(fun s -> s, T_real.SReal)),
    Statement.of_statements @@
    List.map varnames ~f:(Fn.flip Statement.mk_vardecl T_real.SReal) @ stmts }
  | BREAK SEMI { fun senv -> senv, Statement.mk_break () }
  | RETURN term=Term SEMI { fun senv ->
    let term = term senv in
    senv,
    match type_of_nondet term with
    | Some (T_int.SInt, _(*32*), _(*true*)) ->
      Statement.mk_return_nondet_int () (*ToDo*)
    | Some (T_real.SReal, _(*32*), _(*true*)) ->
      Statement.mk_return_nondet_real () (*ToDo*)
    | Some (s, _, _) -> failwith (sprintf "%s not supported in return" (Term.str_of_sort s))
    | None -> Statement.mk_return_int term
  }
  | RETURN SEMI { fun senv -> senv, Statement.mk_return_void () }
  | LBLOCK stmts=Statements RBLOCK { fun senv ->
    senv,
    Statement.of_statements (snd @@ stmts senv) }
  /* goto */
  | GOTO label_name=ID SEMI { fun senv -> senv, Statement.mk_goto label_name }
  /* label */
  | label_name=ID COLON { fun senv -> senv, Statement.mk_label label_name }
  | ASSUME LPAREN fml=Formula RPAREN SEMI { fun senv -> senv, Statement.mk_assume (fml senv) }
  /* abort */
  | ERROR LPAREN RPAREN SEMI { fun senv -> senv, Statement.mk_nop ()(*ToDo*) }
  | ABORT LPAREN RPAREN SEMI { fun senv -> senv, Statement.mk_nop ()(*ToDo*) }
  | ASSERT_FAIL LPAREN args=Arguements RPAREN SEMI { fun senv -> ignore args; senv, Statement.mk_nop ()(*ToDo*) }
  /* nops */
  | t=Term SEMI { fun senv ->
    let t = t senv in
    senv,
    if Term.is_funcall t then
      let funname, args, _ = Term.let_funcall t in
      Statement.mk_call_voidfun funname args
    else
      Statement.mk_assign "#_" t
  }
  | SEMI { fun senv -> senv, Statement.mk_nop () }

/* Ast.LogicOld.Formula.t */
/* not including LetRec */
Formula:
  | fml=FormulaOr { fml }

FormulaOr:
  | left=FormulaAnd OR right=FormulaOr { fun senv ->
    Formula.mk_or (left senv) (right senv) ~info:Dummy }
  | fml=FormulaAnd { fml }

FormulaAnd:
  | left=FormulaNeg AND right=FormulaAnd { fun senv ->
    Formula.mk_and (left senv) (right senv) ~info:Dummy }
  | fml=FormulaNeg { fml }

FormulaNeg:
  | NOT fml=FormulaNeg { fun senv ->
    Formula.mk_neg (fml senv) ~info:Dummy }
  | fml=FormulaAtom { fml }

FormulaAtom:
  | atom=Atom { fun senv -> Formula.mk_atom (atom senv) ~info:Dummy }
  | LPAREN fml=Formula RPAREN { fml }
  | term=T_intAtom { fun senv -> formula_of_term (term senv) }
  /* | n=INTL { T_int.from_int n ~info:Dummy |> formula_of_term }
  | varname=ID { Term.mk_var (Ident.Tvar varname) T_int.SInt ~info:Dummy |> formula_of_term } */

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
  | t1=T_intAddSub ADD t2=T_intMulDivMod { fun senv ->
    let t1 = t1 senv in
    let t2 = t2 senv in
    match Term.sort_of t1, Term.sort_of t2 with
    | (T_int.SInt, _) | (_, T_int.SInt) -> T_int.mk_add t1 t2 ~info:Dummy
    | (T_real.SReal, _) | (_, T_real.SReal) -> T_real.mk_radd t1 t2 ~info:Dummy
    | _ -> T_num.mk_nadd t1 t2 ~info:Dummy }
  | t1=T_intAddSub MINUS t2=T_intMulDivMod { fun senv ->
    let t1 = t1 senv in
    let t2 = t2 senv in
    match Term.sort_of t1, Term.sort_of t2 with
    | (T_int.SInt, _) | (_, T_int.SInt) -> T_int.mk_sub t1 t2 ~info:Dummy
    | (T_real.SReal, _) | (_, T_real.SReal) -> T_real.mk_rsub t1 t2 ~info:Dummy
    | _ -> T_num.mk_nsub t1 t2 ~info:Dummy }

T_intMulDivMod:
  | t=T_intUnary { t }
  | t1=T_intMulDivMod ASTERISK t2=T_intUnary { fun senv ->
    let t1 = t1 senv in
    let t2 = t2 senv in
    match Term.sort_of t1, Term.sort_of t2 with
    | (T_int.SInt, _) | (_, T_int.SInt) -> T_int.mk_mul t1 t2 ~info:Dummy
    | (T_real.SReal, _) | (_, T_real.SReal) -> T_real.mk_rmul t1 t2 ~info:Dummy
    | _ -> T_num.mk_nmul t1 t2 ~info:Dummy }
  | t1=T_intMulDivMod DIV t2=T_intUnary { fun senv ->
    let t1 = t1 senv in
    let t2 = t2 senv in
    match Term.sort_of t1, Term.sort_of t2 with
    | (T_int.SInt, _) | (_, T_int.SInt) -> T_int.mk_div Value.Truncated t1 t2 ~info:Dummy
    | (T_real.SReal, _) | (_, T_real.SReal) -> T_real.mk_rdiv t1 t2 ~info:Dummy
    | _ -> T_num.mk_ndiv Value.Truncated t1 t2 ~info:Dummy }
  | t1=T_intMulDivMod MOD t2=T_intUnary { fun senv ->
    let t1 = t1 senv in
    let t2 = t2 senv in
    match Term.sort_of t1, Term.sort_of t2 with
    | (T_int.SInt, _) | (_, T_int.SInt) -> T_int.mk_rem Value.Truncated  t1 t2 ~info:Dummy
    | (T_real.SReal, _) | (_, T_real.SReal) -> assert false
    | _ -> T_num.mk_nrem Value.Truncated t1 t2 ~info:Dummy }

T_intUnary:
  | t=T_intParen { t }
  | Cast t=T_intUnary { t }
  | MINUS t=T_intUnary { fun senv ->
    let t = t senv in
    match Term.sort_of t with
    | T_int.SInt -> T_int.mk_neg t ~info:Dummy
    | T_real.SReal -> T_real.mk_rneg t ~info:Dummy
    | _ -> T_num.mk_nneg t ~info:Dummy }

T_intParen:
  | t=T_intAtom { t }
  | LPAREN t=T_int RPAREN { t }

T_intAtom:
  | n=INTL { fun _ -> T_int.from_int n ~info:Dummy }
  | f=FLOATL { fun _ -> T_real.mk_real (Q.of_float f) ~info:Dummy }
  | varname=ID { fun senv ->
    let sort =
      match Map.Poly.find senv varname with
      | Some s -> s
      | None -> if true(*ToDo*) then T_int.SInt else Sort.mk_fresh_svar ()
    in
    Term.mk_var (Ident.Tvar varname) sort ~info:Dummy }
  | funname=ID LPAREN args=Arguements RPAREN { fun senv ->
    Term.mk_fsym_app (FunCall funname) (args senv) ~info:Dummy }
  | funname=ID LPAREN t1=T_int op=PREDSYM t2=T_int RPAREN { fun senv -> (* ToDo *)
    let t1 = t1 senv in
    let t2 = t2 senv in
    let cond = Formula.mk_atom @@ Atom.mk_psym_app (op (Term.sort_of t1)) [t1; t2] ~info:Dummy in
    Term.mk_fsym_app (FunCall funname) [T_bool.ifte cond (T_int.one ()) (T_int.zero ()) ~info:Dummy] ~info:Dummy
  }
  | ADDR varname=ID { fun _ ->
    Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy }
  | ASTERISK varname=ID { fun _ ->
    Term.mk_var (Ident.Tvar varname) T_int.SUnrefInt ~info:Dummy }
  /* sizeof(char) -> 1 */
  | SIZEOF LPAREN CHAR RPAREN { fun _ -> T_int.from_int 1 ~info:Dummy }
  /* sizeof(short) -> 2 */
  | SIZEOF LPAREN SHORT RPAREN { fun _ -> T_int.from_int 2 ~info:Dummy }
  /* sizeof(int) -> 4 */
  | SIZEOF LPAREN INT RPAREN { fun _ -> T_int.from_int 4 ~info:Dummy }
  /* sizeof(long) -> 8 */
  | SIZEOF LPAREN LONG RPAREN { fun _ -> T_int.from_int 8 ~info:Dummy }
  /* --x, ++x */
  | MINUSMINUS varname=ID { fun _ ->
    Term.mk_fsym_app (FunCall "#dec")
      [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy }
  | PLUSPLUS varname=ID { fun _ ->
    Term.mk_fsym_app (FunCall "#inc")
      [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy }
  /* x--, x++ */
  | varname=ID MINUSMINUS { fun _ ->
    T_int.mk_add (Term.mk_fsym_app (FunCall "#dec")
      [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy)
      (T_int.one ()) ~info:Dummy }
  | varname=ID PLUSPLUS { fun _ ->
    T_int.mk_sub (Term.mk_fsym_app (FunCall "#inc")
      [Term.mk_var (Ident.Tvar varname) T_int.SRefInt ~info:Dummy] ~info:Dummy)
      (T_int.one ()) ~info:Dummy }
  /* "hoge" */
  | str=STRINGL { fun _ -> term_of_string str }
  /* "hoge" "fuga" */
  | str1=STRINGL str2=STRINGL { fun _ -> term_of_string (str1 ^ str2) }
  /* nondet() */
  | NONDET_BOOL LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_bool) [] ~info:Dummy }
  | NONDET_CHAR LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_char) [] ~info:Dummy }
  | NONDET_UCHAR LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_uchar) [] ~info:Dummy }
  | NONDET_SHORT LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_short) [] ~info:Dummy }
  | NONDET_USHORT LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_ushort) [] ~info:Dummy }
  | NONDET_INT LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_int) [] ~info:Dummy }
  | NONDET_UINT LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_uint) [] ~info:Dummy }
  | NONDET_LONG LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_long) [] ~info:Dummy }
  | NONDET_ULONG LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_ulong) [] ~info:Dummy }
  | NONDET_FLOAT LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_float) [] ~info:Dummy }
  | NONDET_DOUBLE LPAREN RPAREN { fun _ -> Term.mk_fsym_app (FunCall funname_nondet_double) [] ~info:Dummy }

Cast:
  | LPAREN Int RPAREN
  | LPAREN UNSIGNED Int RPAREN
  | LPAREN VOID RPAREN { () }

/* Ast.LogicOld.T_bool */
T_bool:
  | t1=T_int op=PREDSYM t2=T_int { fun senv ->
    let t1 = t1 senv in
    let t2 = t2 senv in
    Atom.mk_psym_app (op (Term.sort_of t1)) [t1; t2] ~info:Dummy }
