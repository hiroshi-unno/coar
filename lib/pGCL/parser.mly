%{
  open Core
  open Ast
  open Ast.LogicOld
  open PgclSyntax

%}

%token BOOL NAT REAL CONST
%token RPARAM NPARAM
%token EOF 
%token SKIP WHILE
%token IF ELSE
%token TICK OBSERVE LOOP
%token EXPECTATION PRQUERY PRINT PLOT OPTIMIZE
%token DUNIFORM CUNIFORM GEOMETRIC POISSON
%token LOGDIST BINOMIAL BERNOULLI IID
%token TRUE FALSE INFINITY
%token ASSIGN
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE
%token COMMA
%token AND OR
%token <Ast.LogicOld.pred_sym> PREDSYM
%token EQUAL
%token COLON
%token PLUS MINUS MULT DIV MOD
%token POW NOT
%token <int> NATL
%token <string> REALL
%token <string> ID

%start toplevel
%type <Program.t> toplevel
%start expr
%type <Term.t> expr
%%

toplevel:
    decls=Declarations insts=Instructions queries=Query EOF 
		{ decls |> ( fun (vars,consts) -> Program.make (vars,consts) insts queries ) }
    | decls=Declarations insts=Instructions EOF 
		{ 
			let termination = 
			  Query.mk_expectation (T_real.rone ())
			in
			decls |> ( fun (vars,consts) -> Program.make (vars,consts) insts termination ) 
			}

expr:
	expr=Expr EOF { expr }
	
Declarations:
	var=VarDeclaration decls=Declarations { decls |> fun (vars, consts) -> (var :: vars, consts) }
	| const=ConstantDeclaration decls=Declarations { decls |> fun (vars, consts) -> (vars, const :: consts) }
	| { ([], []) }


/* TODO: Implement the bounds for nat and real */
VarDeclaration:
	BOOL varname=ID { (Ident.Tvar varname, T_bool.SBool) }
  | NAT varname=ID  { (Ident.Tvar varname, T_real.SReal) }
  | REAL varname=ID { (Ident.Tvar varname, T_real.SReal) }
  | RPARAM varname=ID { (Ident.Tvar varname, T_real.SReal) }
  | NPARAM varname=ID { (Ident.Tvar varname, T_int.SInt) }

ConstantDeclaration:
| CONST varname=ID ASSIGN body=Expr { (Ident.Tvar varname, Term.sort_of body, body) }

Instructions:
	inst=Instruction insts=Instructions { Statement.mk_compound inst insts }
  | inst=Instruction { inst }

Queries:
    query=Query queries=Queries { query :: queries }
	| { [] }

Instruction:
	SKIP { Statement.mk_skip () }
  | WHILE LPAREN cond=T_bool RPAREN body=Block {
	  Statement.mk_while (Formula.of_bool_term cond) body
	}
  | IF LPAREN cond=T_bool RPAREN then_blk=Block else_blk=Block {
	  Statement.mk_if (Formula.of_bool_term cond) then_blk else_blk
	}
  | IF LPAREN cond=T_bool RPAREN then_blk=Block ELSE else_blk=Block {
	  Statement.mk_if (Formula.of_bool_term cond) then_blk else_blk
	}
  | varname=ID ASSIGN rvalue=Rvalue {
	  Statement.mk_assign (Ident.Tvar varname) rvalue
	}
  | lblk=Block LBRACKET cond=Expr RBRACKET rblk=Block {
	  Statement.mk_choice cond lblk rblk
	}
  | TICK LPAREN expr=Expr RPAREN { Statement.mk_tick expr }
  | OBSERVE LPAREN fml=T_bool RPAREN { Statement.mk_observe (Formula.of_bool_term fml) }
  | LOOP LPAREN n_loop=NATL RPAREN body=Block ;{ Statement.mk_loop (T_int.from_int n_loop) body }

Query:
	EXPECTATION LBRACKET expr=Expr RBRACKET { Query.mk_expectation expr }
 /*
 | PRQUERY LBRACKET expr=Expr RBRACKET { Program.prquery_of expr }
 | PRINT { Program.print_query () }
 | PLOT LBRACKET pb=PlotBlock RBRACKET { Program.plot_query_of pb }
 | OPTIMIZE LBRACKET opb=OptimizeBlock RBRACKET { Program.optimize_query_of opb }
 */

/*PlotBlock:
	v1=ID { Program.PlotVar (Ident.Tvar v1) }
  | v1=ID COMMA v2=ID { Program.PlotVarPair (Ident.Tvar v1, Ident.Tvar v2) }
  | v1=ID COMMA v2=ID COMMA lit=Literal { 
	  let bound =
		match lit with
		| Program.LitInt n -> Term.mk_int n
		| Program.LitReal r -> T_real.mk_real (Q.of_string r)
	  in
	  Program.PlotVarBound (Ident.Tvar v1, Ident.Tvar v2, bound)
	}*/

Block:
	LBRACE insts=Instructions RBRACE { insts }
	| LBRACE  RBRACE { Statement.mk_skip () }

Rvalue:
	expr=Expr { expr }
/*Rvalue:
	DUNIFORM LPAREN low=Expr COMMA high=Expr RPAREN {
	  Statement.mk_duniform low high
	}
  | CUNIFORM LPAREN low=Expr COMMA high=Expr RPAREN {
	  Statement.mk_cuniform low high
	}
  | GEOMETRIC LPAREN expr=Expr RPAREN {
	  Statement.mk_geometric expr
	}
  | POISSON LPAREN expr=Expr RPAREN {
	  Statement.mk_poisson expr
	}
  | LOGDIST LPAREN expr=Expr RPAREN {
	  Statement.mk_logdist expr
	}
  | BINOMIAL LPAREN n=Expr COMMA p=Expr RPAREN {
	  Statement.mk_binomial n p
	}
  | BERNOULLI LPAREN expr=Expr RPAREN {
	  Statement.mk_bernoulli expr
	}
  | IID LPAREN rv=Rvalue COMMA varname=ID RPAREN {
	  Statement.mk_iid rv (Ident.Tvar varname)
	}
  | expr=T_Num { Statement.mk_expr expr }*/

Expr:
	T_bool { $1 }
	| T_Num { $1 }

T_bool:
    T_boolOr { $1 }

T_boolOr:
	e1=T_boolOr OR e2=T_boolAnd
		{ T_bool.of_formula @@ Formula.mk_or (Formula.of_bool_term e1) (Formula.of_bool_term e2) }
	| T_boolAnd { $1 }

T_boolAnd:
	e1=T_boolAnd AND e2=T_boolNeg
		{ T_bool.of_formula @@ Formula.mk_and (Formula.of_bool_term e1) (Formula.of_bool_term e2) }
	| T_boolNeg { $1 }
	
T_boolNeg:
  NOT e=T_boolNeg 		 
  		{ T_bool.negate e}
  | T_boolAtom { $1 }

T_boolAtom:
  | atom=Atom { T_bool.of_atom atom }
  | varname=ID { Term.mk_var (Ident.Tvar varname) @@ Sort.mk_fresh_svar () }
  | LPAREN T_bool RPAREN { $2 }
  

Atom:
  |	TRUE { Atom.True Dummy }
  |	FALSE { Atom.False Dummy }
  | e1=T_Num op=PREDSYM e2=T_Num { Atom.mk_app (Predicate.mk_psym op) [e1; e2] }
//   | e1=Expr EQUAL e2=Expr {
// 	Atom.mk_app (Predicate.mk_psym T_bool.Eq) [e1;e2]
//   }
  | e1=T_Num EQUAL e2=T_Num {
	Atom.mk_app (Predicate.mk_psym T_bool.Eq) [e1;e2]
  }

T_Num:
	T_NumAddSub { $1 }

T_NumAddSub:
  e1=T_NumAddSub PLUS e2=T_NumMulDivMod { T_num.mk_nadd e1 e2 }
	| e1=T_NumAddSub MINUS e2=T_NumMulDivMod { T_num.mk_nsub e1 e2 }
	| T_NumMulDivMod { $1 }

 /*Expr4:
  e4=Expr4 COLON e5=Expr5 { Expr.mk_mul e4 e5 }
	| Expr5 { $1 }*/

T_NumMulDivMod:
  e1=T_NumMulDivMod MULT e2=T_NumPow { T_num.mk_nmul e1 e2 }
	| e1=T_NumMulDivMod DIV e2=T_NumPow { T_num.mk_ndiv Value.Truncated e1 e2 }
	| e1=T_NumMulDivMod MOD e2=T_NumPow { T_num.mk_nrem Value.Truncated e1 e2 }
	| T_NumPow { $1 }

T_NumPow:
  e1=T_NumAtom POW e2=T_NumPow { T_num.mk_npower e1 e2 }
	| T_NumAtom { $1 }

/* TODO: Implement infinity */
T_NumAtom:
	LPAREN e=T_Num RPAREN { e }
  | LBRACKET e=T_bool RBRACKET
  	{ T_bool.mk_if_then_else e (T_real.rone ()) (T_real.rzero ())  }
  | varname=ID { Term.mk_var (Ident.Tvar varname) @@ Sort.mk_fresh_svar () }
//   | n=NATL { T_int.from_int n }
  | n=NATL {T_real.mk_real (Q.of_int n)}
  | r=REALL { T_real.mk_real (Q.of_string r) }

/*   | INFINITY { AstPgcl.Infinity } */