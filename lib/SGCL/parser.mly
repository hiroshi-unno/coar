%{
  open Core
  open Ast
  open Ast.LogicOld
  open SgclSyntax

%}

%token EOF 
%token WHILE
%token IF ELSE FLIP
%token RETURN FAIL OBSERVE SAMPLE
%token UNIFORMDISC GEOMETRIC BERNOULLI CATEGORICAL
%token ASSIGN
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE
%token COMMA
%token AND OR NOT
%token PLUSASSIGN MINUSASSIGN
%token IN
%token <Ast.LogicOld.pred_sym>  PREDSYM
%token PLUS MINUS DIV
%token <int> NATL
%token <string> REALL
%token <string> ID

%start toplevel
%type <Program.t> toplevel
%start expr
%type <Term.t> expr
%%

toplevel:
    insts=Instructions return=Return EOF 
		{ Program.make insts return }

expr:
	expr=T_Num EOF { expr }

Instructions:
	inst=Instruction insts=Instructions { Statement.mk_compound inst insts }
  | inst=Instruction { inst }

Return:
	RETURN var=ID { Term.mk_var (Ident.Tvar var) @@ Sort.mk_fresh_svar () }

Instruction:
  | WHILE  cond=T_bool  body=Block {
	  Statement.mk_while (Formula.of_bool_term cond) body
	}
  | WHILE FLIP LPAREN prob=T_Num RPAREN body=Block {
	  Statement.mk_while_flip prob body
	}
  | IF cond=T_bool then_blk=Block
      { Statement.mk_if (Formula.of_bool_term cond) then_blk (Statement.mk_skip ()) }

  | IF cond=T_bool then_blk=Block ELSE else_stmt=Instruction
      { Statement.mk_if (Formula.of_bool_term cond) then_blk else_stmt }

  | IF FLIP LPAREN prob=T_Num RPAREN then_blk=Block
      { Statement.mk_choice prob then_blk (Statement.mk_skip ()) }

  | IF FLIP LPAREN prob=T_Num RPAREN then_blk=Block ELSE else_stmt=Instruction
      { Statement.mk_choice prob then_blk else_stmt }
  
  | varname=ID SAMPLE rfun=Distribution {
	  rfun (Ident.Tvar varname) Statement.mk_assign
	}

  | varname=ID PLUS SAMPLE rfun=Distribution {
	  rfun (Ident.Tvar varname) Statement.mk_plus_assign
	}

  | varname=ID ASSIGN rvalue=T_Num {
	  Statement.mk_assign (Ident.Tvar varname) rvalue
	}
  | varname=ID PLUSASSIGN rvalue=T_Num {
	  Statement.mk_plus_assign (Ident.Tvar varname) rvalue
	}
  | varname=ID MINUSASSIGN rvalue=T_Num {
	  Statement.mk_minus_assign (Ident.Tvar varname) rvalue
	}
  | lblk=Block LBRACKET cond=T_Num RBRACKET rblk=Block {
	  Statement.mk_choice cond lblk rblk
	}
  | OBSERVE cond=T_bool {
	  Statement.mk_observe (Formula.of_bool_term cond)
	  }
  | Block { $1 }


Block:
	LBRACE insts=Instructions RBRACE { insts }
	| LBRACE RBRACE { Statement.mk_skip () }

Distribution:
	UNIFORMDISC LPAREN a=NATL COMMA b=NATL RPAREN
		{
			fun var assign-> 
			if a=b then assign var (T_real.mk_real (Q.of_int a))
			else 
				let a' = T_real.mk_real (Q.of_int a) in
				let b' = T_real.mk_real (Q.of_int b) in
				let prob = T_real.mk_rdiv (T_real.rone ()) (T_real.mk_radd (T_real.mk_rsub b' a') @@ T_real.rone ()) in
				let rec make_choices i acc =
					if i > b then acc
					else
					let branch = assign var
						(T_real.mk_real (Q.of_int i)) in
					let choice =
						Statement.mk_choice prob branch acc
					in
					make_choices (i + 1) choice
				in
				make_choices (a+1) (assign var a')
		}
	| GEOMETRIC LPAREN p=T_Num RPAREN
		{
			fun var assign ->
			Statement.mk_compound
				(assign var (T_real.rzero ()))
				(Statement.mk_while_flip (T_real.mk_rsub (T_real.rone ()) p)
					(Statement.mk_plus_assign var (T_real.rone ())))
		}

	| BERNOULLI LPAREN p=T_Num RPAREN
		{
			fun var assign ->
			let prob = p in
			let branch_true = assign var (T_real.rone ()) in
			let branch_false = assign var (T_real.rzero ()) in
			Statement.mk_choice prob branch_true branch_false
		}
	// | CATEGORICAL 


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
  | e1=T_Num op=PREDSYM e2=T_Num { Atom.mk_app (Predicate.mk_psym op) [e1; e2] }

T_Num:
	T_NumAddSub { $1 }

T_NumAddSub:
  e1=T_NumAddSub PLUS e2=T_NumAtom { T_real.mk_radd e1 e2 }
	| e1=T_NumAddSub MINUS e2=T_NumAtom { T_real.mk_rsub e1 e2 }
	| e= T_NumDiv { e }

T_NumDiv:
	| e1=T_NumDiv DIV e2=T_NumAtom { T_real.mk_rdiv e1 e2 }
	| e=T_NumAtom { e }

/* TODO: Implement infinity */
T_NumAtom:
	LPAREN e=T_Num RPAREN { e }
  | varname=ID { Term.mk_var (Ident.Tvar varname) @@ T_real.SReal }
  | n=NATL {T_real.mk_real (Q.of_int n)}
  | r=REALL { T_real.mk_real (Q.of_string r) }