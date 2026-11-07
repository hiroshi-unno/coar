%{
  open Core
  open Ast
  open Ast.LogicOld
  open SgclSyntax

  let mk_bound_spec post op bound transformer =
    match op with
    | T_num.NLeq _ -> Program.mk_bound post Program.UB ~transformer bound
    | T_num.NLt _ -> Program.mk_bound post Program.UB ~strict:true ~transformer bound
    | T_num.NGeq _ -> Program.mk_bound post Program.LB ~transformer bound
    | T_num.NGt _ -> Program.mk_bound post Program.LB ~strict:true ~transformer bound
    | _ -> failwith "unsupported SGCL expectation bound comparator"
%}

%token EOF
%token WHILE
%token IF ELSE FLIP
%token RETURN FAIL OBSERVE SAMPLE EXPECTATION
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
    insts=Instructions return=Return spec=BoundSpec EOF 
		{ Program.make ?bound:spec insts return }

expr:
	expr=T_Num EOF { expr }

Instructions:
	inst=Instruction insts=Instructions { Statement.mk_compound inst insts }
  | inst=Instruction { inst }

Return:
	RETURN var=ID { Term.mk_var (Ident.Tvar var) @@ Sort.mk_fresh_svar () }

BoundSpec:
  | EXPECTATION LBRACKET post=T_Num RBRACKET op=PREDSYM bound=T_Num {
      Some (mk_bound_spec post op bound Program.Cwp)
    }
  /* The conditional expectation transformer a bound speaks of on a program
     with observe, written as a word after the bound: cwp (the default), cwlp
     or r2. */
  | EXPECTATION LBRACKET post=T_Num RBRACKET op=PREDSYM bound=T_Num name=ID {
      match Program.transformer_of_string name with
      | Some transformer -> Some (mk_bound_spec post op bound transformer)
      | None ->
        Common.Refusal.refuse
          "unknown expectation transformer %s: expected cwp, cwlp or r2" name
    }
  | { None }

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
			(* The uniform distribution on the integers a..b-1: the upper end is
			   excluded, as in Diabolo (Zaiser, Murawski and Ong, POPL 2025), whose
			   benchmarks draw a fair die as [UniformDisc(1, 7)] and one of five
			   coupons as [UniformDisc(0, 5)], and whose stated expected values
			   hold only for the half-open range.  Reading b as included put a
			   value in the support that the program never draws, and a bound was
			   proved about a different distribution.
			   It is built as nested binary choices: [acc] is uniform on a..i-1
			   when value [i] is added, and the choice takes [i] with probability
			   1/(i-a+1), so the result is uniform on a..i.  Every value then has
			   probability 1/(b-a).  The weight must shrink with the nesting:
			   weighting every level alike put the largest probability on the
			   last value and geometrically less on the values below it.  An
			   empty range (a >= b) has no distribution and is refused. *)
			if a >= b then
				Common.Refusal.refuse
					"UniformDisc(%d, %d) has an empty support" a b;
			fun var assign->
				let rec make_choices i acc =
					if i >= b then acc
					else
					let branch = assign var
						(T_num.mk_value (string_of_int i)) in
					let prob = T_real.mk_real (Q.of_ints 1 (i - a + 1)) in
					let choice =
						Statement.mk_choice prob branch acc
					in
					make_choices (i + 1) choice
				in
				make_choices (a+1) (assign var (T_num.mk_value (string_of_int a)))
		}
	/* The three distributions are supported on the naturals, so the values
	   they assign are numerals, which leave the variable an integer unless
	   something else makes it real (see [SGCL.Util.infer_sorts]); their
	   probabilities are reals. */
	| GEOMETRIC LPAREN p=T_Num RPAREN
		{
			fun var assign ->
			Statement.mk_compound
				(assign var (T_num.mk_value "0"))
				(Statement.mk_while_flip (T_real.mk_rsub (T_real.rone ()) p)
					(Statement.mk_plus_assign var (T_num.mk_value "1")))
		}

	| BERNOULLI LPAREN p=T_Num RPAREN
		{
			fun var assign ->
			let prob = p in
			let branch_true = assign var (T_num.mk_value "1") in
			let branch_false = assign var (T_num.mk_value "0") in
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

/* Variables are not declared: a variable's sort, and a numeral's, is inferred
   from the whole program by [SGCL.Util.infer_sorts].  [+] and [-] take the
   sort of their operands; [/] is exact division, so its operands and result
   are real. */
T_NumAddSub:
  e1=T_NumAddSub PLUS e2=T_NumAtom { T_num.mk_nadd e1 e2 }
	| e1=T_NumAddSub MINUS e2=T_NumAtom { T_num.mk_nsub e1 e2 }
	| e= T_NumDiv { e }

T_NumDiv:
	| e1=T_NumDiv DIV e2=T_NumAtom { T_real.mk_rdiv e1 e2 }
	| e=T_NumAtom { e }

/* TODO: Implement infinity */
T_NumAtom:
	LPAREN e=T_Num RPAREN { e }
  /* the indicator [b]: 1 where b holds, 0 elsewhere */
  | LBRACKET e=T_bool RBRACKET
  	{ T_bool.mk_if_then_else e (T_real.rone ()) (T_real.rzero ()) }
  | varname=ID { Term.mk_var (Ident.Tvar varname) @@ Sort.mk_fresh_svar () }
  | n=NATL { T_num.mk_value (string_of_int n) }
  | r=REALL { T_real.mk_real (Q.of_string r) }
