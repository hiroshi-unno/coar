%{
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open Ast.Ident
open Grammar

let cgen_config = Envs.cgen_config
let denv = Envs.denv
let renv = Envs.renv
let renv_local = ref (Rtype.Env.mk_empty ())

let verbose = false
module Debug = Debug.Make (val if verbose then Debug.Config.enable else Debug.Config.disable)

let sort_of_var _v = Sort.mk_fresh_svar ()

let print_error_information () =
  let st = Parsing.symbol_start_pos () in
  let en = Parsing.symbol_end_pos () in
  print_string ("File \"" ^ st.Lexing.pos_fname);
  Format.printf "\", line %d" st.Lexing.pos_lnum;
  Format.printf ", characters %d-%d:\n"
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
    (en.Lexing.pos_cnum - en.Lexing.pos_bol)
%}

%token <string> UNKNOWN
%token <string> IDENT
%token <string> IDENT_T
%token <string> CONST
%token <bool> BOOL
%token <int> INT
%token <float> FLOAT
%token <string> RECOGNIZER
%token <string * int> ACCESSOR
%token <string * string> SIZE

%token TEMPLATE
%token MAXIMIZE
%token MINIMIZE
%token PRIORITIZE

%token LET
%token IN
%token EQUAL
%token NOTEQUAL
%token COMMA
%token LPAREN // '('
%token RPAREN // ')'
%token AMP // '&'
%token VERT // '|'

%token PROJ

%token FORALL EXISTS MU NU
%token DOT
%token AND OR IMP IFF NOT
%token LT GT LEQ GEQ
%token ADD SUB AST DIV MOD
%token EXC
%token FADD FSUB FMUL FDIV
%token EQEQ

%token LBRA
%token RBRA
%token COLON // ':'
%token COLCOL // "::"
%token SLASLA // "//"
%token ARROW
%token LARROW
//%token PAIR
%token SUBTYPE
%token MEMBER
%token SUBSET
%token SUNION
%token SINTERSECT
%token SDIFF
%token SEMPTY
%token SCOMP

%token LBRACKET
%token RBRACKET
%token APPLY

%token QUESTION

%token LABRA
%token RABRA

%token TYPEOF
%token FINEFFECTOF
%token INFEFFECTOF

%token EPSILON
%token EVENT
%token PLUSPLUS

%token COLEQ
%token COLMIN // ":-"
%token QMIN // "?-"

%token SEMICOLON
%token TURNSTILE
%token RTRI // |>
%token WILDCARD // _

%token EOF

%right prec_tyarrow
%nonassoc prec_typair
%left prec_tyapp

%right LARROW COLEQ
%left COMMA

%right IMP
%left OR VERT
%left AND AMP
%right NOT EXC
%nonassoc FORALL EXISTS MU NU

%left EQUAL NOTEQUAL LT GT LEQ GEQ
%left EQEQ

%left PLUSPLUS

%left SUNION
%left SINTERSECT SDIFF
%right SCOMP

%left ADD SUB FADD FSUB
%left AST DIV FMUL FDIV MOD
%right unary_minus
%left DOT

%start constraints val_ty_env assertions opt_problems comp_ty

%type <Term.t> term
%type <Atom.t> atom
%type <Formula.t> prop

%type <Ident.tvar * Sort.t> bind

%type <Rtype.t> val_ty
%type <Rtype.c> comp_ty
%type <Rtype.o> opsig_ty
%type <Rtype.o> op_tys
%type <Rtype.s> cont_eff_ty

%type <(tvar * CHCOpt.Problem.direction) list> directs

%type <Formula.t list> constraints
%type <Rtype.Env.t> val_ty_env
%type <(Ident.tvar * Problem.assertion) list> assertions
%type <(Ident.tvar * (tvar * CHCOpt.Problem.direction) list * (Ident.tvar * PCSP.SolSpace.space_flag * int) list) list> opt_problems

%%

term:
  | LPAREN term RPAREN { $2 }
  | IDENT { Term.mk_var (Ident.Tvar $1) @@ sort_of_var @@ Ident.Tvar $1 }
  /* this causes reduce/reduce conflict on RPAREN
  | BOOL { Term.Bool.make $1 } */
  | INT { T_int.from_int $1 }
  | FLOAT { T_real.mk_real @@ Q.of_float $1 }
  | APPLY IDENT LPAREN terms RPAREN {
    let var = Ident.Tvar $2 in
    match Rtype.Env.look_up !renv var with
    | Some t ->
      let args, ret = Sort.args_ret_of @@ Rtype.sort_of_val t in
      Term.mk_fvar_app var (args @ [ret]) $4
    | None ->
      match Map.Poly.find (Atomic.get ref_fenv) var with
      | Some (params, ret_sort, _, _, _) ->
        Term.mk_fvar_app var (List.map params ~f:snd @ [ret_sort]) $4
      | None -> failwith @@ "unbound function variable: " ^ $2
  }
  | SUB term %prec unary_minus { T_int.mk_neg $2 }
  | term ADD term { T_int.mk_add $1 $3 }
  | term SUB term { T_int.mk_sub $1 $3 }
  | term AST term { T_int.mk_mult $1 $3 }
  | term DIV term { T_int.mk_div $1 $3 }
  | term MOD term { T_int.mk_mod $1 $3}
  | term FADD term { T_real.mk_radd $1 $3 }
  | term FSUB term { T_real.mk_rsub $1 $3 }
  | term FMUL term { T_real.mk_rmult $1 $3 }
  | term FDIV term { T_real.mk_rdiv $1 $3 }
  /*| LPAREN terms RPAREN {
    T_tuple.mk_tuple_cons (List.map ~f:Term.sort_of $2) $2
  }
  | PROJ LPAREN INT COMMA term RPAREN {
    T_tuple.mk_tuple_sel [](*ToDo*) $5 $3
  }*/
  | CONST LPAREN terms RPAREN {
    match DTEnv.look_up_dt_by_cons_name !denv $1 with
    | Some dt -> T_dt.mk_cons dt $1 $3
    | _ -> failwith @@ "undefined constructor: " ^ $1
  }
  | CONST term {
    match DTEnv.look_up_dt_by_cons_name !denv $1 with
    | Some dt -> T_dt.mk_cons dt $1 [$2]
    | _ -> failwith @@ "undefined constructor: " ^ $1
  }
  | COLCOL LPAREN terms RPAREN {
    match DTEnv.look_up_dt_by_cons_name !denv "::" with
    | Some dt -> T_dt.mk_cons dt "::" $3
    | _ -> failwith @@ "undefined constructor: " ^ "::"
  }
  | CONST {
    match DTEnv.look_up_dt_by_cons_name !denv $1 with
    | Some dt -> T_dt.mk_cons dt $1 []
    | _ -> failwith @@ "undefined constructor: " ^ $1
  }
  | ACCESSOR LPAREN term RPAREN {
    let cons_name, n = $1 in
    match DTEnv.look_up_dt_by_cons_name !denv cons_name with
    | Some dt -> T_dt.mk_sel_by_cons dt cons_name n $3
    | None -> failwith @@ "undefined constructor" ^ cons_name
  }
  | EPSILON { Term.mk_fsym_app T_sequence.Epsilon [] }
  | EVENT LPAREN IDENT RPAREN { Term.mk_fsym_app (T_sequence.Symbol $3) [] }
  | term PLUSPLUS term { Term.mk_fsym_app (T_sequence.Concat true(*ToDo: fix*)) [$1; $3] }
  //  | term EQEQ term { T_bool.of_atom @@ T_bool.mk_eq $1 $3 }
  //  | SEMPTY { Term.Set.mk_empty (Type.mk_unknown) }
  //  | LBRA terms RBRA {
  //      List.fold_left
  //        (Fn.flip (Term.Set.mk_add Type.mk_unknown))
  //        (Term.Set.mk_empty Type.mk_unknown)
  //        $2
  //    }
  //  | term SUNION term { Term.Set.mk_union Type.mk_unknown $1 $3 }
  //  | term SINTERSECT term { Term.Set.mk_intersect Type.mk_unknown $1 $3 }
  //  | term SDIFF term { Term.Set.mk_diff Type.mk_unknown $1 $3 }
  //  | SCOMP term { Term.Set.mk_comp Type.mk_unknown $2 }
  //  | SIZE term {
  //      let size_var = (fst $1) ^ "_" ^ (snd $1) in
  //      Term.mk_ufun
  //        (Idnt.make size_var, Type.mk_fun [Type.mk_unknown; Type.mk_int])
  //        [$2]
  //    }
terms:
  | term { [$1] }
  | term COMMA terms { $1 :: $3 }

// Temporal Effects

eff:
  | EVENT LPAREN IDENT RPAREN { true, RegWordExp.Symbol $3 }
  | EVENT LPAREN IDENT RPAREN AST { true, RegWordExp.Repeat (RegWordExp.Symbol $3) }
  | EVENT LPAREN IDENT RPAREN EXC { false, RegWordExp.RepeatInf (RegWordExp.Symbol $3) }
  | LPAREN eff RPAREN { $2 }
  | LPAREN eff RPAREN AST { let fin, regexp = $2 in assert fin; true, RegWordExp.Repeat regexp }
  | LPAREN eff RPAREN EXC { let fin, regexp = $2 in assert fin; false, RegWordExp.RepeatInf regexp }
  | eff eff { let fin1, regexp1 = $1 in let fin2, regexp2 = $2 in assert fin1; fin2, RegWordExp.Concat (regexp1, regexp2) }
  | eff VERT eff { let fin1, regexp1 = $1 in let fin2, regexp2 = $3 in assert (fin1 = fin2); fin1, RegWordExp.Alter (regexp1, regexp2) }

atom:
  | IDENT LPAREN RPAREN /* to avoid reduce/reduce conflict on RPAREN */ {
    Atom.of_bool_var @@ Ident.Tvar $1
  }
  | BOOL { if $1 then Atom.mk_true () else Atom.mk_false () }
  | IDENT LPAREN terms RPAREN {
    match Map.Poly.find (Atomic.get ref_fenv) (Tvar $1) with
    | Some (params, ret_sort, _, _, _) ->
      if Stdlib.(ret_sort = T_bool.SBool) then
        let sorts = List.map params ~f:snd in
        T_bool.mk_eq (Term.mk_fvar_app (Tvar $1) (sorts @ [ret_sort]) $3) @@ T_bool.mk_true ()
      else failwith ""
    | None ->
      match Map.Poly.find (Rtype.Env.pred_sort_env_of !renv) (Pvar $1) with
      | Some sorts -> Atom.mk_pvar_app (Pvar $1) sorts $3
      | _ -> Atom.mk_pvar_app (Pvar $1) (List.map $3 ~f:Term.sort_of) $3
  }
  | atom_or_term EQUAL    atom_or_term { T_bool.mk_eq $1 $3 }
  | atom_or_term NOTEQUAL atom_or_term { T_bool.mk_neq $1 $3 }
  | term LT term { T_num.mk_nlt $1 $3 }
  | term GT term { T_num.mk_ngt $1 $3 }
  | term LEQ term { T_num.mk_nleq $1 $3 }
  | term GEQ term { T_num.mk_ngeq $1 $3 }
  | RECOGNIZER LPAREN term RPAREN{
    match DTEnv.look_up_dt_by_cons_name !denv $1 with
    | Some dt -> T_dt.mk_is_cons dt $1 $3
    | None -> failwith @@ "unknown cons name" ^ $1
  }
  // | term IN term { Formula.Set.mk_mem Type.mk_unknown $1 $3 }
  // | term SUBSET term { Formula.Set.mk_subset Type.mk_unknown $1 $3 }
  | term IN eff {
    let fin, regexp = $3 in
    Atom.mk_psym_app (T_sequence.InRegExp (fin, regexp)) [$1]
  }
atom_or_term:
  | atom { T_bool.of_atom $1 }
  | term { $1 }

prop:
  | LPAREN prop RPAREN { $2 }
  | atom { Formula.mk_atom $1 }
  | NOT prop { Formula.mk_neg $2 }
  | prop AND prop { Formula.mk_and $1 $3 }
  | prop OR prop { Formula.mk_or $1 $3 }
  | prop IMP prop { Formula.mk_imply $1 $3 }
  | prop IFF prop { Formula.mk_iff $1 $3 }
  // | LBRACKET IDENT RBRACKET prop { Formula.box $2 $4 }
  // | LT IDENT GT prop { Formula.diamond $2 $4 }
  // | MU IDENT DOT prop { Formula.mu (Idnt.make $2) $4 }
  // | NU IDENT DOT prop { Formula.nu (Idnt.make $2) $4 }
  | FORALL binds DOT prop {
    Typeinf.typeinf_formula @@ Formula.forall $2 $4
  }
  | EXISTS binds DOT prop {
    Typeinf.typeinf_formula @@ Formula.exists $2 $4
  }
  | FORALL DOT prop {
    Typeinf.typeinf_formula @@ Formula.forall [] $3
  }
binds:
  | bind { [$1] }
  | bind binds { $1 :: $2 }
bind:
  | IDENT COLON val_ty /*ToDo*/  {
    let tvar, ty = Ident.Tvar $1, $3 in
    tvar, Rtype.sort_of_val ty
  }

val_ty:
  | LPAREN val_ty RPAREN { $2 }
  | IDENT {
    Rtype.mk_simple_val_rtype ~config:!cgen_config @@ Typeinf.sort_of_name !denv $1
  }
  | LBRA AST IDENT RBRA {
    Rtype.val_type_of_sort ~config:!cgen_config
      (Rtype.Env.dep_args_of @@ Rtype.Env.mk_empty ()) @@
      Typeinf.sort_of_name !denv $3
  }
  | LBRA IDENT COLON IDENT VERT prop RBRA {
    let ty = Typeinf.sort_of_name !denv $4 in
    renv_local :=
      Rtype.Env.set_ty !renv_local (Ident.Tvar $2) @@
      Rtype.mk_simple_val_rtype ~config:!cgen_config ty;
    Rtype.mk_rgeneral ~config:!cgen_config (Ident.Tvar $2) ty $6
  }
  | val_ty IDENT %prec prec_tyapp {
    Rtype.mk_rgeneral ~config:!cgen_config
      ~params:[$1] (Rtype.mk_fresh_tvar_with "v") (Typeinf.sort_of_name !denv $2) @@
    Formula.mk_true ()
  }
  | LPAREN val_tys_comma RPAREN IDENT %prec prec_tyapp {
    Rtype.mk_rgeneral ~config:!cgen_config
      ~params:$2 (Rtype.mk_fresh_tvar_with "v") (Typeinf.sort_of_name !denv $4) @@
    Formula.mk_true ()
  }
  | LBRA IDENT COLON val_ty IDENT VERT prop RBRA %prec prec_tyapp {
    Rtype.mk_rgeneral ~config:!cgen_config
      ~params:[$4] (Ident.Tvar $2) (Typeinf.sort_of_name !denv $5) $7
  }
  | LBRA IDENT COLON LPAREN val_tys_comma RPAREN IDENT VERT prop RBRA %prec prec_tyapp {
    Rtype.mk_rgeneral ~config:!cgen_config
      ~params:$5 (Ident.Tvar $2) (Typeinf.sort_of_name !denv $7) $9
  }
  | val_ty ARROW comp_ty %prec prec_tyarrow {
    Rtype.mk_rarrow (Rtype.tvar_of_val $1) $1 $3 @@ Rtype.mk_fresh_trivial_pred ()
  }
  | LPAREN IDENT COLON val_ty RPAREN ARROW comp_ty %prec prec_tyarrow {
    renv_local := Rtype.Env.set_ty !renv_local (Ident.Tvar $2) $4;
    Rtype.mk_rarrow (Ident.Tvar $2) $4 $7 @@ Rtype.mk_fresh_trivial_pred ()
  }
  | val_ty AST val_tys_ast %prec prec_typair {
    Rtype.mk_rtuple (Rtype.mk_fresh_tvar_with "v") ($1 :: $3) @@ Formula.mk_true ()
  }
  | LBRA IDENT COLON val_tys_ast VERT prop RBRA %prec prec_typair {
    Rtype.mk_rtuple (Ident.Tvar $2) $4 $6
  }
val_tys_comma:
  | val_ty { [$1] }
  | val_ty COMMA val_tys_comma { $1 :: $3 }
val_tys_ast:
  | val_ty { [$1] }
  | val_ty AST val_tys_ast { $1 :: $3 }

op_tys: 
    | CONST COLON val_ty RBRA { Rtype.singleton_opsig $1 $3 }
    | CONST COLON val_ty COMMA op_tys {Rtype.append_opsig $5 $1 $3}

opsig_ty:
    | SEMPTY { Rtype.empty_opsig } // SEMPTY has higher precedence than "LBRA RBRA"
    | LBRA RBRA { Rtype.empty_opsig } 
    | LBRA op_tys { $2 }

cont_eff_ty:
    | WILDCARD { Rtype.Pure }
    | comp_ty IMP comp_ty {Rtype.Eff ((Rtype.mk_fresh_tvar_with "x"), $1, $3) }
    | LPAREN FORALL IDENT DOT comp_ty RPAREN IMP comp_ty {Rtype.Eff (Ident.Tvar $3, $5, $8) }

comp_ty:
  // T
  | val_ty {
    Rtype.comp_type_of ~config:!cgen_config [] $1
  }
  // (T & E)
  | LPAREN val_ty AMP IDENT DOT prop COMMA IDENT DOT prop RPAREN {
    Rtype.empty_opsig(*temporary*), $2, ((Ident.Tvar $4, $6), (Ident.Tvar $8, $10)), Rtype.Pure
  }
  // (T / S)
  | LPAREN val_ty DIV cont_eff_ty RPAREN {
    Rtype.empty_opsig, $2, Rtype.mk_temp_eff_trivial () (*temporary*), $4
  }
  // (sigma |> T / S)
  | LPAREN opsig_ty RTRI val_ty DIV cont_eff_ty RPAREN {
    $2, $4, Rtype.mk_temp_eff_trivial (), $6
  }
  // (sigma |> T & E / S)
  | LPAREN opsig_ty RTRI val_ty AMP IDENT DOT prop COMMA IDENT DOT prop DIV cont_eff_ty RPAREN {
    $2, $4, ((Ident.Tvar $6, $8), (Ident.Tvar $10, $12)), $14
  }

val_ty_bind:
  | IDENT COLCOL val_ty {
    renv_local :=
      Rtype.Env.disj_union !renv_local @@
      Rtype.Env.singleton_ty (Ident.Tvar $1) $3;
    Ident.Tvar $1, Rtype.set_sort_val Map.Poly.empty $3
  }
  | CONST COLCOL val_ty {
    renv_local :=
      Rtype.Env.disj_union !renv_local @@
      Rtype.Env.singleton_ty (Ident.Tvar $1) $3;
    Ident.Tvar $1, Rtype.set_sort_val Map.Poly.empty $3
  }
val_ty_env:
  | val_ty_bind {
    let tvar, ty = $1 in
    Rtype.Env.singleton_ty tvar @@ Rtype.aconv_val_type Map.Poly.empty ty
  }
  | val_ty_bind val_ty_env {
    let tvar, ty = $1 in
    Rtype.Env.set_ty $2 tvar @@ Rtype.aconv_val_type Map.Poly.empty ty
  }
  | EOF { Rtype.Env.mk_empty () }

// Space Constraints

space_constr:
  | IDENT DOT IDENT EQUAL INT { Tvar $1, PCSP.SolSpace.space_flag_of $3, $5 }
  | IDENT_T DOT IDENT EQUAL INT { Tvar $1, PCSP.SolSpace.space_flag_of $3, $5 }
space_constrs:
  | space_constr { [$1] }
  | space_constr SEMICOLON space_constrs { $1 :: $3 }
  | EOF { [] }

// Logical Constraints

constraints :
  | prop { [$1] }
  | prop SEMICOLON constraints { $1 :: $3 }
  | EOF { [] }

// Refinement Type and Effect Inference

assertions:
  | assertion { [$1] }
  | assertion assertions { $1 :: $2 }
  | EOF { [] }
  | error {
    print_error_information ();
    raise (Failure "Syntax error")
  }
assertion:
  | TYPEOF LPAREN IDENT RPAREN SUBTYPE val_ty {
     Ident.Tvar $3, Problem.Type (Rtype.aconv_val_type Map.Poly.empty $6)
  }
  | FINEFFECTOF LPAREN IDENT RPAREN SUBTYPE eff {
    let fin, regexp = $6 in assert fin;
    Ident.Tvar $3, Problem.FinEff regexp
  }
  | INFEFFECTOF LPAREN IDENT RPAREN SUBTYPE eff {
    let fin, regexp = $6 in assert (not fin);
    Ident.Tvar $3, Problem.InfEff regexp
  }

// Refinement Type Optimization

direct:
  | MAXIMIZE LPAREN IDENT RPAREN { Tvar $3, CHCOpt.Problem.DUp }
  | MINIMIZE LPAREN IDENT RPAREN { Tvar $3, CHCOpt.Problem.DDown }
directs:
  | direct { [$1] }
  | direct COMMA directs { $1 :: $3 }
opt_pair:
  | IDENT { Tvar $1, [], [] }
  | IDENT COLON directs { Tvar $1, $3, [] }
  | IDENT COLON directs COLON space_constrs { Tvar $1, $3, $5 }
  | IDENT COLON COLON space_constrs { Tvar $1, [], $4 }
opt_problems:
  | opt_pair { [$1] }
  | opt_pair opt_problems { $1 :: $2 }
  | EOF { [] }
