%{
open Common.Ext
open Common.Util
open Ident
open LogicOld
open Grammar

let print _ = ()

(*let print_error_information () =
  let st = Parsing.symbol_start_pos () in
  let en = Parsing.symbol_end_pos () in
  print_string ("File \"" ^ st.Lexing.pos_fname);
  Format.printf "\", line %d" st.Lexing.pos_lnum;
  Format.printf ", characters %d-%d:\n"
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
    (en.Lexing.pos_cnum - en.Lexing.pos_bol)*)
%}

//%token <string> UNKNOWN
%token <string> IDENT
%token <string> IDENT_T
%token <string> CONST
%token <bool> BOOL
%token <int> INT
%token <float> FLOAT
%token <string> RECOGNIZER
%token <string * int> ACCESSOR
//%token <string * string> SIZE

%token TRUE FALSE

//%token TEMPLATE
%token MAXIMIZE
%token MINIMIZE
//%token PRIORITIZE

//%token LET
%token IN
%token EQUAL
%token NOTEQUAL
%token COMMA
%token LPAREN // '('
%token RPAREN // ')'
%token AMP // '&'
%token VERT // '|'

%token PROJ ABS SQRT ToInt ToReal

%token FORALL EXISTS //MU NU
%token DOT
%token AND OR IMP IFF NOT
%token LT GT LEQ GEQ
%token ADD SUB AST DIV MOD
%token EXC
%token FADD FSUB FMUL FDIV
//%token EQEQ

%token LBRA
%token RBRA
%token COLON // ':'
%token COLCOL // "::"
//%token SLASLA // "//"
%token ARROW
//%token LARROW
//%token PAIR
%token SUBTYPE
//%token MEMBER
//%token SUBSET
//%token SUNION
//%token SINTERSECT
//%token SDIFF
%token SEMPTY
//%token SCOMP

//%token LBRACKET
//%token RBRACKET
%token APPLY

%token QUESTION

//%token LABRA
//%token RABRA

%token TYPEOF
%token FINEFFECTOF
%token INFEFFECTOF

%token EPSILON
%token EVENT
%token PLUSPLUS

//%token COLEQ
//%token COLMIN // ":-"
//%token QMIN // "?-"

%token SEMICOLON
//%token TURNSTILE
%token RTRI // |>
%token WILDCARD // _

%token EOF

//%right prec_tyarrow
%nonassoc prec_typair
//%left prec_tyapp

//%right LARROW COLEQ
//%left COMMA

%right IMP
%left OR VERT
%left AND //AMP
%right NOT //EXC
//%nonassoc FORALL EXISTS //MU NU

%left EQUAL NOTEQUAL LT GT LEQ GEQ
//%left EQEQ

%right COLCOL

%left PLUSPLUS

//%left SUNION
//%left SINTERSECT SDIFF
//%right SCOMP

%left ADD SUB FADD FSUB
%left AST DIV FMUL FDIV MOD
%right unary_minus
%left prec_app
%left DOT

%start constraints val_ty_env comp_ty assertions opt_problems formula

%type <LogicOld.sort_env_map -> LogicOld.Term.t> term
%type <LogicOld.sort_env_map -> LogicOld.Atom.t> atom
%type <LogicOld.sort_env_map -> LogicOld.Formula.t> prop
%type <LogicOld.Formula.t> formula

%type <LogicOld.sort_bind> bind
%type <LogicOld.sort_env_list> binds

%type <LogicOld.sort_env_map -> Rtype.t> val_ty
%type <LogicOld.sort_env_map -> Rtype.c> comp_ty
%type <LogicOld.sort_env_map -> Rtype.o> opsig_ty
%type <LogicOld.sort_env_map -> Sort.t -> Rtype.s> cont_eff_ty

%type <LogicOld.Formula.t list> constraints
%type <Rtype.Env.t> val_ty_env

%type <(Ident.tvar * Assertion.t) list> assertions
%type <(Ident.tvar * (Ident.tvar * Assertion.direction) list * (Ident.tvar * SolSpace.space_flag * int) list) list> opt_problems

%%

term:
  | LPAREN term RPAREN { $2 }
  | VERT prop VERT { fun env -> T_bool.of_formula @@ $2 env }
  | IDENT {
    let var = Ident.Tvar $1 in
    fun env ->
      Term.mk_var var @@ try Map.Poly.find_exn env var with Core.Not_found_s _ -> Sort.mk_fresh_svar ()
    (*failwith @@ (Ident.name_of_tvar var) ^ " not found"*) }
  /* this causes reduce/reduce conflict on RPAREN
  | BOOL { fun _ -> T_bool.make $1 } */
  | TRUE { fun _ -> T_bool.make true }
  | FALSE { fun _ -> T_bool.make false }
  | INT { fun _ -> T_int.from_int $1 }
  | FLOAT { fun _ -> T_real.mk_real @@ Q.of_float $1 }
  | APPLY IDENT LPAREN terms RPAREN {
    let var = Ident.Tvar $2 in
    match Rtype.Env.look_up !Rtype.renv_ref var with
    | Some t ->
      let args, ret = Sort.args_ret_of @@ Rtype.sort_of_val t in
      fun env -> Term.mk_fvar_app var (args @ [ret]) ($4 env)
    | None ->
      match Map.Poly.find (get_fenv ()) var with
      | Some (params, ret_sort, _, _, _) ->
        fun env -> Term.mk_fvar_app var (List.map params ~f:snd @ [ret_sort]) ($4 env)
      | None -> failwith @@ "unbound function variable: " ^ $2
  }
  | SUB term %prec unary_minus { fun env -> T_num.mk_nneg ($2 env) }
  | FSUB term %prec unary_minus { fun env -> T_real.mk_rneg ($2 env) }
  | ABS term %prec prec_app { fun env -> T_int.mk_abs ($2 env) }
  | SQRT term %prec prec_app { fun env -> T_real.mk_rpower ($2 env) (T_real.mk_real @@ Q.of_float 0.5) }
  | ToInt term %prec prec_app { fun env -> T_irb.mk_real_to_int ($2 env) }
  | ToReal term %prec prec_app { fun env -> T_irb.mk_int_to_real ($2 env) }
  | term ADD term { fun env -> T_num.mk_nadd ($1 env) ($3 env) }
  | term SUB term { fun env -> T_num.mk_nsub ($1 env) ($3 env) }
  | term AST term { fun env -> T_num.mk_nmult ($1 env) ($3 env) }
  | term DIV term { fun env -> T_num.mk_ndiv ($1 env) ($3 env) }
  | term MOD term { fun env -> T_num.mk_nmod ($1 env) ($3 env) }
  | term FADD term { fun env -> T_real.mk_radd ($1 env) ($3 env) }
  | term FSUB term { fun env -> T_real.mk_rsub ($1 env) ($3 env) }
  | term FMUL term { fun env -> T_real.mk_rmult ($1 env) ($3 env) }
  | term FDIV term { fun env -> T_real.mk_rdiv ($1 env) ($3 env) }
  /*| LPAREN terms RPAREN {
    fun env ->
    let ts = $2 env in
    T_tuple.mk_tuple_cons (List.map ~f:Term.sort_of ts) ts
  }*/
  | PROJ LPAREN INT COMMA term RPAREN {
    fun env ->
    let t = $5 env in
    match Term.sort_of t with
    | T_tuple.STuple sorts -> T_tuple.mk_tuple_sel sorts t $3
    | _ -> failwith "type error"
  }
  | CONST LPAREN terms RPAREN {
    fun env ->
    let ts = $3 env in
    if String.($1 = "Tuple")
    then T_tuple.mk_tuple_cons (List.map ~f:Term.sort_of ts) ts
    else
      match DTEnv.look_up_dt_by_cons_name (get_dtenv ()) $1 with
      | Some dt -> T_dt.mk_cons dt $1 ts
      | _ -> failwith @@ "undefined constructor: " ^ $1
  }
  | CONST {
    match DTEnv.look_up_dt_by_cons_name (get_dtenv ()) $1 with
    | Some dt -> fun _ -> T_dt.mk_cons dt $1 []
    | _ -> failwith @@ "undefined constructor: " ^ $1
  }
  | CONST term {
    match DTEnv.look_up_dt_by_cons_name (get_dtenv ()) $1 with
    | Some dt -> fun env -> T_dt.mk_cons dt $1 [$2 env]
    | _ -> failwith @@ "undefined constructor: " ^ $1
  }
  | term COLCOL term {
    match DTEnv.look_up_dt_by_cons_name (get_dtenv ()) "::" with
    | Some dt -> fun env -> T_dt.mk_cons dt "::" [$1 env; $3 env]
    | _ -> failwith @@ "undefined constructor: " ^ "::"
  }
  | COLCOL LPAREN terms RPAREN {
    match DTEnv.look_up_dt_by_cons_name (get_dtenv ()) "::" with
    | Some dt -> fun env -> T_dt.mk_cons dt "::" ($3 env)
    | _ -> failwith @@ "undefined constructor: " ^ "::"
  }
  | ACCESSOR LPAREN term RPAREN {
    let cons_name, n = $1 in
    match DTEnv.look_up_dt_by_cons_name (get_dtenv ()) cons_name with
    | Some dt -> fun env -> T_dt.mk_sel_by_cons dt cons_name n ($3 env)
    | None -> failwith @@ "undefined constructor" ^ cons_name
  }
  | EPSILON { fun _ -> Term.mk_fsym_app T_sequence.SeqEpsilon [] }
  | EVENT LPAREN IDENT RPAREN { fun _ -> Term.mk_fsym_app (T_sequence.SeqSymbol $3) [] }
  | term PLUSPLUS term {
    fun env ->
    match Term.sort_of @@ $1 env with
    | T_sequence.SSequence fin ->
      Term.mk_fsym_app (T_sequence.SeqConcat fin) [$1 env; $3 env]
    | _ -> failwith "type error"
  }
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
  | term { fun env -> [$1 env] }
  | term COMMA terms { fun env -> $1 env :: $3 env }

// Temporal Effects

eff:
  | EVENT LPAREN IDENT RPAREN {
    true, RegWordExp.Symbol $3
  }
  | EVENT LPAREN IDENT RPAREN AST {
    true, RegWordExp.Repeat (RegWordExp.Symbol $3)
  }
  | EVENT LPAREN IDENT RPAREN EXC {
    false, RegWordExp.RepeatInf (RegWordExp.Symbol $3)
  }
  | LPAREN eff RPAREN { $2 }
  | LPAREN eff RPAREN AST {
    let fin, regexp = $2 in assert fin; true, RegWordExp.Repeat regexp
  }
  | LPAREN eff RPAREN EXC {
    let fin, regexp = $2 in assert fin; false, RegWordExp.RepeatInf regexp
  }
  | eff eff {
    let fin1, regexp1 = $1 in
    let fin2, regexp2 = $2 in
    assert fin1;
    fin2, RegWordExp.Concat (regexp1, regexp2)
  }
  | eff VERT eff {
    let fin1, regexp1 = $1 in
    let fin2, regexp2 = $3 in
    assert (fin1 = fin2);
    fin1, RegWordExp.Alter (regexp1, regexp2)
  }

atom:
  | IDENT LPAREN RPAREN /* to avoid reduce/reduce conflict on RPAREN */ {
    fun _ -> Atom.of_bool_var @@ Ident.Tvar $1
  }
  | BOOL { fun _ -> Atom.mk_bool $1 }
  | TRUE LPAREN RPAREN { fun _ -> Atom.mk_bool true }
  | FALSE LPAREN RPAREN { fun _ -> Atom.mk_bool false }
  | IDENT LPAREN terms RPAREN {
    match Map.Poly.find (get_fenv ()) (Tvar $1) with
    | Some (params, ret_sort, _, _, _) ->
      if Term.is_bool_sort ret_sort then
        let sorts = List.map params ~f:snd in
        fun env ->
        T_bool.mk_eq (Term.mk_fvar_app (Tvar $1) (sorts @ [ret_sort]) ($3 env)) @@
        T_bool.mk_true ()
      else failwith ""
    | None ->
      fun env ->
      let ts = $3 env in
      match Map.Poly.find (Rtype.Env.pred_sort_env_of !Rtype.renv_ref) (Pvar $1) with
      | Some sorts -> Atom.mk_pvar_app (Pvar $1) sorts ts
      | _ -> Atom.mk_pvar_app (Pvar $1) (List.map ts ~f:Term.sort_of) ts
  }
  | atom_or_term EQUAL atom_or_term { fun env -> T_bool.mk_eq ($1 env) ($3 env) }
  | atom_or_term NOTEQUAL atom_or_term { fun env -> T_bool.mk_neq ($1 env) ($3 env) }
  | term LT term { fun env -> T_num.mk_nlt ($1 env) ($3 env) }
  | term GT term { fun env -> T_num.mk_ngt ($1 env) ($3 env) }
  | term LEQ term { fun env -> T_num.mk_nleq ($1 env) ($3 env) }
  | term GEQ term { fun env -> T_num.mk_ngeq ($1 env) ($3 env) }
  | RECOGNIZER LPAREN term RPAREN{
    match DTEnv.look_up_dt_by_cons_name (get_dtenv ()) $1 with
    | Some dt -> fun env -> T_dt.mk_is_cons dt $1 ($3 env)
    | None -> failwith @@ "unknown cons name" ^ $1
  }
  // | term IN term { Formula.Set.mk_mem Type.mk_unknown $1 $3 }
  // | term SUBSET term { Formula.Set.mk_subset Type.mk_unknown $1 $3 }
  | term IN eff {
    let fin, regexp = $3 in
    fun env -> Atom.mk_psym_app (T_sequence.SeqInRegExp (fin, regexp)) [$1 env]
  }
atom_or_term:
  | atom { fun env -> T_bool.of_atom ($1 env) }
  | term { fun env -> $1 env }

prop:
  | LPAREN prop RPAREN { $2 }
  | atom { fun env -> Typeinf.typeinf_formula ~print @@ Formula.mk_atom ($1 env) }
  | NOT prop { fun env -> Formula.mk_neg ($2 env) }
  | prop AND prop { fun env -> Formula.mk_and ($1 env) ($3 env) }
  | prop OR prop { fun env -> Formula.mk_or ($1 env) ($3 env) }
  | prop IMP prop { fun env -> Formula.mk_imply ($1 env) ($3 env) }
  | prop IFF prop { fun env -> Formula.mk_iff ($1 env) ($3 env) }
  // | LBRACKET IDENT RBRACKET prop { Formula.box $2 $4 }
  // | LT IDENT GT prop { Formula.diamond $2 $4 }
  // | MU IDENT DOT prop { Formula.mu (Idnt.make $2) $4 }
  // | NU IDENT DOT prop { Formula.nu (Idnt.make $2) $4 }
  | FORALL binds DOT prop {
    fun env ->
    let env' = List.fold $2 ~init:env ~f:(fun env (x, s) -> Map.Poly.set env ~key:x ~data:s) in
    Formula.forall $2 ($4 env')
  }
  | EXISTS binds DOT prop {
    fun env ->
    let env' = List.fold $2 ~init:env ~f:(fun env (x, s) -> Map.Poly.set env ~key:x ~data:s) in
    Formula.exists $2 ($4 env')
  }
  | FORALL DOT prop {
    fun env -> Formula.forall [] ($3 env)
  }
binds:
  | bind { [$1] }
  | bind binds { $1 :: $2 }
bind:
  | IDENT COLON val_ty /*ToDo*/  {
    let tvar, ty = Ident.Tvar $1, $3 Map.Poly.empty in
    tvar, Rtype.sort_of_val ty
  }

formula:
  | prop EOF { $1 Map.Poly.empty }

val_ty:
  | LPAREN val_ty RPAREN { $2 }
  | IDENT {
    fun _ ->
    Rtype.simple_val_of_sort ~config:!Rtype.cgen_config @@
    Typeinf.sort_of_name (get_dtenv ()) $1
  }
  | val_ty IDENT /*%prec prec_tyapp*/ {
    if String.($2 = "ref") then
      fun env -> Rtype.mk_rref ($1 env) (Rtype.mk_fresh_trivial_pred ())
    else
      fun env ->
      Rtype.mk_rcompound [$1 env] (Typeinf.sort_of_name (get_dtenv ()) $2) @@
      Rtype.mk_fresh_trivial_pred ()
  }
  | LPAREN val_tys_comma RPAREN IDENT /*%prec prec_tyapp*/ {
    fun env ->
    Rtype.mk_rcompound ($2 env) (Typeinf.sort_of_name (get_dtenv ()) $4) @@
    Rtype.mk_fresh_trivial_pred ()
  }
  | val_ty ARROW comp_ty /*%prec prec_tyarrow*/ {
    fun env ->
    let t = $1 env in
    let x = Rtype.tvar_of_val t in
    let c = $3 env in
    Rtype.mk_rarrow x t c @@ Rtype.mk_fresh_trivial_pred ()
  }
  | LPAREN IDENT COLON val_ty RPAREN ARROW comp_ty /*%prec prec_tyarrow*/ {
    fun env ->
    let x = Ident.Tvar $2 in
    let t = $4 env in
    let c = $7 (Map.Poly.set env ~key:x ~data:(Rtype.sort_of_val t)) in
    Rtype.mk_rarrow x t c @@ Rtype.mk_fresh_trivial_pred ()
  }
  | val_tys_ast %prec prec_typair {
    fun env ->
    Rtype.mk_rtuple ($1 env) @@ Rtype.mk_fresh_trivial_pred ()
  }
  | LBRA IDENT COLON val_ty VERT prop RBRA {
    fun env ->
    let x = Ident.Tvar $2 in
    let t = $4 env in
    Rtype.conj_pred_val (x, $6 (Map.Poly.set env ~key:x ~data:(Rtype.sort_of_val t))) t
  }
val_tys_comma:
  | val_ty COMMA val_ty { fun env -> [$1 env; $3 env] }
  | val_tys_comma COMMA val_ty { fun env -> $1 env @ [$3 env] }
val_tys_ast:
  | val_ty AST val_ty { fun env -> [$1 env; $3 env] }
  | val_tys_ast AST val_ty { fun env -> $1 env @ [$3 env] }

opsig_ty:
  | SEMPTY { fun _ -> (ALMap.empty, None) } // SEMPTY has higher precedence than "LBRA RBRA"
  | LBRA RBRA { fun _ -> (ALMap.empty, None) }
  | LBRA op_tys { fun env -> ($2 env, None) }
op_tys:
  | CONST COLON val_ty RBRA { fun env -> ALMap.singleton $1 ($3 env) }
  | CONST COLON val_ty COMMA op_tys {
    fun env -> ALMap.add_exn ~key:$1 ~data:($3 env) ($5 env)
  }

cont_eff_ty:
  | WILDCARD { fun _ _ -> Rtype.Pure }
  | QUESTION { fun _ _ -> Rtype.EVar (Ident.mk_fresh_evar ()) }
  | comp_ty IMP comp_ty {
    fun env _ -> Rtype.Eff ((Rtype.mk_fresh_tvar_with "x"), $1 env, $3 env)
  }
  | LPAREN FORALL IDENT DOT comp_ty RPAREN IMP comp_ty {
    fun env sort ->
    let x = Ident.Tvar $3 in
    Rtype.Eff (x, $5 (Map.Poly.set env ~key:x ~data:sort), $8 env)
  }

comp_ty:
  // T
  | val_ty {
    fun env -> Rtype.pure_comp_of_val ~config:!Rtype.cgen_config ($1 env)
  }
  | QUESTION {
    fun _ ->
    { op_sig = ALMap.empty, Some (Ident.mk_fresh_rvar ());
      val_type = Rtype.simple_val_of_sort ~config:!Rtype.cgen_config (Sort.mk_fresh_svar ());
      temp_eff = ((Ident.mk_fresh_tvar (), Formula.mk_true ()), (Ident.mk_fresh_tvar (), Formula.mk_true ()));
      cont_eff = Rtype.EVar (Ident.mk_fresh_evar ()) }
  }
  // (T & E)
  | LPAREN val_ty AMP IDENT DOT prop COMMA IDENT DOT prop RPAREN {
    fun env ->
    let x1 = Ident.Tvar $4 in
    let x2 = Ident.Tvar $8 in
    { op_sig = ALMap.empty(*temporary*), None;
      val_type = $2 env;
      temp_eff = ((x1, $6 (Map.Poly.set env ~key:x1 ~data:(T_sequence.SSequence true))),
                  (x2, $10 (Map.Poly.set env ~key:x2 ~data:(T_sequence.SSequence false))));
      cont_eff = Rtype.Pure }
  }
  // (T / S)
  | LPAREN val_ty DIV cont_eff_ty RPAREN {
    fun env ->
    let t = $2 env in
    { op_sig = ALMap.empty, None;
      val_type = t;
      temp_eff = Rtype.mk_temp_trivial ()(*temporary*);
      cont_eff = $4 env (Rtype.sort_of_val t) }
  }
  // (sigma |> T / S)
  | LPAREN opsig_ty RTRI val_ty DIV cont_eff_ty RPAREN {
    fun env ->
    let t = $4 env in
    { op_sig = $2 env;
      val_type = t;
      temp_eff = Rtype.mk_temp_trivial ();
      cont_eff = $6 env (Rtype.sort_of_val t) }
  }
  // (sigma |> T & E / S)
  | LPAREN opsig_ty RTRI val_ty AMP IDENT DOT prop COMMA IDENT DOT prop DIV cont_eff_ty RPAREN {
    fun env ->
    let x1 = Ident.Tvar $6 in
    let x2 = Ident.Tvar $10 in
    let t = $4 env in
    { op_sig = $2 env;
      val_type = t;
      temp_eff =
        ((x1, $8 (Map.Poly.set env ~key:x1 ~data:(T_sequence.SSequence true))),
         (x2, $12 (Map.Poly.set env ~key:x1 ~data:(T_sequence.SSequence false))));
      cont_eff = $14 env (Rtype.sort_of_val t) }
  }

val_ty_bind:
  | IDENT COLCOL val_ty {
    Ident.Tvar $1, Rtype.set_sort_val ~print Map.Poly.empty ($3 Map.Poly.empty)
  }
  | CONST COLCOL val_ty {
    Ident.Tvar $1, Rtype.set_sort_val ~print Map.Poly.empty ($3 Map.Poly.empty)
  }
  | COLCOL COLCOL val_ty {
    Ident.Tvar "::", Rtype.set_sort_val ~print Map.Poly.empty ($3 Map.Poly.empty)
  }
val_ty_env:
  | val_ty_bind val_ty_env {
    let tvar, ty = $1 in
    Rtype.Env.set_ty $2 tvar @@ Rtype.aconv_val Map.Poly.empty ty
  }
  | EOF { Rtype.Env.mk_empty () }

// Space Constraints

space_constr:
  | IDENT DOT IDENT EQUAL INT { Tvar $1, SolSpace.space_flag_of $3, $5 }
  | IDENT_T DOT IDENT EQUAL INT { Tvar $1, SolSpace.space_flag_of $3, $5 }
space_constrs:
  | space_constr { [$1] }
  | space_constr SEMICOLON space_constrs { $1 :: $3 }
  | EOF { [] }

// Logical Constraints

constraints:
  | prop SEMICOLON constraints { $1 Map.Poly.empty :: $3 }
  | EOF { [] }

// Refinement Type and Temporal Effect Inference

assertions:
  | assertion assertions { $1 :: $2 }
  | EOF { [] }
  /*| error {
    print_error_information ();
    failwith "Syntax error"
  }*/
assertion:
  | TYPEOF LPAREN IDENT RPAREN SUBTYPE val_ty {
    Ident.Tvar $3, Assertion.Type (Rtype.aconv_val Map.Poly.empty ($6 Map.Poly.empty))
  }
  | FINEFFECTOF LPAREN IDENT RPAREN SUBTYPE eff {
    let fin, regexp = $6 in assert fin;
    Ident.Tvar $3, Assertion.FinEff regexp
  }
  | INFEFFECTOF LPAREN IDENT RPAREN SUBTYPE eff {
    let fin, regexp = $6 in assert (not fin);
    Ident.Tvar $3, Assertion.InfEff regexp
  }

// Refinement Type Optimization

direct:
  | MAXIMIZE LPAREN IDENT RPAREN { Tvar $3, Assertion.DUp }
  | MINIMIZE LPAREN IDENT RPAREN { Tvar $3, Assertion.DDown }
directs:
  | direct { [$1] }
  | direct COMMA directs { $1 :: $3 }
opt_pair:
  | IDENT { Tvar $1, [], [] }
  | IDENT COLON directs { Tvar $1, $3, [] }
  | IDENT COLON directs COLON space_constrs { Tvar $1, $3, $5 }
  | IDENT COLON COLON space_constrs { Tvar $1, [], $4 }
opt_problems:
  | opt_pair opt_problems { $1 :: $2 }
  | EOF { [] }
