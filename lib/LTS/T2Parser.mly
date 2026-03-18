%{
  open Core
  open Ast
  open Ast.LogicOld
%}

%token START TYPE ERROR CUTPOINT FROM TO AT SHADOW
%token COLON SEMICOLON COMMA
%token SKIP ASSUME SUBST
%token SBV_TO_REAL UBV_TO_REAL INT_TO_REAL REAL_TO_INT
%token NONDET NONDET_CHAR NONDET_SHORT NONDET_INT NONDET_LONG NONDET_UCHAR NONDET_USHORT NONDET_UINT NONDET_ULONG

%token CONST_ARRAY SELECT_ARRAY STORE_ARRAY SELECT_TUPLE CONSTR_TUPLE
%token LPAREN RPAREN
%token <string> VAR
%token <int> INT
%token <char> CHAR
%token <Q.t> FLOAT
%token STRING
%token PLUS MINUS
%token TIMES DIV REM SDIV UDIV SREM UREM
%token EQ NEQ GEQ GT LEQ LT SGT UGT SLT ULT SGE UGE SLE ULE
%token AND OR NOT
%token BV
%token EXTRACT SEXT ZEXT SHL LSHR ASHR BITOR BITAND
%token EOF

%left OR
%left AND
%nonassoc NOT
%left PLUS MINUS
%left TIMES DIV REM SDIV UDIV SREM UREM
%nonassoc UMINUS

%type <Problem.lts> main
%start main

%%

main:
  | start_opt type_opt error_opt cutpoint_opt list(transition) EOF
    { ($1, $2, $3, $4, List.filter_map ~f:(fun f -> f (Map.Poly.of_alist_exn $2)) $5) }

start_opt:
    { None }
  | START COLON state SEMICOLON { Some $3 }

type_opt:
    { [] }
  | TYPE VAR COLON BV LPAREN INT RPAREN SEMICOLON type_opt {
      (Ident.Tvar $2, if !Problem.bv_mode then T_bv.SBV (Some $6) else T_int.SInt) :: $9
    }

error_opt:
    { None }
  | ERROR COLON state SEMICOLON { Some $3 }

cutpoint_opt:
    { None }
  | CUTPOINT COLON state SEMICOLON { Some $3 }

transition:
  | from list(command) to_ { fun senv ->
    Some ($1, Problem.seq (List.map $2 ~f:(fun f -> f senv)), $3) }
  | SHADOW LPAREN VAR COMMA VAR RPAREN SEMICOLON { fun _senv -> None }

from:
  | FROM COLON state SEMICOLON { $3 }

to_:
  | TO COLON state SEMICOLON { $3 }

state:
  | INT { string_of_int $1 }
  | VAR { $1 }

at:
  | AT LPAREN INT COMMA STRING RPAREN { () }

command:
  | at command_body { $2 }
  | command_body { $1 }
command_body:
  | VAR SUBST expr SEMICOLON { fun senv ->
    let e = $3 senv in
    Problem.Subst ((Ident.Tvar $1, Term.sort_of e), e) }
  | ASSUME LPAREN cond RPAREN SEMICOLON { fun senv -> Problem.Assume ($3 senv) }
  | SKIP SEMICOLON { fun _senv -> Problem.Skip }

expr:
  | MINUS expr %prec UMINUS { fun senv ->
    let e = $2 senv in
    if T_num.is_value e then T_num.mk_neg_value @@ fst @@ T_num.let_value e else T_num.mk_nneg e
  }
  | expr PLUS expr { fun senv ->
    let e1 = $1 senv in
    let e2 = $3 senv in
    T_num.mk_nadd e1 e2 }
  | expr MINUS expr { fun senv ->
    let e1 = $1 senv in
    let e2 = $3 senv in
    T_num.mk_nsub e1 e2 }
  | expr TIMES expr { fun senv ->
    let e1 = $1 senv in
    let e2 = $3 senv in
    T_num.mk_nmul e1 e2 }
  | expr DIV expr { fun senv ->
    let e1 = $1 senv in
    let e2 = $3 senv in
    T_num.mk_ndiv Value.Truncated e1 e2 }
  | expr SDIV expr { fun senv ->
    let e1 = $1 senv in
    let e2 = $3 senv in
    T_num.mk_ndiv Value.Truncated e1 e2 }
  | expr UDIV expr { fun senv ->
    if !Problem.bv_mode then
      let e1 = $1 senv in
      let e2 = $3 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvdiv ~size ~signed:(Some false) e1 e2
    else
      let e1 = $1 senv in
      let e2 = $3 senv in
      T_num.mk_ndiv Value.Truncated e1 e2 }
  | expr REM expr { fun senv ->
    let e1 = $1 senv in
    let e2 = $3 senv in
    T_num.mk_nrem Value.Truncated e1 e2 }
  | expr SREM expr { fun senv ->
    let e1 = $1 senv in
    let e2 = $3 senv in
    T_num.mk_nrem Value.Truncated e1 e2 }
  | expr UREM expr { fun senv ->
    if !Problem.bv_mode then
      let e1 = $1 senv in
      let e2 = $3 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvrem ~size ~signed:(Some false) e1 e2
    else
      let e1 = $1 senv in
      let e2 = $3 senv in
      T_num.mk_nrem Value.Truncated e1 e2 }
  | EXTRACT LPAREN INT COMMA INT COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e = $7 senv in
      let size =
        match Term.sort_of e with
        | T_bv.SBV size -> size
        | _ -> None
      in
      T_bv.mk_bvextract ~size $3 $5 e
    else $7 senv }
  | SEXT LPAREN INT COMMA INT COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e = $7 senv in
      T_bv.mk_bvsext ~size:(Some $3) ($5 - $3) e
    else $7 senv }
  | ZEXT LPAREN INT COMMA INT COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e = $7 senv in
      T_bv.mk_bvzext ~size:(Some $3) ($5 - $3) e
    else $7 senv }
  | SHL LPAREN expr COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e1 = $3 senv in
      let e2 = $5 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvshl ~size e1 e2
    else if true then failwith "bitwise operations are not supported in non-BV mode"
    else T_num.mk_nmul ($3 senv) (T_num.mk_npower (T_num.mk_value "2") ($5 senv)) }
  | LSHR LPAREN expr COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e1 = $3 senv in
      let e2 = $5 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvlshr ~size e1 e2
    else if true then failwith "bitwise operations are not supported in non-BV mode"
    else T_num.mk_nmul ($3 senv) (T_num.mk_npower (T_num.mk_value "2") ($5 senv)) }
  | ASHR LPAREN expr COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e1 = $3 senv in
      let e2 = $5 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvashr ~size e1 e2
    else if true then failwith "bitwise operations are not supported in non-BV mode"
    else T_num.mk_ndiv Value.Truncated ($3 senv) (T_num.mk_npower (T_num.mk_value "2") ($5 senv)) }
  | BITOR LPAREN expr COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e1 = $3 senv in
      let e2 = $5 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvor ~size e1 e2
    else failwith "bitwise operations are not supported in non-BV mode" }
  | BITAND LPAREN expr COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e1 = $3 senv in
      let e2 = $5 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvand ~size e1 e2
    else failwith "bitwise operations are not supported in non-BV mode" }
  | SBV_TO_REAL LPAREN INT COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      T_irb.mk_int_to_real (T_irb.mk_bv_to_int ~size:(Some $3) ~signed:(Some true) ($5 senv))
    else T_irb.mk_int_to_real ($5 senv) }
  | UBV_TO_REAL LPAREN INT COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      T_irb.mk_int_to_real (T_irb.mk_bv_to_int ~size:(Some $3) ~signed:(Some false) ($5 senv))
    else T_irb.mk_int_to_real ($5 senv) }
  | INT_TO_REAL LPAREN expr RPAREN { fun senv -> T_irb.mk_int_to_real ($3 senv) }
  | REAL_TO_INT LPAREN expr RPAREN { fun senv -> T_irb.mk_real_to_int ($3 senv) }
  | CONST_ARRAY LPAREN expr RPAREN { fun senv ->
    let e = $3 senv in
    T_array.mk_const_array (if true then (*ToDo*)Sort.mk_fresh_svar () else T_int.SInt) (Term.sort_of e) e }
  | SELECT_ARRAY LPAREN expr COMMA expr RPAREN { fun senv ->
    let e1 = $3 senv in
    let e2 = $5 senv in
    T_array.mk_select (if true then Term.sort_of e2 else T_int.SInt) ((*ToDo*)Sort.mk_fresh_svar ()) e1 e2 }
  | STORE_ARRAY LPAREN expr COMMA expr COMMA expr RPAREN { fun senv ->
    let e1 = $3 senv in
    let e2 = $5 senv in
    let e3 = $7 senv in
    T_array.mk_store (if true then Term.sort_of e2 else T_int.SInt) (Term.sort_of e3) e1 e2 e3 }
  | SELECT_TUPLE LPAREN expr COMMA INT COMMA INT RPAREN { fun senv ->
    let e = $3 senv in
    if $5 = 0 && $7 = 1 then e
    else T_tuple.mk_tuple_sel (List.init $7 ~f:(fun _ -> (*ToDo*)Sort.mk_fresh_svar ())) e $5 }
  | CONSTR_TUPLE LPAREN exprs RPAREN { fun senv ->
    let es = List.map $3 ~f:(fun f -> f senv) in
    if List.length es = 1 then List.hd_exn es
    else T_tuple.mk_tuple_cons (List.map es ~f:Term.sort_of) es }
  | LPAREN expr RPAREN { $2 }
  | INT { fun _senv -> T_num.mk_value (string_of_int $1) }
  | CHAR { fun _senv -> T_num.mk_value (string_of_int (int_of_char $1)) }
  | FLOAT { fun _senv -> T_real.mk_real $1 }
  | VAR { fun senv ->
    match Map.find senv (Ident.Tvar $1) with
    | Some s -> Term.mk_var (Ident.Tvar $1) s
    | None -> Term.mk_var (Ident.Tvar $1) ((*ToDo*)Sort.mk_fresh_svar ()) }
  | NONDET LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet None) ((*ToDo*)Sort.mk_fresh_svar ()) }
  | NONDET_CHAR LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (8, true))) T_int.SInt }
  | NONDET_UCHAR LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (8, false))) T_int.SInt }
  | NONDET_SHORT LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (16, true))) T_int.SInt }
  | NONDET_USHORT LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (16, false))) T_int.SInt }
  | NONDET_INT LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (32, true))) T_int.SInt }
  | NONDET_UINT LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (32, false))) T_int.SInt }
  | NONDET_LONG LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (64, true))) T_int.SInt }
  | NONDET_ULONG LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (64, false))) T_int.SInt }

exprs:
  | expr { [ $1 ] }
  | expr COMMA exprs { $1 :: $3 }

cond:
  | LPAREN cond RPAREN { $2 }
  | cond AND cond { fun senv -> Formula.mk_and ($1 senv) ($3 senv) }
  | cond OR cond { fun senv -> Formula.mk_or ($1 senv) ($3 senv) }
  | NOT cond { fun senv -> Formula.mk_neg ($2 senv) }
  | atom { fun senv -> Formula.mk_atom ($1 senv) }

atom:
  | expr EQ expr { fun senv -> T_bool.mk_eq ($1 senv) ($3 senv) }
  | expr NEQ expr { fun senv -> T_bool.mk_neq ($1 senv) ($3 senv) }
  | expr GEQ expr { fun senv -> T_num.mk_ngeq ($1 senv) ($3 senv) }
  | expr SGE expr { fun senv -> T_num.mk_ngeq ($1 senv) ($3 senv) }
  | expr UGE expr { fun senv ->
    if !Problem.bv_mode then
      let e1 = $1 senv in
      let e2 = $3 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvgeq ~size ~signed:(Some false) e1 e2
    else T_num.mk_ngeq ($1 senv) ($3 senv) }
  | expr GT expr { fun senv -> T_num.mk_ngt ($1 senv) ($3 senv) }
  | expr SGT expr { fun senv -> T_num.mk_ngt ($1 senv) ($3 senv) }
  | expr UGT expr { fun senv ->
    if !Problem.bv_mode then
      let e1 = $1 senv in
      let e2 = $3 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvgt ~size ~signed:(Some false) e1 e2
    else T_num.mk_ngt ($1 senv) ($3 senv) }
  | expr LEQ expr { fun senv -> T_num.mk_nleq ($1 senv) ($3 senv) }
  | expr SLE expr { fun senv -> T_num.mk_nleq ($1 senv) ($3 senv) }
  | expr ULE expr { fun senv ->
    if !Problem.bv_mode then
      let e1 = $1 senv in
      let e2 = $3 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvleq ~size ~signed:(Some false) e1 e2
    else T_num.mk_nleq ($1 senv) ($3 senv) }
  | expr LT expr { fun senv -> T_num.mk_nlt ($1 senv) ($3 senv) }
  | expr SLT expr { fun senv -> T_num.mk_nlt ($1 senv) ($3 senv) }
  | expr ULT expr { fun senv ->
    if !Problem.bv_mode then
      let e1 = $1 senv in
      let e2 = $3 senv in
      let size =
        match Term.sort_of e1, Term.sort_of e2 with
        | T_bv.SBV size1, T_bv.SBV size2 ->
          T_bv.merge_size size1 size2
        | T_bv.SBV size1, _ -> size1
        | _, T_bv.SBV size2 -> size2
        | _ -> None
      in
      T_bv.mk_bvlt ~size ~signed:(Some false) e1 e2
    else T_num.mk_nlt ($1 senv) ($3 senv) }
