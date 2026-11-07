%{
  open Core
  open Ast
  open Ast.LogicOld

(* the sort of a sized nondet (these were T_int.SInt
   regardless of the mode, so under -p ltstermbv a nondet_int() assigned to a
   bv(32) variable failed with "unification failure: bv32 = int") *)
let nondet_sort _bits =
  (* in BV mode the sort is a fresh variable, as for the unsized [nondet ()]:
     it unifies with the width of the variable the value is assigned to
     (a [nondet_char ()] stored in a [bv(32)] is a 32-bit value in
     [-128, 127]); the width range itself is added by
     [LTS.Problem.range_of_nondet] in bit-vector terms *)
  if !Problem.bv_mode then Sort.mk_fresh_svar () else T_int.SInt

(* [shl], [lshr], [ashr], [or] and [and] are read only in bit-vector mode.
   In integer mode the file asks about a program whose arithmetic the
   integer reading cannot express, so it is refused as input (the same
   [Problem.Malformed] refusal as an ill-sorted file), naming the operation
   and the bit-vector problems that do read it.  The disabled integer
   readings kept beside the shifts are not equivalent to them on negative
   operands: [ashr] rounds towards minus infinity where truncated division
   rounds towards zero, and [lshr] of a negative value is a large positive
   one. *)
let bitwise_in_integer_mode op =
  raise
    (Problem.Malformed
       (sprintf
          "the bitwise operation '%s' is read only over bit-vectors, and \
           this problem reads the file over the integers; read it with a \
           bit-vector LTS problem (-p ltstermbv or -p ltsntermbv)"
          op))
%}

%token START TYPE ERROR CUTPOINT FROM TO AT SHADOW BUCHI PRE LBRACE RBRACE
%token COLON SEMICOLON COMMA
%token SKIP ASSUME SUBST
%token SBV_TO_REAL UBV_TO_REAL INT_TO_REAL REAL_TO_INT
%token NONDET NONDET_CHAR NONDET_SHORT NONDET_INT NONDET_LONG NONDET_UCHAR NONDET_USHORT NONDET_UINT NONDET_ULONG

%token CONST_ARRAY SELECT_ARRAY STORE_ARRAY SELECT_TUPLE CONSTR_TUPLE
%token LPAREN RPAREN
%token <string> VAR
%token <string> INT
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

(* The header of LTL-VerP's dialect (the FM 2024 artifact of Chatterjee et al.)
   is START, BUCHI, CUTPOINT and PRE in that order, CUTPOINT a braced list.
   A [PRE: {c};] (the initial condition) becomes a fresh start location with
   one transition [assume(c)] into the stated start, which every mode reads
   as restricting the initial states to [c]: the query of each encoding
   quantifies over the start location's variables, and the weakest
   precondition of the new transition is [c => P_start] (its dual
   [c /\ ...] in the existential modes). *)
main:
  | start_opt type_opt error_opt buchi_opt cutpoint_opt pre_opt list(transition) EOF
    { let senv = Map.Poly.of_alist_exn $2 in
      let trans = List.filter_map ~f:(fun f -> f senv) $7 in
      (* In LTL-VerP's dialect [/] divides exactly by a constant (a rational
         coefficient: its reader multiplies by the inverse), where T2's [/]
         read here is truncated integer division, under which
         [b := (1/2) * b] would be [b := 0].  [Problem.division] chooses the
         reading of a file with a BUCHI line; the PRE line is among [trans]
         below only after this point, so it is rewritten separately. *)
      let divides =
        List.exists trans ~f:(fun (_, c, _) -> Problem.divides c)
        || Option.exists $6 ~f:(fun pre ->
             Problem.divides (Problem.Assume (pre senv)))
      in
      let exact =
        Option.is_some $4 && divides
        && (match !Problem.division with Problem.Exact -> true | _ -> false)
      in
      if Option.is_some $4 && divides then (
        match !Problem.division with
        | Problem.Refuse ->
          raise
            (Problem.Malformed
               "division is not supported in a file with a BUCHI line: \
                LTL-VerP's '/' divides exactly by a constant, T2's truncates")
        | Problem.Exact when !Problem.bv_mode ->
          raise
            (Problem.Malformed
               "exact division in a file with a BUCHI line is defined over \
                integer variables, not bit-vectors")
        | Problem.Exact | Problem.Truncate -> ());
      let trans, pre =
        if not exact then (trans, Option.map $6 ~f:(fun pre -> pre senv))
        else
          let used =
            Set.Poly.union_list
              (Set.Poly.of_list (List.map ~f:fst $2)
               :: List.map trans ~f:(fun (_, c, _) -> Problem.tvs_of_command c)
               @ Option.to_list
                   (Option.map $6 ~f:(fun pre -> Formula.tvs_of (pre senv))))
          in
          let rec fresh n =
            let v = Ident.Tvar (sprintf "__div%d" n) in
            if Set.mem used v then fresh (n + 1) else v
          in
          let tmp = fresh 0 in
          let rewrite c =
            try Problem.exact_division ~tmp c
            with Problem.Inexact why ->
              raise
                (Problem.Malformed
                   ("exact division in a file with a BUCHI line: " ^ why))
          in
          ( List.map trans ~f:(fun (f, c, t) -> (f, rewrite c, t)),
            Option.map $6 ~f:(fun pre ->
                match rewrite (Problem.Assume (pre senv)) with
                | Problem.Assume phi -> phi
                | _ -> assert false) )
      in
      (* the encodings ask about the runs from the start location, so a
         system with a transition and no START states no question *)
      if Option.is_none $1 && not (List.is_empty trans) then
        raise (Problem.Malformed "a transition system needs a START line");
      match pre, $1 with
      | None, start -> (start, $2, $3, $5, trans, $4)
      | Some _, None -> raise (Problem.Malformed "a PRE line needs a START line")
      | Some pre, Some start ->
        let used =
          Set.Poly.of_list
          @@ (start :: List.concat_map trans ~f:(fun (f, _, t) -> [ f; t ]))
        in
        let rec fresh n =
          let s = sprintf "__pre%d" n in
          if Set.mem used s then fresh (n + 1) else s
        in
        let s0 = fresh 0 in
        (Some s0, $2, $3, $5, (s0, Problem.Assume pre, start) :: trans, $4) }

buchi_opt:
    { None }
  | BUCHI COLON LBRACE separated_list(COMMA, state) RBRACE SEMICOLON { Some $4 }
  | BUCHI COLON separated_nonempty_list(COMMA, state) SEMICOLON { Some $3 }

pre_opt:
    { None }
  | PRE COLON LBRACE cond RBRACE SEMICOLON { Some $4 }

start_opt:
    { None }
  | START COLON state SEMICOLON { Some $3 }

type_opt:
    { [] }
  | TYPE VAR COLON BV LPAREN INT RPAREN SEMICOLON type_opt {
      (Ident.Tvar $2, if !Problem.bv_mode then T_bv.SBV (Some (int_of_string $6)) else T_int.SInt) :: $9
    }

error_opt:
    { None }
  | ERROR COLON state SEMICOLON { Some $3 }

cutpoint_opt:
    { None }
  | CUTPOINT COLON state SEMICOLON { Some $3 }
  (* LTL-VerP's braced list: a hint where its tool places invariants, which
     that tool itself recomputes; no encoding here reads a cut point hint *)
  | CUTPOINT COLON LBRACE separated_list(COMMA, state) RBRACE SEMICOLON { None }

transition:
  | from list(command) to_ { fun senv ->
    Some ($1, Problem.seq (List.map $2 ~f:(fun f -> f senv)), $3) }
  | SHADOW LPAREN VAR COMMA VAR RPAREN SEMICOLON { fun _senv -> None }

from:
  | FROM COLON state SEMICOLON { $3 }

to_:
  | TO COLON state SEMICOLON { $3 }

state:
  | INT { match int_of_string_opt $1 with Some n -> string_of_int n | None -> $1 }
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
      T_bv.mk_bvextract ~size (int_of_string $3) (int_of_string $5) e
    else $7 senv }
  | SEXT LPAREN INT COMMA INT COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e = $7 senv in
      T_bv.mk_bvsext ~size:(Some (int_of_string $3)) (int_of_string $5 - int_of_string $3) e
    else $7 senv }
  | ZEXT LPAREN INT COMMA INT COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      let e = $7 senv in
      T_bv.mk_bvzext ~size:(Some (int_of_string $3)) (int_of_string $5 - int_of_string $3) e
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
    else if true then bitwise_in_integer_mode "shl"
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
    else if true then bitwise_in_integer_mode "lshr"
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
    else if true then bitwise_in_integer_mode "ashr"
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
    else bitwise_in_integer_mode "or" }
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
    else bitwise_in_integer_mode "and" }
  | SBV_TO_REAL LPAREN INT COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      T_irb.mk_int_to_real (T_irb.mk_bv_to_int ~size:(Some (int_of_string $3)) ~signed:(Some true) ($5 senv))
    else T_irb.mk_int_to_real ($5 senv) }
  | UBV_TO_REAL LPAREN INT COMMA expr RPAREN { fun senv ->
    if !Problem.bv_mode then
      T_irb.mk_int_to_real (T_irb.mk_bv_to_int ~size:(Some (int_of_string $3)) ~signed:(Some false) ($5 senv))
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
    let i = int_of_string $5 and n = int_of_string $7 in
    if i = 0 && n = 1 then e
    else T_tuple.mk_tuple_sel (List.init n ~f:(fun _ -> (*ToDo*)Sort.mk_fresh_svar ())) e i }
  | CONSTR_TUPLE LPAREN exprs RPAREN { fun senv ->
    let es = List.map $3 ~f:(fun f -> f senv) in
    if List.length es = 1 then List.hd_exn es
    else T_tuple.mk_tuple_cons (List.map es ~f:Term.sort_of) es }
  | LPAREN expr RPAREN { $2 }
  | INT { fun _senv -> T_num.mk_value $1 }
  | CHAR { fun _senv -> T_num.mk_value (string_of_int (int_of_char $1)) }
  | FLOAT { fun _senv -> T_real.mk_real $1 }
  | VAR { fun senv ->
    match Map.find senv (Ident.Tvar $1) with
    | Some s -> Term.mk_var (Ident.Tvar $1) s
    | None -> Term.mk_var (Ident.Tvar $1) ((*ToDo*)Sort.mk_fresh_svar ()) }
  | NONDET LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet None) ((*ToDo*)Sort.mk_fresh_svar ()) }
  | NONDET_CHAR LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (8, true))) (nondet_sort 8) }
  | NONDET_UCHAR LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (8, false))) (nondet_sort 8) }
  | NONDET_SHORT LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (16, true))) (nondet_sort 16) }
  | NONDET_USHORT LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (16, false))) (nondet_sort 16) }
  | NONDET_INT LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (32, true))) (nondet_sort 32) }
  | NONDET_UINT LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (32, false))) (nondet_sort 32) }
  | NONDET_LONG LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (64, true))) (nondet_sort 64) }
  | NONDET_ULONG LPAREN RPAREN { fun _senv ->
    Term.mk_var (Problem.mk_nondet (Some (64, false))) (nondet_sort 64) }

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
