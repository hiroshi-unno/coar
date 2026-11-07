%{
  open Core
  open Ast
  open Ast.LogicOld

  (* Terms and formulas are read by one set of productions, and a phrase is
     classified as one or the other only where its context needs one.  The
     reason is the phrase [( ID )]: with separate grammars a parser must decide
     whether it is a parenthesised term or a parenthesised formula when it
     reaches the [)], and the token that decides ([> 0] after it, or [/\])
     comes later, so an LR(1) parser cannot.  Read as one phrase, the decision
     is made once the context is known.

     [Tm (t, Some x)] is a term that is exactly the identifier [x], possibly
     parenthesised.  In term position it is the variable [x]; in formula
     position it is an application of the predicate [x] without arguments,
     which is how a declared nullary predicate may be applied besides [x ()].
     Whether [x] is such a predicate is known only once every definition has
     been read, so such an application is marked and resolved by
     [resolve_bare] at the top level. *)
  type expr = Fml of Formula.t | Tm of Term.t * string option

  type info += Bare_nullary

  let fail msg = raise (Problem.Syntax_error msg)

  let fml_of = function
    | Fml phi -> phi
    | Tm (_, Some x) ->
        Formula.mk_atom
          (Atom.mk_pvar_app ~info:Bare_nullary (Ident.Pvar x) [] [])
    | Tm (t, None) ->
        fail (sprintf "the term %s stands where a formula is expected"
                (Term.str_of t))

  let tm_of = function
    | Tm (t, _) -> t
    | Fml phi ->
        fail (sprintf "the formula %s stands where a term is expected"
                (Formula.str_of phi))

  let is_bare = function
    | Atom.App (Predicate.Var (_, []), [], Bare_nullary) -> true
    | _ -> false

  (* Contract: every marked application of [x] in [phi] is checked against the
     scope it occurs in.  It is the predicate [x] when [x] is not bound there
     (by a binder of [phi] or by a parameter in [bound]) and [nullary] holds
     it; a bound [x] is a variable, and a variable is not a formula, so it is
     refused, as is a name that is no nullary predicate.  The grammar builds
     only atoms, connectives and binders, so the walk needs no other case. *)
  let rec check_bare ~nullary bound phi =
    match phi with
    | Formula.Atom ((Atom.App (Predicate.Var (Ident.Pvar x, []), [], _) as atm), _)
      when is_bare atm ->
        if Set.mem bound x then
          fail (sprintf "%s is a variable here and stands as a formula; a \
                         variable is not a formula" x)
        else if not (Set.mem nullary x) then
          fail (sprintf "%s stands as a formula but names no predicate \
                         without parameters" x)
    | Formula.Atom _ -> ()
    | Formula.UnaryOp (_, phi, _) -> check_bare ~nullary bound phi
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        check_bare ~nullary bound phi1; check_bare ~nullary bound phi2
    | Formula.Bind (_, senv, phi, _) ->
        check_bare ~nullary
          (List.fold senv ~init:bound ~f:(fun s (Ident.Tvar x, _) -> Set.add s x))
          phi
    | Formula.LetRec _ | Formula.LetFormula _ -> ()

  let has_bare phi =
    let found = ref false in
    Formula.iter_atom phi ~f:(fun atm -> if is_bare atm then found := true);
    !found

  (* the marked application, once checked, becomes the ordinary one [x ()]
     builds; a formula without one is returned as it is *)
  let unmark phi =
    if has_bare phi then
      Formula.map_atom phi ~f:(function
        | Atom.App (p, args, Bare_nullary) -> Formula.mk_atom (Atom.mk_app p args)
        | atm -> Formula.mk_atom atm)
    else phi

  (* Datatypes.  A file may open with SMT-LIB [declare-datatypes] commands,
     which the loader reads before this grammar runs and registers in the
     process-wide datatype environment; the actions below consult it.

     Contract: a name that the environment declares as a constructor or a
     selector is that function wherever it is applied, and a constructor
     without fields is that constant wherever its name stands as a term, so
     such a name cannot also be used as a variable or a predicate.  A
     datatype's name is a sort.  A file without declarations reads exactly as
     before, since the environment then declares nothing.  Parametric
     datatypes are refused: this format writes no sort arguments. *)
  let datatype_func name =
    match DTEnv.look_up_func (get_dtenv ()) name with
    | Some (dt, (Datatype.FCons _ | Datatype.FSel _ as func)) ->
        Some (Datatype.fresh_of dt, func)
    | _ -> None

  let datatype_app name args =
    match datatype_func name, args with
    | Some (dt, Datatype.FCons _), _ -> Some (T_dt.mk_cons dt name args)
    | Some (dt, Datatype.FSel _), [ arg ] -> Some (T_dt.mk_sel dt name arg)
    | Some (_, Datatype.FSel _), _ ->
        fail (sprintf "the selector %s takes one argument, applied to %d"
                name (List.length args))
    | _ -> None

  let datatype_const name =
    match datatype_func name with
    | Some (dt, Datatype.FCons cons)
      when List.is_empty (Datatype.sels_of_cons cons) ->
        Some (T_dt.mk_cons dt name [])
    | _ -> None

  let datatype_sort name =
    match DTEnv.look_up_dt (get_dtenv ()) name with
    | Some dt when List.is_empty (Datatype.params_of dt) -> T_dt.SDT dt
    | Some _ ->
        fail (sprintf "the datatype %s is parametric, and this format writes \
                       no sort arguments" name)
    | None -> fail (sprintf "%s names no sort" name)

  (* A tester is written [is_C t] for a constructor [C], as a predicate
     application, since the identifier class of this format has no [-] for
     SMT-LIB's [is-C].  It is a tester only when no predicate of that name is
     defined, which is known only once every definition has been read, so the
     resolution runs at the top level, after [resolve_bare]. *)
  let resolve_testers preds query =
    let defined =
      String.Set.of_list
        (List.map preds ~f:(fun (pred : Pred.t) -> Ident.name_of_pvar pred.name))
    in
    let tester = function
      | Atom.App (Predicate.Var (Ident.Pvar name, _), [ t ], _) as atm -> (
          match String.chop_prefix name ~prefix:"is_" with
          | Some c when not (Set.mem defined name) -> (
              match datatype_func c with
              | Some (dt, Datatype.FCons _) ->
                  Formula.mk_atom (T_dt.mk_is_cons dt c t)
              | _ -> Formula.mk_atom atm)
          | _ -> Formula.mk_atom atm)
      | atm -> Formula.mk_atom atm
    in
    if Map.Poly.is_empty (get_dtenv ()) then (preds, query)
    else
      ( List.map preds ~f:(Pred.map (Formula.map_atom ~f:tester)),
        Formula.map_atom query ~f:tester )

  (* An equation defines its predicate once: a second definition of a name
     left which body the name meant to whichever lookup ran first, and the
     predicate sort environment refused the repeat with an uncaught
     exception. *)
  let check_defined_once preds =
    match List.find_a_dup preds ~compare:(fun (p1 : Pred.t) (p2 : Pred.t) ->
              String.compare (Ident.name_of_pvar p1.name) (Ident.name_of_pvar p2.name)) with
    | Some pred ->
        fail (sprintf "the predicate %s is defined twice"
                (Ident.name_of_pvar pred.name))
    | None -> ()

  (* Predicates and variables are two name spaces of this format: [G (H: int)]
     may apply a predicate [H] in its body, and [H (H + 1)] applies the
     predicate to the variable.  Type inference keeps one environment for both,
     in which a binder's sort shadows the predicate's, so such an application
     failed on the arity.  Contract: a binder (parameter or quantified
     variable) named like a predicate with parameters that is applied in its
     scope is renamed to a name spelled nowhere in the problem, which is an
     alpha-renaming of the variable alone (predicate applications are left as
     they are); every other binder is untouched, so the result differs from
     the input only where inference would have failed.  The walk covers what
     the grammar builds: atoms, connectives and binders. *)
  let rename_shadowing_binders preds query =
    let with_params =
      String.Set.of_list
        (List.filter_map preds ~f:(fun (pred : Pred.t) ->
             if List.is_empty pred.args then None
             else Some (Ident.name_of_pvar pred.name)))
    in
    if Set.is_empty with_params then (preds, query)
    else
      let taken =
        ref
          (List.fold preds
             ~init:(Set.Poly.map ~f:Ident.name_of_tvar
                      (Formula.names_spelled_in query))
             ~f:(fun names (pred : Pred.t) ->
               Set.union
                 (Set.add names (Ident.name_of_pvar pred.name))
                 (Set.union
                    (Set.Poly.map ~f:Ident.name_of_tvar
                       (Formula.names_spelled_in pred.body))
                    (Set.Poly.of_list
                       (List.map pred.args ~f:(fun (x, _) -> Ident.name_of_tvar x))))))
      in
      let fresh base =
        let rec draw k =
          let name = sprintf "%s_%d" base k in
          if Set.mem !taken name then draw (k + 1)
          else (taken := Set.add !taken name; name)
        in
        draw 1
      in
      (* the variable [x] renamed to [x'] at its free occurrences, which in a
         parsed formula are inside atoms' arguments; a predicate's name is
         another name space and is kept *)
      let rec rename_var x x' phi =
        match phi with
        | Formula.Atom (Atom.App (p, args, info), info') ->
            let ren = Map.Poly.singleton x x' in
            Formula.mk_atom ~info:info'
              (Atom.mk_app ~info p (List.map args ~f:(Term.rename ren)))
        | Formula.Atom _ -> phi
        | Formula.UnaryOp (op, phi1, info) ->
            Formula.mk_unop ~info op (rename_var x x' phi1)
        | Formula.BinaryOp (op, phi1, phi2, info) ->
            Formula.mk_binop ~info op (rename_var x x' phi1) (rename_var x x' phi2)
        | Formula.Bind (b, senv, body, info) ->
            if List.exists senv ~f:(fun (y, _) -> Ident.tvar_equal x y) then phi
            else Formula.mk_bind ~info b senv (rename_var x x' body)
        | Formula.LetRec _ | Formula.LetFormula _ -> phi
      in
      let applied name phi =
        Set.exists (Formula.pvs_of phi) ~f:(fun (Ident.Pvar p) -> String.equal p name)
      in
      let rename_senv senv body =
        List.fold_right senv ~init:([], body) ~f:(fun (x, s) (senv, body) ->
            let name = Ident.name_of_tvar x in
            if Set.mem with_params name && applied name body then
              let x' = Ident.Tvar (fresh name) in
              ((x', s) :: senv, rename_var x x' body)
            else ((x, s) :: senv, body))
      in
      let rec walk phi =
        match phi with
        | Formula.Atom _ -> phi
        | Formula.UnaryOp (op, phi1, info) -> Formula.mk_unop ~info op (walk phi1)
        | Formula.BinaryOp (op, phi1, phi2, info) ->
            Formula.mk_binop ~info op (walk phi1) (walk phi2)
        | Formula.Bind (b, senv, body, info) ->
            let senv, body = rename_senv senv (walk body) in
            Formula.mk_bind ~info b senv body
        | Formula.LetRec _ | Formula.LetFormula _ -> phi
      in
      ( List.map preds ~f:(fun (pred : Pred.t) ->
            let args, body = rename_senv pred.args (walk pred.body) in
            { pred with args; body }),
        walk query )

  let resolve_bare preds query =
    let nullary =
      String.Set.of_list
        (List.filter_map preds ~f:(fun (pred : Pred.t) ->
             if List.is_empty pred.args then Some (Ident.name_of_pvar pred.name)
             else None))
    in
    let params senv =
      String.Set.of_list (List.map senv ~f:(fun (x, _) -> Ident.name_of_tvar x))
    in
    check_bare ~nullary String.Set.empty query;
    List.iter preds ~f:(fun (pred : Pred.t) ->
        check_bare ~nullary (params pred.args) pred.body);
    (List.map preds ~f:(Pred.map unmark), unmark query)
%}

%token COLON INT BOOL REAL
%token LPAREN RPAREN EOF
%token <Ast.LogicOld.Predicate.fixpoint> EQFIX
%token <Ast.LogicOld.Formula.binder> BINDER
%token DOT SEMI
%token NOT
%token AND OR IMPLY IFF
%token MINUS ADD MULT
%token <Ast.Value.modulo> DIV MOD
%token RMINUS RADD RMULT RDIV RABS
%token <Ast.LogicOld.pred_sym> PREDSYM
%token <string> INTL
%token <string> REALL
%token TRUE FALSE TT FF
%token WHERE
%token <string> ID

%start toplevel
%type <Problem.t> toplevel
%start query
%type <Problem.query> query
%%

/*
;; forall x. F1 x
;; s.t.
;; F1 (x: int): bool =nu G1 x /\ (x <= 5 => F2 x) /\ (x <= 5 => F1 (x + 1)) /\ (x > 5 => F1 (x + 1));
;; F2 (x: int): bool =nu G2 x /\ (x <= 2 => F1 x) /\ (x > 2 => F2 (x-1));
;; G1 (x: int): bool =mu x >= 1 \/ (x <= 5 /\ G2 x) \/ (x <= 5 => G1 (x + 1)) /\ (x > 5 => G1 (x + 1));
;; G2 (x: int): bool =mu x >= 1 \/ (x <= 2 => G1 x) /\ (x > 2 => G2 (x-1));
*/

toplevel:
    query=Formula WHERE preds=Funs EOF {
      let preds, query = resolve_bare preds query in
      let preds, query = resolve_testers preds query in
      check_defined_once preds;
      let preds, query = rename_shadowing_binders preds query in
      Problem.make preds query
    }

query:
    fml=Formula EOF {
      (* no definitions: a bare identifier is no predicate here *)
      let _, fml = resolve_bare [] fml in
      let _, fml = resolve_testers [] fml in
      fml
    }

Funs:
    f=Fun SEMI preds=Funs { f :: preds }
  | f=Fun SEMI { [f] }

Fun:
    funname=ID bounds=Bounds COLON BOOL fix=EQFIX body=Formula {
      (* two parameters of one name leave the body's occurrences ambiguous,
         and type inference kept one of them, so the predicate silently lost
         an argument and every application of it failed on the arity *)
      (match List.find_a_dup bounds ~compare:(fun (x, _) (y, _) ->
                 Ident.tvar_compare x y) with
       | Some (x, _) ->
           fail (sprintf "the predicate %s has two parameters named %s"
                   funname (Ident.name_of_tvar x))
       | None -> ());
      Pred.make fix (Ident.Pvar funname) bounds body
    }

Formula:
    e=Expr { fml_of e }

/* not including LetRec */
Expr:
    e=ExprBinder { e }

ExprBinder:
    binder=BINDER bounds=Bounds DOT body=Formula {
      Fml (Formula.mk_bind binder bounds body)
    }
  | e=ExprIff { e }

ExprIff:
    left=ExprImply IFF right=ExprImply {
      Fml (Formula.mk_iff (fml_of left) (fml_of right))
    }
  | e=ExprImply { e }

ExprImply:
    left=ExprOr IMPLY right=ExprImply {
      Fml (Formula.mk_imply (fml_of left) (fml_of right))
    }
  | e=ExprOr { e }

ExprOr:
    left=ExprAnd OR right=ExprOr {
      Fml (Formula.mk_or (fml_of left) (fml_of right))
    }
  | e=ExprAnd { e }

ExprAnd:
    left=ExprNeg AND right=ExprAnd {
      Fml (Formula.mk_and (fml_of left) (fml_of right))
    }
  | e=ExprNeg { e }

ExprNeg:
    NOT e=ExprNegParen { Fml (Formula.mk_neg (fml_of e)) }
  | e=ExprAtom { e }

ExprNegParen:
    NOT e=ExprNegParen { Fml (Formula.mk_neg (fml_of e)) }
  | LPAREN e=Expr RPAREN { e }

ExprAtom:
    t1=T_num op=PREDSYM t2=T_num {
      Fml (Formula.mk_atom
             (Atom.mk_app (Predicate.mk_psym op) [tm_of t1; tm_of t2]))
    }
  | TRUE { Fml (Formula.mk_atom (Atom.mk_true ~info:Dummy ())) }
  | FALSE { Fml (Formula.mk_atom (Atom.mk_false ~info:Dummy ())) }
  | e=T_num { e }

AtomAppArgs:
    { [] }
  | arg=T_numAtom args=AtomAppArgs { tm_of arg :: args }

/* Arguments of a predicate application in formula position. Must not accept an
   empty argument list -- do not collapse this into AtomAppArgs: a bare `ID` in
   formula position is read as a term and classified afterwards (see the
   header), and an `ID` followed by an empty argument list here would make the
   parser choose between the two readings at the next token. A nullary
   predicate is applied as `P ()` or as the bare `P`. */
AtomAppArgs1:
    LPAREN RPAREN { [] }
  | arg=T_numAtom args=AtomAppArgs { tm_of arg :: args }


/* Ast.LogicOld.Term.t, read as an expression: a level without its operator
   passes the phrase beneath it on unchanged, so a parenthesised formula can
   reach formula position through them; an operator classifies its operands
   as terms. */

T_num:
    e=T_numAddSub { e }

T_numAddSub:
    e=T_numMulDivMod { e }
  | t1=T_numAddSub ADD t2=T_numMulDivMod { Tm (T_num.mk_nadd (tm_of t1) (tm_of t2), None) }
  | t1=T_numAddSub MINUS t2=T_numMulDivMod { Tm (T_num.mk_nsub (tm_of t1) (tm_of t2), None) }
  | t1=T_numAddSub RADD t2=T_numMulDivMod { Tm (T_real.mk_radd (tm_of t1) (tm_of t2), None) }
  | t1=T_numAddSub RMINUS t2=T_numMulDivMod { Tm (T_real.mk_rsub (tm_of t1) (tm_of t2), None) }

T_numMulDivMod:
    e=T_numNeg { e }
  | t1=T_numMulDivMod MULT t2=T_numNeg { Tm (T_num.mk_nmul (tm_of t1) (tm_of t2), None) }
  | t1=T_numMulDivMod RMULT t2=T_numNeg { Tm (T_real.mk_rmul (tm_of t1) (tm_of t2), None) }
  | t1=T_numMulDivMod RDIV t2=T_numNeg { Tm (T_real.mk_rdiv (tm_of t1) (tm_of t2), None) }
  | t1=T_numMulDivMod m=DIV t2=T_numNeg { Tm (T_num.mk_ndiv m (tm_of t1) (tm_of t2), None) }
  | t1=T_numMulDivMod m=MOD t2=T_numNeg { Tm (T_num.mk_nrem m (tm_of t1) (tm_of t2), None) }

T_numNeg:
    e=T_numApp { e }
  | MINUS t=T_numNeg { Tm (T_num.mk_nneg (tm_of t), None) }
  | RMINUS t=T_numNeg { Tm (T_real.mk_rneg (tm_of t), None) }
  | RABS t=T_numNeg { Tm (T_real.mk_rabs (tm_of t), None) }

/* An application binds tighter than every operator, so [hd l >= 1] and
   [p = cons x l] read as the printer writes them.  It is a predicate
   application, or a constructor or selector application when the datatype
   environment declares the name; which one is classified where the phrase is
   used (see the header), so a predicate application standing as an operand is
   refused there as a formula where a term is expected. */
T_numApp:
    funname=ID args=AtomAppArgs1 {
      match datatype_app funname args with
      | Some t -> Tm (t, None)
      | None ->
      Fml (Formula.mk_atom
             (Atom.mk_pvar_app (Ident.Pvar funname)
                (List.map args ~f:Term.sort_of) args))
    }
  | e=T_numAtom { e }

T_numAtom:
    LPAREN e=Expr RPAREN { e }
  | n=INTL { Tm (T_int.mk_int (Z.of_string n), None) }
  | n=REALL { Tm (T_real.mk_real (Q.of_string n), None) }
  | TT { Tm (T_bool.mk_true (), None) }
  | FF { Tm (T_bool.mk_false (), None) }
  | varname=ID {
      match datatype_const varname with
      | Some t -> Tm (t, None)
      | None ->
      Tm (Term.mk_var (Ident.Tvar varname) @@ Sort.mk_fresh_svar (), Some varname)
    }

/* Ast.LogicOld.Sort.t */
Sort:
    INT { T_int.SInt }
  | BOOL { T_bool.SBool }
  | REAL { T_real.SReal }
  | name=ID { datatype_sort name }

/* Bounds */
Bounds:
    { [] }
  | LPAREN varname=ID COLON sort=Sort RPAREN bounds=Bounds {
    (* A name the datatype environment declares is that constructor or
       selector at every occurrence (the header's contract), so as a binder
       it would bind nothing: [forall (nil: L). is_nil nil] read as the
       constant's test, which holds, where every list was meant.  Refused,
       as SMT-LIB's shadowing reading is not what the actions implement. *)
    if Option.is_some (datatype_func varname) then
      fail (sprintf "%s is a datatype constructor or selector and cannot \
                     be bound as a variable" varname);
    (Ident.Tvar varname, sort) :: bounds
  }
