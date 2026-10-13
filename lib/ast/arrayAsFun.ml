(* A formula that reads its arrays only through [select], asked with each array
   an uninterpreted function.

   WHY.  A counterexample query for a candidate that states a universal over
   array cells -- [forall ka kb. ... a[ka] ... b[kb] ...] asserted as a
   premise, with reads of two free arrays -- asks the solver for arrays meeting
   a universal.  Z3 (4.15.2) leaves such queries undecided at a 10 s budget,
   where the same question with [a] and [b] declared as functions [Int -> Int]
   is answered in a tenth of a second: model-based quantifier instantiation
   builds a finite function graph for a function symbol directly, while for an
   array it has to go through the array axioms and extensionality.

   THE FRAGMENT.  [translate] succeeds only when all of the following hold, and
   returns [Error reason] otherwise, leaving the caller to ask the formula as
   it is:
   - after the read-over-write rewriting below, every array-sorted term is a
     FULL read chain [select(...select(a, i1)..., in)] whose base [a] is a free
     variable of array sort (a curried array is read at all its indices);
   - so no [store] survives, no array equality, no array-valued [ite] outside
     a read, no array literal ([const], [lambda]), no array passed to a
     function or a constructor, and no array inside another sort (a tuple of
     arrays, a datatype with an array field);
   - no binder binds an array-sorted variable ([forall], [exists], [let]);
   - no recursive definition ([letrec]) and no fixpoint predicate occurs.
   A free array variable may be read under a binder: its function symbol is
   global, so reading it there is what reading the array there means.

   READ OVER WRITE.  Before the test, a read of a write and a read of an
   array-valued [ite] are pushed down:
     select(store(a, j, v), t) = ite(t = j, v, select(a, t))
     select(ite(c, x, y), t)   = ite(c, select(x, t), select(y, t))
   Both are identities in every model of the array theory, so the rewritten
   formula is equivalent to the input; they widen the fragment to step clauses
   that write an array and only read the result.

   THE TRANSLATION.  Each array variable [a : Array S1 (... (Array Sn E))] is
   replaced by a fresh function symbol [f_a : S1 x ... x Sn -> E], every full
   read chain of [a] at [i1 .. in] by [f_a(i1, .., in)].

   THE CLAIM: the input and its translation are EQUISATISFIABLE, and a model of
   the translation reads back to a model of the input.
   - An array model gives a function model: interpret [f_a] as
     [x1..xn |-> select(..select(a, x1).., xn)].  Since the formula reads [a]
     only through full chains, every subformula has the same value in both.
     So [unsat] of the translation implies [unsat] of the input, in every
     model of the array theory.
   - A function model gives an array model in the standard array structure,
     where the arrays of index sort [S] and element sort [E] are all functions
     from [S] to [E]: take [a] to be the function [f_a] denotes (curried).  So
     [sat] of the translation yields a model of the input, and [read_back]
     writes the function down as an array term that denotes exactly it.
   A counterexample to a candidate is a model of the negated clause, and one
   model suffices to refute a candidate: the candidate must hold in every model
   of the theory, so a countermodel in the standard structure is enough.

   CONTRACT.  [translate] raises nothing but asynchronous exceptions; it draws
   fresh names (one function symbol per array variable) only on a formula that
   has an array variable and lies in the fragment.  A formula with no array
   variable is [Error "no array"] with nothing drawn. *)

open Core
open Common.Ext
open LogicOld

exception Outside of string

type binding = {
  arr_var : Ident.tvar;
  arr_sort : Sort.t;
  fun_var : Ident.tvar;
  index_sorts : Sort.t list;
  elem_sort : Sort.t;
}

type t = {
  formula : Formula.t;  (** equisatisfiable with the input *)
  bindings : binding list;  (** one per free array variable *)
}

let rec uncurry = function
  | T_array.SArray (si, se) ->
      let is, e = uncurry se in
      (si :: is, e)
  | s -> ([], s)

(* Does [sort] contain an array, at the top or inside a tuple, a sequence, a
   reference or a datatype's constructor arguments?  [Term.sorts_of_sort] is
   not the test: it lists the index and element sorts of an array but not the
   array sort itself. *)
let has_array_sort sort =
  let rec go visited = function
    | T_array.SArray _ -> true
    | T_tuple.STuple sorts -> List.exists sorts ~f:(go visited)
    | T_seq.SSeq se -> go visited se
    | T_ref.SRef s -> go visited s
    | T_dt.SDT dt as s ->
        if Set.mem visited s then false
        else
          let visited = Set.add visited s in
          List.exists (Datatype.conses_of dt) ~f:(fun cons ->
              List.exists (Datatype.sorts_of_cons dt cons) ~f:(go visited))
    | _ -> false
  in
  go Set.Poly.empty sort

(* ---- read over write ---- *)

let rec row_term (t : Term.t) : Term.t =
  match t with
  | Term.Var _ -> t
  | Term.FunApp (T_array.ASelect (si, se), [ a; i ], info) ->
      push_select si se (row_term a) (row_term i) info
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      Term.mk_fsym_app ~info (T_bool.Formula (row_formula phi)) []
  | Term.FunApp (sym, args, info) ->
      Term.mk_fsym_app ~info sym (List.map args ~f:row_term)
  | Term.LetTerm (x, s, d, b, info) ->
      Term.mk_let_term ~info x s (row_term d) (row_term b)

and push_select si se a i info =
  match a with
  | Term.FunApp (T_array.AStore _, [ a'; j; v ], _) ->
      T_bool.ifte (Formula.eq i j) v (push_select si se a' i info)
  | Term.FunApp (T_bool.IfThenElse, [ c; x; y ], _) ->
      T_bool.mk_if_then_else c
        (push_select si se x i info)
        (push_select si se y i info)
  | _ -> Term.mk_fsym_app ~info (T_array.ASelect (si, se)) [ a; i ]

and row_formula (phi : Formula.t) : Formula.t =
  match phi with
  | Formula.Atom (Atom.App (p, args, ai), info) ->
      Formula.mk_atom ~info (Atom.mk_app ~info:ai p (List.map args ~f:row_term))
  | Formula.Atom _ -> phi
  | Formula.UnaryOp (op, p, info) -> Formula.mk_unop ~info op (row_formula p)
  | Formula.BinaryOp (op, p, q, info) ->
      Formula.mk_binop ~info op (row_formula p) (row_formula q)
  | Formula.Bind (b, senv, p, info) ->
      Formula.mk_bind ~info b senv (row_formula p)
  | Formula.LetRec _ -> raise (Outside "a recursive definition")
  | Formula.LetFormula (x, s, d, b, info) ->
      Formula.mk_let_formula ~info x s (row_term d) (row_formula b)

(* ---- the fragment test and the replacement, in one pass ---- *)

type state = {
  vars : (Ident.tvar, binding) Hashtbl.Poly.t;
  arr_memo : (Sort.t, bool) Hashtbl.Poly.t;
}

let arrayish st sort =
  Hashtbl.Poly.find_or_add st.arr_memo sort ~default:(fun () ->
      has_array_sort sort)

let binding_of st x sort =
  match Hashtbl.Poly.find st.vars x with
  | Some b ->
      if Stdlib.(b.arr_sort <> sort) then
        raise (Outside "one array name at two sorts")
      else b
  | None ->
      let index_sorts, elem_sort = uncurry sort in
      if arrayish st elem_sort then
        raise (Outside "an array element sort containing an array");
      let b =
        {
          arr_var = x;
          arr_sort = sort;
          fun_var = Ident.mk_fresh_tvar ();
          index_sorts;
          elem_sort;
        }
      in
      Hashtbl.Poly.set st.vars ~key:x ~data:b;
      b

(* the base and the indices of a read chain, outermost index last *)
let rec chain (t : Term.t) acc =
  match t with
  | Term.FunApp (T_array.ASelect _, [ a; i ], _) -> chain a (i :: acc)
  | _ -> (t, acc)

let rec tr_term st (t : Term.t) : Term.t =
  match t with
  | Term.Var (_, s, _) ->
      if arrayish st s then raise (Outside "an array outside a read") else t
  | Term.FunApp (T_array.ASelect _, [ _; _ ], _) -> (
      match chain t [] with
      | Term.Var (x, s, _), idxs when T_array.is_sarray s ->
          let b = binding_of st x s in
          if List.length idxs <> List.length b.index_sorts then
            raise (Outside "a partial read of a curried array");
          Term.mk_fvar_app b.fun_var b.index_sorts b.elem_sort
            (List.map idxs ~f:(tr_term st))
      | _ -> raise (Outside "a read of an array that is not a variable"))
  | Term.FunApp ((T_array.AStore _ | T_array.AConst _ | T_array.ALambda _), _, _)
    ->
      raise (Outside "an array write or literal")
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      Term.mk_fsym_app ~info (T_bool.Formula (tr_formula st phi)) []
  | Term.FunApp (sym, args, info) ->
      let s =
        try Term.sort_of t
        with exn_ when not (Common.Timer.is_async exn_) ->
          raise (Outside "a term whose sort is not known")
      in
      if arrayish st s then
        raise (Outside "an array-valued term outside a read");
      Term.mk_fsym_app ~info sym (List.map args ~f:(tr_term st))
  | Term.LetTerm (x, s, d, b, info) ->
      if arrayish st s then raise (Outside "an array bound by let");
      Term.mk_let_term ~info x s (tr_term st d) (tr_term st b)

and tr_formula st (phi : Formula.t) : Formula.t =
  match phi with
  | Formula.Atom (Atom.App ((Predicate.Psym _ as p), args, ai), info) ->
      Formula.mk_atom ~info
        (Atom.mk_app ~info:ai p (List.map args ~f:(tr_term st)))
  | Formula.Atom (Atom.App _, _) ->
      raise (Outside "a predicate variable or a fixpoint")
  | Formula.Atom _ -> phi
  | Formula.UnaryOp (op, p, info) -> Formula.mk_unop ~info op (tr_formula st p)
  | Formula.BinaryOp (op, p, q, info) ->
      Formula.mk_binop ~info op (tr_formula st p) (tr_formula st q)
  | Formula.Bind (b, senv, p, info) ->
      if List.exists senv ~f:(fun (_, s) -> arrayish st s) then
        raise (Outside "an array bound by a quantifier");
      Formula.mk_bind ~info b senv (tr_formula st p)
  | Formula.LetRec _ -> raise (Outside "a recursive definition")
  | Formula.LetFormula (x, s, d, b, info) ->
      if arrayish st s then raise (Outside "an array bound by let");
      Formula.mk_let_formula ~info x s (tr_term st d) (tr_formula st b)

let mentions_array phi =
  Set.exists (Formula.term_sort_env_of phi) ~f:(fun (_, s) -> has_array_sort s)

let translate (phi : Formula.t) : (t, string) Result.t =
  if not (mentions_array phi) then Error "no array"
  else
    let st =
      { vars = Hashtbl.Poly.create (); arr_memo = Hashtbl.Poly.create () }
    in
    match
      try Ok (tr_formula st (row_formula phi)) with
      | Outside reason -> Error reason
      | exn_ when not (Common.Timer.is_async exn_) ->
          Error ("not translatable: " ^ Exn.to_string exn_)
    with
    | Error _ as e -> e
    | Ok _ when Hashtbl.Poly.is_empty st.vars -> Error "no array read"
    | Ok phi' ->
        let bindings =
          List.sort (Hashtbl.Poly.data st.vars) ~compare:(fun a b ->
              String.compare
                (Ident.name_of_tvar a.arr_var)
                (Ident.name_of_tvar b.arr_var))
        in
        Ok { formula = phi'; bindings }

(* ---- reading a function model back as arrays ---- *)

(** The array term denoting the function [fv] gives, curried at [index_sorts]. A
    one-dimensional function whose default is closed is written the way a solver
    writes an array, as writes over a constant array -- the entries are read in
    order and the first match wins, so the first entry is the outermost write.
    Any other is written as nested [lambda]s over the parameters, whose body is
    the entries' [ite] chain ending in the default: a default that depends on
    its argument (Z3 writes, for instance, [ite(1 <= x, 5, 0)]) has no
    store-over-constant form. The parameters are the value's own fresh
    variables, so the binders are fresh. Either term agrees with [fv] at every
    index, not only at the ones the formula reads. *)
let array_of_fun_value ~index_sorts ~elem_sort (fv : FunValue.t) : Term.t =
  match (index_sorts, fv.params) with
  | [ si ], [ _ ]
    when Set.is_empty (Term.fvs_of fv.default)
         && List.for_all fv.entries ~f:(fun (args, _) -> List.length args = 1)
    ->
      List.fold_right fv.entries
        ~init:(T_array.mk_const_array si elem_sort fv.default)
        ~f:(fun (args, v) acc ->
          T_array.mk_store si elem_sort acc (List.hd_exn args) v)
  | _ ->
      let body =
        FunValue.apply fv
          (List.map fv.params ~f:(fun (x, s) -> Term.mk_var x s))
      in
      let rec wrap = function
        | [] -> (body, elem_sort)
        | (x, s) :: rest ->
            let inner, inner_sort = wrap rest in
            ( T_array.mk_lambda (x, s) inner_sort inner,
              T_array.SArray (s, inner_sort) )
      in
      fst (wrap fv.params)

(** A model of the translation read back as a model of the input: every array
    variable is given the array its function denotes, the function names are not
    listed, and every other entry is kept. [None] when some function has no
    value in [fun_values] -- a value the reader could not decode is dropped
    there, and treating it as "any array" would turn a model that constrains the
    array into one that does not -- or a value has the wrong number of
    parameters. Then the caller asks the untranslated query. *)
let read_back (tr : t) (model : model)
    (fun_values : (sort_bind * FunValue.t) list) : model option =
  let values =
    List.map tr.bindings ~f:(fun b ->
        match
          List.find_map fun_values ~f:(fun ((f, _), fv) ->
              if Stdlib.(f = b.fun_var) then Some fv else None)
        with
        | Some fv when List.length fv.params = List.length b.index_sorts ->
            Some
              ( (b.arr_var, b.arr_sort),
                Some
                  (array_of_fun_value ~index_sorts:b.index_sorts
                     ~elem_sort:b.elem_sort fv) )
        | _ -> None)
  in
  match Option.all values with
  | None -> None
  | Some values ->
      let own =
        Set.Poly.of_list @@ List.map tr.bindings ~f:(fun b -> b.fun_var)
      in
      let rest =
        List.filter model ~f:(fun ((x, _), _) -> not (Set.mem own x))
      in
      Some (rest @ values)
