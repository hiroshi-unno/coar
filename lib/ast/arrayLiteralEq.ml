(* Equalities of arrays, sequences and records rewritten into equalities of
   their elements or components, each rewrite an equivalence in every model of
   the theories involved (array extensionality, sequence extensionality over
   valid indices, the datatype and tuple axioms), so a question rewritten
   with them is the same question.

   They exist for a solver that answers such an equality wrongly when it is
   asked as written -- an array literal over a finite index sort, or an
   array, sequence or record holding an array [lambda] -- while it answers the
   element-wise form correctly; which solver and which version needs which
   rewrite is the solver interface's decision, not this module's.  Nothing
   here asks a solver. *)

open Core
open Common.Ext
open LogicOld

(* The elements of a finite index sort, as ground terms: [Bool], and a datatype
   every constructor of which has only fields that are themselves such sorts.
   The walk is depth-bounded, which is what makes a recursive datatype answer
   [None] rather than diverge, and the element count is bounded, since past it
   the rewrite hands the solver more reads than the literal it replaces. *)
let elements_of_finite_index =
  let max_elements = 64 in
  let max_depth = 4 in
  let rec elements depth srt =
    if depth > max_depth then None
    else
      match srt with
      | T_bool.SBool -> Some [ T_bool.mk_true (); T_bool.mk_false () ]
      | T_dt.SDT dt when not (List.is_empty (Datatype.conses_of dt)) ->
          let per_cons c =
            Option.bind
              (Option.all
              @@ List.map (Datatype.sorts_of_cons dt c)
                   ~f:(elements (depth + 1)))
              ~f:(fun choices ->
                (* the size is checked before the product is built *)
                let size =
                  List.fold choices ~init:1 ~f:(fun acc es ->
                      if acc > max_elements then acc else acc * List.length es)
                in
                if size > max_elements then None
                else
                  Some
                    (List.map
                       (List.fold_right choices ~init:[ [] ] ~f:(fun es acc ->
                            List.concat_map es ~f:(fun e ->
                                List.map acc ~f:(fun tl -> e :: tl))))
                       ~f:(fun args ->
                         T_dt.mk_cons dt (Datatype.name_of_cons c) args)))
          in
          Option.bind
            (Option.all @@ List.map (Datatype.conses_of dt) ~f:per_cons)
            ~f:(fun ls ->
              let es = List.concat ls in
              if List.length es <= max_elements then Some es else None)
      | _ -> None
  in
  elements 0

(* [Some b] when two terms built only from constructors and boolean constants
   are ([b = true]) or are not ([b = false]) the same value; [None] when either
   is anything else, which leaves the question to the solver *)
let rec ground_value_equal t1 t2 =
  match (t1, t2) with
  | ( Term.FunApp (T_dt.DTCons (n1, _, _), args1, _),
      Term.FunApp (T_dt.DTCons (n2, _, _), args2, _) ) ->
      if not (String.equal n1 n2) then Some false
      else if List.length args1 <> List.length args2 then None
      else
        List.fold2_exn args1 args2 ~init:(Some true) ~f:(fun acc a b ->
            match acc with
            | Some true -> ground_value_equal a b
            | other -> other)
  | _ ->
      if (T_bool.is_true t1 || T_bool.is_false t1)
         && (T_bool.is_true t2 || T_bool.is_false t2)
      then Some (Bool.equal (T_bool.is_true t1) (T_bool.is_true t2))
      else None

let array_sorts_of_literal = function
  | Term.FunApp (T_array.AConst (si, se), _, _) -> Some (si, se)
  | Term.FunApp (T_array.AStore (si, se), _, _) -> Some (si, se)
  | _ -> None

(* whether [t1 = t2] is an equality the expansion below rewrites: one side an
   array literal whose index sort is finite *)
let is_finite_array_literal_eq t1 t2 =
  match
    match array_sorts_of_literal t1 with
    | Some p -> Some p
    | None -> array_sorts_of_literal t2
  with
  | Some (si, _) -> (
      match elements_of_finite_index si with Some (_ :: _) -> true | _ -> false)
  | None -> false

(* A read of a literal at a constructor of a finite index sort, computed rather
   than left to the solver: [select (const v) e] is [v], and
   [select (store a i v) e] is [v] when [i] and [e] are the same ground value
   and [select a e] when they are different ones.  Anything else
   stays a [select].

   The computing is what makes the expansion below complete.  A curried
   universal function over the finite sort is an array whose VALUE is again an
   array, so reading an equality of two such literals at each element leaves
   equalities between the values, and those are literals of array sort once
   more -- the very equality the solver answers wrongly, one level down.  Left
   as [select (const (store ...)) e] the value is not syntactically a literal,
   the expansion did not look inside it, and the solver was handed
   [const (store (const (const true)) b0 (const false)) =
    const (const (const false))] over two two-element sorts, answered [sat], and
   a conflict between two examples that do not unify refuted a satisfiable
   instance. *)
let rec read_finite_literal si se t e =
  match t with
  | Term.FunApp (T_array.AConst _, [ v ], _) -> v
  | Term.FunApp (T_array.AStore _, [ a; i; v ], _) -> (
      match ground_value_equal i e with
      | Some true -> v
      | Some false -> read_finite_literal si se a e
      | None -> T_array.mk_select si se t e)
  | _ -> T_array.mk_select si se t e

(* Recursive: an element read off the equality is again an equality, and when
   its sides are array literals over a finite index it is expanded in turn,
   down to the first element sort that is not such an array.  It terminates
   because each level strips one array constructor from the sort. *)
let rec expand_finite_array_eq_atom atom =
  match atom with
  | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) -> (
      match
        match array_sorts_of_literal t1 with
        | Some p -> Some p
        | None -> array_sorts_of_literal t2
      with
      | Some (si, se) -> (
          match elements_of_finite_index si with
          | Some (_ :: _ as es) ->
              Formula.and_of
              @@ List.map es ~f:(fun e ->
                     expand_finite_array_eq_atom
                     @@ T_bool.mk_eq
                          (read_finite_literal si se t1 e)
                          (read_finite_literal si se t2 e))
          | _ -> Formula.mk_atom atom)
      | None -> Formula.mk_atom atom)
  | _ -> Formula.mk_atom atom

(* Every equality of [phi] one side of which is an array literal over a
   finite index sort, replaced by the conjunction of its reads at every
   element ([expand_finite_array_eq_atom]); everything else as it is.
   Equivalent in every model of the array theory. *)
let expand_finite_array_eqs phi =
  Formula.fold phi
    ~f:
      (object
         method fatom atom = expand_finite_array_eq_atom atom
         method fand p1 p2 = Formula.mk_and p1 p2
         method for_ p1 p2 = Formula.mk_or p1 p2
         method fnot p1 = Formula.mk_neg p1
         method fimply p1 p2 = Formula.mk_imply p1 p2
         method fiff p1 p2 = Formula.mk_iff p1 p2
         method fxor p1 p2 = Formula.mk_xor p1 p2
         method fletrec funcs p1 = Formula.mk_letrec funcs p1
         method flet var sort def body = Formula.mk_let_formula var sort def body
         method fbind binder senv p1 = Formula.mk_bind binder senv p1
      end)

let rec term_contains_lambda (t : Term.t) =
  match t with
  | Term.Var _ -> false
  | Term.FunApp (T_array.ALambda _, _, _) -> true
  | Term.FunApp (_, args, _) -> List.exists args ~f:term_contains_lambda
  | Term.LetTerm (_, _, def, body, _) ->
      term_contains_lambda def || term_contains_lambda body

(* [t[x]], computed through [store], safe [lambda] beta reduction and
   constant arrays; a [select] anywhere else. Unsupported substitution scope
   retains the original read instead of renaming an independent head. *)
let rec read_array_at si se (t : Term.t) x =
  match t with
  | Term.FunApp (T_array.AConst _, [ v ], _) -> v
  | Term.FunApp (T_array.AStore _, [ a; i; v ], _) ->
      T_bool.ifte (Formula.eq i x) v (read_array_at si se a x)
  | Term.FunApp (T_array.ALambda _, _, _) -> (
      match T_array.eval_select t x with
      | Some value -> value
      | None -> T_array.mk_select si se t x)
  | _ -> T_array.mk_select si se t x

(* The binder is inserted around both terms, so its spelling must avoid
   every input name, including bound variables and callable heads. Keep an
   ordinary unprefixed first draw when it is already fresh. *)
let fresh_index t1 t2 =
  let taken = Formula.names_spelled_in (Formula.eq t1 t2) in
  let rec draw () =
    let x = Ident.mk_fresh_tvar () in
    if Set.mem taken x then draw () else x
  in
  draw ()

(* [t1 = t2] for two array terms, as [forall x. t1[x] = t2[x]] *)
let extensional_array_eq t1 t2 =
  match Term.sort_of t1 with
  | T_array.SArray (si, se) ->
      let x = fresh_index t1 t2 in
      let xv = Term.mk_var x si in
      Formula.mk_forall [ (x, si) ]
        (Formula.eq (read_array_at si se t1 xv) (read_array_at si se t2 xv))
  | _ -> Formula.eq t1 t2

(* Sequence extensionality needs both equal lengths and element equality at
   valid indices. In particular, no constraint may be imposed on [seq.nth]
   outside that range. The reads below are used ONLY under that guard (and
   the equal-length conjunct), so a singleton's read is its element and a
   concatenation's read can descend into the selected, valid sub-index.
   Exposing these elements also lets the array/datatype rewrites below see
   a [lambda] nested inside a singleton rather than handing it to the solver. *)
let rec lambda_sequence_length se = function
  | Term.FunApp (T_seq.SqEmpty _, [], _) -> T_int.mk_int Z.zero
  | Term.FunApp (T_seq.SqUnit _, [ _ ], _) -> T_int.mk_int Z.one
  | Term.FunApp (T_seq.SqConcat _, [ a; b ], _) ->
      T_int.mk_add (lambda_sequence_length se a) (lambda_sequence_length se b)
  | t -> T_seq.mk_len se t

let rec read_sequence_at_valid_index se t i =
  match t with
  | Term.FunApp (T_seq.SqUnit _, [ v ], _) -> v
  | Term.FunApp (T_seq.SqConcat _, [ a; b ], _) ->
      let len = lambda_sequence_length se a in
      T_bool.ifte (Formula.lt i len)
        (read_sequence_at_valid_index se a i)
        (read_sequence_at_valid_index se b (T_int.mk_sub i len))
  | _ -> T_seq.mk_nth se t i

let extensional_sequence_eq t1 t2 =
  match (t1, t2) with
  | ( Term.FunApp (T_seq.SqUnit _, [ a ], _),
      Term.FunApp (T_seq.SqUnit _, [ b ], _) ) ->
      Formula.eq a b
  | Term.FunApp (T_seq.SqUnit se, [ a ], _), t
  | t, Term.FunApp (T_seq.SqUnit se, [ a ], _) ->
      (* The singleton case needs no universal index; this also avoids
         nested index quantifiers for sequences of sequences. *)
      Formula.and_of
        [
          Formula.eq (lambda_sequence_length se t) (T_int.mk_int Z.one);
          Formula.eq (read_sequence_at_valid_index se t (T_int.mk_int Z.zero)) a;
        ]
  | _ -> (
      match Term.sort_of t1 with
      | T_seq.SSeq se ->
          let i = fresh_index t1 t2 in
          let iv = Term.mk_var i T_int.SInt in
          let len1 = lambda_sequence_length se t1 in
          let len2 = lambda_sequence_length se t2 in
          Formula.and_of
            [
              Formula.eq len1 len2;
              Formula.mk_forall
                [ (i, T_int.SInt) ]
                (Formula.mk_imply
                   (Formula.and_of
                      [
                        Formula.leq (T_int.mk_int Z.zero) iv; Formula.lt iv len1;
                      ])
                   (Formula.eq
                      (read_sequence_at_valid_index se t1 iv)
                      (read_sequence_at_valid_index se t2 iv)));
            ]
      | _ -> Formula.eq t1 t2)

(* [t1 = t2] for two terms of a datatype or tuple sort one of which contains a
   [lambda], as an equivalent formula whose equalities are between the
   components; [None] where no rule below applies.

   The rules are the datatype and tuple axioms, exact in every model of the
   theory (codatatypes included): [C(u1..un) = C(v1..vn)] iff every [ui = vi];
   two different constructors are never equal; [t = C(u1..un)] iff [t] is
   built by [C] and its [i]-th selector is [ui]; a tuple equals [(u1..un)] iff
   its projections are the [ui]; and an [ite] side is split by its condition.
   Each rule removes the top constructor or [ite] of one side, the side whose
   subterms the new equalities hold, while the other side is at most wrapped
   in a selector, which no rule matches; so the rewriting ends. *)
let component_lambda_eq t1 t2 =
  let eqs ts1 ts2 = Formula.and_of (List.map2_exn ts1 ts2 ~f:Formula.eq) in
  match (t1, t2) with
  | ( Term.FunApp (T_dt.DTCons (n1, _, _), ts1, _),
      Term.FunApp (T_dt.DTCons (n2, _, _), ts2, _) ) ->
      if String.(n1 = n2) && List.length ts1 = List.length ts2 then
        Some (eqs ts1 ts2)
      else Some (Formula.mk_false ())
  | Term.FunApp (T_dt.DTCons (n, _, dt), ts, _), t
  | t, Term.FunApp (T_dt.DTCons (n, _, dt), ts, _) ->
      Some
        (Formula.and_of
           (Formula.mk_atom (T_dt.mk_is_cons dt n t)
           :: List.mapi ts ~f:(fun i u ->
                  Formula.eq (T_dt.mk_sel_by_cons dt n i t) u)))
  | ( Term.FunApp (T_tuple.TupleCons _, ts1, _),
      Term.FunApp (T_tuple.TupleCons _, ts2, _) )
    when List.length ts1 = List.length ts2 ->
      Some (eqs ts1 ts2)
  | Term.FunApp (T_tuple.TupleCons sorts, ts, _), t
  | t, Term.FunApp (T_tuple.TupleCons sorts, ts, _) ->
      Some
        (Formula.and_of
           (List.mapi ts ~f:(fun i u ->
                Formula.eq (T_tuple.mk_tuple_sel sorts t i) u)))
  | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _), t
  | t, Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) ->
      let c = Formula.of_bool_term c in
      Some
        (Formula.or_of
           [
             Formula.and_of [ c; Formula.eq a t ];
             Formula.and_of [ Formula.mk_neg c; Formula.eq b t ];
           ])
  | _ -> None
