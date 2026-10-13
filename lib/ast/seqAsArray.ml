(* A sequence formula without concatenation, asked as arrays plus a length.

   WHY.  SMT-LIB sequences have no write, so [seq.store] reaches the solver as
   [ite(0 <= i < len s, extract(s,0,i) ++ unit v ++ extract(s,i+1,..), s)].  A
   query that mentions only reads, lengths and writes therefore arrives with
   concatenation and extraction, and Z3 (4.15.2) decides nothing about
   [seq.nth] over that: the six-line frame fact
   [t = store s i 0 /\ 0 <= j < len s /\ j != i => nth t j = nth s j] times out
   at 20 s, where cvc5 answers it in 0.2 s.  The same question over an array
   and an integer is quantifier-free read-over-write arithmetic, which the
   array solver decides at once.

   THE FRAGMENT.  A formula is translated only when all of the following hold,
   and [translate] returns [Error reason] otherwise, leaving the caller to ask
   the formula as it is:
   - sequence terms are built from free sequence variables, [seq.empty],
     [seq.unit e], [seq.store u i e] and [ite(c, u, w)] -- no [seq.++], no
     [seq.extract], no other sequence operator, no [let];
   - a sequence term occurs only as the argument of [seq.nth] or [seq.len], as
     a side of an equality or disequality, or inside another sequence term;
   - no quantifier binds a sequence, and no sort other than [Seq T] contains
     one (no tuple of sequences, no sequence of sequences);
   - EVERY read [seq.nth u t] is range-guarded: the literals the read's position
     makes true entail [0 <= t /\ t < len u] (see GUARDS below).

   THE TRANSLATION.  A sequence variable [s : Seq T] becomes an array
   [a_s : Array Int T] and a length [n_s : Int], with [n_s >= 0] conjoined:
     nth u t           |-> select a_u t
     len u             |-> n_u
     store u i e       |-> (ite(0 <= i < n_u, store a_u i e, a_u), n_u)
     unit e            |-> (const e, 1)
     empty             |-> (a fresh array, 0)
     ite(c, u, w)      |-> (ite(c, a_u, a_w), ite(c, n_u, n_w))
     u = w             |-> n_u = n_w /\ forall k. 0 <= k < n_u => a_u[k] = a_w[k]
   and every other symbol is kept.

   THE CLAIM.  For a formula in the fragment, the input and its translation
   are EQUISATISFIABLE, and a model of the translation reads back to a model of
   the input (each sequence the word a_s[0..n_s-1]).  So a validity question
   asked as the unsatisfiability of the translated negation is the same
   question.  The proof relates a sequence model and an array model when they
   share the element and integer domains and every sequence term's length, and
   its array agrees with its word on [0, length); nothing is required out of
   range.  By induction, under related models every formula of the fragment
   has one truth value at every valuation satisfying its guard literals: a
   guard literal reads no sequence element, so it has one value in both; an
   in-range read has one value in both; and equality of sequences is equality
   of length plus agreement in range, which is what the translation says.
   Every sequence model has a related array model and conversely, so the two
   are equisatisfiable.  (The proof is by hand and is not machine-checked.)

   WHY THE GUARD IS NOT OPTIONAL.  An out-of-range [seq.nth] is open in the
   sequence theory but it is a FUNCTION of the sequence's value, so two
   sequences equal in range read alike everywhere; two arrays equal in range
   need not.  [len s = 1 /\ len t = 1 /\ nth s 0 = nth t 0 /\ nth s 5 != nth t 5]
   is unsatisfiable over sequences and its unguarded image is satisfiable.  With
   the store written as an array store, an unguarded read also invents
   constraints: over sequences the reads of [store s 0 v] out of range are
   unrelated to those of [s], and over arrays they coincide.  Both would turn a
   satisfiable query unsatisfiable, that is an invalid clause valid, so an
   unguarded read refuses the translation outright.

   GUARDS.  After negation normal form, a subformula of a conjunction may
   assume what its sibling conjuncts say, and a subformula of a disjunction
   what the negations of its sibling disjuncts say; the same holds inside a
   formula embedded in a term, and a branch of an [ite] may assume its
   condition (the else branch its negation).  What a sibling "says" is a
   WEAKENING of it that reads no sequence element: every subformula that reads
   an element, binds a variable or is outside the fragment is replaced by
   [true], a positive sequence equality by the equality of the two lengths, a
   negative one by [true].  A quantifier forgets the assumptions that mention
   its variables.  Whether the assumptions entail the range of a read is
   decided by a syntactic test and then by the [entails] argument, which must
   answer [true] only on a proof.  Assuming a sibling's weakening is sound
   because the weakening reads no element, so it has one value in both related
   models, and where it is false the sibling is false as well, which makes the
   conjunction false (the disjunction true) in both; an [ite]'s condition has
   one value in both because its own reads are checked like every other.

   CONTRACT.  [translate] raises nothing but asynchronous exceptions; it draws
   fresh names (the position variable of each sequence equality) only on a
   formula that contains a sequence.  A formula mentioning no sequence is
   [Error] with nothing drawn. *)

open Core
open Common.Ext
open Common.Combinator
open LogicOld

exception Outside of string

type binding = {
  seq_var : Ident.tvar;
  elem_sort : Sort.t;
  arr_var : Ident.tvar;
  len_var : Ident.tvar;
}

type t = {
  formula : Formula.t;  (** equisatisfiable with the input *)
  bindings : binding list;  (** one per free sequence variable *)
  own_vars : Ident.tvar Set.Poly.t;  (** every name the pass introduced *)
}

type pair = { arr : Term.t; len : Term.t }

let has_seq_sort sort = Set.exists (Term.sorts_of_sort sort) ~f:T_seq.is_sseq

let is_seq_sym = function
  | T_seq.SqEmpty _ | T_seq.SqUnit _ | T_seq.SqConcat _ | T_seq.SqLen _
  | T_seq.SqNth _ | T_seq.SqExtract _ | T_seq.SqStore _ ->
      true
  | _ -> false

let mentions_seq phi =
  Set.exists (Formula.funsyms_of phi) ~f:is_seq_sym
  || Set.exists (Formula.term_sort_env_of phi) ~f:(snd >> has_seq_sort)
  || Set.exists (Formula.quantified_sort_env_of phi) ~f:(snd >> has_seq_sort)

let reads_element phi =
  Set.exists (Formula.funsyms_of phi) ~f:(function
    | T_seq.SqNth _ -> true
    | _ -> false)

let arr_sort se = T_array.SArray (T_int.SInt, se)

let in_range i n =
  Formula.and_of [ Formula.leq (T_int.zero ()) i; Formula.lt i n ]

(* A read met while translating one literal: its position and the length it
   must stay below, the variables bound between the literal and the read, and
   the hypotheses its place inside the literal makes true (the condition of an
   enclosing [ite], the siblings of an enclosing connective of an embedded
   formula). *)
type read = {
  pos : Term.t;
  bound_len : Term.t;
  inner : Ident.tvar Set.Poly.t;
  local : Formula.t list;
}

(* The per-call state: the sequence variables met so far, the fresh arrays
   standing for [seq.empty], the reads of the literal being translated, and the
   entailment questions already answered. *)
type state = {
  vars : (Ident.tvar, binding) Hashtbl.Poly.t;
  mutable empties : Ident.tvar list;
  mutable reads : read list;
  memo : (string, bool) Hashtbl.Poly.t;
}

let binding_of st x se =
  match Hashtbl.Poly.find st.vars x with
  | Some b -> b
  | None ->
      let name = Ident.name_of_tvar x in
      let b =
        {
          seq_var = x;
          elem_sort = se;
          arr_var = Ident.Tvar ("sqa#" ^ name);
          len_var = Ident.Tvar ("sql#" ^ name);
        }
      in
      Hashtbl.Poly.set st.vars ~key:x ~data:b;
      b

(* hypotheses that mention a variable about to be rebound are forgotten *)
let forget bound hyps =
  List.filter hyps ~f:(fun h ->
      Set.is_empty (Set.inter (Formula.fvs_of h) bound))

(* linear in the operands, unlike appending at every node, which a chain
   nested to the left made quadratic *)
let conjuncts = Formula.conjuncts_list_of
let disjuncts = Formula.disjuncts_list_of

let is_literal = function
  | Formula.Atom _ | Formula.UnaryOp (Not, Formula.Atom _, _) -> true
  | _ -> false

let rec tau_seq st ~inner ~local (t : Term.t) : pair =
  match t with
  | Term.Var (x, T_seq.SSeq se, _) ->
      if has_seq_sort se then raise (Outside "a sequence of sequences");
      if Set.mem inner x then raise (Outside "a bound sequence variable");
      let b = binding_of st x se in
      {
        arr = Term.mk_var b.arr_var (arr_sort se);
        len = Term.mk_var b.len_var T_int.SInt;
      }
  | Term.FunApp (T_seq.SqEmpty se, [], _) ->
      let a = Ident.Tvar (sprintf "sqe#%d" (List.length st.empties)) in
      st.empties <- a :: st.empties;
      { arr = Term.mk_var a (arr_sort se); len = T_int.zero () }
  | Term.FunApp (T_seq.SqUnit se, [ e ], _) ->
      {
        arr = T_array.mk_const_array T_int.SInt se (tau st ~inner ~local e);
        len = T_int.one ();
      }
  | Term.FunApp (T_seq.SqStore se, [ u; i; e ], _) ->
      let p = tau_seq st ~inner ~local u in
      let i' = tau st ~inner ~local i in
      let e' = tau st ~inner ~local e in
      {
        arr =
          T_bool.ifte (in_range i' p.len)
            (T_array.mk_store T_int.SInt se p.arr i' e')
            p.arr;
        len = p.len;
      }
  | Term.FunApp (T_bool.IfThenElse, [ c; u; w ], _) ->
      let c' = tau st ~inner ~local c in
      let pu = tau_seq st ~inner ~local:(Formula.of_bool_term c' :: local) u in
      let pw =
        tau_seq st ~inner ~local:(Formula.of_neg_bool_term c' :: local) w
      in
      {
        arr = T_bool.mk_if_then_else c' pu.arr pw.arr;
        len = T_bool.mk_if_then_else c' pu.len pw.len;
      }
  | Term.FunApp (T_seq.SqConcat _, _, _) -> raise (Outside "seq.++")
  | Term.FunApp (T_seq.SqExtract _, _, _) -> raise (Outside "seq.extract")
  | Term.LetTerm _ -> raise (Outside "a let")
  | _ -> raise (Outside ("a sequence term " ^ Term.str_of t))

(* a term that is not itself a sequence *)
and tau st ~inner ~local (t : Term.t) : Term.t =
  match t with
  | Term.Var (_, s, _) ->
      if has_seq_sort s then raise (Outside "a sequence outside a read") else t
  | Term.FunApp (T_seq.SqNth se, [ u; i ], _) ->
      let p = tau_seq st ~inner ~local u in
      let i' = tau st ~inner ~local i in
      st.reads <- { pos = i'; bound_len = p.len; inner; local } :: st.reads;
      T_array.mk_select T_int.SInt se p.arr i'
  | Term.FunApp (T_seq.SqLen _, [ u ], _) -> (tau_seq st ~inner ~local u).len
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      T_bool.of_formula ~info (tau_embedded st ~inner ~local phi)
  | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], info)
    when not (has_seq_sort (Term.sort_of t)) ->
      let c' = tau st ~inner ~local c in
      T_bool.mk_if_then_else ~info c'
        (tau st ~inner ~local:(Formula.of_bool_term c' :: local) a)
        (tau st ~inner ~local:(Formula.of_neg_bool_term c' :: local) b)
  | Term.FunApp (fs, args, info) ->
      if has_seq_sort (Term.sort_of t) then
        raise (Outside ("a sequence-valued term " ^ Term.str_of t));
      Term.mk_fsym_app ~info fs
        (List.map args ~f:(fun a ->
             if has_seq_sort (Term.sort_of a) then
               raise (Outside ("a sequence argument of " ^ Term.str_of t))
             else tau st ~inner ~local a))
  | Term.LetTerm _ -> raise (Outside "a let")

and tau_atom st ~inner ~local (atom : Atom.t) : Formula.t =
  match atom with
  | Atom.True _ | Atom.False _ -> Formula.mk_atom atom
  | Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op), [ u; w ], _)
    when T_seq.is_sseq (Term.sort_of u) ->
      let pu = tau_seq st ~inner ~local u in
      let pw = tau_seq st ~inner ~local w in
      let k = Ident.mk_fresh_tvar () in
      let vk = Term.mk_var k T_int.SInt in
      let se = T_seq.elem_sort_of (Term.sort_of u) in
      let eq =
        Formula.and_of
          [
            Formula.eq pu.len pw.len;
            Formula.mk_forall
              [ (k, T_int.SInt) ]
              (Formula.mk_imply (in_range vk pu.len)
                 (Formula.eq
                    (T_array.mk_select T_int.SInt se pu.arr vk)
                    (T_array.mk_select T_int.SInt se pw.arr vk)));
          ]
      in
      if Stdlib.(op = T_bool.Eq) then eq else Formula.nnf_of (Formula.mk_neg eq)
  | Atom.App (pred, args, info) ->
      (match pred with
      | Predicate.Psym _ -> ()
      | _ ->
          if List.exists args ~f:(fun a -> has_seq_sort (Term.sort_of a)) then
            raise (Outside "a sequence argument of a predicate"));
      Formula.mk_atom
        (Atom.mk_app ~info pred (List.map args ~f:(tau st ~inner ~local)))

(* a formula embedded in a term: a read in one part of a conjunction may
   assume what the other parts say, a read in one part of a disjunction what
   the negations of the others say, as at the formula level; the reads
   themselves are checked at the enclosing literal *)
and tau_embedded st ~inner ~local (phi : Formula.t) : Formula.t =
  match phi with
  | Formula.Atom (atom, _) -> tau_atom st ~inner ~local atom
  | Formula.BinaryOp (((And | Or) as op), _, _, _) ->
      let parts = match op with And -> conjuncts phi | _ -> disjuncts phi in
      let hyps = List.map parts ~f:(sibling_hyp st op) in
      let parts' =
        List.mapi parts ~f:(fun k p ->
            let others =
              List.filter_mapi hyps ~f:(fun m h -> if m = k then None else h)
            in
            tau_embedded st ~inner ~local:(others @ local) p)
      in
      (match op with And -> Formula.and_of | _ -> Formula.or_of) parts'
  | Formula.UnaryOp (Not, p, _) ->
      Formula.mk_neg (tau_embedded st ~inner ~local p)
  | Formula.BinaryOp (op, p1, p2, _) ->
      Formula.mk_binop op
        (tau_embedded st ~inner ~local p1)
        (tau_embedded st ~inner ~local p2)
  | Formula.Bind (((Forall | Exists) as b), senv, p, _) ->
      if List.exists senv ~f:(snd >> has_seq_sort) then
        raise (Outside "a quantifier over sequences");
      let bound = Set.Poly.of_list (List.map senv ~f:fst) in
      Formula.mk_bind b senv
        (tau_embedded st ~inner:(Set.union inner bound)
           ~local:(forget bound local) p)
  | _ -> raise (Outside "a let, letrec or random binder")

(* What a sibling part says when the connective lets it be assumed: the part
   itself beside a conjunction, its negation beside a disjunction; [None] when
   nothing usable is said. *)
and sibling_hyp st op p =
  match
    try
      Some
        (Formula.nnf_of
           (match op with Formula.And -> p | _ -> Formula.mk_neg p))
    with Failure _ -> None
  with
  | None -> None
  | Some h -> (
      match hyp_formula st h with
      | Formula.Atom (Atom.True _, _) -> None
      | h -> Some h)

(* A WEAKENING of an assumed formula [phi] (in negation normal form), over the
   array side and reading no element: a subformula that reads an element,
   binds a variable, or is outside the fragment becomes [true]; a positive
   sequence equality becomes the equality of the lengths and a negative one
   [true].  It is a weakening because all of these stand at positive polarity
   in negation normal form.  Reading no element, it has one value in related
   models, which is what makes assuming it sound: where it is false the
   assumed formula is false too, in both. *)
and hyp_formula st (phi : Formula.t) : Formula.t =
  let top = Formula.mk_true () in
  match phi with
  | Formula.BinaryOp (And, p1, p2, _) ->
      Formula.mk_and (hyp_formula st p1) (hyp_formula st p2)
  | Formula.BinaryOp (Or, p1, p2, _) ->
      Formula.mk_or (hyp_formula st p1) (hyp_formula st p2)
  | Formula.Atom _ | Formula.UnaryOp (Not, Formula.Atom _, _) -> (
      if reads_element phi then top
      else
        let seq_eq_sides = function
          | Atom.App (Predicate.Psym T_bool.Eq, [ u; w ], _)
            when T_seq.is_sseq (Term.sort_of u) ->
              Some (`Pos, u, w)
          | Atom.App (Predicate.Psym T_bool.Neq, [ u; w ], _)
            when T_seq.is_sseq (Term.sort_of u) ->
              Some (`Neg, u, w)
          | _ -> None
        in
        let saved = st.reads in
        let inner = Set.Poly.empty and local = [] in
        let len_eq u w =
          Formula.eq (tau_seq st ~inner ~local u).len
            (tau_seq st ~inner ~local w).len
        in
        try
          let r =
            match phi with
            | Formula.Atom (atom, _) -> (
                match seq_eq_sides atom with
                | Some (`Pos, u, w) -> len_eq u w
                | Some (`Neg, _, _) -> top
                | None -> tau_atom st ~inner ~local atom)
            | Formula.UnaryOp (Not, Formula.Atom (atom, _), _) -> (
                match seq_eq_sides atom with
                | Some (`Neg, u, w) -> len_eq u w
                | Some (`Pos, _, _) -> top
                | None -> Formula.mk_neg (tau_atom st ~inner ~local atom))
            | _ -> top
          in
          st.reads <- saved;
          r
        with Outside _ ->
          st.reads <- saved;
          top)
  | _ -> top

let entailed st ~entails hyps goal =
  let goal = Evaluator.simplify goal in
  Formula.is_true goal
  ||
  let hyps =
    List.filter hyps ~f:(function
      | Formula.Atom (Atom.True _, _) -> false
      | _ -> true)
  in
  let g = Formula.str_of goal in
  let hs = List.map hyps ~f:(fun h -> Formula.str_of (Evaluator.simplify h)) in
  List.exists hs ~f:(String.equal g)
  ||
  let key = String.concat ~sep:" ; " (g :: hs) in
  match Hashtbl.Poly.find st.memo key with
  | Some b -> b
  | None ->
      let b = entails hyps goal in
      Hashtbl.Poly.set st.memo ~key ~data:b;
      b

let rec tr st ~entails (gamma : Formula.t list) (phi : Formula.t) : Formula.t =
  match phi with
  | Formula.Atom _ | Formula.UnaryOp (Not, Formula.Atom _, _) ->
      st.reads <- [];
      let inner = Set.Poly.empty and local = [] in
      let phi' =
        match phi with
        | Formula.Atom (atom, _) -> tau_atom st ~inner ~local atom
        | Formula.UnaryOp (Not, Formula.Atom (atom, _), _) ->
            Formula.nnf_of (Formula.mk_neg (tau_atom st ~inner ~local atom))
        | _ -> assert false
      in
      let reads = st.reads in
      st.reads <- [];
      List.iter reads ~f:(fun r ->
          let hyps = forget r.inner gamma @ r.local in
          if
            not
              (entailed st ~entails hyps (Formula.leq (T_int.zero ()) r.pos)
              && entailed st ~entails hyps (Formula.lt r.pos r.bound_len))
          then
            raise
              (Outside
                 (sprintf "an unguarded read at %s in %s" (Term.str_of r.pos)
                    (Formula.str_of phi))));
      phi'
  | Formula.BinaryOp (((And | Or) as op), _, _, _) ->
      let parts = match op with And -> conjuncts phi | _ -> disjuncts phi in
      let hyps = List.map parts ~f:(sibling_hyp st op) in
      let parts' =
        List.mapi parts ~f:(fun k p ->
            let others =
              List.filter_mapi hyps ~f:(fun m h -> if m = k then None else h)
            in
            tr st ~entails (gamma @ others) p)
      in
      (match op with And -> Formula.and_of | _ -> Formula.or_of) parts'
  | Formula.BinaryOp (op, p1, p2, _) ->
      Formula.mk_binop op (tr st ~entails gamma p1) (tr st ~entails gamma p2)
  | Formula.UnaryOp (Not, p, _) -> Formula.mk_neg (tr st ~entails gamma p)
  | Formula.Bind (((Forall | Exists) as b), senv, p, _) ->
      if List.exists senv ~f:(snd >> has_seq_sort) then
        raise (Outside "a quantifier over sequences");
      let bound = Set.Poly.of_list (List.map senv ~f:fst) in
      Formula.mk_bind b senv (tr st ~entails (forget bound gamma) p)
  | _ -> raise (Outside "a let, letrec or random binder")

let translate ?(entails = fun _ _ -> false) (phi : Formula.t) :
    (t, string) Result.t =
  if not (mentions_seq phi) then Error "no sequence"
  else
    let st =
      {
        vars = Hashtbl.Poly.create ();
        empties = [];
        reads = [];
        memo = Hashtbl.Poly.create ();
      }
    in
    match
      try Ok (tr st ~entails [] (Formula.nnf_of phi)) with
      | Outside reason -> Error reason
      | exn_ when not (Common.Timer.is_async exn_) ->
          Error ("not translatable: " ^ Exn.to_string exn_)
    with
    | Error _ as e -> e
    | Ok phi' ->
        let bindings =
          List.sort (Hashtbl.Poly.data st.vars) ~compare:(fun a b ->
              String.compare
                (Ident.name_of_tvar a.seq_var)
                (Ident.name_of_tvar b.seq_var))
        in
        let defs =
          List.map bindings ~f:(fun b ->
              Formula.geq (Term.mk_var b.len_var T_int.SInt) (T_int.zero ()))
        in
        let own_vars =
          Set.Poly.of_list
            (st.empties
            @ List.concat_map bindings ~f:(fun b -> [ b.arr_var; b.len_var ]))
        in
        Ok { formula = Formula.and_of (defs @ [ phi' ]); bindings; own_vars }

(* The largest sequence a model is read back into; a longer one is not read
   back, and the caller asks the untranslated query instead. *)
let max_read_back_length = 4096

(* A model of the translation read back as a model of the input: each
   sequence variable is given the word [a_s[0..n_s-1]] and the pass's own
   names are dropped.  A sequence whose length the model leaves out is left
   out too (the model says nothing about it).  [None] when a length or an
   element cannot be read, or the length is over [max_read_back_length]. *)
let read_back (tr : t) (model : model) : model option =
  let find x =
    List.find_map model ~f:(fun ((y, _), v) ->
        if Stdlib.(x = y) then Some v else None)
  in
  let int_of t =
    try Some (Z.to_int (T_int.let_int t))
    with exn_ when not (Common.Timer.is_async exn_) -> None
  in
  let seq_of b =
    match find b.len_var with
    | None | Some None -> Some None
    | Some (Some lt) -> (
        match int_of lt with
        | None -> None
        | Some n when n < 0 || n > max_read_back_length -> None
        | Some n -> (
            let arr =
              match find b.arr_var with Some (Some a) -> Some a | _ -> None
            in
            let elems =
              List.init n ~f:(fun k ->
                  match arr with
                  | None -> None
                  | Some a -> T_array.eval_select a (T_int.mk_int (Z.of_int k)))
            in
            match Option.all elems with
            | None -> None
            | Some es ->
                let se = b.elem_sort in
                let value =
                  match List.map es ~f:(T_seq.mk_unit se) with
                  | [] -> T_seq.mk_empty se
                  | u :: us ->
                      List.fold us ~init:u ~f:(fun acc u ->
                          T_seq.mk_concat se acc u)
                in
                Some (Some value)))
  in
  let values =
    List.map tr.bindings ~f:(fun b ->
        Option.map (seq_of b) ~f:(fun v -> (b, v)))
  in
  match Option.all values with
  | None -> None
  | Some values ->
      let rest =
        List.filter model ~f:(fun ((x, _), _) -> not (Set.mem tr.own_vars x))
      in
      Some
        (rest
        @ List.filter_map values ~f:(fun (b, v) ->
            Option.map v ~f:(fun v ->
                ((b.seq_var, T_seq.mk_seq_sort b.elem_sort), Some v))))
