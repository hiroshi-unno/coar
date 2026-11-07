(* A sequence formula asked as arrays plus a length.

   WHY.  SMT-LIB sequences have no write, so [seq.store] reaches the solver as
   [ite(0 <= i < len s, extract(s,0,i) ++ unit v ++ extract(s,i+1,..), s)].  A
   query that mentions only reads, lengths and writes therefore arrives with
   concatenation and extraction, and Z3 (4.15.2) decides nothing about
   [seq.nth] over that: the six-line frame fact
   [t = store s i 0 /\ 0 <= j < len s /\ j != i => nth t j = nth s j] times out
   at 20 s, where cvc5 answers it in 0.2 s.  The same question over an array
   and an integer is quantifier-free read-over-write arithmetic, which the
   array solver decides at once.  Concatenation is admitted for the second
   reason the translation exists: a question whose every countermodel holds a
   very long sequence -- a counter kept equal to the length of the sequence a
   loop has produced, bounded by 2^64 - 1, over a range longer than that, the
   produced sequence written as [s ++ unit x ++ unit y] -- is one Z3's
   sequence solver gives up on ("reached max unfolding"), while over an
   integer length the countermodel (a length of 2^64 - 2) is found at once.

   THE FRAGMENT.  A formula is translated only when all of the following hold,
   and [translate] returns [Error reason] otherwise, leaving the caller to ask
   the formula as it is:
   - sequence terms are built from free sequence variables, [seq.empty],
     [seq.unit e], [seq.store u i e], [ite(c, u, w)] and the binary
     [seq.++ u w] -- no [seq.extract], no other sequence operator, no [let];
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
     u ++ w            |-> (a_u ++ a_w, n_u + n_w)
     u = w             |-> n_u = n_w /\ forall k. 0 <= k < n_u => a_u[k] = a_w[k]
   and every other symbol is kept.  No array term denotes [a_u ++ a_w], so a
   sequence term that contains a concatenation is translated as a READ
   FUNCTION rather than an array (the [Fn] case of [pair]): its read at [k] is
     (a_u ++ a_w)[k]   =  ite(k < n_u, a_u[k], a_w[k - n_u])
   and [store], [ite] and equality over such a term are written through that
   read ([ite(0 <= i < n /\ k = i, e, a[k])] for a store).  A term with no
   concatenation in it is translated to an array exactly as listed above, so a
   concat-free formula has the same image it had before concatenation was
   admitted.

   THE CLAIM.  For a formula in the fragment, the input and its translation
   are EQUISATISFIABLE, and a model of the translation reads back to a model of
   the input (each sequence the word a_s[0..n_s-1]).  So a validity question
   asked as the unsatisfiability of the translated negation is the same
   question.  The proof relates a sequence model and an array model when they
   share the element and integer domains and every sequence term's length, and
   its array (or read function) agrees with its word on [0, length); nothing is
   required out of range.  For a concatenation this is SMT-LIB's definition of
   [seq.++] as the concatenation of words: [len (u ++ w) = len u + len w], and
   at [0 <= k < len u + len w] the letter of [u ++ w] is [u]'s at [k] when
   [k < len u] and [w]'s at [k - len u] otherwise -- and in each case that
   position is inside the operand read, so the induction hypothesis for the
   operand applies and no operand is read out of its range.  By induction, under related models every formula of the fragment
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
   answer [true] only on a proof; it is given each hypothesis with a number
   standing for its simplified printed form, the same number exactly when the
   texts are equal within the call (the same identification the translation's
   own memo of answered questions makes).  Assuming a sibling's weakening is
   sound because the weakening reads no element, so it has one value in both
   related models, and where it is false the sibling is false as well, which
   makes the conjunction false (the disjunction true) in both; an [ite]'s
   condition has one value in both because its own reads are checked like
   every other.

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
  concat : bool;
      (** whether a concatenation was translated (as a read function); [false]
          exactly when the input is in the concat-free fragment, whose image is
          the array form it had before concatenation was admitted *)
}

(* The image of a sequence term: its length, and how a read of it at a
   position is written.  [Arr] is backed by an array term (a variable's array,
   a constant array, a store, an [ite] of two such), read by [select]; [Fn]
   gives the read as a term built from the position, which is what a
   concatenation needs, since no array term denotes [a_u ++ a_w] without a
   lambda.  A term of the concat-free fragment is always [Arr], so such a
   formula is translated exactly as it was before concatenation was admitted.
   Contract of [Fn { read; len }]: at every position [k] with [0 <= k < len],
   [read k] is the element there; at any other position it is unconstrained
   and is never read, since every read is range-guarded (GUARDS below). *)
type pair =
  | Arr of { arr : Term.t; len : Term.t }
  | Fn of { read : Term.t -> Term.t; len : Term.t }

let len_of = function Arr { len; _ } | Fn { len; _ } -> len

let read_of se p k =
  match p with
  | Arr { arr; _ } -> T_array.mk_select T_int.SInt se arr k
  | Fn { read; _ } -> read k

(* [read_of] as a read function writes it: a read of a constant array (the
   image of [seq.unit e]) is its element, [select (const e) k = e] in every
   model.  Used only inside the [Fn] cases, so that a concat-free formula keeps
   its earlier image, and so that a concatenation of units leaves no array
   literal behind (an array literal puts a formula outside the
   arrays-as-functions translation the caller may ask next). *)
let read_in_fn se p k =
  match p with
  | Arr { arr = Term.FunApp (T_array.AConst _, [ e ], _); _ } -> e
  | _ -> read_of se p k

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

(* A hypothesis of the range-guard questions, made once where it enters the
   context -- a sibling literal of a connective, the condition of an [ite]
   (or its negation), a sibling of a connective inside an embedded formula --
   and then shared by every question asked under it, with its free variables
   and its printed form (and the number standing for that text, by which an
   [entails] recognises a hypothesis it has seen without reading it again),
   each computed at most once.  Making it there rather than at each read
   changes no question: a read is given the same formulas in the same order.
   Why: a clause of 66,000 nodes holding concatenations put some 200
   literals of 11,000 nodes in the context of each of its 1,200 reads, and
   recomputing, printing or even hashing them for each question took longer
   than asking them; and an [ite] condition made anew for each read beneath
   it was a third of the 121,000 hypotheses converted for 44,000 questions
   in one run, each also a new label in the guards' solver and a new
   printed form. *)
type hyp = {
  hyp : Formula.t;
  hyp_fvs : Ident.tvar Set.Poly.t Lazy.t;
  hyp_shown : (string * int) Lazy.t;
      (** the simplified form printed, and a number standing for that text,
          equal for equal texts within the translation *)
}

(* A read met while translating one literal: its position and the length it
   must stay below, the variables bound between the literal and the read, and
   the hypotheses its place inside the literal makes true (the condition of an
   enclosing [ite], the siblings of an enclosing connective of an embedded
   formula).  The latter are hypotheses, each made once where its [ite] or
   connective is met and shared by every read beneath it (see [hyp]). *)
type read = {
  pos : Term.t;
  bound_len : Term.t;
  inner : Ident.tvar Set.Poly.t;
  local : hyp list;
  of_fn : bool;  (** the sequence read is a read function ([Fn]) *)
}

(* The per-call state: the sequence variables met so far, the fresh arrays
   standing for [seq.empty], the reads of the literal being translated, and the
   entailment questions already answered. *)
type state = {
  vars : (Ident.tvar, binding) Hashtbl.Poly.t;
  mutable empties : Ident.tvar list;
  mutable reads : read list;
  memo : (string, bool) Hashtbl.Poly.t;
  shown_ids : (string, int) Hashtbl.Poly.t;
      (** the numbers standing for the hypotheses' printed forms *)
  nonneg : (Ident.tvar, hyp) Hashtbl.Poly.t;
      (** each sequence variable's [n_s >= 0], made once *)
  mutable occupied : Ident.tvar Set.Poly.t;
  mutable concat : bool;
}

let reserve_preferred st name =
  let rec choose n =
    let candidate =
      Ident.Tvar (if n = 0 then name else sprintf "%s#%d" name n)
    in
    if Set.mem st.occupied candidate then choose (n + 1)
    else (
      st.occupied <- Set.add st.occupied candidate;
      candidate)
  in
  choose 0

let fresh_index st =
  let rec draw () =
    let candidate = Ident.mk_fresh_tvar () in
    if Set.mem st.occupied candidate then draw ()
    else (
      st.occupied <- Set.add st.occupied candidate;
      candidate)
  in
  draw ()

let binding_of st x se =
  match Hashtbl.Poly.find st.vars x with
  | Some b -> b
  | None ->
      let name = Ident.name_of_tvar x in
      let b =
        {
          seq_var = x;
          elem_sort = se;
          arr_var = reserve_preferred st ("sqa#" ^ name);
          len_var = reserve_preferred st ("sql#" ^ name);
        }
      in
      Hashtbl.Poly.set st.vars ~key:x ~data:b;
      b

let mk_hyp st phi =
  {
    hyp = phi;
    hyp_fvs = lazy (Formula.fvs_of phi);
    hyp_shown =
      lazy
        (let text = Formula.str_of (Evaluator.simplify phi) in
         match Hashtbl.Poly.find st.shown_ids text with
         | Some n -> (text, n)
         | None ->
             let n = Hashtbl.Poly.length st.shown_ids in
             Hashtbl.Poly.set st.shown_ids ~key:text ~data:n;
             (text, n));
  }

(* hypotheses that mention a variable about to be rebound are forgotten *)
let forget_hyps bound hyps =
  if Set.is_empty bound then hyps
  else
    List.filter hyps ~f:(fun h ->
        Set.is_empty (Set.inter (Lazy.force h.hyp_fvs) bound))

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
      Arr
        {
          arr = Term.mk_var b.arr_var (arr_sort se);
          len = Term.mk_var b.len_var T_int.SInt;
        }
  | Term.FunApp (T_seq.SqEmpty se, [], _) ->
      let a =
        reserve_preferred st (sprintf "sqe#%d" (List.length st.empties))
      in
      st.empties <- a :: st.empties;
      Arr { arr = Term.mk_var a (arr_sort se); len = T_int.zero () }
  | Term.FunApp (T_seq.SqUnit se, [ e ], _) ->
      Arr
        {
          arr = T_array.mk_const_array T_int.SInt se (tau st ~inner ~local e);
          len = T_int.one ();
        }
  | Term.FunApp (T_seq.SqStore se, [ u; i; e ], _) -> (
      let p = tau_seq st ~inner ~local u in
      let i' = tau st ~inner ~local i in
      let e' = tau st ~inner ~local e in
      let len = len_of p in
      match p with
      | Arr { arr; _ } ->
          Arr
            {
              arr =
                T_bool.ifte (in_range i' len)
                  (T_array.mk_store T_int.SInt se arr i' e')
                  arr;
              len;
            }
      | Fn _ ->
          (* the same read as the array store's: [e] at [i] when [i] is in
             range, the stored-into sequence's element elsewhere *)
          Fn
            {
              read =
                (fun k ->
                  T_bool.ifte
                    (Formula.and_of [ in_range i' len; Formula.eq k i' ])
                    e' (read_in_fn se p k));
              len;
            })
  | Term.FunApp (T_bool.IfThenElse, [ c; u; w ], _) -> (
      let c' = tau st ~inner ~local c in
      let pu =
        tau_seq st ~inner
          ~local:(mk_hyp st (Formula.of_bool_term c') :: local)
          u
      in
      let pw =
        tau_seq st ~inner
          ~local:(mk_hyp st (Formula.of_neg_bool_term c') :: local)
          w
      in
      let len = T_bool.mk_if_then_else c' (len_of pu) (len_of pw) in
      match (pu, pw) with
      | Arr { arr = au; _ }, Arr { arr = aw; _ } ->
          Arr { arr = T_bool.mk_if_then_else c' au aw; len }
      | _ ->
          let se = T_seq.elem_sort_of (Term.sort_of t) in
          Fn
            {
              read =
                (fun k ->
                  T_bool.mk_if_then_else c' (read_in_fn se pu k)
                    (read_in_fn se pw k));
              len;
            })
  | Term.FunApp (T_seq.SqConcat se, [ u; w ], _) ->
      (* [len (u ++ w) = len u + len w], and for [0 <= k < len u + len w]
         the element of [u ++ w] at [k] is [u]'s at [k] when [k < len u] and
         [w]'s at [k - len u] otherwise (SMT-LIB's [seq.++] is concatenation
         of words).  Under the read's range guard each branch reads its
         operand inside that operand's range, which is why only the read of
         the whole needs a guard. *)
      let pu = tau_seq st ~inner ~local u in
      let pw = tau_seq st ~inner ~local w in
      let nu = len_of pu in
      st.concat <- true;
      Fn
        {
          read =
            (fun k ->
              T_bool.ifte (Formula.lt k nu) (read_in_fn se pu k)
                (read_in_fn se pw (T_int.mk_sub k nu)));
          len = T_int.mk_add nu (len_of pw);
        }
  | Term.FunApp (T_seq.SqConcat _, _, _) -> raise (Outside "seq.++ not binary")
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
      let of_fn = match p with Fn _ -> true | Arr _ -> false in
      st.reads <-
        { pos = i'; bound_len = len_of p; inner; local; of_fn } :: st.reads;
      read_of se p i'
  | Term.FunApp (T_seq.SqLen _, [ u ], _) -> len_of (tau_seq st ~inner ~local u)
  | Term.FunApp (T_bool.Formula phi, [], info) ->
      T_bool.of_formula ~info (tau_embedded st ~inner ~local phi)
  | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], info)
    when not (has_seq_sort (Term.sort_of t)) ->
      let c' = tau st ~inner ~local c in
      T_bool.mk_if_then_else ~info c'
        (tau st ~inner
           ~local:(mk_hyp st (Formula.of_bool_term c') :: local)
           a)
        (tau st ~inner
           ~local:(mk_hyp st (Formula.of_neg_bool_term c') :: local)
           b)
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
      let k = fresh_index st in
      let vk = Term.mk_var k T_int.SInt in
      let se = T_seq.elem_sort_of (Term.sort_of u) in
      (* two array images are compared cell by cell exactly as before
         concatenation was admitted; a read function on either side reads
         a unit's element directly *)
      let rd =
        match (pu, pw) with Arr _, Arr _ -> read_of | _ -> read_in_fn
      in
      let eq =
        Formula.and_of
          [
            Formula.eq (len_of pu) (len_of pw);
            Formula.mk_forall
              [ (k, T_int.SInt) ]
              (Formula.mk_imply
                 (in_range vk (len_of pu))
                 (Formula.eq (rd se pu vk) (rd se pw vk)));
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
      let hyps =
        List.map parts ~f:(fun p ->
            Option.map (sibling_hyp st op p) ~f:(mk_hyp st))
      in
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
           ~local:(forget_hyps bound local) p)
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
          Formula.eq
            (len_of (tau_seq st ~inner ~local u))
            (len_of (tau_seq st ~inner ~local w))
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

let entailed st ~entails (hyps : hyp list) goal =
  let goal = Evaluator.simplify goal in
  Formula.is_true goal
  ||
  let hyps =
    List.filter hyps ~f:(fun h ->
        match h.hyp with Formula.Atom (Atom.True _, _) -> false | _ -> true)
  in
  let g = Formula.str_of goal in
  let shown = List.map hyps ~f:(fun h -> Lazy.force h.hyp_shown) in
  List.exists shown ~f:(fun (text, _) -> String.equal g text)
  ||
  (* The key is the number of hypotheses, the number standing for each one's
     printed form in order, four bytes each, and then the goal's text: the
     fixed-width prefix fixes where the text starts, so equal keys are
     exactly equal questions as the texts would identify them.  Why packed:
     a question carries some 200 hypotheses, and spelling their numbers in
     decimal and joining them cost 6.7 s over 44,000 questions in one run,
     more than the hashing does. *)
  let key =
    let buf =
      Stdlib.Buffer.create (4 + (4 * List.length shown) + String.length g)
    in
    Stdlib.Buffer.add_int32_le buf (Int32.of_int_exn (List.length shown));
    List.iter shown ~f:(fun (_, n) ->
        Stdlib.Buffer.add_int32_le buf (Int32.of_int_exn n));
    Stdlib.Buffer.add_string buf g;
    Stdlib.Buffer.contents buf
  in
  match Hashtbl.Poly.find st.memo key with
  | Some b -> b
  | None ->
      (* each hypothesis goes with the number of its printed form, so a
         hypothesis printed alike in another place of the formula is
         recognised as the one already met *)
      let b =
        entails (List.map2_exn hyps shown ~f:(fun h (_, n) -> (n, h.hyp))) goal
      in
      Hashtbl.Poly.set st.memo ~key ~data:b;
      b

let rec tr st ~entails (gamma : hyp list) (phi : Formula.t) : Formula.t =
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
      (* every length is non-negative: the translation conjoins [n_s >= 0]
         for each sequence variable, and in a sequence model [len s >= 0], so
         the two related models agree on it and assuming it is sound; a read
         of [u ++ w] inside [u]'s range is inside the whole's only given
         [n_w >= 0].  Assumed for a read of a read function only, so that a
         read of a concat-free term is admitted or refused exactly as before
         concatenation was admitted.  One hypothesis per sequence variable
         for the whole translation, so that every question shares it. *)
      let nonneg_all =
        lazy
          (List.map (Hashtbl.Poly.data st.vars) ~f:(fun b ->
               Hashtbl.Poly.find_or_add st.nonneg b.seq_var ~default:(fun () ->
                   mk_hyp st
                     (Formula.geq (Term.mk_var b.len_var T_int.SInt)
                        (T_int.zero ())))))
      in
      List.iter reads ~f:(fun r ->
          let nonneg = if not r.of_fn then [] else Lazy.force nonneg_all in
          let hyps =
            forget_hyps r.inner gamma @ r.local @ nonneg
          in
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
      let hyps =
        List.map parts ~f:(fun p ->
            Option.map (sibling_hyp st op p) ~f:(mk_hyp st))
      in
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
      Formula.mk_bind b senv (tr st ~entails (forget_hyps bound gamma) p)
  | _ -> raise (Outside "a let, letrec or random binder")

let translate ?(entails = fun _ _ -> false) ?(reserved = Set.Poly.empty)
    (phi : Formula.t) : (t, string) Result.t =
  if not (mentions_seq phi) then Error "no sequence"
  else
    let st =
      {
        vars = Hashtbl.Poly.create ();
        empties = [];
        reads = [];
        memo = Hashtbl.Poly.create ();
        shown_ids = Hashtbl.Poly.create ();
        nonneg = Hashtbl.Poly.create ();
        occupied = Set.union reserved (Formula.names_spelled_in phi);
        concat = false;
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
        Ok
          {
            formula = Formula.and_of (defs @ [ phi' ]);
            bindings;
            own_vars;
            concat = st.concat;
          }

(* The largest sequence a model is read back into as a word; a longer one is
   left out of the model read back (see [read_back]). *)
let max_read_back_length = 4096

(* A model of the translation read back as a model of the input: each
   sequence variable is given the word [a_s[0..n_s-1]] and the pass's own
   names are dropped.  A sequence whose length the model leaves out is left
   out too (the model says nothing about it), and so is one whose length is
   over [max_read_back_length]: the translation's model still shows that the
   input is satisfiable (the two are equisatisfiable), so the decision stands
   and only that sequence's value is not given.  Why the long one must not
   void the answer: a validity question about a sequence read only through
   its length and range-guarded reads -- "the length plus one, times ten, does
   not overflow a 64-bit word, given every element is in range" -- has its
   countermodels only at lengths near 2^62, which no sequence solver builds a
   model for, while the translated question over an array and a length is
   decided at once; discarding the model sent it back to the untranslated
   question, which ran out of every budget.
   Pre: [model] is a model of [tr.formula].  Post: [Some m'] where [m'] holds
   every entry of [model] that is not the pass's own name nor an obsolete
   entry of a translated sequence variable, plus each translated sequence
   whose length is read as an integer in [0, max_read_back_length] and
   whose elements are all read, as its word; [None] when a length is not an
   integer numeral, is negative, or a short sequence's element cannot be
   read. *)
let read_back (tr : t) (model : model) : model option =
  let same_sort left right =
    phys_equal left right
    || Sexp.equal
         (Datatype.structural_sort_key left)
         (Datatype.structural_sort_key right)
  in
  let find x sort =
    List.find_map model ~f:(fun ((y, actual), v) ->
        if Ident.tvar_equal x y && same_sort sort actual then Some v else None)
  in
  let z_of t =
    try Some (T_int.let_int t)
    with exn_ when not (Common.Timer.is_async exn_) -> None
  in
  let seq_of b =
    match find b.len_var T_int.SInt with
    | None | Some None -> Some None
    | Some (Some lt) -> (
        match z_of lt with
        | None -> None
        | Some n when Z.(lt n zero) -> None
        | Some n when Z.(gt n (of_int max_read_back_length)) -> Some None
        | Some n -> (
            let n = Z.to_int n in
            let arr =
              match find b.arr_var (arr_sort b.elem_sort) with
              | Some (Some a) -> Some a
              | _ -> None
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
  | Some values -> (
      try
        let reconstructed =
          List.filter_map values ~f:(fun (b, v) ->
              Option.map v ~f:(fun v ->
                  ((b.seq_var, T_seq.mk_seq_sort b.elem_sort), Some v)))
        in
        let owned_keys =
          Set.to_list (Formula.term_sort_env_of tr.formula)
          |> List.filter ~f:(fun (x, _) -> Set.mem tr.own_vars x)
        in
        let owned_keys =
          owned_keys
          @ List.concat_map tr.bindings ~f:(fun b ->
              [ (b.arr_var, arr_sort b.elem_sort); (b.len_var, T_int.SInt) ])
        in
        (* A translated model can also assign the now-unused source symbol.
           That obsolete entry is not evidence about its original value,
           even when no length was supplied for reconstruction. Same-spelled
           symbols of other sorts stay. *)
        let rest =
          List.filter model ~f:(fun ((x, sort), _) ->
              (not
                 (List.exists owned_keys ~f:(fun (owned, expected) ->
                      Ident.tvar_equal x owned && same_sort sort expected)))
              && not
                   (List.exists tr.bindings ~f:(fun binding ->
                        Ident.tvar_equal x binding.seq_var
                        && same_sort sort (T_seq.mk_seq_sort binding.elem_sort))))
        in
        Some (rest @ reconstructed)
      with exn when not (Common.Timer.is_async exn) -> None)
