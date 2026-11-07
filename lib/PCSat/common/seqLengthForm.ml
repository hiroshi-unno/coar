open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* A validity question over free sequence variables, asked over lengths and
   arrays instead of sequences.

   Why.  Z3's sequence solver builds a model of a sequence variable one
   element at a time, so a satisfiable query that forces a long sequence does
   not come back: [(assert (> (seq.len d) 1000))] over a free [d : Seq Int]
   runs past 30 s (Z3 4.13.3, 4.15.2 and 5.1.0 alike; [> 100] takes about
   5 s, [= 2000] does not return either), and its memory grows meanwhile.
   Z3's own [timeout] does not bound it (2000 ms returned after 7 s).  A
   truth table's cell at an example whose sequence argument is a parameter
   is such a question when the qualifier compares that sequence's length or a
   read of it with a large integer the counterexample model put beside it
   ([0 <= 13705 - seq.len (d ++ [0] ++ [0])] asked valid: its negation needs
   [len d >= 13704]).  cvc5 answers the same query at once.

   The same holds of a sequence equality whose countermodel must be long: a
   cell whose two arguments are suffixes of one free sequence at constant
   offsets asks [seq.extract d 12279 (len d - 12279) = seq.extract d 24388
   (len d - 24388)] valid; its negation needs [len d > 12279], and Z3 5.1.0
   asked it without a budget grew past 6 GB in about 100 s, and a 2 s budget
   that holds when the query is replayed alone was ignored in one run of two
   inside a long-lived solving process.

   What.  [decide ~ask phi] translates [phi] when every sequence-sorted term
   in it is a concatenation of pieces -- free sequence variables, units,
   empties, and [seq.extract d i n] of a free variable [d] -- occurring
   directly under [seq.len] or [seq.nth] or as a side of an equality that
   occurs only positively (a disequality only negatively), and [phi] has no
   binder.  A variable [d] of sort [Seq E] becomes a length [l_d >= 0] and an
   array [A_d : Int -> E]; [seq.extract d i n] becomes the slice of [A_d]
   from [i] of length [ite (0 <= i < l_d /\ 0 < n) (min n (l_d - i)) 0],
   which is SMT-LIB's [str.substr] rule (empty unless the offset is in range
   and the count positive, else as much as remains); [seq.len t] becomes the
   sum of its pieces' lengths (1 for a unit); [seq.nth t i] becomes the value
   of the piece holding index [i] ([A_d[base + i - off]] or the unit's
   element) when [i] is in range, and a fresh variable of sort [E] (one per
   occurrence) otherwise.  An equality [t1 = t2] becomes
   [L1 = L2 /\ (0 <= j < L1 -> t1[j] = t2[j])] with [j] a fresh integer (one
   per occurrence) and [t[j]] the in-range read as above.  The equality is
   [forall j] of that; at a positive occurrence the universal moves to the
   front of [phi] (no other part mentions [j]), and a validity question is
   the same with [j] free, so the free [j] is exact there and only there: a
   negative occurrence would need an existential under the negation the
   questions below ask, and is refused.
   Then, with [phi'] the translation:
   - [ask [not phi' /\ l >= 0]] unsatisfiable: [phi] is valid.  Every model
     and assignment falsifying [phi] gives one of [not phi'] (the lengths, the
     reads, each out-of-range read's value for its fresh variable), so none
     exists.
   - otherwise, [ask [not phi' /\ l >= 0 /\ every read in range]]
     satisfiable (asked only when [phi] has a read; with none the first
     question is this one): [phi] is invalid.  The sequences
     [d := A_d[0 .. l_d - 1]] give every length and every read the value the
     model gave its translation, and no out-of-range read is consulted, so
     the model falsifies [phi] itself.
   Anything else, and any formula outside the fragment, returns [None] and
   the caller asks the question as it would have.  So the answer, when there
   is one, is the answer to the same question; what changes is that the
   solver is asked about integers and arrays, whose models it builds at once.

   [ask] is a satisfiability check returning [`Sat], [`Unsat] or anything
   else (undecided). *)

exception Refuse

let is_seq_sort s = match s with T_seq.SSeq _ -> true | _ -> false

(* [PArr (len, arr, elem, base)]: the elements [arr[base]] .. [arr[base +
   len - 1]], a free variable ([base] 0) or a slice of one *)
type piece = PArr of Term.t * Term.t * Sort.t * Term.t
           | PUnit of Term.t

type polarity = Pos | Neg | Both

let flip = function Pos -> Neg | Neg -> Pos | Both -> Both

(* the free sequence variables of [phi] *)
let has_free_seq_var phi =
  Set.exists (Formula.term_sort_env_of phi) ~f:(fun (_, s) -> is_seq_sort s)

let translate phi =
  let vars = Hashtbl.Poly.create () in
  let lens = ref [] in
  let reads = ref [] in
  let oor = ref 0 in
  let fresh_oor elem =
    incr oor;
    Term.mk_var (Ident.Tvar (sprintf "#sqlf_oor_%d" !oor)) elem
  in
  let idx = ref 0 in
  let var_of x elem =
    match Hashtbl.Poly.find vars x with
    | Some v -> v
    | None ->
        let (Ident.Tvar n) = x in
        let l = Term.mk_var (Ident.Tvar ("#sqlf_len_" ^ n)) T_int.SInt in
        let asort = T_array.mk_array_sort T_int.SInt elem in
        let a = Term.mk_var (Ident.Tvar ("#sqlf_arr_" ^ n)) asort in
        Hashtbl.Poly.set vars ~key:x ~data:(l, a);
        lens := l :: !lens;
        (l, a)
  in
  let rec term t =
    match t with
    | Term.Var (_, s, _) -> if is_seq_sort s then raise Refuse else t
    | Term.FunApp (T_seq.SqLen _, [ s ], _) ->
        List.fold (pieces s) ~init:(T_int.zero ()) ~f:(fun acc p ->
            T_int.mk_add acc (len_of p))
    | Term.FunApp (T_seq.SqNth _, [ s; i ], _) ->
        let elem = Term.sort_of t in
        let i = term i in
        let total, v = read_at (pieces s) elem i in
        reads :=
          Formula.and_of [ Formula.leq (T_int.zero ()) i; Formula.lt i total ]
          :: !reads;
        v
    | Term.FunApp (T_bool.Formula phi, [], info) ->
        Term.mk_fsym_app ~info (T_bool.Formula (formula Both phi)) []
    | Term.FunApp (T_array.ALambda _, _, _) -> raise Refuse
    | Term.FunApp (sym, args, info) ->
        if is_seq_sort (Term.sort_of t) then raise Refuse
        else Term.mk_fsym_app ~info sym (List.map args ~f:term)
    | Term.LetTerm _ -> raise Refuse
  (* the total length of [ps], and the element at [i]: the piece holding it
     when [0 <= i < total], a fresh variable of sort [elem] otherwise *)
  and read_at ps elem i =
    let total, branches =
      List.fold ps ~init:(T_int.zero (), []) ~f:(fun (off, acc) p ->
          let len = len_of p in
          let next = T_int.mk_add off len in
          let b =
            match p with
            | PArr (_, a, e, base) ->
                ( Formula.and_of [ Formula.leq off i; Formula.lt i next ],
                  T_array.mk_select T_int.SInt e a
                    (T_int.mk_add base (T_int.mk_sub i off)) )
            | PUnit v -> (Formula.eq i off, v)
          in
          (next, b :: acc))
    in
    (* branches are in reverse order; the default is the out-of-range
       value *)
    ( total,
      List.fold branches ~init:(fresh_oor elem) ~f:(fun acc (c, v) ->
          T_bool.ifte c v acc) )
  and len_of = function PArr (l, _, _, _) -> l | PUnit _ -> T_int.one ()
  and pieces s =
    match s with
    | Term.Var (x, T_seq.SSeq e, _) ->
        let l, a = var_of x e in
        [ PArr (l, a, e, T_int.zero ()) ]
    | Term.FunApp
        (T_seq.SqExtract _, [ (Term.Var (x, T_seq.SSeq e, _)); i; n ], _) ->
        let l, a = var_of x e in
        let i = term i and n = term n in
        let in_range =
          Formula.and_of
            [
              Formula.leq (T_int.zero ()) i;
              Formula.lt i l;
              Formula.lt (T_int.zero ()) n;
            ]
        in
        let len =
          T_bool.ifte in_range (T_int.mk_min n (T_int.mk_sub l i)) (T_int.zero ())
        in
        [ PArr (len, a, e, i) ]
    | Term.FunApp (T_seq.SqEmpty _, [], _) -> []
    | Term.FunApp (T_seq.SqUnit _, [ v ], _) -> [ PUnit (term v) ]
    | Term.FunApp (T_seq.SqConcat _, [ a; b ], _) -> pieces a @ pieces b
    | _ -> raise Refuse
  (* [t1 = t2] over sequences, at a positive occurrence (see the header) *)
  and seq_eq t1 t2 =
    match Term.sort_of t1 with
    | T_seq.SSeq elem ->
        incr idx;
        let j = Term.mk_var (Ident.Tvar (sprintf "#sqlf_idx_%d" !idx)) T_int.SInt in
        let l1, v1 = read_at (pieces t1) elem j in
        let l2, v2 = read_at (pieces t2) elem j in
        Formula.and_of
          [
            Formula.eq l1 l2;
            Formula.mk_imply
              (Formula.and_of [ Formula.leq (T_int.zero ()) j; Formula.lt j l1 ])
              (Formula.eq v1 v2);
          ]
    | _ -> raise Refuse
  and formula pol phi =
    match phi with
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
      when is_seq_sort (Term.sort_of t1) -> (
        match pol with Pos -> seq_eq t1 t2 | Neg | Both -> raise Refuse)
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _)
      when is_seq_sort (Term.sort_of t1) -> (
        match pol with
        | Neg -> Formula.mk_neg (seq_eq t1 t2)
        | Pos | Both -> raise Refuse)
    | Formula.Atom (Atom.App (pred, args, ainfo), info) ->
        Formula.mk_atom ~info (Atom.mk_app ~info:ainfo pred (List.map args ~f:term))
    | Formula.Atom (_, _) -> phi
    | Formula.UnaryOp (op, p, info) ->
        Formula.mk_unop ~info op (formula (flip pol) p)
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, info) ->
        Formula.mk_binop ~info op (formula pol p) (formula pol q)
    | Formula.BinaryOp (Formula.Imply, p, q, info) ->
        Formula.mk_binop ~info Formula.Imply (formula (flip pol) p) (formula pol q)
    | Formula.BinaryOp (((Formula.Iff | Formula.Xor) as op), p, q, info) ->
        Formula.mk_binop ~info op (formula Both p) (formula Both q)
    | Formula.Bind _ | Formula.LetRec _ | Formula.LetFormula _ -> raise Refuse
  in
  match formula Pos phi with
  | phi' ->
      let nonneg =
        List.map !lens ~f:(fun l -> Formula.leq (T_int.zero ()) l)
      in
      Some (phi', nonneg, List.rev !reads)
  | exception Refuse -> None

(* see the header; [None] when not in the fragment or not decided *)
let decide ~ask phi =
  if not (has_free_seq_var phi) then None
  else
    match translate phi with
    | None -> None
    | Some (phi', nonneg, reads) -> (
        let neg = Formula.mk_neg phi' in
        match ask (neg :: nonneg) with
        | `Unsat -> Some true
        | `Sat when List.is_empty reads -> Some false
        | `Sat -> (
            match ask ((neg :: nonneg) @ reads) with
            | `Sat -> Some false
            | _ -> None)
        | _ -> None)

(* The switch, set from [PCSat.Config.simplifier.truth_table_seq_length_form] (on by
   default there); off here so that a process that reads no PCSat
   configuration asks as before. *)
let enabled = Atomic.make false

(* [decide] with Z3 as [ask] (no budget beyond [timeout], milliseconds) *)
let decide_z3 ?(timeout = None) ~id fenv phi =
  decide phi ~ask:(fun phis ->
      match Z3Smt.Z3interface.check_sat ~timeout ~id fenv phis with
      | `Unsat -> `Unsat
      | `Sat _ -> `Sat
      | _ -> `Other)
