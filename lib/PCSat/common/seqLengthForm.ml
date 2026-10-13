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

   What.  [decide ~ask phi] translates [phi] when every sequence-sorted term
   in it is a concatenation of free sequence variables, units and empties
   occurring directly under [seq.len] or [seq.nth], and [phi] has no binder.
   A variable [d] of sort [Seq E] becomes a length [l_d >= 0] and an array
   [A_d : Int -> E]; [seq.len t] becomes the sum of its pieces' lengths
   ([l_d], or 1 for a unit); [seq.nth t i] becomes the value of the piece
   holding index [i] ([A_d[i - off]] or the unit's element) when [i] is in
   range, and a fresh variable of sort [E] (one per occurrence) otherwise.
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

type piece = PVar of Term.t (* length *) * Term.t (* array *) * Sort.t
           | PUnit of Term.t

(* the free sequence variables of [phi] *)
let has_free_seq_var phi =
  Set.exists (Formula.term_sort_env_of phi) ~f:(fun (_, s) -> is_seq_sort s)

let translate phi =
  let vars = Hashtbl.Poly.create () in
  let lens = ref [] in
  let reads = ref [] in
  let oor = ref 0 in
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
        let ps = pieces s in
        let total, branches =
          List.fold ps ~init:(T_int.zero (), []) ~f:(fun (off, acc) p ->
              let len = len_of p in
              let next = T_int.mk_add off len in
              let b =
                match p with
                | PVar (_, a, e) ->
                    ( Formula.and_of
                        [
                          Formula.leq off i;
                          Formula.lt i next;
                        ],
                      T_array.mk_select T_int.SInt e a (T_int.mk_sub i off) )
                | PUnit v -> (Formula.eq i off, v)
              in
              (next, b :: acc))
        in
        incr oor;
        let o = Term.mk_var (Ident.Tvar (sprintf "#sqlf_oor_%d" !oor)) elem in
        reads :=
          Formula.and_of [ Formula.leq (T_int.zero ()) i; Formula.lt i total ]
          :: !reads;
        (* branches are in reverse order; the default is the out-of-range
           value *)
        List.fold branches ~init:o ~f:(fun acc (c, v) -> T_bool.ifte c v acc)
    | Term.FunApp (T_bool.Formula phi, [], info) ->
        Term.mk_fsym_app ~info (T_bool.Formula (formula phi)) []
    | Term.FunApp (T_array.ALambda _, _, _) -> raise Refuse
    | Term.FunApp (sym, args, info) ->
        if is_seq_sort (Term.sort_of t) then raise Refuse
        else Term.mk_fsym_app ~info sym (List.map args ~f:term)
    | Term.LetTerm _ -> raise Refuse
  and len_of = function PVar (l, _, _) -> l | PUnit _ -> T_int.one ()
  and pieces s =
    match s with
    | Term.Var (x, T_seq.SSeq e, _) ->
        let l, a = var_of x e in
        [ PVar (l, a, e) ]
    | Term.FunApp (T_seq.SqEmpty _, [], _) -> []
    | Term.FunApp (T_seq.SqUnit _, [ v ], _) -> [ PUnit (term v) ]
    | Term.FunApp (T_seq.SqConcat _, [ a; b ], _) -> pieces a @ pieces b
    | _ -> raise Refuse
  and formula phi =
    match phi with
    | Formula.Atom (Atom.App (pred, args, ainfo), info) ->
        Formula.mk_atom ~info (Atom.mk_app ~info:ainfo pred (List.map args ~f:term))
    | Formula.Atom (_, _) -> phi
    | Formula.UnaryOp (op, p, info) -> Formula.mk_unop ~info op (formula p)
    | Formula.BinaryOp (op, p, q, info) ->
        Formula.mk_binop ~info op (formula p) (formula q)
    | Formula.Bind _ | Formula.LetRec _ | Formula.LetFormula _ -> raise Refuse
  in
  match formula phi with
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

(* The switch, set from [PCSat.Config.truth_table_seq_length_form] (on by
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
