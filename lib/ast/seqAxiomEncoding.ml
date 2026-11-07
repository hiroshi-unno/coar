(* The sequence-free copy of a formula over SMT-LIB sequences, for a validity
   check that native sequences leave undecided.

   WHAT.  [encode phi] returns [phi] with every sequence sort [(Seq E)]
   replaced by a fresh uninterpreted sort, one per element sort, and every
   sequence operation by an uninterpreted function over it: [seq.len],
   [seq.nth], [seq.++], [seq.unit], [seq.empty], [seq.extract] and this tree's
   [seq.store].  Datatypes, arrays and tuples whose components mention a
   sequence get the same substitution in their components; a datatype that
   does is copied under a new name, so that the original stays as it is in
   every other query.  The caller asks the copy together with axioms about
   the new functions ([families] says which were introduced) and reads only an
   [unsat] of its negation.

   WHY THAT IS SOUND FOR VALIDITY, AND ONLY FOR VALIDITY.  Every model [M] of
   the negation of [phi] gives a model of the negation of the copy: interpret
   each new sort as [M]'s own sequences over that element sort, each new
   function as [M]'s operation, each copied datatype as its original.  The
   copy then evaluates exactly as [phi] does, by induction on the formula, and
   every axiom the caller adds holds, provided it is a theorem of the sequence
   theory (each one is checked against z3's native theory where the axioms are
   built).  So "the copy's negation with the axioms is unsatisfiable" implies
   "the negation of [phi] is unsatisfiable", i.e. [phi] is valid.  The converse
   fails: a model of the copy need not interpret the new sort as sequences at
   all (two different elements may have the same length and the same reads),
   so a satisfying assignment of the copy says nothing about [phi] and must
   never be used as a counterexample, an example or a refutation.

   The rewrite of concatenations to one association (and the removal of empty
   operands) is done on the way, because it is exact on sequences -- they form
   a monoid -- and it is what lets the copy relate [(a ++ b) ++ c] to
   [a ++ (b ++ c)] without an associativity axiom, which no sequence prelude of
   a deployed verifier states as a quantified fact (it loops under matching).

   WHAT IT DECLINES.  Anything it cannot translate faithfully: a sequence under
   a reference, an arrow or a polymorphic sort, a [Random] binder, a fixpoint,
   a recursive let, a datatype cycle through a copied datatype, or anything
   that raises.  A decline is [Error reason], and the caller then keeps the
   answer it had. *)
open Core
open Common.Ext
open Common.Combinator
open LogicOld

exception Decline of string

let decline fmt = Printf.ksprintf (fun s -> raise (Decline s)) fmt

type family = {
  elem : Sort.t;  (** the element sort, already translated *)
  seq_sort : Sort.t;  (** the uninterpreted sort standing for [(Seq elem)] *)
  len : Ident.tvar;
  nth : Ident.tvar;
  concat : Ident.tvar;
  unit_ : Ident.tvar;
  empty : Ident.tvar;
  extract : Ident.tvar;
  store : Ident.tvar;
}

(* Copying any member renames the whole declaration group, including
   siblings with no path back to its sequence-bearing member. Inspect every
   member so all occurrences of those siblings use the copied sorts too. *)
let mentions_seq_sort root =
  let module Groups = Stdlib.Hashtbl.Make (struct
    type t = Datatype.dt list
    let equal = phys_equal
    let hash (group : t) =
      match group with [] -> 0 | d :: _ -> String.hash d.Datatype.name
  end) in
  let groups = Groups.create 16 in
  let rec sort = function
    | T_seq.SSeq _ -> true
    | T_array.SArray (a, b) -> sort a || sort b
    | T_tuple.STuple ss | T_dt.SUS (_, ss) -> List.exists ss ~f:sort
    | T_ref.SRef s | Sort.SPoly (_, s) -> sort s
    | Sort.SArrow (arg, result) -> sort arg || sort result.val_type
    | T_dt.SDT dt ->
        let ds = Datatype.dts_of dt in
        if Groups.mem groups ds then false
        else (
          Groups.add groups ds ();
          (match Datatype.flag_of dt with Datatype.Alias s -> sort s | _ -> false)
          || List.exists ds ~f:(fun (d : Datatype.dt) ->
              List.exists d.params ~f:sort
              || List.exists d.conses ~f:(fun (c : Datatype.cons) ->
                  List.exists c.sels ~f:(function
                    | Datatype.Sel (_, s) -> sort s
                    | Datatype.InSel (_, _, ss) -> List.exists ss ~f:sort))))
    | _ -> false
  in
  sort root

(* Whether a formula mentions a sequence anywhere: a variable, a binder, a
   term's sort or a sequence operation.  The cheap test that decides whether
   the fallback applies at all. *)
let mentions_seq phi =
  Set.exists (Formula.term_sort_env_of phi) ~f:(snd >> mentions_seq_sort)
  || Set.exists (Formula.quantified_sort_env_of phi) ~f:(snd >> mentions_seq_sort)
  || Set.exists (Formula.funsyms_of phi) ~f:(function
       | T_seq.(
           ( SqEmpty _ | SqUnit _ | SqConcat _ | SqLen _ | SqNth _
           | SqExtract _ | SqStore _ )) ->
           true
       | _ -> false)

let suffix = "#seqax"

(* One translation, with its own family table and datatype copies. *)
let encode_exn ?(context = []) ?(sorts = []) phi =
  (* Generated declarations share the solver's symbol tables with the input
     and its defining context. Reserve those names before allocating any. *)
  let reserved = ref Set.Poly.empty in
  let reserve name = reserved := Set.add !reserved name in
  let seen_sorts = ref Set.Poly.empty in
  let rec reserve_sort s =
    if not (Set.mem !seen_sorts s) then (
      seen_sorts := Set.add !seen_sorts s;
      match s with
      | T_dt.SUS (name, params) ->
          reserve name;
          List.iter params ~f:reserve_sort
      | T_dt.SDT dt ->
          reserve dt.Datatype.name;
          List.iter dt.Datatype.dts ~f:(fun (d : Datatype.dt) ->
              reserve d.name;
              List.iter d.params ~f:reserve_sort;
              List.iter d.conses ~f:(fun (c : Datatype.cons) ->
                  reserve c.name;
                  List.iter c.sels ~f:(function
                    | Datatype.Sel (name, s) -> reserve name; reserve_sort s
                    | Datatype.InSel (name, ret, params) ->
                        reserve name; reserve ret;
                        List.iter params ~f:reserve_sort)))
      | T_seq.SSeq s | T_ref.SRef s | Sort.SPoly (_, s) -> reserve_sort s
      | T_array.SArray (a, b) -> reserve_sort a; reserve_sort b
      | T_tuple.STuple ss -> List.iter ss ~f:reserve_sort
      | Sort.SArrow (arg, result) ->
          reserve_sort arg; reserve_sort result.val_type
      | _ -> ())
  in
  let module Seen = Stdlib.Hashtbl.Make (struct
    type t = Term.t
    let equal = phys_equal
    let hash = Common.Ext.Hashtbl.phys_hash
  end) in
  let seen_terms = Seen.create 128 in
  let rec reserve_term t =
    if not (Seen.mem seen_terms t) then (
      Seen.add seen_terms t ();
      reserve_sort (Term.sort_of t);
      match t with
      | Term.Var _ -> ()
      | Term.FunApp (fsym, args, _) ->
          (match fsym with
           | FVar (_, args, ret) -> List.iter (ret :: args) ~f:reserve_sort
           | T_bool.Formula phi -> reserve_formula phi
           | T_array.ALambda ((_, index), _) -> reserve_sort index
           | _ -> ());
          List.iter args ~f:reserve_term
      | Term.LetTerm (_, s, def, body, _) ->
          reserve_sort s; reserve_term def; reserve_term body)
  and reserve_formula phi =
    Set.iter (Formula.names_spelled_in phi)
      ~f:(fun v -> reserve (Ident.name_of_tvar v));
    Set.iter (Formula.quantified_sort_env_of phi) ~f:(snd >> reserve_sort);
    Set.iter (Formula.sort_env_of phi) ~f:(snd >> reserve_sort);
    Set.iter (Formula.terms_of phi) ~f:reserve_term
  in
  List.iter (phi :: context) ~f:reserve_formula;
  List.iter sorts ~f:reserve_sort;
  let allocate candidates =
    let rec choose n =
      let names = candidates n in
      if List.exists names ~f:(Set.mem !reserved) then choose (n + 1)
      else (List.iter names ~f:reserve; n)
    in
    choose 0
  in
  let families : (Sort.t * family) list ref = ref [] in
  let copies : (string * Datatype.t) list ref = ref [] in
  let originals : (string * Datatype.t) list ref = ref [] in
  let group_suffixes = ref [] in
  let in_progress : string list ref = ref [] in
  let family_of elem =
    match
      List.find !families ~f:(fun (e, _) -> Stdlib.( = ) e elem)
    with
    | Some (_, fam) -> fam
    | None ->
        let base = sprintf "%s#%d" (Term.str_of_sort elem) (List.length !families) in
        let key n = if n = 0 then base else sprintf "%s#%d" base n in
        let ops = [ "len"; "nth"; "concat"; "unit"; "empty"; "extract"; "store" ] in
        let chosen = allocate (fun n ->
            ("seqax!" ^ key n)
            :: List.map ops ~f:(fun op -> sprintf "seqax!%s!%s" op (key n))) in
        let key = key chosen in
        let name op = Ident.Tvar (sprintf "seqax!%s!%s" op key) in
        let fam =
          {
            elem;
            seq_sort = T_dt.SUS ("seqax!" ^ key, []);
            len = name "len";
            nth = name "nth";
            concat = name "concat";
            unit_ = name "unit";
            empty = name "empty";
            extract = name "extract";
            store = name "store";
          }
        in
        families := !families @ [ (elem, fam) ];
        fam
  in
  let rec sort s =
    if not (mentions_seq_sort s) then s
    else
      match s with
      | T_seq.SSeq se -> (family_of (sort se)).seq_sort
      | T_array.SArray (si, se) -> T_array.SArray (sort si, sort se)
      | T_tuple.STuple ss -> T_tuple.STuple (List.map ss ~f:sort)
      | T_dt.SUS (name, ps) -> T_dt.SUS (name, List.map ps ~f:sort)
      | T_dt.SDT dt -> T_dt.SDT (copy_dt dt)
      | s -> decline "a sequence under the sort %s" (Term.str_of_sort s)
  and copy_dt (dt : Datatype.t) =
    let key = Datatype.instance_key dt in
    match List.Assoc.find !copies key ~equal:String.equal with
    | Some c ->
        (match List.Assoc.find !originals key ~equal:String.equal with
         | Some original when Stdlib.compare original dt = 0 -> c
         | _ -> decline "conflicting datatype definition for %s" (Datatype.name_of dt))
    | None ->
        if List.mem !in_progress key ~equal:String.equal then
          decline "a datatype cycle through %s" key;
        in_progress := key :: !in_progress;
        (match Datatype.flag_of dt with
        | Datatype.FDt -> ()
        | _ -> decline "a sequence inside the non-inductive datatype %s" key);
        let group = List.map (Datatype.dts_of dt) ~f:Datatype.name_of_dt in
        let group_key = (dt.Datatype.flag, dt.Datatype.dts) in
        let chosen_suffix =
          match List.Assoc.find !group_suffixes group_key
              ~equal:(fun a b -> Stdlib.compare a b = 0) with
          | Some chosen -> chosen
          | None ->
              let copy_suffix n = if n = 0 then suffix else sprintf "%s#%d" suffix n in
              let chosen = allocate (fun n ->
                  List.map group ~f:(fun name -> name ^ copy_suffix n)) in
              let chosen = copy_suffix chosen in
              (* Every root view of this complete instantiated group must
                 use the same renamed sibling sorts. *)
              group_suffixes := (group_key, chosen) :: !group_suffixes;
              chosen
        in
        let rename name = name ^ chosen_suffix in
        let copy_sel = function
          | Datatype.Sel (n, s) -> Datatype.Sel (n, sort s)
          | Datatype.InSel (n, ret, ps) ->
              if List.mem group ret ~equal:String.equal then
                Datatype.InSel (n, rename ret, List.map ps ~f:sort)
              else decline "a recursive selector of %s outside its group" key
        in
        let copy =
          {
            Datatype.name = rename dt.Datatype.name;
            flag = dt.Datatype.flag;
            dts =
              List.map dt.Datatype.dts ~f:(fun (d : Datatype.dt) ->
                  {
                    Datatype.name = rename d.Datatype.name;
                    params = List.map d.Datatype.params ~f:sort;
                    conses =
                      List.map d.Datatype.conses ~f:(fun (c : Datatype.cons) ->
                          {
                            Datatype.name = c.Datatype.name;
                            sels = List.map c.Datatype.sels ~f:copy_sel;
                          });
                  });
          }
        in
        in_progress := List.tl_exn !in_progress;
        originals := (key, dt) :: !originals;
        copies := (key, copy) :: !copies;
        copy
  in
  let fvar v sargs sret args = Term.mk_fsym_app (FVar (v, sargs, sret)) args in
  (* [a ++ b ++ ...] as one left-nested chain without empty operands: exact on
     sequences, which are a monoid *)
  let rec concat_operands = function
    | Term.FunApp (T_seq.SqConcat _, [ a; b ], _) ->
        concat_operands a @ concat_operands b
    | Term.FunApp (T_seq.SqEmpty _, [], _) -> []
    | t -> [ t ]
  in
  let rec term t =
    match t with
    | Term.Var (x, s, _) -> Term.mk_var x (sort s)
    | Term.LetTerm (x, s, def, body, _) ->
        Term.mk_let_term x (sort s) (term def) (term body)
    | Term.FunApp (T_seq.SqConcat se, _, _) -> (
        let fam = family_of (sort se) in
        match List.map (concat_operands t) ~f:term with
        | [] -> fvar fam.empty [] fam.seq_sort []
        | first :: rest ->
            List.fold rest ~init:first ~f:(fun acc u ->
                fvar fam.concat [ fam.seq_sort; fam.seq_sort ] fam.seq_sort
                  [ acc; u ]))
    | Term.FunApp (fsym, args, _) -> (
        let args = List.map args ~f:term in
        let fam se = family_of (sort se) in
        match (fsym, args) with
        | T_seq.SqEmpty se, [] ->
            let f = fam se in
            fvar f.empty [] f.seq_sort []
        | T_seq.SqUnit se, [ x ] ->
            let f = fam se in
            fvar f.unit_ [ f.elem ] f.seq_sort [ x ]
        | T_seq.SqLen se, [ a ] ->
            let f = fam se in
            fvar f.len [ f.seq_sort ] T_int.SInt [ a ]
        | T_seq.SqNth se, [ a; i ] ->
            let f = fam se in
            fvar f.nth [ f.seq_sort; T_int.SInt ] f.elem [ a; i ]
        | T_seq.SqExtract se, [ a; o; n ] ->
            let f = fam se in
            fvar f.extract
              [ f.seq_sort; T_int.SInt; T_int.SInt ]
              f.seq_sort [ a; o; n ]
        | T_seq.SqStore se, [ a; i; v ] ->
            let f = fam se in
            fvar f.store [ f.seq_sort; T_int.SInt; f.elem ] f.seq_sort
              [ a; i; v ]
        | T_seq.(
            ( SqEmpty _ | SqUnit _ | SqConcat _ | SqLen _ | SqNth _
            | SqExtract _ | SqStore _ )),
          _ ->
            decline "a sequence operation at the wrong arity"
        | T_bool.Formula phi, [] -> T_bool.of_formula (formula phi)
        | FVar (v, sargs, sret), _ ->
            fvar v (List.map sargs ~f:sort) (sort sret) args
        | T_array.AConst (si, se), _ ->
            Term.mk_fsym_app (T_array.AConst (sort si, sort se)) args
        | T_array.AStore (si, se), _ ->
            Term.mk_fsym_app (T_array.AStore (sort si, sort se)) args
        | T_array.ASelect (si, se), _ ->
            Term.mk_fsym_app (T_array.ASelect (sort si, sort se)) args
        | T_array.ALambda ((x, si), se), _ ->
            Term.mk_fsym_app (T_array.ALambda ((x, sort si), sort se)) args
        | T_tuple.TupleCons ss, _ ->
            Term.mk_fsym_app (T_tuple.TupleCons (List.map ss ~f:sort)) args
        | T_tuple.TupleSel (ss, i), _ ->
            Term.mk_fsym_app (T_tuple.TupleSel (List.map ss ~f:sort, i)) args
        | T_dt.DTCons (n, ss, dt), _ ->
            Term.mk_fsym_app
              (T_dt.DTCons (n, List.map ss ~f:sort, dt_of dt))
              args
        | T_dt.DTSel (n, dt, s), _ ->
            Term.mk_fsym_app (T_dt.DTSel (n, dt_of dt, sort s)) args
        | T_ref.(Ref s | Deref s | Update s), _ when mentions_seq_sort s ->
            decline "a sequence under a reference"
        | fsym, _ -> Term.mk_fsym_app fsym args)
  and dt_of dt =
    match sort (T_dt.SDT dt) with T_dt.SDT dt -> dt | _ -> assert false
  and atom = function
    | Atom.True _ | Atom.False _ as a -> a
    | Atom.App (pred, args, _) ->
        let args = List.map args ~f:term in
        let pred =
          match pred with
          | Predicate.Var (p, ss) -> Predicate.Var (p, List.map ss ~f:sort)
          | Predicate.Psym (T_tuple.IsTuple ss) ->
              Predicate.Psym (T_tuple.IsTuple (List.map ss ~f:sort))
          | Predicate.Psym (T_tuple.NotIsTuple ss) ->
              Predicate.Psym (T_tuple.NotIsTuple (List.map ss ~f:sort))
          | Predicate.Psym (T_dt.IsCons (n, dt)) ->
              Predicate.Psym (T_dt.IsCons (n, dt_of dt))
          | Predicate.Psym (T_dt.NotIsCons (n, dt)) ->
              Predicate.Psym (T_dt.NotIsCons (n, dt_of dt))
          | Predicate.Psym _ as p -> p
          | Predicate.Fixpoint _ -> decline "a fixpoint predicate"
        in
        Atom.mk_app pred args
  and formula phi =
    match phi with
    | Formula.Atom (a, _) -> Formula.mk_atom (atom a)
    | Formula.UnaryOp (op, p, _) -> Formula.mk_unop op (formula p)
    | Formula.BinaryOp (op, p1, p2, _) ->
        Formula.mk_binop op (formula p1) (formula p2)
    | Formula.Bind (Formula.Random _, _, _, _) -> decline "a random binder"
    | Formula.Bind (b, bounds, body, _) ->
        Formula.mk_bind b
          (List.map bounds ~f:(fun (x, s) -> (x, sort s)))
          (formula body)
    | Formula.LetRec ([], body, _) -> formula body
    | Formula.LetRec (_, _, _) -> decline "a recursive let"
    | Formula.LetFormula (x, s, def, body, _) ->
        Formula.mk_let_formula x (sort s) (term def) (formula body)
  in
  let phi' = formula phi in
  (* Nothing sequence-sorted may survive: a symbol whose sort parameter this
     function does not know would keep one, and asking such a copy would mix
     the two theories.  Declining is the answer then, not a guess. *)
  if mentions_seq phi' then decline "a sequence survived the translation";
  (phi', List.map !families ~f:snd, List.map !copies ~f:snd)

let encode ?context ?sorts phi =
  match encode_exn ?context ?sorts phi with
  | r -> Ok r
  | exception Decline reason -> Error reason
  | exception exn_ when not (Common.Timer.is_async exn_) ->
      Error ("the translation raised " ^ Exn.to_string exn_)
