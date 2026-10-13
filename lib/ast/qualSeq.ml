open Core
open Common.Ext
open LogicOld

(* Terms and qualifiers over SMT-LIB sequences, the counterpart of the array
   module beside this one.  Nothing here knows about traces ([T_trace]): that is
   a different theory, of words over abstract symbols, with no length and no
   indexing.

   What a sequence contributes to the hypothesis space is not a predicate of its
   own but two families of TERMS: its length, which is an integer and therefore
   feeds every integer qualifier the space already builds, and its elements at
   the index terms in scope.  A loop over a slice wants exactly those -- the
   invariants such a program needs compare an index with a length and an element
   with a value. *)
let update_term_map ?(depth = 0) sort
    (terms : (Term.t * Formula.t list) Set.Poly.t)
    (term_map : (Sort.t, (Term.t * Formula.t list) Set.Poly.t) Map.Poly.t) =
  if depth = 0 || Set.length terms > 1000 then term_map
  else
    match sort with
    | T_seq.SSeq se ->
        let int_terms =
          match Map.Poly.find term_map T_int.SInt with
          | Some ts -> ts
          | None -> Set.Poly.empty
        in
        (* the length of each sequence in scope, as an integer term *)
        let len_terms =
          Set.union int_terms
          @@ Set.Poly.map terms ~f:(fun (t, conds) ->
              (T_seq.mk_len se t, conds))
        in
        (* each sequence read at each index term in scope.  The index is not
           guarded here: an out-of-range read is a value the theory leaves open
           rather than an error, and a qualifier that mentions one is merely
           uninformative. *)
        let nth_terms =
          let se_terms =
            match Map.Poly.find term_map se with
            | Some ts -> ts
            | None -> Set.Poly.empty
          in
          Set.union se_terms
          @@ Set.fold terms ~init:Set.Poly.empty ~f:(fun ret (t, conds) ->
              Set.union ret
              @@ Set.Poly.map int_terms ~f:(fun (i, conds1) ->
                  (T_seq.mk_nth se t i, conds @ conds1)))
        in
        (* the SUFFIX of each sequence from each index term in scope.  Not
           every (offset, length) pair: that is quadratic in the integer terms,
           and the relation a loop over a slice needs is exactly the suffix --
           "what is left to process is the original from here on", which is how
           such an invariant is written and how a front end encodes
           subsequence(i, len). *)
        let extract_terms =
          (* from the ARGUMENTS only, on both sides.  Taking the suffix of a
             derived sequence, or at a derived index, multiplies with the term
             map's depth and buys nothing: the relation an invariant of this
             shape states is between two arguments of the predicate, "what is
             left is the original from this argument on". *)
          let var_terms = Set.filter terms ~f:(fun (t, _) -> Term.is_var t) in
          let var_ints =
            Set.filter int_terms ~f:(fun (t, _) -> Term.is_var t)
          in
          Set.union terms
          @@ Set.fold var_terms ~init:Set.Poly.empty ~f:(fun ret (t, conds) ->
              Set.union ret
              @@ Set.Poly.map var_ints ~f:(fun (i, conds1) ->
                  ( T_seq.mk_extract se t i (T_int.mk_sub (T_seq.mk_len se t) i),
                    conds @ conds1 )))
        in
        (* The three families go to three keys, and two of those keys are the
           SAME whenever the element sort is Int -- which is the common case, a
           sequence of integers.  Writing them one after another then made the
           later write drop the earlier, and since each family was built from the
           map as it stood BEFORE any of them, the lengths were simply lost: a
           [Seq Int] contributed [seq.nth s i] and no [seq.len s], while a
           [Seq Real] kept its length because its element sort is a different
           key.  They are unioned into their destinations instead, so a
           coincidence of sorts adds rather than replaces. *)
        List.fold
          [ (T_int.SInt, len_terms); (se, nth_terms); (sort, extract_terms) ]
          ~init:term_map
          ~f:(fun acc (key, data) ->
            Map.Poly.update acc key ~f:(function
              | None -> data
              | Some old -> Set.union old data))
    | _ -> term_map

(* Sequences themselves are compared only by equality: a sequence has no order
   the theory fixes, and the relation these programs need between two of them --
   one is a subsequence of the other from an index on -- is not a qualifier over
   the two arguments but a statement with an index in it, which belongs to a
   template rather than here. *)
let qualifiers_of sort (terms : (Term.t * Formula.t list) Set.Poly.t) =
  match sort with
  | T_seq.SSeq _ ->
      (* equalities over ALL the sequence terms, not only the variables among
         them.  The relation these invariants need is between an argument and a
         DERIVED sequence -- "s is what is left of slice from i on" -- so
         restricting to variables, which is what the array module beside this
         one does, would leave exactly the useful equation out. *)
      Set.Poly.of_list @@ Formula.eqs @@ Set.to_list
      @@ Set.Poly.map terms ~f:fst
  | _ -> Set.Poly.empty
