(* A clause asked by its pieces: the conjuncts of its negation normal form,
   with a disjunction distributed over its disjuncts' pieces within a bound.
   Shared by the zero-unknown verdict and the validator, so it lives here. *)

open Core
open Ast.LogicOld

let max_pieces = 64

(* linear in the operands, unlike appending at every node, which a chain
   nested to the left made quadratic in its length *)
let conjuncts = Formula.conjuncts_list_of
let disjuncts = Formula.disjuncts_list_of

(* A conjunction's pieces are its conjuncts' pieces, kept whole past
   [max_pieces].  A disjunction [d1 \/ ... \/ dm] is distributed over the
   pieces of as many disjuncts as the bound allows, those with the most
   pieces first, and every other disjunct stays whole in each piece: with
   [D] the distributed disjuncts and [K] the kept ones,
   [\/ D \/ \/ K <=> /\ (over one piece chosen from each d in D) (\/ chosen
   \/ \/ K)], which is distribution of [\/] over [/\] and exact.  Choosing
   rather than distributing all or nothing is what reaches a clause's head:
   in disjunctive form a clause [b1 /\ (p \/ q) /\ ... => c1 /\ ... /\ c5]
   is [... \/ (not p /\ not q) \/ ... \/ (c1 /\ ... /\ c5)], and there,
   on the Creusot-form [Skip], the premise's case splits alone took the
   product past the bound, so an all-or-nothing split left the head joined.
   Each piece keeps the disjuncts in their original order. *)
let rec pieces ?(max = max_pieces) phi =
  match phi with
  | Formula.BinaryOp (Formula.And, _, _, _) ->
      let ps = List.concat_map (conjuncts phi) ~f:(pieces ~max) in
      if List.length ps <= max then ps else [ phi ]
  | Formula.BinaryOp (Formula.Or, _, _, _) ->
      let ds =
        List.mapi (disjuncts phi) ~f:(fun i d -> (i, d, pieces ~max d))
      in
      let by_size =
        List.stable_sort ds ~compare:(fun (_, _, a) (_, _, b) ->
            Int.compare (List.length b) (List.length a))
      in
      let chosen, _ =
        List.fold by_size ~init:(Set.empty (module Int), 1)
          ~f:(fun (chosen, product) (i, _, ps) ->
            let n = List.length ps in
            if n > 1 && product * n <= max then
              (Set.add chosen i, product * n)
            else (chosen, product))
      in
      if Set.is_empty chosen then [ phi ]
      else
        List.fold_right ds ~init:[ [] ] ~f:(fun (i, d, ps) acc ->
            let options = if Set.mem chosen i then ps else [ d ] in
            List.concat_map options ~f:(fun o ->
                List.map acc ~f:(fun rest -> o :: rest)))
        |> List.map ~f:Formula.or_of
  | _ -> [ phi ]

(** the pieces of a clause, taken of its negation normal form -- an
    implication is a disjunction there, so a head's conjunction is one of
    its disjuncts -- and the clause itself, whole, when the normal form
    cannot be built.  No simplification is applied: [nnf_of] is exact in
    every model, which is what lets a piece's countermodel stand as the
    clause's *)
let of_clause ?max c =
  match Formula.nnf_of c with
  | exception exn when not (Common.Timer.is_async exn) -> [ c ]
  | nnf -> pieces ?max nnf

(** The pieces of [of_clause ?max c] with each piece counted by its own
    [pieces] (a piece that does not split counts one): how many questions
    [ask_by_pieces ~refine:true] asks of a clause none of whose pieces it
    decides whole and whose sub-pieces are all within its budget.  At least
    [List.length (of_clause ?max c)]. *)
let leaf_count ?max c =
  List.sum (module Int) (of_clause ?max c) ~f:(fun p ->
      Int.max 1 (List.length (pieces p)))

(** One clause asked alone, by its pieces first.  Each piece of
    [of_clause c] is asked with [ask], in order: every piece [`Valid]
    proves the clause, and a piece [`Invalid] refutes it, the piece's
    countermodel being a model of the clause's negation as it stands.  At
    the first piece that is neither, the whole clause is asked -- the
    question that was asked before this existed -- and its answer is
    returned, so the split cannot lose an answer that question gives; what
    it costs on such a clause is the pieces asked up to and including that
    one.  A clause of one piece, and every clause when [enabled] is false,
    is asked whole and only whole.  [note] is told which way each split
    clause went.

    What it buys: a clause [body => c1 /\ ... /\ cn] whose conjuncts are
    each decided at once while the clause is not.  The goal clause of the
    Creusot-form [Skip::next] is undecided in 10 s on 3 of 4 seeds, with
    each conjunct decided in 0.01 s.

    With [refine], an undecided piece is split once more before the whole
    clause is asked: [pieces] applied to the piece itself, whose
    distributed disjuncts are now single pieces, spends the bound on the
    disjuncts the first split had to keep whole.  Exact for the same
    reason as the first split -- the piece is the conjunction of its
    sub-pieces in every model, so all of them valid proves the piece, and
    one refuted is a model of the piece's negation, hence of the
    clause's.  At most [max_pieces] sub-pieces are asked over the whole
    clause, so the refinement costs at most one more split's worth of
    questions.  What it buys: the bound is chosen largest disjunct first,
    so a head that splits into more than [max_pieces / 3] pieces takes it
    alone and leaves a premise's three-way case split undistributed in
    every piece; on a Rust-derived call-site clause whose head split into
    38 pieces once a rewrite had dropped the array binders around its
    conjuncts, the first piece, carrying the whole case split, was
    undecided at once, while its three cases asked apart -- the pieces of
    the same clause before the rewrite -- were each shown valid.

    With [unproved], a piece left undecided (after its refinement) does
    not end the pass: every piece is asked, a refuted one still refutes at
    once, and when some are undecided [unproved] is given them, in order,
    before the whole clause is asked and its answer returned.  A refined
    piece is asked every sub-piece and is given as its undecided sub-pieces
    (it is their conjunction with the valid ones).  [unproved] is called
    only when some piece or sub-piece was shown valid: otherwise what is
    left is the clause again, and a conjunction of coarse pieces is a form
    a later split may cut worse than the clause (the sequence
    instantiation keeps a conjunction whole once its conjuncts' pieces
    pass its bound).  The clause
    is the conjunction of its pieces in every model, so the clause is valid
    exactly when the given pieces are, whatever the whole clause's answer;
    that is what a caller may use them for.

    With [max] below [max_pieces], the clause is first split into at most
    [max] pieces -- coarser ones, each keeping whole some of the disjuncts
    the default split distributes -- and a piece left undecided is always
    refined as above, so that the fine split remains the fallback within
    the refinement's bound.  Exact for the same reason as the default split.
    What it buys: a clause whose pieces are a six-way case split was asked
    as 64 fresh-context questions, each repeating the clause's common
    premise of several hundred disjuncts, and most of each question's cost
    was the making of its context, not its solving. *)
let ask_by_pieces ?(refine = false) ?max ?unproved ~enabled ~note ~ask c =
  let max = Option.map max ~f:(Int.min max_pieces) in
  let refine =
    refine || match max with Some m -> m < max_pieces | None -> false
  in
  if not enabled then ask c
  else
    match of_clause ?max c with
    | [] | [ _ ] -> ask c
    | ps ->
        let n = List.length ps in
        (* the sub-pieces still allowed over the whole clause *)
        let budget = ref (if refine then max_pieces else 0) in
        (* a piece that is neither valid nor refuted, split once more:
           [`Valid] when every sub-piece is, [`Invalid] at the first one
           refuted, and [None] when it cannot be split within the budget or
           a sub-piece is undecided too *)
        let refined k p =
          match pieces p with
          | ([] | [ _ ]) -> None
          | sub when List.length sub > !budget -> None
          | sub ->
              budget := !budget - List.length sub;
              let m = List.length sub in
              (* with [unproved], every sub-piece is asked: the undecided ones
                 are what is left of the piece, and the piece is valid exactly
                 when they are *)
              let rec all j proved_any acc = function
                | [] when List.is_empty acc ->
                    note
                      (sprintf "piece %d of %d valid by its %d sub-pieces" k n
                         m);
                    Some `Valid
                | [] ->
                    note
                      (sprintf "piece %d of %d: %d of %d sub-pieces undecided"
                         k n (List.length acc) m);
                    Some (`Partial (List.rev acc, proved_any))
                | q :: rest -> (
                    match ask q with
                    | `Valid -> all (j + 1) true acc rest
                    | `Invalid model ->
                        note
                          (sprintf
                             "piece %d of %d: sub-piece %d of %d invalid, \
                              which refutes the clause"
                             k n j m);
                        Some (`Invalid model)
                    | _ -> all (j + 1) proved_any (q :: acc) rest)
              in
              let rec each j = function
                | [] ->
                    note
                      (sprintf "piece %d of %d valid by its %d sub-pieces" k n
                         m);
                    Some `Valid
                | q :: rest -> (
                    match ask q with
                    | `Valid -> each (j + 1) rest
                    | `Invalid model ->
                        note
                          (sprintf
                             "piece %d of %d: sub-piece %d of %d invalid, \
                              which refutes the clause"
                             k n j m);
                        Some (`Invalid model)
                    | _ ->
                        note
                          (sprintf "piece %d of %d: sub-piece %d of %d undecided"
                             k n j m);
                        None)
              in
              if Option.is_some unproved then all 1 false [] sub else each 1 sub
        in
        (* [left]: the pieces passed over undecided, newest first; only
           [unproved] passes a piece over, so it is empty without it *)
        (* [proved_any]: some piece or sub-piece was shown valid, so that
           what is left is smaller than the clause; only then is [unproved]
           given it, since with nothing proved the pieces left are the
           clause again, in a form a later split may cut worse *)
        let rec go k proved_any left = function
          | [] when List.is_empty left ->
              note (sprintf "valid by its %d pieces" n);
              `Valid
          | [] ->
              note
                (sprintf
                   "%d of %d pieces undecided, asking the clause whole"
                   (List.length left) n);
              if proved_any then
                Option.iter unproved ~f:(fun f -> f (List.rev left));
              ask c
          | p :: rest -> (
              match ask p with
              | `Valid -> go (k + 1) true left rest
              | `Invalid model ->
                  note
                    (sprintf "piece %d of %d invalid, which refutes the clause"
                       k n);
                  `Invalid model
              | _ -> (
                  match refined k p with
                  | Some `Valid -> go (k + 1) true left rest
                  | Some (`Invalid model) -> `Invalid model
                  | Some (`Partial (subs, sub_proved)) ->
                      note
                        (sprintf "piece %d of %d undecided, its undecided \
                                  sub-pieces kept" k n);
                      go (k + 1) (proved_any || sub_proved)
                        (List.rev_append subs left) rest
                  | None when Option.is_some unproved ->
                      note (sprintf "piece %d of %d undecided, kept" k n);
                      go (k + 1) proved_any (p :: left) rest
                  | None ->
                      note
                        (sprintf
                           "piece %d of %d undecided, asking the clause whole"
                           k n);
                      ask c))
        in
        go 1 false [] ps

(** [of_clause ?max c]'s pieces asked with [ask], in order, and the whole
    clause never: [`Unsplit] when [c] has at most one piece (nothing is
    asked); [`Invalid m] at the first piece [ask] refutes, [m] being its
    model of the piece's negation, hence of [c]'s; [`Valid] when [ask] shows
    every piece valid; otherwise [`Rest (r, proved, total)], where [r] is
    the conjunction of the pieces left undecided, in their order, [proved]
    the number shown valid and [total] the number of pieces.  [r] is valid
    exactly when [c] is, since [c] is the conjunction of its pieces in every
    model and the pieces left out of [r] are valid; so is a model of [r]'s
    negation one of [c]'s.  Every piece is asked once, and only [ask]'s
    [`Valid] and [`Invalid _] are read.

    What it is for: a clause whose negation is a case split of hundreds of
    shared premise disjuncts, which a solver leaves undecided whole while it
    proves each case in a fraction of a second. *)
let prove_pieces ?max ~ask c =
  match of_clause ?max c with
  | [] | [ _ ] -> `Unsplit
  | ps ->
      let total = List.length ps in
      let rec go proved left = function
        | [] when List.is_empty left -> `Valid
        | [] -> `Rest (Formula.and_of (List.rev left), proved, total)
        | p :: rest -> (
            match ask p with
            | `Valid -> go (proved + 1) left rest
            | `Invalid m -> `Invalid m
            | _ -> go proved (p :: left) rest)
      in
      go 0 [] ps

(** The early rewritten pass's treatment of one clause, given the bound
    [max_pieces] on the questions it may ask of it ([leaf_count ?max]).
    Within the bound (or with no bound), [ask_pieces c] is asked and its
    answer returned as [`Asked]; nothing else is asked.

    Past the bound the clause is skipped -- left to a later stage that splits
    it itself -- and with [refute_skipped] it is first asked once more, as a
    whole, with [ask_whole]: exactly one question per skipped clause, and only
    a countermodel is read from it ([`Skipped (Some model)]); a proof or an
    undecided answer gives [`Skipped None], as when the switch is off, so a
    valid clause costs that one question and goes on to the later stage
    unchanged.  The countermodel is one of [c] as asked, so it refutes the
    clause [c] stands for whenever [c] is an exact rewrite of it (equivalent
    in every model, no free variable added).  Without [refute_skipped] a
    skipped clause is asked nothing.

    Why: the bound keeps the pass off a clause of many pieces that the later
    stage proves with far fewer questions, but an invalid such clause was
    refuted by the pass at once and, skipped, waited for the late stages,
    which the time limit did not reach. *)
let refinement_budget = max_pieces

(** the sub-pieces [ask_by_pieces ~refine:true ?max] asks of [c] when it
    refines every piece of [of_clause ?max c] that splits: the sum of
    [List.length (pieces p)] over those pieces.  Every such piece is refined,
    whatever the answers, exactly when this is at most [refinement_budget]:
    the refinement takes a piece's sub-pieces out of that budget and refines
    no piece whose sub-pieces exceed what is left, so with the sum within it
    no piece is refused, and past it the refined ones cannot all have been
    paid for.  At most [leaf_count ?max c]. *)
let refinement_size ?max c =
  List.sum (module Int) (of_clause ?max c) ~f:(fun p ->
      match pieces p with [] | [ _ ] -> 0 | sub -> List.length sub)

(** [within_refinement]: also skip a clause whose [refinement_size ?max]
    exceeds [refinement_budget], the number of sub-pieces
    [ask_by_pieces ~refine:true] may ask over one clause.  Such a clause
    cannot have every undecided piece refined: the budget runs out after the
    first few, the pieces after them are asked only coarse, and the
    undecided pieces it hands on under [unproved] mix sub-pieces with whole
    coarse pieces, cut differently from the clause's own split by a later
    stage.  Within the budget the pass can always refine every piece, so the
    skip changes nothing there.  Not exact: a skipped clause is first asked
    by the later stage instead.  Why: on a Rust-derived loop-body clause of
    four coarse pieces of 32 sub-pieces each the pass asked 69 questions
    (each refused natively for a quantifier over a sequence and asked of
    the sequence-axiom fallback, 20-30 s), proved 39, refined two of the four
    coarse pieces and handed on the rest; the sequence instantiation then
    left a grouped question of that remainder undecided and asked its members
    one by one, and under a concurrent batch the input answered in none of
    five runs against three of five with the clause skipped. *)
let early_question ?max ?(within_refinement = false) ~max_pieces
    ~refute_skipped ~ask_whole ~ask_pieces c =
  let skip =
    (match max_pieces with Some n -> leaf_count ?max c > n | None -> false)
    || (within_refinement && refinement_size ?max c > refinement_budget)
  in
  match skip with
  | true ->
      if not refute_skipped then `Skipped None
      else (
        match ask_whole c with
        | `Invalid model -> `Skipped (Some model)
        | _ -> `Skipped None)
  | false -> `Asked (ask_pieces c)
