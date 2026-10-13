open Core
open Common.Ext

(* Refuting a constraint with no predicate variable left by fixing the length
   of its free sequence variables -- the sequence counterpart of pinning an
   array literal's range bounds on the same path.

   The constraint [phi] (the conjunction of the clauses, each read as valid
   when it holds for every value of its free variables) is refuted by a model
   of its NEGATION, in which those free variables are existential.  Adding a
   conjunct to that negation only removes models, so a model of a
   strengthened negation is a model of the negation: a satisfiable
   strengthening is a refutation, and an unsatisfiable or undecided one says
   nothing and is dropped.  Nothing here may be read as validity -- the
   strengthening discards models, so its unsatisfiability is not the
   negation's -- which is why [refute] returns a countermodel or nothing and
   has no answer meaning "valid".

   The strengthening used is [s = unit c1 ++ ... ++ unit ck] for each free
   sequence [s], with fresh element variables [c_i] (the empty sequence for
   k = 0), and [s] is also substituted by that literal inside the negation.
   Keeping the equation alongside the substitution is exact -- [exists s.
   s = t /\ psi(s)] is [exists s. s = t /\ psi(t)] -- and asserting the
   equation is the same strengthening as asserting [seq.len s = k], because
   every sequence of length [k] is such a concatenation for some elements.
   The substituted form is what makes it worth asking: a read [seq.nth s j]
   at a symbolic index becomes a read of a concatenation of units, which the
   exact read-over-concatenation split turns into a case analysis over
   [j]'s value, and [seq.len s] a length the solver computes; pinning only the
   length would leave every read to the sequence solver.  The equation keeps
   [s] in the query so that the model names its value, which the
   countermodel witness is checked against.  No rewrite that is exact only
   under validity (the per-clause substitution of a sequence's definition)
   is applied, because the model must satisfy the negation pointwise.

   A name that occurs at two sorts is left unpinned: clauses may reuse a
   variable name at different sorts, and substituting a sequence into an
   occurrence of another sort would build an ill-sorted term.  All free
   sequences take the same length at once, and only 0, 1 and 2 are tried, as
   on the array side: three bounded queries on a path that was about to
   return [unknown] or [timeout], so it cannot cost an answer.  Lengths that
   differ per sequence are read from a model when a caller asks (below). *)

open Ast.LogicOld

let lengths = [ 0; 1; 2 ]

(** the variables free in [phi] at a sequence sort and at no other sort,
    each with its element sort, sorted by name *)
let free_sequences phi =
  let env = Set.to_list (Formula.term_sort_env_of phi) in
  List.filter_map env ~f:(function
    | x, T_seq.SSeq se
      when List.for_all env ~f:(fun (y, s') ->
               (not (Ast.Ident.tvar_equal x y))
               || Stdlib.( = ) s' (T_seq.SSeq se)) ->
        Some (x, se)
    | _ -> None)
  |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) ->
      Ast.Ident.tvar_compare x y)

(** [unit c1 ++ (unit c2 ++ ... unit ck)] over fresh [c_i : se], or the
    empty sequence when [k = 0] *)
let literal_of se k =
  List.fold_right
    (List.init k ~f:(fun _ ->
         T_seq.mk_unit se (Term.mk_var (Ast.Ident.mk_fresh_tvar ()) se)))
    ~init:None
    ~f:(fun u acc ->
      Some (match acc with None -> u | Some t -> T_seq.mk_concat se u t))
  |> Option.value ~default:(T_seq.mk_empty se)

(** A formula every model of which is a model of the negation of
    [and_of clauses], with every free sequence of length [length]; [None]
    when the clauses have no free sequence variable. *)
let strengthened_negation ~length clauses =
  match free_sequences (Formula.and_of clauses) with
  | [] -> None
  | seqs ->
      let defs =
        List.map seqs ~f:(fun (s, se) -> (s, se, literal_of se length))
      in
      let sub =
        Map.Poly.of_alist_exn @@ List.map defs ~f:(fun (s, _, t) -> (s, t))
      in
      let body =
        List.map clauses ~f:(fun c ->
            Ast.Evaluator.rewrite_seq_read_over_concat (Formula.subst sub c))
      in
      let eqs =
        List.map defs ~f:(fun (s, se, t) ->
            Formula.eq (Term.mk_var s (T_seq.SSeq se)) t)
      in
      Some
        (Formula.and_of
        @@ (Formula.nnf_of @@ Formula.negate @@ Formula.and_of body)
           :: eqs)

(* Lengths read from a model, one per sequence.

   The fixed lengths above give every free sequence the same length, and a
   countermodel whose sequences must have different lengths -- a sequence of
   closures one longer than the sequence of values they produced, ten items
   where the premises force ten -- is not among them.  Its lengths are often
   fixed by the quantifier-free part of the negation alone, by linear
   arithmetic over [seq.len] terms, while the solver, asked the whole negation,
   is left to find them while instantiating the quantified parts and does not
   (a ten-line negation of that shape: no answer in 60 s, [sat] in 0.2 s once
   one length equation was added).

   So a GUESS is taken from a model of the RELAXATION [R]: the negation in
   negation normal form with every quantified part reached through
   conjunctions and disjunctions replaced by [true]
   ([ScalarPin.drop_quantified]).  Every model of the negation satisfies [R],
   so the lengths of any countermodel are among the lengths [R] admits; a
   model of [R] is NOT a countermodel, and nothing about it is reported.  Each
   free sequence [s] whose length in that model is a literal [k] with
   [0 <= k <= max_model_length] is then pinned by the conjunct
   [seq.len s = k], the others are left free, and the pinned negation is asked
   like the fixed ones.  The soundness argument is the fixed lengths' own:
   the pinned query is a STRENGTHENING of the negation, so only a model of it
   is read, and that model is a countermodel.  Only the length equations are
   added -- not the literal substitution the fixed lengths use, which at
   [k = 32] would bring 32 fresh element variables per sequence; the measured
   effect is of the equations. *)

let max_model_length = 32

(** the quantifier-free relaxation of the negation of [and_of clauses] with
    one fresh integer [n_s = seq.len s] per free sequence [s], and the list of
    [(s, se, n_s)]; [None] when there is no free sequence *)
let length_guess_query clauses =
  match free_sequences (Formula.and_of clauses) with
  | [] -> None
  | seqs ->
      let named =
        List.map seqs ~f:(fun (s, se) -> (s, se, Ast.Ident.mk_fresh_tvar ()))
      in
      let relaxed =
        ScalarPin.drop_quantified
        @@ Formula.nnf_of @@ Formula.negate @@ Formula.and_of clauses
      in
      let defs =
        List.map named ~f:(fun (s, se, n) ->
            Formula.eq (Term.mk_var n T_int.SInt)
              (T_seq.mk_len se (Term.mk_var s (T_seq.SSeq se))))
      in
      Some (Formula.and_of (relaxed :: defs), named)

(** the length [model] gives each [n_s] of [named], kept only where it is an
    integer literal in [0, max_model_length] *)
let lengths_of_model named (model : model) =
  List.filter_map named ~f:(fun (s, se, n) ->
      List.find_map model ~f:(fun ((y, _), t) ->
          if Ast.Ident.tvar_equal n y then t else None)
      |> Option.bind ~f:(function
        | Term.FunApp (T_int.Int k, [], _)
          when Z.(geq k zero && leq k (of_int max_model_length)) ->
            Some (s, se, Z.to_int k)
        | _ -> None))

(** the negation of [and_of clauses] strengthened by [seq.len s = k] for each
    [(s, se, k)] of [pins]; [None] when [pins] is empty *)
let length_pinned_negation pins clauses =
  if List.is_empty pins then None
  else
    Some
      (Formula.and_of
      @@ (Formula.nnf_of @@ Formula.negate @@ Formula.and_of clauses)
         :: List.map pins ~f:(fun (s, se, k) ->
             Formula.eq
               (T_seq.mk_len se (Term.mk_var s (T_seq.SSeq se)))
               (T_int.from_int k)))

(** A countermodel of [and_of clauses] found under the strengthening, or
    [None]; [ask] is asked for a model of each strengthened negation in
    turn.  Nothing is asked when [enabled] is false.  With [guess] (the
    model-read lengths above), first, for each clause in turn, [guess] is
    asked for a model of the relaxation of that clause's negation, and the
    clause's negation pinned to the lengths it gives is asked; then the fixed
    lengths.  [guess]'s model is only ever read for lengths.

    Applicability ([already_valid], [classify]; both absent: the search
    above, step for step).  A clause whose index [already_valid] holds -- one
    a question before the pin has PROVED valid -- is left out of every
    question, and with [classify] in place of [guess] (the same question,
    telling [`Unsat] apart from an undecided answer) so is a clause whose
    relaxation has no model.  Why nothing is lost: the negation of the
    conjunction is the disjunction of the clauses' negations, and the negation
    of a clause of either kind has no model (a valid clause's is false in
    every model; the relaxation is implied by the negation).  Substituting a
    literal for a sequence under the equation [s = lit] keeps a disjunct
    without a model without one, so each fixed-length question with those
    disjuncts left out has the same models, read on the variables it still
    mentions, as the question with them; and no per-clause question is
    asked about such a clause, since it could only be [unsat]. *)
let refute ?guess ?classify ?(already_valid = fun (_ : int) -> false) ~enabled
    ~(ask : Formula.t -> model option) clauses =
  if not enabled then None
  else
    let indexed = List.filteri clauses ~f:(fun i _ -> not (already_valid i)) in
    let hopeless = Hash_set.Poly.create () in
    let classify =
      match (classify, guess) with
      | Some f, _ -> Some f
      | None, Some g ->
          Some
            (fun q -> match g q with Some m -> `Model m | None -> `Undecided)
      | None, None -> None
    in
    (* one clause at a time: the negation of the conjunction is the
       disjunction of the clauses' negations, so a model of its relaxation may
       satisfy the relaxed negation of one clause and give the lengths of
       another's countermodel nothing; a countermodel of one clause is one of
       the conjunction *)
    let from_model () =
      match classify with
      | None -> None
      | Some classify ->
          List.find_mapi indexed ~f:(fun j c ->
              Option.bind (length_guess_query [ c ]) ~f:(fun (q, named) ->
                  Common.PhaseTime.event_here ~in_copy:false "clause";
                  match classify q with
                  | `Unsat ->
                      Hash_set.add hopeless j;
                      None
                  | `Undecided -> None
                  | `Model model ->
                      Option.bind
                        (length_pinned_negation (lengths_of_model named model)
                           [ c ])
                        ~f:ask))
    in
    match from_model () with
    | Some model -> Some model
    | None ->
        let live =
          List.filteri indexed ~f:(fun j _ -> not (Hash_set.mem hopeless j))
        in
        if Hash_set.length hopeless > 0 then
          Common.PhaseTime.event_here ~in_copy:false "skip-infeasible";
        List.find_map lengths ~f:(fun length ->
            Option.bind (strengthened_negation ~length live) ~f:(fun q ->
                Common.PhaseTime.event_here ~in_copy:false "fixed";
                ask q))


(* The one sequence-length question worth asking before a long stage.

   [refute] asks, per clause, a relaxation and a length-pinned negation, then
   the fixed lengths 0, 1 and 2: up to [2k + 3] questions for [k] clauses.
   When something expensive is about to run first (the exact rewritten forms
   and the sequence instantiation, which on some inputs take a minute and more
   before they leave a clause undecided), a refutation the pin would have found
   in its first second is reached only after that.  [cheap_first] picks out of
   the pin the single question whose cost the problem's shape bounds: the
   negation of the open clauses with every free sequence pinned to the empty
   sequence ([strengthened_negation ~length:0]).

   Why the shape predicts that this question is cheap.  Pinning a sequence to
   the empty sequence makes every read of it a read out of range and every
   bound [i < seq.len s] false, so the simplifier removes each quantifier that
   ranges over the sequence's indices: on Rust-derived inputs half of the
   clauses' length-0 negations simplify to [false] and the others keep a third
   to a half of their quantifiers.  What is left is measured, after
   simplification, in nodes: a question at most [cheap_max_size] nodes long is
   one Z3 builds and converts in negligible time, and its solving time is the
   caller's per-question cap.  So the stage costs one question at most, whatever
   the input, and none when the shape says it cannot act.

   Applicability, decided without a solver.  A clause with no free sequence is
   left out (pinning does nothing to it; asking its plain negation is the
   ordinary questions' job), and so is a clause whose length-0 negation
   simplifies to [false] (it has no model, so leaving it out of the
   disjunction of negations leaves the question's models as they were).
   Leaving out any disjunct only removes models, so whatever model the question
   has is a countermodel of the clauses, exactly as for [refute]'s fixed
   lengths.

   When the shape is wrong -- the question is cheap and has no model, or Z3
   does not answer within the cap -- the cost is that one question and a
   linear simplification of each open clause; nothing else is changed, and the
   full pin still runs at its place in the ladder.

   The bound: the input this was built for has two clauses with a free
   sequence still open when the pin runs, and the pin's length-0 question
   about them refuted it within a one-second cap.  Its clauses' length-0
   negations simplify to at most 1,626 nodes each, so that question is at
   most 1,626 + 1,589 = 3,215 nodes (its two largest); the bound is that,
   with a quarter of headroom.  All ten of its clauses together come to
   7,864 nodes, past the bound: the test is meant to be applied to the open
   clauses only. *)
let cheap_max_size = 4000

(** the clauses of [clauses] that [cheap_first] keeps: those with a free
    sequence whose length-0 negation does not simplify to [false] *)
let cheap_first_live clauses =
  List.filter clauses ~f:(fun c ->
      match strengthened_negation ~length:0 [ c ] with
      | None -> false
      | Some q -> not (Formula.is_false (Ast.Evaluator.simplify q)))

(** [`Ask q]: the length-0 question [q] about the live clauses (see above),
    whose simplified form has at most [max_size] nodes; [`Not_applicable] when
    no clause is live; [`Too_large n] when the simplified question has
    [n > max_size] nodes.  Asks no solver.  Contract: every model of [q] is a
    model of the negation of [and_of clauses] (a countermodel) *)
let cheap_first ?(max_size = cheap_max_size) clauses =
  match cheap_first_live clauses with
  | [] -> `Not_applicable
  | live -> (
      match strengthened_negation ~length:0 live with
      | None -> `Not_applicable
      | Some q ->
          let n = Formula.ast_size (Ast.Evaluator.simplify q) in
          if n > max_size then `Too_large n else `Ask q)
