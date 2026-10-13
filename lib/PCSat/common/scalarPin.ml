open Core
open Common.Ext

(* Refuting a constraint with no predicate variable left by fixing the free
   variables of one of its clauses to a point, and then PROVING that the
   clause fails there.

   The shape it is for.  A clause [C] (read as valid when it holds for every
   value of its free variables) whose free variables are integers, tuples and
   other scalars, and whose premises are universal hypotheses over sequences:
   [(forall s. H(s, a)) /\ ... => G(a)].  A countermodel is a point, say
   [a = 10], at which every hypothesis holds and [G] fails.  A satisfiability
   question about [not C] leaves the sequence universals to the solver's
   quantifier instantiation, which has to build a model of them, and fixing
   the lengths of free sequences does nothing when every sequence is bound.

   The route, per piece [P] of [C] ([SeqInstantiation.pieces]: [C] holds in a
   model exactly when every piece does, so a countermodel of a piece is one
   of [C]):
   1. Guess.  Ask [guess] for a model of a RELAXATION of [not P] -- a formula
      every model of [not P] satisfies -- that is quantifier-free: the
      negation of [P]'s instantiated form ([SeqInstantiation.instantiate_deep]
      strengthens [P], so its negation is weaker than [not P]), then the
      same after [P]'s positive universals are made free variables and its
      one-point binders eliminated (the first is exact for validity, so its
      negation is exact for satisfiability, and the second is an
      equivalence: without them a premise [exists t. a = t /\ Q(t)] of the
      negation offers the instantiation no candidate for [t] and is dropped
      whole, so the relaxation says nothing about [a]), then [not P]
      with each quantified part reached through conjunctions and disjunctions
      replaced by [true].  Every countermodel of [P] is among the models of
      either relaxation, so the guesses cover the points worth trying; but a
      model of a relaxation is NOT a countermodel -- it may violate the
      hypotheses that were weakened or dropped -- and nothing about it is
      reported.  A strengthening of [not P] would be a refutation by itself
      and is not what this step asks for; nor may a model of the negation of
      a WEAKENING of [P] be read as anything.  After a point fails, the next
      model is asked with that point excluded.
   2. Pin.  Fix every free variable of [P] to its value in the guess: a
      closed value (a literal, not a term mentioning a variable) for each;
      where the model leaves an integer, real or Boolean variable unassigned
      it takes 0, 0 or false ([default_value]; with [default_compound] also a
      tuple or datatype variable, built from such values), and where it
      leaves any other variable unassigned or gives it an open value the
      point is dropped.
   3. Prove.  [Q = not P[point]] is then a sentence.  It is proved VALID,
      one conjunct at a time (quantifier-free conjuncts first, so a point at
      which the conclusion holds is dropped by its cheapest question): each
      conjunct has its positive universals replaced by fresh free variables
      ([SeqInstantiation.skolemize_positive_universals], exact for validity)
      and is handed to [SeqInstantiation.prove_valid], which only ever reads
      a proof of validity of a strengthening.

   (With [drop_valid_premises_before_pin], step 3 also accepts a point whose
   quantified conjuncts not proved valid have a MODEL: the proved ones are
   true in every model, so a model of the rest is one of [Q]; see
   [proved_at].)

   Why the answer is sound.  If [Q] is valid, then in EVERY model of the
   background theory the hypotheses of [P] hold at the point and its
   conclusion fails there, so [P] -- hence [C], hence the conjunction of the
   clauses -- is false in that model with the free variables at the point.
   The theory has a model, so the constraint is not valid, which with no
   predicate variable left is a refutation; the point is returned as the
   countermodel.  Only [`Valid] answers of [ask] are read, so an undecided or
   refuted form, or a wrong guess, costs time and never an answer.

   What it cannot do.  A point at which the clause fails in SOME models but
   not in all -- one whose failure turns on an interpretation the theory
   leaves open, such as a division by zero or an uninterpreted function -- is
   not proved, since [Q] is then not valid.  A hypothesis that holds at the
   point only by an inductive argument over the sequence is not proved by
   instantiation.  A countermodel whose point the relaxations do not suggest
   within [max_points] guesses is not found.  A variable at two sorts leaves
   the piece alone, as the sequence pin does. *)

open Ast.LogicOld

let max_points = 4
let guesses_per_relaxation = 2

(** the free variables of [phi] with their sorts, sorted by name, or [None]
    when a name occurs at two sorts *)
let free_vars phi =
  let env =
    List.dedup_and_sort ~compare:Stdlib.compare
      (Set.to_list (Formula.term_sort_env_of phi))
  in
  let rec distinct = function
    | (x, _) :: ((y, _) :: _ as rest) ->
        (not (Ast.Ident.tvar_equal x y)) && distinct rest
    | _ -> true
  in
  if distinct env then Some env else None

(** [phi] (in negation normal form) with every part that is not
    quantifier-free and is reached through conjunctions and disjunctions
    alone replaced by [true]: a formula every model of [phi] satisfies *)
let rec drop_quantified phi =
  match phi with
  | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
      Formula.mk_binop op (drop_quantified p) (drop_quantified q)
  | _ when Formula.is_quantifier_free phi -> phi
  | _ -> Formula.mk_true ()

(* The binder-free relaxation ([binder_free_relaxation]).  [not P], after
   [P]'s one-point binders are eliminated (an equivalence), in negation
   normal form, with its binders taken apart from the outside in:
   - an existential's variables are renamed apart and left free;
   - a universal over integers is replaced by the conjunction of its
     instances at the integer literals of the formula, their negations and 0
     (at most [max_int_candidates] values, at most [max_int_instances]
     instances, else by one instance at fresh variables), and a universal
     over any other sort by one instance at fresh variables;
   - any other binder (a probabilistic one) by [true].
   Why every model of [not P] extends to a model of the result.  Going in
   from the outside, an existential met is under no universal still bound
   (each one above it has been replaced by instances), so a model of the
   formula at that point gives its variables values, and fresh free
   variables take them; a universal implies each of its instances, and
   [true] is implied by anything; conjunctions and disjunctions are
   monotone.  So the models of the result, read on the clause's free
   variables, include every countermodel of [P], which is what a guess is
   for; a model of it is never reported as one.  Why it is worth having.  A
   call-site clause in the array-and-length encoding of sequences states its
   premises as [forall s. s[0] = i /\ len s = 1 => exists ta. ... /\
   forall k. 0 <= k < n => ta[k] = k /\ forall k. 3 <= k < n => ta[k] =
   s[k - 3]]; the other relaxations drop such a premise whole, so the guess
   leaves the point unconstrained, while the instances at [k = 3] fix it
   ([ta[3] = 3 = i]). *)
let max_int_candidates = 12
let max_int_instances = 64

(** the integer literals of [phi], their negations and 0, distinct, smallest
    magnitude first, at most [max_int_candidates] *)
let int_literal_candidates phi =
  Formula.filtered_terms_of phi ~f:(function
    | Term.FunApp (T_int.Int _, [], _) -> true
    | _ -> false)
  |> Set.to_list
  |> List.concat_map ~f:(function
    | Term.FunApp (T_int.Int c, [], _) -> [ c; Z.neg c ]
    | _ -> [])
  |> List.cons Z.zero
  |> List.dedup_and_sort ~compare:Z.compare
  |> List.stable_sort ~compare:(fun a b -> Z.compare (Z.abs a) (Z.abs b))
  |> (fun cs -> List.take cs max_int_candidates)
  |> List.map ~f:T_int.mk_int

let rename_apart senv phi =
  if List.is_empty senv then phi
  else
    Formula.subst
      (Map.Poly.of_alist_exn
      @@ List.map senv ~f:(fun (x, s) ->
          (x, Term.mk_var (Ast.Ident.mk_fresh_tvar ()) s)))
      phi

(** the binder-free relaxation of [not piece] (see above), or [None] when
    the result is not quantifier-free *)
let binder_free_relaxation piece =
  let neg =
    Formula.nnf_of @@ Formula.mk_neg
    @@ Ast.Evaluator.elim_onepoint_and_split_binders piece
  in
  let ints = int_literal_candidates neg in
  let rec go phi =
    match phi with
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
        Formula.mk_binop op (go p) (go q)
    | Formula.Bind (Formula.Exists, senv, body, _) -> go (rename_apart senv body)
    | Formula.Bind (Formula.Forall, senv, body, _) -> (
        let is, others =
          List.partition_tf senv ~f:(fun (_, s) ->
              Stdlib.( = ) s T_int.SInt)
        in
        let body = rename_apart others body in
        let n = List.length is in
        let count =
          List.fold is ~init:1 ~f:(fun acc _ ->
              if acc > max_int_instances then acc else acc * List.length ints)
        in
        if n = 0 || List.is_empty ints || count > max_int_instances then
          go (rename_apart is body)
        else
          let rec combos = function
            | [] -> [ [] ]
            | (x, _) :: rest ->
                List.concat_map ints ~f:(fun c ->
                    List.map (combos rest) ~f:(fun cs -> (x, c) :: cs))
          in
          match combos is with
          | subs ->
              Formula.and_of
              @@ List.map subs ~f:(fun sub ->
                  go (Formula.subst (Map.Poly.of_alist_exn sub) body)))
    | Formula.Bind (_, _, _, _) -> Formula.mk_true ()
    | _ when Formula.is_quantifier_free phi -> phi
    | _ -> Formula.mk_true ()
  in
  let r = Ast.Evaluator.simplify (go neg) in
  if Formula.is_quantifier_free r then Some r else None

(* The relaxations instantiate the piece without splitting reads of
   concatenations ([SeqInstantiation.instantiate_deep ~split_reads:false]).
   The split is an identity, so each relaxation is the same formula up to
   equivalence and has the same models; it helps a solver only under a
   quantified hypothesis, and a relaxation is kept only when it is
   quantifier-free.  On an input whose pieces read concatenations of sequence
   literals the split, with the simplification after it, took one relaxation
   to 6.2 million nodes and 45 s of CPU (against 0.02 s without it), past any
   deadline, since a deadline is read only between relaxations. *)
let inst_relaxation ?(skolem = false) piece =
  Formula.nnf_of @@ Formula.mk_neg
  @@ SeqInstantiation.instantiate_deep ~split_reads:false
  @@
  if skolem then
    (* [P] with its positive universals made free (exact for validity, so
       its negation is exact for satisfiability) and its one-point binders
       eliminated (equivalent), before the instantiation *)
    SeqInstantiation.skolemize_positive_universals
    @@ Common.PhaseTime.with_phase "relax-onepoint" (fun () ->
        Ast.Evaluator.elim_onepoint_and_split_binders piece)
  else piece

(** quantifier-free formulas every model of [not piece] satisfies, in the
    order they are asked for guesses *)
let relaxations piece =
  let neg = Formula.nnf_of (Formula.mk_neg piece) in
  let inst = inst_relaxation piece in
  let exact = inst_relaxation ~skolem:true piece in
  List.filter ~f:Formula.is_quantifier_free
    [ inst; exact; drop_quantified neg ]

(** [relaxations piece] as lazy values, in the same order, each built only
    when forced; a forced value that is not quantifier-free is to be skipped.
    For a caller with a deadline ([refute]'s [expired]): building the two
    instantiated relaxations of one piece was measured at 17-25 s on a
    Rust-derived clause, so building all three before asking any guess spends
    a deadline many times over. *)
let lazy_relaxations piece =
  let ph = Common.PhaseTime.with_phase in
  let neg = lazy (Formula.nnf_of (Formula.mk_neg piece)) in
  [
    lazy (ph "relax-inst" @@ fun () -> inst_relaxation piece);
    lazy (ph "relax-exact" @@ fun () -> inst_relaxation ~skolem:true piece);
    lazy (ph "relax-drop" @@ fun () -> drop_quantified (Lazy.force neg));
  ]

(** The relaxations of [piece] a caller with [expired] may use: without it,
    [relaxations piece], all built at once; with it, the lazy ones, each
    forced only while [expired ()] is false, the quantifier-free among them
    kept.  Same formulas in the same order when nothing expires. *)
let relaxations_until ?expired piece =
  match expired with
  | None -> Sequence.of_list (relaxations piece)
  | Some expired ->
      Sequence.of_list (lazy_relaxations piece)
      |> Sequence.take_while ~f:(fun _ -> not (expired ()))
      |> Sequence.map ~f:Lazy.force
      |> Sequence.filter ~f:Formula.is_quantifier_free

(** [relaxations_until], with [binder_free] the binder-free relaxation
    first (built only when reached, and only when [expired] has not
    fired) *)
let relaxations_with ?expired ~binder_free piece =
  let rest = relaxations_until ?expired piece in
  if not binder_free then rest
  else
    let first =
      Sequence.of_lazy
        (lazy
          (if match expired with Some f -> f () | None -> false then
             Sequence.empty
           else Sequence.of_list (Option.to_list (binder_free_relaxation piece))))
    in
    Sequence.append first rest


(** a closed value of sort [s] for a variable the guessed model leaves
    unassigned: [0], [0.0] or [false], and with [compound] also a tuple of
    such values, or a datatype's constructor of fewest arguments among those
    whose arguments all have one, applied to them (a constructor reaching
    back to a datatype being built is not taken, so the recursion ends);
    [None] for any other sort (a sort variable, an uninterpreted sort, an
    array, a sequence, ...).  Any closed value of the right sort will do:
    the point is only a candidate, and it is reported only after the
    pinned negation is proved valid there. *)
let rec default_value ?(compound = false) ?(building = []) = function
  | T_int.SInt -> Some (T_int.zero ())
  | T_real.SReal -> Some (T_real.rzero ())
  | T_bool.SBool -> Some (T_bool.mk_false ())
  | T_tuple.STuple sorts when compound ->
      Option.map
        (Option.all (List.map sorts ~f:(default_value ~compound ~building)))
        ~f:(T_tuple.mk_tuple_cons sorts)
  | T_dt.SDT dt as sort
    when compound && Datatype.is_dt dt
         && not (List.mem building sort ~equal:Stdlib.( = )) ->
      Datatype.conses_of dt
      |> List.stable_sort ~compare:(fun c1 c2 ->
          Int.compare
            (List.length (Datatype.sels_of_cons c1))
            (List.length (Datatype.sels_of_cons c2)))
      |> List.find_map ~f:(fun cons ->
          Option.map
            (Option.all
               (List.map (Datatype.sorts_of_cons dt cons)
                  ~f:(default_value ~compound ~building:(sort :: building))))
            ~f:(T_dt.mk_cons dt (Datatype.name_of_cons cons)))
  | _ -> None

(* Applicability: which pieces no pin can act on, decided before any question.

   [opaque_sort s] holds when EVERY value of sort [s] contains an element of an
   uninterpreted sort or a sort variable: such a sort itself, a tuple with such
   a component, or a datatype each of whose constructors takes such an argument
   (a datatype met again while it is being examined counts as not opaque, so
   this under-approximates and claims opacity only where every value has such
   an element).  Arrays and sequences are never opaque (a constant array, the
   empty sequence).

   Why a piece with a free variable of opaque sort admits no point.  [point_of]
   needs a CLOSED value for every free variable.  A variable the model leaves
   unassigned takes [default_value], which is [None] for an opaque sort (the
   defaults are built from integers, reals and Booleans only, and a tuple or a
   datatype gets one only when every component, or every argument of one
   constructor, has one).  A variable the model assigns gets the decoded model
   value, and the decoder renders an element of an uninterpreted sort -- a
   sort variable is declared to the solver as one -- as a variable (Z3 names
   it [s!val!k]), so a value containing one is open and the point is dropped.
   So the guesses of such a piece are asked and every one is thrown away,
   which on Rust-derived inputs, whose clauses quantify over generic element
   types, was most of what this pin asked.  This rests on the decoder fact
   alone; if a model value of an uninterpreted sort were ever decoded as a
   closed term, a rejected piece could have had a point. *)
let rec opaque_sort ?(building = []) = function
  | Sort.SVar _ | T_dt.SUS _ -> true
  | T_tuple.STuple sorts -> List.exists sorts ~f:(opaque_sort ~building)
  | T_dt.SDT dt as sort
    when Datatype.is_dt dt && not (List.mem building sort ~equal:Stdlib.( = ))
    ->
      let conses = Datatype.conses_of dt in
      (not (List.is_empty conses))
      && List.for_all conses ~f:(fun cons ->
          List.exists (Datatype.sorts_of_cons dt cons)
            ~f:(opaque_sort ~building:(sort :: building)))
  | _ -> false

(** the free variables of [vars] at an opaque sort ([opaque_sort]) *)
let opaque_vars vars = List.filter vars ~f:(fun (_, s) -> opaque_sort s)

(** the cheapest relaxation of [not piece]: its negation normal form with the
    quantified parts reached through conjunctions and disjunctions replaced by
    [true].  Every model of [not piece] satisfies it, so when it has no model
    neither has [not piece]; every pin reads only a model of a strengthening
    of [not piece] or a proof that [not piece] holds at a point (which needs a
    model of [not piece] too), so no pin can act on such a piece *)
let cheapest_relaxation piece = drop_quantified (Formula.nnf_of (Formula.mk_neg piece))

(** the point [model] gives [vars], each a closed value, or [None] *)
let point_of ?(default_compound = false) vars (model : model) =
  Option.all
  @@ List.map vars ~f:(fun (x, s) ->
      let given =
        List.find_map model ~f:(fun ((y, _), t) ->
            if Ast.Ident.tvar_equal x y then Some t else None)
      in
      match given with
      | Some (Some t) ->
          if Set.is_empty (Term.tvs_of t) then Some ((x, s), t) else None
      | Some None | None ->
          Option.map (default_value ~compound:default_compound s)
            ~f:(fun t -> ((x, s), t)))

let excluding point =
  Formula.mk_neg
  @@ Formula.and_of
  @@ List.map point ~f:(fun ((x, s), t) -> Formula.eq (Term.mk_var x s) t)

(** Whether [not piece] at [point] is shown to hold in SOME model of the
    background theory, i.e. whether [point] is shown to be a countermodel of
    [piece].  [Q = not piece[point]] is a sentence (every free variable of
    [piece] is pinned), split into its top-level conjuncts.

    Without [residual_sat]: [Q] is proved VALID, one conjunct at a time, and
    the point holds when every conjunct is proved.  A valid [Q] holds in
    every model, and the theory has one.

    With [residual_sat] (the switch [drop_valid_premises_before_pin]): each
    conjunct is still asked to be proved valid, and the quantified conjuncts
    not proved are KEPT; the point holds when every quantifier-free conjunct
    is proved and [residual_sat] returns a model of the conjunction [R] of
    the kept ones.  Why this is sound.  Write [Q = V /\ R], [V] the conjuncts
    proved valid.  A valid sentence is true in every model of the theory, so
    in any model [M], [M |= Q] iff [M |= R]: dropping [V] does not change
    the models of the negation.  A model of [R] is therefore a model of [Q],
    in which [piece], hence its clause, fails at the point; the constraint is
    not valid in that model, which is a refutation (satisfiability is truth
    in EVERY model, so one model falsifying it suffices).  [residual_sat]
    must return a model only when [R] has one -- an answer of the solver's
    [sat] -- and nothing may be read from [None].  Why it is worth asking.
    A premise of a Rust-derived call-site clause is a universal over
    sequences, [forall t. t <> a \/ exists s. len s = 1 /\ forall k. ...],
    which holds at the point by a witness [s] the instantiation does not
    offer ([unit 1], a term the clause never writes), so its validity proof
    fails; and the whole negation, asked for a model with the other
    quantified premises (laws over sequences) still in it, is left
    undecided by the solver, whose model has to satisfy every one of them.
    With the conjuncts proved valid dropped, the solver answered [sat] on
    that input when asked by hand, where the whole negation timed out at
    20 s. *)
let proved_at ?residual_sat ~log ~ask piece point =
  let sub =
    Map.Poly.of_alist_exn @@ List.map point ~f:(fun ((x, _), t) -> (x, t))
  in
  let q = Formula.nnf_of @@ Formula.mk_neg @@ Formula.subst sub piece in
  let qf, quantified =
    List.partition_tf (Formula.conjuncts_list_of q)
      ~f:Formula.is_quantifier_free
  in
  let conjuncts =
    List.map (qf @ quantified)
      ~f:SeqInstantiation.skolemize_positive_universals
  in
  log
  @@ lazy
       (sprintf "[scalar pin] point %s: %d quantifier-free and %d quantified conjuncts"
          (String.concat ~sep:", "
          @@ List.map point ~f:(fun ((x, _), t) ->
              Ast.Ident.name_of_tvar x ^ " = " ^ Term.str_of t))
          (List.length qf) (List.length quantified));
  List.iteri conjuncts ~f:(fun i c ->
      log
      @@ lazy
           (sprintf "[scalar pin] conjunct %d: %s" i (Formula.str_of c)));
  let prove i c =
    match
      SeqInstantiation.prove_valid ~enabled:true
        ~already_valid:(fun _ -> false)
        ~ask [ c ]
    with
    | `Valid ->
        log (lazy (sprintf "[scalar pin] conjunct %d proved" i));
        true
    | `Undecided ->
        log (lazy (sprintf "[scalar pin] conjunct %d NOT proved" i));
        false
  in
  match residual_sat with
  | None ->
      (* one conjunct at a time, stopping at the first not proved: the same
         answer as asking [prove_valid] the list, which is a conjunction of its
         clauses, with the failing conjunct named in the trace *)
      List.for_alli conjuncts ~f:prove
  | Some sat ->
      (* Every conjunct is still asked to be proved valid, the
         quantifier-free ones first and the first of those not proved
         rejecting the point as above; a QUANTIFIED conjunct not proved is
         kept, unskolemized, and the point is a countermodel when the
         conjunction of the kept ones has a model ([residual_sat]'s
         contract). *)
      let originals = qf @ quantified in
      let n_qf = List.length qf in
      let rec go i kept = function
        | [] -> (
            match List.rev kept with
            | [] -> true
            | kept -> (
                match sat (Formula.and_of kept) with
                | Some _ ->
                    log
                    @@ lazy
                         (sprintf
                            "[scalar pin] %d unproved quantified conjuncts \
                             have a model: a countermodel"
                            (List.length kept));
                    true
                | None ->
                    log
                    @@ lazy
                         (sprintf
                            "[scalar pin] no model of the %d unproved \
                             quantified conjuncts"
                            (List.length kept));
                    false))
        | (orig, c) :: rest ->
            if prove i c then go (i + 1) kept rest
            else if i < n_qf then false
            else go (i + 1) (orig :: kept) rest
      in
      go 0 [] (List.zip_exn originals conjuncts)

(** A countermodel of [and_of clauses], as the point of one clause's free
    variables at which that clause is proved false in every model, or
    [None].  [guess] is asked for a model of quantifier-free formulas only,
    and what it returns is never reported unproved; [ask] is a validity
    question of which only [`Valid] is read.  Clauses whose index
    [already_valid] holds are skipped.  At most [max_points] points are
    tried in all.  Nothing is asked when [enabled] is false.  With
    [expired], no further clause, piece or relaxation is started once
    [expired ()] holds, nor a further guess asked, and a relaxation is built only when it is reached
    ([relaxations_until]); this only stops the search earlier, so a point it
    returns is proved as without it.  Without [expired] the search is the
    one above, step for step.  With [residual_sat], a point is also
    accepted when the quantified conjuncts of its pinned negation that are
    not proved valid have a model ([proved_at]); [residual_sat] is a
    satisfiability question of which only a model is read.  With
    [skip_opaque], a piece with a free variable at an opaque sort
    ([opaque_sort]) is skipped before any question, and with [infeasible] (a
    satisfiability question that must hold only on [unsat]) a piece whose
    [cheapest_relaxation] it shows to have no model is skipped before its
    relaxations are built; neither skips a piece at which a point could have
    been proved, so a point found is one found without them.  With
    [search_complete], it is set, when the search returns, to whether it
    returned [None] having gone through every piece of every clause not
    skipped by [already_valid] with no clause, piece, relaxation or guess
    left out for [expired] or for the [max_points] count (a guess that
    [guess] itself declines is not seen here; the caller's budget tells
    those apart); it is set to [false] when [enabled] is false or a point
    is returned, and the search is the same with and without it. *)
let refute ?(log = fun (_ : string lazy_t) -> ()) ?(default_compound = false)
    ?(binder_free_relaxation = false) ?(skip_opaque = false) ?infeasible ?expired
    ?residual_sat ?search_complete ~enabled ~already_valid
    ~(guess : Formula.t -> model option) ~ask clauses =
  let set_complete b = Option.iter search_complete ~f:(fun r -> r := b) in
  set_complete false;
  if not enabled then None
  else
    let tried = ref 0 in
    let expired_now () = match expired with Some f -> f () | None -> false in
    let try_piece piece =
      Common.PhaseTime.event_here ~in_copy:false "piece";
      match free_vars piece with
      | None | Some [] ->
          log (lazy "[scalar pin] piece skipped: no free variable or one at two sorts");
          Common.PhaseTime.event_here ~in_copy:false "skip-novars";
          None
      | Some vars when skip_opaque && not (List.is_empty (opaque_vars vars)) ->
          (* [opaque_sort]: no guess of this piece can give a closed point *)
          log
          @@ lazy
               (sprintf "[scalar pin] piece skipped: free variables at an opaque sort (%s)"
                  (String.concat ~sep:", "
                  @@ List.map (opaque_vars vars) ~f:(fun (x, s) ->
                      Ast.Ident.name_of_tvar x ^ " : " ^ Term.str_of_sort s)));
          Common.PhaseTime.event_here ~in_copy:false "skip-opaque";
          None
      | Some _
        when match infeasible with
             | Some infeasible -> infeasible (cheapest_relaxation piece)
             | None -> false ->
          (* [cheapest_relaxation]: [not piece] has no model *)
          log (lazy "[scalar pin] piece skipped: its relaxation has no model");
          Common.PhaseTime.event_here ~in_copy:false "skip-infeasible";
          None
      | Some vars ->
          Sequence.find_map
            (relaxations_with ?expired ~binder_free:binder_free_relaxation
               piece) ~f:(fun relaxed ->
              log
              @@ lazy
                   (sprintf "[scalar pin] relaxation: %s"
                      (Formula.str_of relaxed));
              let rec go excluded k =
                if k = 0 || !tried >= max_points || expired_now () then None
                else
                  match guess (Formula.and_of (relaxed :: excluded)) with
                  | None -> None
                  | Some model -> (
                      match point_of ~default_compound vars model with
                      | None ->
                          log
                          @@ lazy
                               (sprintf
                                  "[scalar pin] guess gives no closed point: %s"
                                  (String.concat ~sep:"; "
                                  @@ List.map vars ~f:(fun (x, s) ->
                                      sprintf "%s : %s = %s"
                                        (Ast.Ident.name_of_tvar x)
                                        (Term.str_of_sort s)
                                        (match
                                           List.find_map model
                                             ~f:(fun ((y, _), t) ->
                                               if Ast.Ident.tvar_equal x y
                                               then Some t
                                               else None)
                                         with
                                        | None -> "(absent)"
                                        | Some None -> "(unassigned)"
                                        | Some (Some t) -> Term.str_of t))));
                          None
                      | Some point ->
                          incr tried;
                          Common.PhaseTime.event_here ~in_copy:false "point";
                          if proved_at ?residual_sat ~log ~ask piece point then Some point
                          else go (excluding point :: excluded) (k - 1))
              in
              go [] guesses_per_relaxation)
    in
    let found =
      List.find_mapi clauses ~f:(fun i c ->
          if already_valid i || expired_now () then None
          else begin
            log
            @@ lazy
                 (sprintf "[scalar pin] clause %d (points tried so far %d): %s"
                    i !tried (Formula.str_of c));
            List.find_map
              (SeqInstantiation.pieces
                 (Ast.Evaluator.simplify (Formula.nnf_of c)))
              ~f:(fun piece -> if expired_now () then None else try_piece piece)
          end)
    in
    (* [expired] only turns from false to true, so not expired now means no
       check during the search saw it expired; [tried] below [max_points]
       means the count never stopped a guess *)
    set_complete
      (Option.is_none found && !tried < max_points && not (expired_now ()));
    Option.map found ~f:(List.map ~f:(fun (b, t) -> (b, Some t)))
