(* MuStrat: validity checking of fixpoint logic (muCLP) by strategy synthesis.

   A muCLP problem is read as a game between a primal side, which proves the
   formula, and a dual side, which proves its negation ([MuCLP.Util.get_dual]).
   [solve] preprocesses the problem and reduces each side to a pfwCSP
   ([to_pfwcsp]): existential choices become functional (FN) unknowns by
   Skolemization, and least fixpoints become well-foundedness (WF) unknowns by
   the reduction of [MuCLP.Reducer].  A side's strategy is a ranking for each
   WF unknown and a set of candidate terms for each FN unknown
   ([init_strat_of]).

   [solve_primal_dual] alternates turns.  The side to move substitutes its
   strategy into its problem, which leaves a CHC that the configured CHC solver
   checks under a growing budget ([chc_budget]).  A satisfiable check is a win
   and the answer (valid for the primal side, invalid for the dual), subject to
   the extra conditions some configurations demand of it (transitivity of the
   rankings, an established copy-blind encoding).  An unsatisfiable check gives
   a counter-play, a derivation of the CHC; [refine_strat] turns it into a
   refinement problem for the opponent's strategy, solved by PCSat, and the
   turn passes.  [SkolemTerms] solves the pure-existential refinements by a
   model-guided search for terms instead: the term selection of Farzan and
   Kincaid, "Linear Arithmetic Satisfiability via Strategy Improvement",
   IJCAI-16, pp. 735-743 (Algorithm 2 and Section 4.1), whose [select(M, x,
   F)] takes a formula [F] in which the earlier players' moves are free
   variables and their values only in the model [M]; with
   [refine_counter_play = Lifted_free_goal] the counter-play is read so that
   the opponent's moves stay such variables.

   [solve_pcsp] takes a predicate constraint problem through the same route
   (ordinary unknowns only, since a fixpoint problem has no place for a kind);
   [solve_smt] decides quantified linear arithmetic by [StratSynth].

   Implements the strategy-synthesis view of fixpoint logic solving of Tsukada,
   Unno, Padon and Shoham, A Primal-Dual Perspective on Program Verification
   Algorithms (POPL 2025). *)

open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open MuCLP.Problem
open Preprocessing

(* The steps of the strategy loop, timed: [phase name f] is [f ()], run as
   the phase-time account's phase [name] (so the report divides a run's time
   between building checks, asking them, splitting their goals and refining),
   and, with COAR_MUSTRAT_TIMELINE set, also one stderr line when the step
   ends, with its start and its duration in seconds on the account's clock, so
   that a run without tracing (tracing prints inside a check's budget) tells
   which step of which turn its time went to.  Every solver call of the loop
   and every wait on a forked copy asking a check (the continued check, the
   copy-blind re-check asked aside) is inside one: a run killed at its limit
   on such a wait otherwise reported up to half of its time as unaccounted.
   Returns what [f ()] returns and raises what it raises. *)
module LoopPhase = struct
  let timeline = Option.is_some (Sys.getenv "COAR_MUSTRAT_TIMELINE")

  let phase name f =
    Common.PhaseTime.with_phase name @@ fun () ->
    if not timeline then f ()
    else
      let started = Common.PhaseTime.now () in
      let line outcome =
        eprintf "mustrat-timeline: %s start=%.2f secs=%.2f%s\n%!" name
          (started -. Common.PhaseTime.t0)
          (Common.PhaseTime.now () -. started)
          outcome
      in
      match f () with
      | v ->
          line "";
          v
      | exception e ->
          line (" raised=" ^ Exn.to_string e);
          raise e
end

(* The recency window of [skolem_term_window]: a key's terms, most recently
   added first.  [update ~n ~equal order fresh] is [fresh] followed by the
   elements of [order] not [equal] to it, in their order, cut to [max 1 n]
   elements.  Postconditions: the head is [fresh]; the length is at most
   [max 1 n]; the elements after the head are a prefix of [order] with
   [fresh]'s occurrences removed, so a term proposed again moves to the
   front instead of appearing twice; and when [order] holds no two [equal]
   elements, neither does the result. *)
module SkolemTermWindow = struct
  let update ~n ~equal order fresh =
    List.take
      (fresh :: List.filter order ~f:(fun t -> not (equal t fresh)))
      (max 1 n)
end

(* The joint term alternatives of [joint_term_alternatives]: which Skolem keys
   are offered together, and which tuples of terms they are offered as.

   The history of a key [K] is its initial terms [I(K)] (what it held when a
   refinement first touched it, extended by any term found in its set that no
   refinement proposed) and, per refinement [r] that touched it, the terms
   [S_r(K)] that refinement proposed for it.  The signature of a touched key is
   the set of refinements that touched it; keys with one signature form a
   class.  A class [C] is offered as the rows
     [prod_{K in C} I(K)  @  concat_{r in sig(C)} prod_{K in C} S_r(K)]
   (a row assigns one term to each key of [C]), restricted to the terms the
   keys currently hold and with repeated rows dropped.  A key never touched by
   a refinement is in no class and is offered on its own.

   Two facts the placement relies on:
   - every row is a vector of current terms, so the rows are a subset of the
     product of the keys' term sets (the joint check's clauses imply the
     product check's);
   - the rows cover each key: the terms appearing at a key's position are
     exactly its current term set ([units] drops a class for which this
     fails, which happens only when a term set has lost a term, under
     [skolem_term_window]), so a single key of a class offers what it offers
     alone.
   And one the progress argument relies on: as long as term sets only grow,
   the set of vectors the classes offer (product over classes of their rows,
   untouched keys contributing their whole term sets) only grows when a
   refinement is recorded, and contains the tuple that refinement proposed.
   The restriction of a class's rows to the keys present in a clause is the
   class computed on those keys alone, since every block is a product. *)
module JointTerms = struct
  (* the cartesian product of the lists [ls], in order: the first list's
     element varies slowest *)
  let product ls =
    List.fold_right ls ~init:[ [] ] ~f:(fun l acc ->
        List.concat_map l ~f:(fun x -> List.map acc ~f:(fun row -> x :: row)))

  let equal_terms t1 t2 =
    try Stdlib.( = ) t1 t2
    with exn when not (Common.Timer.is_async exn) -> false

  (* [initial_closed ~term_set ~initial ~refinements]: [initial] followed by
     the terms of [term_set] (in set order) that are neither in [initial] nor
     proposed by any refinement of [refinements].  Postcondition: every term
     of [term_set] is in the result or in some refinement's terms; the result
     extends [initial]. *)
  let initial_closed ~term_set ~initial ~refinements =
    let attributed = List.concat_map refinements ~f:snd in
    initial
    @ List.filter (Set.to_list term_set) ~f:(fun t ->
        not
          (List.mem initial t ~equal:equal_terms
          || List.mem attributed t ~equal:equal_terms))

  (* [units ~term_set ~initial ~refinements keys]: the classes of the keys
     [keys] (pairwise distinct) with at least two members, each with its rows
     aligned with its members; members keep the order of [keys], classes are
     listed by their first member.  [term_set k] is [k]'s current term set,
     [initial k] is [Some I(k)] for a key some refinement has touched and
     [None] otherwise, [refinements k] the pairs [(r, S_r(k))], [r] distinct
     identifiers.  A class with fewer than [min_keys] of the keys (default 2)
     is not returned, so its keys are offered their whole term sets.  Rows: the initial block first, then one block per
     refinement in increasing identifier order; rows keep their first
     occurrence. *)
  let units ?(min_keys = 2) ?(distinct = false) ~term_set ~initial
      ~refinements keys =
    let touched =
      List.filter_map keys ~f:(fun k ->
          Option.map (initial k) ~f:(fun i ->
              let rs = refinements k in
              ( k,
                i,
                rs,
                List.map rs ~f:fst |> List.dedup_and_sort ~compare:Int.compare
              )))
    in
    let same_sig = List.equal Int.equal in
    let classes =
      List.fold touched ~init:[] ~f:(fun acc ((_, _, _, sg) as e) ->
          if List.exists acc ~f:(fun (sg', _) -> same_sig sg sg') then
            List.map acc ~f:(fun (sg', es) ->
                if same_sig sg sg' then (sg', es @ [ e ]) else (sg', es))
          else acc @ [ (sg, [ e ]) ])
    in
    List.filter_map classes ~f:(fun (sg, es) ->
        if List.length es < Int.max 2 min_keys then None
        else
          (* the terms of [ts] the key currently holds; with [distinct], each
             once, at its first occurrence (the products below then hold no
             repeated row, and the rows kept after deduplication are the
             same, in the same order) *)
          let current (k, _, _, _) ts =
            let tset = term_set k in
            let ts = List.filter ts ~f:(Set.mem tset) in
            if not distinct then ts
            else
              List.fold ts ~init:[] ~f:(fun acc t ->
                  if List.mem acc t ~equal:equal_terms then acc else t :: acc)
              |> List.rev
          in
          let initial_block =
            product (List.map es ~f:(fun ((_, i, _, _) as e) -> current e i))
          in
          let ref_blocks =
            List.concat_map sg ~f:(fun r ->
                product
                  (List.map es ~f:(fun ((_, _, rs, _) as e) ->
                       current e
                         (List.concat_map rs ~f:(fun (r', ts) ->
                              if r = r' then ts else [])))))
          in
          let rows =
            List.fold (initial_block @ ref_blocks) ~init:[] ~f:(fun acc row ->
                if List.mem acc row ~equal:(List.equal equal_terms) then acc
                else row :: acc)
            |> List.rev
          in
          if LoopPhase.timeline then
            eprintf
              "mustrat-joint-class: members=%d sig=%d initial_rows=%d \
               ref_rows=%d rows=%d listed_ref_rows=%d\n%!"
              (List.length es) (List.length sg)
              (List.length initial_block)
              (List.length ref_blocks) (List.length rows)
              (* the refinement blocks' size before any reduction to distinct
                 terms, as a product of list lengths (saturating) *)
              (List.sum (module Int) sg ~f:(fun r ->
                   List.fold es ~init:1 ~f:(fun acc ((k, _, rs, _)) ->
                       let tset = term_set k in
                       let n =
                         List.count
                           (List.concat_map rs ~f:(fun (r', ts) ->
                                if r = r' then ts else []))
                           ~f:(Set.mem tset)
                       in
                       if n > 0 && acc > 1_000_000_000 / n then 1_000_000_000
                       else acc * n)));
          let covered =
            List.for_alli es ~f:(fun i (k, _, _, _) ->
                Set.equal
                  (Set.Poly.of_list
                     (List.map rows ~f:(fun row -> List.nth_exn row i)))
                  (term_set k))
          in
          if covered then Some (List.map es ~f:(fun (k, _, _, _) -> k), rows)
          else None)
end

(* Which ordinary strategy checks [race_check_plain_spacer] and
   [race_check_plain_spacer_after_first_rung] race against the plain Spacer.
   [races ~every_rung ~after_first_rung ~initial ~budget] is [true] when every
   check is raced ([every_rung]), or when only later rungs are
   ([after_first_rung]) and the check's budget [budget] (seconds) exceeds the
   first budget [initial].

   A side's budget starts at [initial] and only grows, doubling when a check
   at it ran out (or, under [bound_last_refinement], when the refinement's
   last form ran out of it), so [budget > initial] holds exactly for the
   checks asked after something of that side (of both, under a shared
   budget) was left undecided at its first budget.  The rule reads the budget alone, never an answer,
   so it chooses which checks race and nothing else: a raced check and an
   unraced one are each handled by the rules they are handled by under the
   race field and without it.  With both flags off it is [false] everywhere;
   it is monotone in [budget]. *)
module RaceRung = struct
  let races ~every_rung ~after_first_rung ~initial ~budget =
    every_rung || (after_first_rung && budget > initial)
end

(* Whether the fixpoint system [muclp] is over integers and Booleans only:
   every predicate's parameters, every variable a predicate body or the query
   binds, and every free variable of the query are of sort [Int] or [Bool]
   ([split_ground_goals_first_integer_only]).  Read off the input, before any
   play. *)
module SplitFirstGate = struct
  open Ast.LogicOld

  let discrete s = Term.is_int_sort s || Term.is_bool_sort s

  let applies (muclp : MuCLP.Problem.t) =
    let sorts_ok env = List.for_all env ~f:(fun (_, s) -> discrete s) in
    let set_ok set = Set.for_all set ~f:(fun (_, s) -> discrete s) in
    List.for_all muclp.preds ~f:(fun (p : MuCLP.Pred.t) ->
        sorts_ok p.args && set_ok (Formula.quantified_sort_env_of p.body))
    && set_ok (Formula.quantified_sort_env_of muclp.query)
    && set_ok (Formula.term_sort_env_of muclp.query)
end

(* Whether a ranking refinement whose re-synthesis attempts over all the
   counter-plays of a check failed asks the same attempts over the first play
   alone ([first_play_wf_resynthesis]) before the form with disjoined pieces.
   It does exactly when the field is on, re-synthesis is on, there is a first
   play and at least one further play (otherwise the first play alone is the
   problem just asked), and the build over all the plays declared at least
   one [WF] copy (otherwise there is no ranking to re-synthesise and the
   attempts would only rebuild the problem). *)
module FirstPlayWf = struct
  let asks ~enabled ~resynthesise ~first_plays ~extra_plays ~wf_copies =
    enabled && resynthesise && first_plays > 0 && extra_plays > 0
    && wf_copies > 0
end

(* The stall rule of the turn loop for a refinement that did not succeed.
   [stalls] counts the failed refinements in a row (reset by an accepted one);
   the run answers [unknown] once it reaches two, one per side.

   - [Refinement_failed]: the refinement returned and was unsolvable or left
     the strategy unchanged.  It counts: [after] adds one.
   - [Last_form_expired]: under [bound_last_refinement], the last (bounded)
     form of the refinement ran out of its budget, which is the check's
     current budget.  That is not evidence the refinement has no solution --
     only that this budget did not find one -- so it does not count: [after]
     leaves [stalls] as it is, and [doubles_budget] says the side's check
     budget is doubled before the turn passes, as a timed-out check's is.

   Postconditions: [after] never decreases [stalls]; [gives_up (after ~stalls
   Last_form_expired)] equals [gives_up stalls], so an expiry can never be the
   step that ends a run; and from [stalls = 0] two [Refinement_failed] in a row
   end it whatever expiries lie between them.  No rule here produces an
   answer other than [unknown]: an answer still comes only from a won check. *)
(* Test hooks of [refine_rankings = Joint_steered], read only under it.
   Under [COAR_MUSTRAT_STEER_AUDIT] every joint answer, and every ranking
   installed for a key after one, is checked against the two guarantees of
   the steered refinement, one stderr line each:
   - [answer]: the selected terms and the visit states at the model the
     selection ended at form one resolution of the check's own clauses (the
     goal at the query's values), and each ranking contains that play's
     chain pairs;
   - [install]: a ranking installed for a key contains every such pair an
     earlier joint answer of the run recorded for the key, and the pairs
     every later ranking of the key must contain include them.
   [COAR_MUSTRAT_STEER_MUTANT] breaks the arm on purpose, [drop_record] by
   recording none of the answer's own pairs, [generalised] by selecting on
   the lifted clauses with the goal generalised, so that a test can show the
   audit catches each; no configuration sets it, and without it nothing
   here changes a run. *)
module SteerAudit = struct
  type mutant = No_mutant | Drop_record | Generalised_source

  let mutant =
    lazy
      (match Sys.getenv "COAR_MUSTRAT_STEER_MUTANT" with
      | Some "drop_record" -> Drop_record
      | Some "generalised" -> Generalised_source
      | _ -> No_mutant)

  let mutant_is m =
    match (Lazy.force mutant, m) with
    | No_mutant, No_mutant
    | Drop_record, Drop_record
    | Generalised_source, Generalised_source ->
        true
    | _ -> false

  let enabled = lazy (Option.is_some (Sys.getenv "COAR_MUSTRAT_STEER_AUDIT"))

  (* per ranking key (by name), the pairs of the plays the run's joint
     answers ended at *)
  let moved :
      (string, (Ast.LogicOld.Term.t list * Ast.LogicOld.Term.t list) list)
      Hashtbl.t =
    Hashtbl.create (module String)

  let reset () = Hashtbl.clear moved

  let answer ~source ~own ~contained per_key =
    if Lazy.force enabled then (
      let own =
        match own () with
        | None -> "unavailable"
        | Some true -> "ok"
        | Some false -> "FAIL"
      in
      let contained = if contained () then "ok" else "FAIL" in
      List.iter per_key ~f:(fun (key, qs) ->
          Hashtbl.update moved key ~f:(fun old ->
              Option.value ~default:[] old @ qs));
      eprintf
        "mustrat-steer-audit: answer source=%s own_resolution=%s \
         contained=%s pairs=%d\n%!"
        source own contained
        (List.sum (module Int) per_key ~f:(fun (_, qs) -> List.length qs)))

  let install ~key ~contains ~demand =
    if Lazy.force enabled then
      match Hashtbl.find moved key with
      | None | Some [] -> ()
      | Some qs ->
          let n = List.length qs in
          let c = List.count qs ~f:contains in
          let d =
            List.count qs ~f:(fun q ->
                List.exists demand ~f:(fun p -> Stdlib.compare p q = 0))
          in
          eprintf
            "mustrat-steer-audit: install key=%s audited=%d contained=%d \
             demand=%d %s\n%!"
            key n c d
            (if c = n && d = n then "ok" else "FAIL")
end

module StallRule = struct
  type failure = Refinement_failed | Last_form_expired

  let after ~stalls = function
    | Refinement_failed -> stalls + 1
    | Last_form_expired -> stalls

  let gives_up stalls = stalls >= 2

  let doubles_budget = function
    | Refinement_failed -> false
    | Last_form_expired -> true
end

(* [closed_result args t]: for a term [t] of a functional Skolem key with
   parameters [args] (the result last), written as the equation [y = e] or
   [e = y] with [y] the result parameter, the term [e] when it mentions no
   variable; [None] for every other shape (a guarded definition, a term over
   the parameters).  Used to offer an argument-free key the constants it
   already holds. *)
module SnapConstants = struct
  let closed_result (args : Logic.sort_env_list) t =
    match List.last args with
    | None -> None
    | Some (y, _) -> (
        let is_y = function
          | Logic.Var (v, _) -> Ident.tvar_equal v y
          | _ -> false
        in
        match Logic.Term.let_apps t with
        | ( ( Logic.TyApp (Logic.Con (Logic.ExtTerm.Eq, _), _, _)
            | Logic.Con (Logic.ExtTerm.Eq, _) ),
            [ a; b ] ) ->
            let e = if is_y a then Some b else if is_y b then Some a else None in
            Option.bind e ~f:(fun e ->
                if Set.is_empty (Logic.Term.fvs_of e) then Some e else None)
        | _ -> None)
end

(* Model-guided term selection on a refinement problem; see [SkolemTerms]. *)
module SkolemTerms = SkolemTerms


(* Nested Skolem keys in a strategy check.

   A Skolem key [K] occurs in a check's clause as applications
   [K a_1 .. a_n r], whose last argument [r] (the result) is a universal of
   the clause.  A key [L] one of whose applications has an argument that
   mentions [K]'s result is the Skolem function of an existential nested
   inside [K]'s: its result is chosen after [K]'s, as a function of it.

   The check substitutes a key's term set by copying a formula once per term
   [t], the key replaced by [t] and its result renamed apart per copy, and
   joins the copies by a disjunction.  The result of every application nested
   in [K] must be renamed apart per copy as well.  A universal shared by two
   disjuncts of a clause is one value for both, while the nested application
   has different arguments in the two copies (its argument [r] is renamed);
   once [L]'s terms are substituted, the shared result must equal two
   different values, which none does, and the clause holds vacuously:
   [forall y. (y <> s t1 \/ B1 y) \/ (y <> s t2 \/ B2 y)] is true whenever
   [s t1 <> s t2], where the copies mean [B1 (s t1) \/ B2 (s t2)].  A vacuous
   clause of the check removes a derivation of the refuter's counter-play, so
   the side under check was reported winning when it was not.  Renaming each
   nested result apart per copy gives the disjunction of the copies'
   meanings, which is exact by the same argument as for the key's own result.
   Conversely, after such copying a key has several applications with
   distinct results, and each of them is renamed apart per term. *)
module NestedKeys = struct
  (* Every application of [key] in [t] as its arguments without the result
     and the result variable, in the order of a left-to-right traversal.
     Precondition: the last argument of every application of [key] is a
     variable (a Skolem key's result is a universal of the clause). *)
  let apps_of key t =
    let rec go acc t =
      if
        Logic.Term.is_var_app t
        && Ident.tvar_equal (Logic.Term.pvar_of_atom t) key
      then
        let _, args = Logic.Term.let_var_app t in
        match List.rev args with
        | ret :: rargs ->
            (List.rev rargs, fst (Logic.Term.let_var ret)) :: acc
        | [] -> acc
      else
        match t with
        | Logic.Var (_, _) | Logic.Con (_, _) -> acc
        | Logic.App (t1, t2, _) | Logic.Let (_, _, t1, t2, _) ->
            go (go acc t1) t2
        | Logic.Bin (_, _, _, t1, _)
        | Logic.TyApp (t1, _, _)
        | Logic.TyLam (_, t1, _) ->
            go acc t1
    in
    List.rev (go [] t)

  (* The results of the applications of [key] in [t], each once. *)
  let rets_of key t =
    List.map (apps_of key t) ~f:snd
    |> List.dedup_and_sort ~compare:Ident.tvar_compare

  (* The results of the applications of the keys [keys] in [t] that are
     nested, transitively, in a variable of [rets]: an application is nested
     when one of its arguments mentions [rets] or a nested result.
     Postcondition: disjoint from [rets]. *)
  let nested_rets ~keys t rets =
    let apps =
      List.concat_map keys ~f:(fun k ->
          List.map (apps_of k t) ~f:(fun (args, ret) ->
              ( Set.Poly.union_list (List.map args ~f:Logic.ExtTerm.fvs_of),
                ret )))
    in
    let rec fix scope =
      let scope' =
        List.fold apps ~init:scope ~f:(fun scope (fvs, ret) ->
            if Set.is_empty (Set.inter fvs scope) then scope
            else Set.add scope ret)
      in
      if Set.length scope' = Set.length scope then scope else fix scope'
    in
    let rets = Set.Poly.of_list rets in
    Set.diff (fix rets) rets |> Set.to_list

  (* [keys] reordered so that a key comes after every key it is nested in
     (in [t]); keys unrelated by nesting keep their relative order, and a
     cycle (which a Skolemisation does not produce) is broken by the given
     order. *)
  let order ~keys t =
    let rets = List.map keys ~f:(fun k -> (k, rets_of k t)) in
    let inside k k' =
      (* some application of [k] is nested in a result of [k'] *)
      (not (Ident.tvar_equal k k'))
      && List.exists (apps_of k t) ~f:(fun (args, _) ->
          let fvs = Set.Poly.union_list (List.map args ~f:Logic.ExtTerm.fvs_of) in
          List.exists
            (List.Assoc.find_exn ~equal:Ident.tvar_equal rets k')
            ~f:(Set.mem fvs))
    in
    let rec go acc = function
      | [] -> List.rev acc
      | remaining -> (
          match
            List.find remaining ~f:(fun k ->
                not (List.exists remaining ~f:(inside k)))
          with
          | Some k ->
              go (k :: acc)
                (List.filter remaining ~f:(Fn.non (Ident.tvar_equal k)))
          | None ->
              let k = List.hd_exn remaining in
              go (k :: acc) (List.tl_exn remaining))
    in
    go [] keys

  (* A renaming of the variables [vs] to fresh names absent from [taken]
     (and pairwise distinct, every name being drawn fresh). *)
  let renaming ~taken vs =
    Map.Poly.of_alist_exn
    @@ List.map vs ~f:(fun v ->
        (v, Ident.mk_fresh_tvar_avoiding ~prefix:"x" ~taken ()))
end

(* Which universals of a clause a key's choice among its terms may depend on.

   A clause of a side's pfwCSP is a fixpoint equation [U_X(p) => phi] (or the
   query) with every positive universal removed into the clause's
   universals, and each existential binder [exists r. theta] written as the
   disjunct [not K(a, r)] of an [or] node, [a] the variables bound above the
   binder (universal and existential alike) and the predicate's own
   parameters.  Substituting a term set [T] for [K] into a part [s] of the
   clause joins one copy of [s] per term with [or].  When [theta] holds a
   universal [forall y] of its own, [y] is a universal of the whole clause,
   and if it is shared by the copies, the clause [forall y. s_1(y) \/ s_2(y)]
   lets the choice of the term depend on [y]: a variable the opponent picks
   AFTER the binder.  That is weaker than [(forall y. s_1(y)) \/ (forall y.
   s_2(y))], the choice at the binder, and a check won by it is not a win:
   [exists x. forall y. y <> x + 1 \/ A y] with the terms [0] and [-2] for
   [x] was accepted because the shared [y] could be [1] in one copy and [-1]
   in the other.  So each copy renames apart the universals of [s] that the
   choice may not depend on: the inner universals of the clause's keys
   ([TermAlternatives.inner_vars], followed through the names earlier copies
   gave them), except the arguments [a] of the key's applications (an inner
   universal of an outer key is in scope of a nested one), the head's
   parameters [p] (a parameter the reduction adds to a predicate is not
   among [a] and is fixed for the whole equation), and the variables
   occurring outside [s].  Renaming a variable whose binder is not above the
   key's binder is exact either way: such a variable occurs only inside the
   part of the clause that its own binder governs, and a choice at the key's
   binder does not see it.  For the renaming to be possible, the part [s]
   must hold every occurrence of the inner universals it renames, so the
   placement is widened to them.  On a clause whose keys have no inner
   universal nothing is renamed and the placement is the one it was. *)
module ChoiceScope = struct
  (* The variables of the negated applications of unknowns that are neither
     keys ([is_key]) nor universals of the clause: the head's parameters.  An
     unknown of a fixpoint body occurs positively (negation normal form), so
     a negated application of an unknown that is not a key is the head. *)
  let heads ~uni_senv ~is_key phi =
    let rec go acc t =
      if Logic.BoolTerm.is_not t then
        match Logic.Term.let_apps (Logic.BoolTerm.let_not t) with
        | Logic.Var (v, _), args
          when (not (Map.Poly.mem uni_senv v)) && not (is_key v) ->
            Set.Poly.union_list (acc :: List.map args ~f:Logic.ExtTerm.fvs_of)
        | _ -> go acc (Logic.BoolTerm.let_not t)
      else
        match t with
        | Logic.Var (_, _) | Logic.Con (_, _) -> acc
        | Logic.App (t1, t2, _) | Logic.Let (_, _, t1, t2, _) ->
            go (go acc t1) t2
        | Logic.Bin (_, _, _, t1, _)
        | Logic.TyApp (t1, _, _)
        | Logic.TyLam (_, t1, _) ->
            go acc t1
    in
    go Set.Poly.empty phi

  (* The free variables of the arguments, result excluded, of the
     applications of the keys [keys] in [t]. *)
  let args_fvs ~keys t =
    Set.Poly.union_list
    @@ List.concat_map keys ~f:(fun key ->
        List.concat_map (NestedKeys.apps_of key t) ~f:(fun (args, _) ->
            List.map args ~f:Logic.ExtTerm.fvs_of))

  (* The universals of the part [t] of a clause to rename apart in each copy
     of [t] made for the keys [keys], [all_keys] being every key of the
     clause: those of [inner] (the inner universals of the clause's keys, with
     the names earlier copies gave them) occurring in [t], except the arguments of the
     keys' applications in [t], the head's parameters [heads], the variables
     in [outside] (every free variable of the clause outside [t]), the
     variables [local] the caller renames already and the results of the
     other keys; and then the results of the other keys' applications whose
     arguments mention a renamed variable, transitively.  A result of another
     key is the same side's choice: shared, it lets the choice of [keys]
     depend on it, which is exact when that key chooses before or beside them
     and owes nothing to a renamed variable. *)
  (* After a copy renames the variables by [ren], its new names of inner
     universals are inner too: a key substituted later inside the copy renames
     them apart again. *)
  let record ~inner ren =
    Map.Poly.iteri ren ~f:(fun ~key ~data ->
        if Hash_set.mem inner key then Hash_set.add inner data)

  let renamed ~inner ~keys ~all_keys ~heads ~outside ~local t =
    let args = args_fvs ~keys t in
    let local = Set.Poly.of_list local in
    let others =
      List.filter all_keys ~f:(fun k ->
          not (List.mem keys k ~equal:Ident.tvar_equal))
    in
    let other_rets =
      Set.Poly.of_list
        (List.concat_map others ~f:(fun k -> NestedKeys.rets_of k t))
    in
    let base =
      Logic.ExtTerm.fvs_of t
      |> Set.filter ~f:(fun v ->
          Hash_set.mem inner v
          && (not (Set.mem args v))
          && (not (Set.mem heads v))
          && (not (Set.mem outside v))
          && (not (Set.mem local v))
          && not (Set.mem other_rets v))
      |> Set.to_list
    in
    match base with
    | [] -> []
    | _ ->
        base
        @ List.filter (NestedKeys.nested_rets ~keys:others t base) ~f:(fun v ->
            (not (Set.mem local v)) && not (Set.mem outside v))
end

(* Where in a clause each key's term alternatives are placed
   ([miniscope_term_alternatives]).

   The strategy check substitutes a side's term-set strategy into its clauses:
   a Skolem key [K] with result [r] and term set [T] turns a clause [F] into
   the disjunction, over the terms [t] of [T], of [F] with [K := t] and [r]
   renamed apart per term.  Substituting into the WHOLE clause makes a clause
   that mentions keys [K_1 .. K_m] the disjunction of [prod |T_i|] copies,
   even when the keys occur in parts of the clause that have nothing to do with
   each other -- two existential blocks in two disjuncts of one fixpoint body,
   say, where the owner's choice in one block cannot interact with the other.

   This module places each key's disjunction instead at the smallest
   subformula that contains every occurrence of the key and of its result
   variable (its footprint), descending through conjunctions and disjunctions
   of the clause's negation normal form and grouping the operands of one
   n-ary connective into the connected components of the footprints they
   share.  Exact, by one identity: a context [C] built from [and] and [or]
   alone, with its hole occurring once and outside every negation, satisfies
   [C[a \/ b] <=> C[a] \/ C[b]] (by induction on [C]: [or] is associative and
   idempotent, [and] distributes over [or]).  A key's substitution at the
   subformula [s] of [C[s]], where [C] mentions neither the key nor its result
   variable, therefore gives a formula equivalent to its substitution into the
   whole clause: every copy of [C] is [C] itself, since the substitution and
   the renaming change only [s].  The fresh result variables are universals of
   the clause either way, one per copy, and so are the universals each copy
   renames apart because the choice may not depend on them ([ChoiceScope]);
   a key's footprint is widened by those ([inner_vars]), so that [s] holds
   every occurrence of each and renaming it inside [s] alone is exact.  So the clause decides exactly what the whole-clause
   substitution decides, and only the number and size of the alternatives
   change: two independent blocks of two keys with three terms each give
   [9 + 9] alternatives instead of [81].

   The result is a tree whose [Alts] nodes are the disjunctions created by the
   substitution (the alternatives), so that the caller can name each
   alternative by a fresh predicate wherever it sits; the tree read as a
   formula ([to_term]) is the substituted clause. *)
module TermAlternatives = struct
  type t =
    | Leaf of Logic.term
    | And of t list
    | Or of t list
    | Alts of t list  (** one disjunct per term of a key (alternatives) *)

  let rec to_term = function
    | Leaf t -> t
    | And ts -> Logic.BoolTerm.and_of (List.map ts ~f:to_term)
    | Or ts | Alts ts -> Logic.BoolTerm.or_of (List.map ts ~f:to_term)

  (* The tree of the connectives [and]/[or] of an NNF formula; everything else
     (a literal, a quantifier, an equality between Booleans, an if-then-else)
     is a leaf, and a key inside a leaf is substituted at the leaf. *)
  let rec of_nnf t =
    match Logic.Term.let_apps t with
    | Logic.Con (Logic.BoolTerm.And, _), _ :: _ :: _ ->
        And (List.map (Logic.BoolTerm.conjuncts_of t) ~f:of_nnf)
    | Logic.Con (Logic.BoolTerm.Or, _), _ :: _ :: _ ->
        Or (List.map (Logic.BoolTerm.disjuncts_of t) ~f:of_nnf)
    | _ -> Leaf t

  let rec map_leaves ~f = function
    | Leaf t -> Leaf (f t)
    | And ts -> And (List.map ts ~f:(map_leaves ~f))
    | Or ts -> Or (List.map ts ~f:(map_leaves ~f))
    | Alts ts -> Alts (List.map ts ~f:(map_leaves ~f))

  let rec fvs_of = function
    | Leaf t -> Logic.ExtTerm.fvs_of t
    | And ts | Or ts | Alts ts -> Set.Poly.union_list (List.map ts ~f:fvs_of)

  (* [mem_fv x t] is [Set.mem (Logic.ExtTerm.fvs_of t) x], case for case:
     a variable counts unless it is a dummy term or a name of the function
     environment, a binder removes its variable from its body's set, and a
     [let] removes its variable from its body's set only (its definition is
     outside the name's scope, so an occurrence of the bound name there is
     free, as in [Logic.Term.occurs_free]).  It stops at the first
     occurrence and allocates nothing. *)
  let rec mem_fv x = function
    | Logic.Var (v, _) ->
        Ident.tvar_equal v x
        && (not (LogicOld.is_dummy_term v None))
        && not (Map.Poly.mem (LogicOld.get_fenv ()) v)
    | Logic.Con (_, _) -> false
    | Logic.App (t1, t2, _) -> mem_fv x t1 || mem_fv x t2
    | Logic.Bin (_, v, _, t, _) -> (not (Ident.tvar_equal v x)) && mem_fv x t
    | Logic.Let (v, _, t1, t2, _) ->
        mem_fv x t1 || ((not (Ident.tvar_equal v x)) && mem_fv x t2)
    | Logic.TyApp (t, _, _) | Logic.TyLam (_, t, _) -> mem_fv x t

  (* [tree_meets ys t] is [not (Set.is_empty (Set.inter (fvs_of t) ys))]: [fvs_of]
     of a tree is the union of its leaves' sets, so the intersection is
     non-empty iff some leaf has some member of [ys] free.  Allocation-free,
     stopping at the first such leaf. *)
  let rec tree_meets ys = function
    | Leaf t -> Set.exists ys ~f:(fun y -> mem_fv y t)
    | And ts | Or ts | Alts ts -> List.exists ts ~f:(tree_meets ys)

  (* [inner_vars ~uni_senv ~is_key ~heads tree]: for each key with a
     literal [not K(a, r)] in the NNF tree [tree] of a clause, the universals
     its choice may not depend on and that a placement must therefore hold
     every occurrence of ([ChoiceScope]).  The binder of [K] is read as the
     [or] node the literal is a disjunct of (the literal itself when it is
     no disjunct); its inner universals are the universals occurring in that
     node and nowhere outside it, except the literal's arguments [a], the
     head's parameters [heads], and the results of the other keys (the same
     side's choices), but with the results of the keys whose arguments mention
     an inner universal, transitively.  The set may also hold a variable bound in a branch
     beside the binder inside the node; renaming that apart per copy is
     exact too, and only widens the placement. *)
  let inner_vars ~uni_senv ~is_key ~heads tree =
    let key_lit = function
      | Leaf l when Logic.BoolTerm.is_not l -> (
          match Logic.Term.let_apps (Logic.BoolTerm.let_not l) with
          | Logic.Var (v, _), args when is_key v -> (
              match List.rev args with
              | Logic.Var (y, _) :: rargs -> Some (v, List.rev rargs, Some y)
              | rargs -> Some (v, List.rev rargs, None))
          | _ -> None)
      | _ -> None
    in
    (* per key: the paths of its binder nodes, the free variables of its
       literals' arguments, and the results of the key literals beside it *)
    let binders = Hashtbl.Poly.create () in
    let note key path args sibs =
      let paths, afvs, srets =
        Option.value (Hashtbl.find binders key)
          ~default:([], Set.Poly.empty, Set.Poly.empty)
      in
      Hashtbl.set binders ~key
        ~data:
          ( path :: paths,
            Set.Poly.union_list (afvs :: List.map args ~f:Logic.ExtTerm.fvs_of),
            Set.union srets sibs )
    in
    let rec collect path t =
      match t with
      | Or ts ->
          let lits = List.filter_map ts ~f:key_lit in
          let sibs =
            Set.Poly.of_list (List.filter_map lits ~f:(fun (_, _, y) -> y))
          in
          List.iter lits ~f:(fun (k, args, _) -> note k path args sibs);
          List.iteri ts ~f:(fun i d ->
              if Option.is_none (key_lit d) then collect (path @ [ i ]) d)
      | And ts | Alts ts -> List.iteri ts ~f:(fun i d -> collect (path @ [ i ]) d)
      | Leaf _ -> (
          match key_lit t with
          | Some (k, args, y) ->
              note k path args
                (Option.value_map y ~default:Set.Poly.empty
                   ~f:Set.Poly.singleton)
          | None -> ())
    in
    collect [] tree;
    let rec subtree path t =
      match (path, t) with
      | [], _ -> t
      | i :: rest, (And ts | Or ts | Alts ts) -> subtree rest (List.nth_exn ts i)
      | _ :: _, Leaf _ -> t
    in
    (* the free variables of the leaves outside the nodes at [paths] *)
    let outside paths =
      let rec go path t =
        if List.mem paths path ~equal:(List.equal Int.equal) then
          Set.Poly.empty
        else
          match t with
          | Leaf l -> Logic.ExtTerm.fvs_of l
          | And ts | Or ts | Alts ts ->
              Set.Poly.union_list
                (List.mapi ts ~f:(fun i d -> go (path @ [ i ]) d))
      in
      go [] tree
    in
    let memo = Hashtbl.Poly.create () in
    let whole = to_term tree in
    let all_keys = Set.to_list (Set.filter (Logic.ExtTerm.fvs_of whole) ~f:is_key) in
    let rets_of = Hashtbl.Poly.create () in
    List.iter all_keys ~f:(fun k ->
        Hashtbl.set rets_of ~key:k ~data:(NestedKeys.rets_of k whole));
    Hashtbl.fold binders ~init:Map.Poly.empty
      ~f:(fun ~key ~data:(paths, afvs, sibs) acc ->
        (* the results of the other keys: the same side's choices, which the
           key may depend on unless they owe something to an inner universal
           (added back below) *)
        let other_rets =
          Set.Poly.of_list
            (List.concat_map all_keys ~f:(fun k ->
                 if Ident.tvar_equal k key then []
                 else Hashtbl.find_exn rets_of k))
        in
        let own_rets = Set.Poly.of_list (Hashtbl.find_exn rets_of key) in
        let paths = List.dedup_and_sort paths ~compare:(List.compare Int.compare) in
        let inside, out =
          Hashtbl.find_or_add memo paths ~default:(fun () ->
              ( Set.Poly.union_list
                  (List.map paths ~f:(fun p -> fvs_of (subtree p tree))),
                outside paths ))
        in
        let inner =
          Set.filter inside ~f:(fun v ->
              Map.Poly.mem uni_senv v
              && (not (Set.mem out v))
              && (not (Set.mem afvs v))
              && (not (Set.mem heads v))
              && (not (Set.mem sibs v))
              && (not (Set.mem own_rets v))
              && not (Set.mem other_rets v))
        in
        let inner =
          if Set.is_empty inner then inner
          else
            Set.union inner
              (Set.Poly.of_list
                 (NestedKeys.nested_rets ~keys:all_keys whole
                    (Set.to_list inner)))
        in
        Map.Poly.set acc ~key ~data:inner)

  (* The number of alternatives the substitution created: the disjuncts of
     every [Alts] node, nested ones included. *)
  let rec num_alternatives = function
    | Leaf _ -> 0
    | And ts | Or ts -> List.sum (module Int) ts ~f:num_alternatives
    | Alts ts -> List.length ts + List.sum (module Int) ts ~f:num_alternatives

  (* A key to place: its name, its parameters, its terms (already
     deduplicated by the caller), its footprint and every key of the clause.
     The footprint is the names of the keys related to it by nesting
     ([NestedKeys]), transitively in either direction, and of their results:
     a key nested in [K] is copied and renamed with [K]'s copies, so all
     occurrences of either must lie inside the subformula where [K] is
     substituted, and a nested key must be placed at that subformula and not
     below it, where its own copies would be copied again by [K] with their
     results shared. *)
  type key = {
    key : Ident.tvar;
    params : Logic.sort_env_list;
    terms : Logic.term list;
    footprint : Ident.tvar Set.Poly.t;
    all_keys : Ident.tvar list;
    members : (Ident.tvar * Logic.sort_env_list) list;
        (** empty for a single key; otherwise a unit of
            [joint_term_alternatives]: at least two keys, none related by
            nesting to another key of the clause, substituted together, [key]
            and [params] being the first member's, [terms] empty and
            [footprint] the union of the members' footprints *)
    rows : Logic.term list list;
        (** a unit's alternatives, each a term per member in the order of
            [members]; empty for a single key *)
  }

  (* A single key [k] with its terms [terms]. *)
  let single ~key ~params ~terms ~footprint ~all_keys =
    { key; params; terms; footprint; all_keys; members = []; rows = [] }

  (* The keys a record substitutes, with their parameters, and its
     alternatives as one term per key: for a single key, one alternative per
     term. *)
  let members_of k =
    if List.is_empty k.members then [ (k.key, k.params) ] else k.members

  let rows_of k =
    if List.is_empty k.members then List.map k.terms ~f:(fun t -> [ t ])
    else k.rows

  let meets k fvs = not (Set.is_empty (Set.inter k.footprint fvs))

  (* [substitute ~uni_senv ~taken k tree]: [Alts] of one copy of [tree] per
     term of [k] (per row of a unit, every member replaced by its term of the
     row at once), the key replaced by the term and the results of its
     applications and of the applications nested in them ([NestedKeys])
     renamed apart, per copy, to names absent from [uni_senv] and from
     [taken], which must hold every free variable of the clause; the renamed
     environment is returned too.  A copy that is itself an [Alts] is spliced
     in ([or] is associative).  Precondition: every key [k] is nested in has
     been substituted already, and every occurrence of the renamed results in
     the clause lies inside [tree]. *)
  let substitute ~uni_senv ~taken ~inner ~heads ~outside k tree =
    let whole = to_term tree in
    let members = members_of k in
    let rets =
      match members with
      | [ (key, _) ] -> NestedKeys.rets_of key whole
      | _ ->
          List.concat_map members ~f:(fun (key, _) ->
              NestedKeys.rets_of key whole)
          |> List.dedup_and_sort ~compare:Ident.tvar_compare
    in
    (* Only the keys of [k]'s footprint can have an application nested in a
       result of [k]: the footprint holds every key related to [k] by nesting
       in the whole clause, and [tree] is a part of the clause with some keys
       already substituted, which removes applications (and the edges from
       their arguments to their results) and renames variables consistently,
       so it adds no nesting.  Reading every key of the clause instead made
       each substitution scan the applications of all of them, and a clause
       with hundreds of keys placed by footprints (a check whose terms are not
       of the one-point form) spent minutes here. *)
    let nest_keys = List.filter k.all_keys ~f:(Set.mem k.footprint) in
    let local = rets @ NestedKeys.nested_rets ~keys:nest_keys whole rets in
    (* with two copies or more, also the universals the choice may not
       depend on ([ChoiceScope]); one copy needs no renaming *)
    let local =
      match rows_of k with
      | _ :: _ :: _ ->
          local
          @ ChoiceScope.renamed ~inner ~keys:(List.map members ~f:fst)
              ~all_keys:k.all_keys ~heads ~outside ~local whole
      | _ -> local
    in
    let copies =
      List.map (rows_of k) ~f:(fun row ->
          let term_fvs =
            Set.Poly.union_list (List.map row ~f:Logic.ExtTerm.fvs_of)
          in
          let ren =
            NestedKeys.renaming local ~taken:(fun v ->
                Map.Poly.mem uni_senv v || Set.mem taken v
                || Set.mem term_fvs v)
          in
          ChoiceScope.record ~inner ren;
          (* every member at once: each is replaced by a lambda over its own
             parameters, which mentions no other member *)
          let sub =
            Map.Poly.of_alist_exn
            @@ List.map2_exn members row ~f:(fun (key, params) term ->
                (key, Logic.ExtTerm.mk_lambda params term))
          in
          let copy =
            map_leaves tree ~f:(fun leaf ->
                Logic.ExtTerm.rename ren @@ Logic.ExtTerm.subst sub leaf)
          in
          (Map.rename_keys_map ren uni_senv, copy))
    in
    let uni_senv' =
      match copies with
      | [] -> List.fold local ~init:uni_senv ~f:Map.Poly.remove
      | _ -> Map.force_merge_list (List.map copies ~f:fst)
    in
    ( uni_senv',
      Alts
        (List.concat_map copies ~f:(fun (_, c) ->
             match c with Alts cs -> cs | c -> [ c ])) )

  (* [substitute_seq ~uni_senv ~taken ks tree]: the keys [ks] substituted
     one after another into [tree] by [substitute], in the order of [ks].
     A maximal run of keys that each have one alternative and no other key in
     their footprint is done without rebuilding and traversing the whole tree
     once per key, with the same result, fresh names included: such a key's
     results and the results nested in them are neither renamed nor removed
     by another key of the run (no other key's applications are nested in its
     results, and its own applications mention no other key's result), so its
     results, its renaming and its substitution are those the one-by-one form
     computes.  The steps are taken key by key as there, each drawing its
     renaming and then rewriting the leaves in the order [map_leaves] visits
     them, but only the leaves that mention the key or a name it renames, and
     every leaf holding a binder (the substitution renames a binder, drawing a
     fresh name, even where it substitutes nothing); on any other leaf the
     substitution and the renaming change nothing and draw nothing.  With one
     alternative a step's [Alts] has one copy, so the run gives one [Alts]
     node, as the one-by-one form does once copies that are [Alts] are
     spliced in.  A clause of a transition system placed by footprints holds
     hundreds of such keys at its root, and the one-by-one form rebuilt and
     traversed the whole clause for each of them. *)
  (* how many runs of at least two keys [substitute_seq] has done in one
     traversal in this process; read only by tests *)
  let batched_runs = Atomic.make 0

  let substitute_seq ~uni_senv ~taken ~inner ~heads ~outside ks tree =
    let batchable k =
      List.length (rows_of k) = 1
      && Set.for_all k.footprint ~f:(fun v ->
          List.exists (members_of k) ~f:(fun (m, _) -> Ident.tvar_equal m v)
          || not (List.mem k.all_keys v ~equal:Ident.tvar_equal))
    in
    let rec has_binder = function
      | Logic.Bin _ | Logic.Let _ -> true
      | Logic.Var _ | Logic.Con _ -> false
      | Logic.App (t1, t2, _) -> has_binder t1 || has_binder t2
      | Logic.TyApp (t, _, _) | Logic.TyLam (_, t, _) -> has_binder t
    in
    let run uni_senv tree run_ks =
      match run_ks with
      | [] -> (uni_senv, tree)
      | [ k ] -> substitute ~uni_senv ~taken ~inner ~heads ~outside k tree
      | _ ->
          Atomic.incr batched_runs;
          let whole = to_term tree in
          (* the leaves in the order [map_leaves] visits them *)
          let acc = ref [] in
          ignore
            (map_leaves tree ~f:(fun leaf ->
                 acc := leaf :: !acc;
                 leaf));
          let leaves = Array.of_list (List.rev !acc) in
          let with_binder =
            List.filter (List.init (Array.length leaves) ~f:Fn.id) ~f:(fun i ->
                has_binder leaves.(i))
          in
          let occurrences = Hashtbl.Poly.create () in
          Array.iteri leaves ~f:(fun i leaf ->
              Set.iter (Logic.ExtTerm.fvs_of leaf) ~f:(fun v ->
                  Hashtbl.add_multi occurrences ~key:v ~data:i));
          let uni_senv =
            List.fold run_ks ~init:uni_senv ~f:(fun uni_senv k ->
                let members = members_of k in
                let rets =
                  match members with
                  | [ (key, _) ] -> NestedKeys.rets_of key whole
                  | _ ->
                      List.concat_map members ~f:(fun (key, _) ->
                          NestedKeys.rets_of key whole)
                      |> List.dedup_and_sort ~compare:Ident.tvar_compare
                in
                let nest_keys =
                  List.filter k.all_keys ~f:(Set.mem k.footprint)
                in
                let local =
                  rets @ NestedKeys.nested_rets ~keys:nest_keys whole rets
                in
                let row = List.hd_exn (rows_of k) in
                let term_fvs =
                  Set.Poly.union_list (List.map row ~f:Logic.ExtTerm.fvs_of)
                in
                let ren =
                  NestedKeys.renaming local ~taken:(fun v ->
                      Map.Poly.mem uni_senv v || Set.mem taken v
                      || Set.mem term_fvs v)
                in
                let sub =
                  Map.Poly.of_alist_exn
                  @@ List.map2_exn members row ~f:(fun (key, params) term ->
                      (key, Logic.ExtTerm.mk_lambda params term))
                in
                let touched =
                  List.concat_map
                    (List.map members ~f:fst @ local)
                    ~f:(fun v ->
                      Option.value ~default:[] (Hashtbl.find occurrences v))
                  @ with_binder
                  |> List.dedup_and_sort ~compare:Int.compare
                in
                List.iter touched ~f:(fun i ->
                    leaves.(i) <-
                      Logic.ExtTerm.rename ren
                      @@ Logic.ExtTerm.subst sub leaves.(i));
                Map.rename_keys_map ren uni_senv)
          in
          let next = ref 0 in
          let copy =
            map_leaves tree ~f:(fun _ ->
                let leaf = leaves.(!next) in
                incr next;
                leaf)
          in
          (uni_senv, Alts (match copy with Alts cs -> cs | c -> [ c ]))
    in
    let uni_senv, tree, pending =
      List.fold ks ~init:(uni_senv, tree, [])
        ~f:(fun (uni_senv, tree, pending) k ->
          if batchable k then (uni_senv, tree, k :: pending)
          else
            let uni_senv, tree = run uni_senv tree (List.rev pending) in
            let uni_senv, tree =
              substitute ~uni_senv ~taken ~inner ~heads ~outside k tree
            in
            (uni_senv, tree, []))
    in
    run uni_senv tree (List.rev pending)

  (* Union-find over the operand indices [0 .. n-1] of one connective: two
     operands are in one component when some key's footprint meets both. *)
  let components ks fvss =
    let n = Array.length fvss in
    let parent = Array.init n ~f:Fn.id in
    let rec find i = if parent.(i) = i then i else find parent.(i) in
    let union i j =
      let ri = find i and rj = find j in
      if ri <> rj then parent.(ri) <- rj
    in
    List.iter ks ~f:(fun k ->
        match List.filter (List.init n ~f:Fn.id) ~f:(fun i -> meets k fvss.(i)) with
        | i :: is -> List.iter is ~f:(union i)
        | [] -> ());
    List.init n ~f:Fn.id
    |> List.map ~f:(fun i -> (find i, i))
    |> List.Assoc.sort_and_group ~compare:Int.compare
    |> List.map ~f:snd

  (* [place ~uni_senv ~taken ks tree]: every key of [ks] -- each one's
     footprint lying inside [tree] -- substituted at the smallest subformula
     holding its footprint, keys in the order of [ks] wherever two are placed
     at one node. *)
  let rec place ~uni_senv ~taken ~inner ~heads ~outside ks tree =
    let subst_all uni_senv tree =
      substitute_seq ~uni_senv ~taken ~inner ~heads ~outside ks tree
    in
    match (ks, tree) with
    | [], _ -> (uni_senv, tree)
    | _, ((And ts | Or ts) as node) ->
        let rebuild ts = match node with And _ -> And ts | _ -> Or ts in
        let arr = Array.of_list ts in
        let fvss = Array.map arr ~f:fvs_of in
        (* the free variables of the clause outside the operands [idxs] *)
        let outside_of idxs =
          Set.Poly.union_list
            (outside
            :: List.filter_mapi (Array.to_list fvss) ~f:(fun j fvs ->
                if List.mem idxs j ~equal:Int.equal then None else Some fvs))
        in
        let uni_senv, parts =
          List.fold_map (components ks fvss) ~init:uni_senv
            ~f:(fun uni_senv idxs ->
              let kc =
                List.filter ks ~f:(fun k ->
                    List.exists idxs ~f:(fun i -> meets k fvss.(i)))
              in
              match idxs with
              | [ i ] ->
                  place ~uni_senv ~taken ~inner ~heads ~outside:(outside_of [ i ]) kc
                    arr.(i)
              | _ ->
                  let spanning, local =
                    List.partition_tf kc ~f:(fun k ->
                        List.count idxs ~f:(fun i -> meets k fvss.(i)) >= 2)
                  in
                  let uni_senv, sub =
                    List.fold_map idxs ~init:uni_senv ~f:(fun uni_senv i ->
                        place ~uni_senv ~taken ~inner ~heads
                          ~outside:(outside_of [ i ])
                          (List.filter local ~f:(fun k -> meets k fvss.(i)))
                          arr.(i))
                  in
                  substitute_seq ~uni_senv ~taken ~inner ~heads
                    ~outside:(outside_of idxs) spanning (rebuild sub))
        in
        (uni_senv, rebuild parts)
    | _, (Leaf _ | Alts _) -> subst_all uni_senv tree

  (* [one_point ~uni_senv ks tree]: the placement of the keys [ks] (terms
     already deduplicated) in the NNF tree [tree] of a clause by the one-point
     rule, or [None] when its preconditions fail and the caller is to place
     by footprints as above.

     A Skolemised clause states a key [K] with result [y] as a disjunct
     [not K(a, y)] of an [or] node (the clause's top for an outermost
     existential, an inner disjunction for a nested one), [y] a universal of
     the clause.  [place] counts that literal in [K]'s footprint, so every
     key's footprint reaches the literal's node, and a clause with keys
     [K_1 .. K_m] becomes the
     disjunction of [prod |T_i|] copies even when each result occurs in one
     small part of it: an integer transition system's initial clause draws
     six to twenty nondeterministic values, each a key, and its check grew to
     thousands of named alternatives after one refinement.  When every term
     of [K] has the form [y = s] (or [s = y]) with [y] not in [s], the copy
     for that term is [forall y. C[y <> s(a) \/ R(y)]], which is [C[R(s(a))]]
     when [y] occurs nowhere outside the literal's node and the context [C] is
     built from [and]/[or] alone (take [y := s(a)] one way; the other way,
     [y = s(a)] gives [C[R(s(a))]] itself and any other [y] makes the node
     true, and [C] is monotone); so the literal is dropped (a node left with
     no disjunct is [false]) and [y] is replaced by [s(a)] wherever it
     occurs.  The footprint of [K] is then the occurrences of its
     results alone, and [K] is substituted at the smallest subformula holding
     them, the operands of an [and]/[or] node that hold them regrouped into
     one node of the same connective (associativity and commutativity): by
     the identity stated above ([C[a \/ b] <=> C[a] \/ C[b]] for a context of
     [and]/[or] with its hole once), the result is equivalent to the
     whole-clause substitution.

     Preconditions, each checked (any failure answers [None]): a key occurs
     only as such a disjunct, a negated application whose last argument is a
     variable of [uni_senv] occurring nowhere outside the disjunct's [or]
     node; results are pairwise distinct and
     none occurs in an argument of an application of its own key; every term
     of every key has the one-point form; and the keys can be ordered so that
     a key comes before every key whose results its arguments mention (a key
     nested in another is substituted first, so that no dropped literal still
     mentions a result being replaced).  Among the keys allowed next, one
     whose results occur only in predicate-free leaves is taken first, so that
     its alternatives stay inside a predicate-free part and are not copied
     with the predicate atoms of the keys taken later; any order gives an
     equivalent formula, since the disjunction over a product of term choices
     does not depend on the order the choices are made in.
     Postcondition: the tree read as a formula ([to_term]) is equivalent,
     under the returned environment (the clause's without the eliminated
     results), to the substitution of the strategy into the whole clause.  No
     variable is renamed, since no result survives. *)
  (* how many clauses [of_clause] has placed by [one_point] in this process;
     read only by the trace of a strategy check *)
  let one_point_count = Atomic.make 0

  (* how many units of [joint_term_alternatives] [of_clause] has placed in
     this process, and how many rows they had; read only by a census line of
     a strategy check *)
  let unit_count = Atomic.make 0
  let unit_rows_count = Atomic.make 0

  let one_point ~uni_senv ks tree =
    let exception Fallback in
    try
      (* the record substituting the key [v] (a single key, or the unit [v]
         is a member of) *)
      let key_of v =
        List.find ks ~f:(fun k ->
            List.exists (members_of k) ~f:(fun (m, _) -> Ident.tvar_equal m v))
      in
      (* A key literal [not K(a, y)] as a disjunct of an [or] node (the
         clause's top counts as one), with [y] a universal of the clause. *)
      let key_app = function
        | Leaf l when Logic.BoolTerm.is_not l -> (
            match Logic.Term.let_apps (Logic.BoolTerm.let_not l) with
            | Logic.Var (v, _), args when Option.is_some (key_of v) -> (
                match List.rev args with
                | Logic.Var (y, _) :: rargs when Map.Poly.mem uni_senv y ->
                    Some (Option.value_exn (key_of v), v, List.rev rargs, y)
                | _ -> raise Fallback)
            | _ -> None)
        | _ -> None
      in
      (* The tree without its key literals, and each literal with the path
         (child indices from the root) of the [or] node it was a disjunct of;
         an [or] node left with no disjunct is [false]. *)
      let apps = ref [] in
      let rec strip path t =
        match t with
        | Or ts ->
            let kept =
              List.filter_mapi ts ~f:(fun i d ->
                  match key_app d with
                  | Some (k, m, args, y) ->
                      apps := (k, m, args, y, path) :: !apps;
                      None
                  | None -> Some (strip (path @ [ i ]) d))
            in
            (match kept with
            | [] -> Leaf (Logic.BoolTerm.mk_bool false)
            | [ d ] -> d
            | ds -> Or ds)
        | And ts -> And (List.mapi ts ~f:(fun i d -> strip (path @ [ i ]) d))
        | Leaf _ | Alts _ -> t
      in
      let body =
        match tree with
        | Or _ -> strip [] tree
        | t -> (
            match key_app t with
            | Some (k, m, args, y) ->
                apps := [ (k, m, args, y, []) ];
                Leaf (Logic.BoolTerm.mk_bool false)
            | None -> strip [] t)
      in
      let apps = List.rev !apps in
      (* [y] occurs in the original tree outside the node at [path] (its own
         literal and every other occurrence must lie inside that node, so that
         the one-point rule may be applied there). *)
      let occurs_outside path y =
        let rec go p t =
          if List.equal Int.equal p path then false
          else
            match t with
            | Leaf l -> mem_fv y l
            | And ts | Or ts | Alts ts ->
                List.existsi ts ~f:(fun i d -> go (p @ [ i ]) d)
        in
        go [] tree
      in
      if List.exists apps ~f:(fun (_, _, _, y, path) -> occurs_outside path y)
      then raise Fallback;
      let apps = List.map apps ~f:(fun (k, m, args, y, _) -> (k, m, args, y)) in
      let key_set =
        Set.Poly.of_list
          (List.concat_map ks ~f:(fun k -> List.map (members_of k) ~f:fst))
      in
      let rets = List.map apps ~f:(fun (_, _, _, y) -> y) in
      let args_fvs args =
        Set.Poly.union_list (List.map args ~f:Logic.ExtTerm.fvs_of)
      in
      if
        (not (Set.is_empty (Set.inter (fvs_of body) key_set)))
        || List.contains_dup rets ~compare:Ident.tvar_compare
        || List.exists ks ~f:(fun k ->
               List.exists (members_of k) ~f:(fun (m, _) ->
                   not
                     (List.exists apps ~f:(fun (_, m', _, _) ->
                          Ident.tvar_equal m m'))))
        || List.exists apps ~f:(fun (_, m, args, _) ->
               (* an application whose arguments mention a result of its own
                  key; a unit's member may mention another member's results,
                  which the row's substitution resolves *)
               List.exists apps ~f:(fun (_, m', _, y) ->
                   Ident.tvar_equal m m' && Set.mem (args_fvs args) y))
      then raise Fallback;
      (* Each term as the right-hand side [s] of [ret = s], [ret] the last
         of the key's parameters [params]. *)
      let rhs_of params term =
        match List.last params with
        | None -> raise Fallback
        | Some (ret, _) -> (
            let is_ret = function
              | Logic.Var (v, _) -> Ident.tvar_equal v ret
              | _ -> false
            in
            let free_of_ret t = not (Set.mem (Logic.ExtTerm.fvs_of t) ret) in
            match Logic.Term.let_apps term with
            | Logic.TyApp (Logic.Con (Logic.BoolTerm.Eq, _), _, _), [ a; b ]
              when is_ret a && free_of_ret b ->
                b
            | Logic.TyApp (Logic.Con (Logic.BoolTerm.Eq, _), _, _), [ a; b ]
              when is_ret b && free_of_ret a ->
                a
            | _ -> raise Fallback)
      in
      (* per record, its alternatives, each the right-hand side per member *)
      let rhss =
        List.map ks ~f:(fun k ->
            ( k.key,
              List.map (rows_of k) ~f:(fun row ->
                  List.map2_exn (members_of k) row ~f:(fun (m, params) term ->
                      (m, rhs_of params term))) ))
      in
      (* [Set.for_all (Logic.ExtTerm.fvs_of t) ~f:(Map.Poly.mem uni_senv)],
         without building the set: a variable bound by an enclosing binder or
         [let] of [t] ([bound]) is not free there, nor is a dummy term or a
         name of the function environment ([mem_fv]'s cases). *)
      let pure_leaf t =
        let rec all bound = function
          | Logic.Var (v, _) ->
              List.mem bound v ~equal:Ident.tvar_equal
              || LogicOld.is_dummy_term v None
              || Map.Poly.mem (LogicOld.get_fenv ()) v
              || Map.Poly.mem uni_senv v
          | Logic.Con (_, _) -> true
          | Logic.App (t1, t2, _) -> all bound t1 && all bound t2
          | Logic.Bin (_, v, _, t, _) -> all (v :: bound) t
          | Logic.Let (v, _, t1, t2, _) ->
              (* the definition is outside [v]'s scope *)
              all bound t1 && all (v :: bound) t2
          | Logic.TyApp (t, _, _) | Logic.TyLam (_, t, _) -> all bound t
        in
        all [] t
      in
      (* The leaves of [tree] that are not predicate-free: the results [ys]
         occur only in predicate-free leaves of [tree] iff no member of [ys]
         is free in one of these, which is the emptiness of [ys] against the
         union of their free variables. *)
      let rec impure_leaves acc = function
        | Leaf t -> if pure_leaf t then acc else t :: acc
        | And ts | Or ts | Alts ts -> List.fold ts ~init:acc ~f:impure_leaves
      in
      (* [k], with its applications [kapps] (member, arguments and result),
         substituted at the smallest subformula of [tree] holding the results
         [ys]. *)
      let substitute_at k kapps ys tree =
        let params_of m =
          let ps =
            List.Assoc.find_exn (members_of k) ~equal:Ident.tvar_equal m
          in
          List.map ~f:fst (List.take ps (List.length ps - 1))
        in
        (* A unit's member whose arguments mention another member's result
           has that result replaced too: the row's map is closed under itself
           (the one-point rule applied to the inner member first, then to the
           outer one, as for two keys taken one after the other); at most one
           round per member, since nesting has no cycle, else [Fallback].  A
           single key's map mentions none of its own results, so it is closed
           as it is. *)
        let rec close n sub =
          if
            not
              (Map.Poly.exists sub ~f:(fun t ->
                   Set.exists (Logic.ExtTerm.fvs_of t) ~f:(Map.Poly.mem sub)))
          then sub
          else if n = 0 then raise Fallback
          else close (n - 1) (Map.Poly.map sub ~f:(Logic.ExtTerm.subst sub))
        in
        let subs =
          List.map (List.Assoc.find_exn rhss ~equal:Ident.tvar_equal k.key)
            ~f:(fun alt ->
              close (List.length (members_of k))
              @@ Map.Poly.of_alist_exn
              @@ List.map kapps ~f:(fun (m, args, y) ->
                  ( y,
                    Logic.ExtTerm.subst
                      (Map.Poly.of_alist_exn (List.zip_exn (params_of m) args))
                      (List.Assoc.find_exn alt ~equal:Ident.tvar_equal m) )))
        in
        let meets t = tree_meets ys t in
        let subst_here t =
          Alts
            (List.concat_map subs ~f:(fun sub ->
                 match map_leaves t ~f:(Logic.ExtTerm.subst sub) with
                 | Alts cs -> cs
                 | c -> [ c ]))
        in
        let rec go t =
          if not (meets t) then t
          else
            match t with
            | And ts | Or ts -> (
                let rebuild ts = match t with And _ -> And ts | _ -> Or ts in
                match List.partition_tf ts ~f:meets with
                | [ _ ], _ ->
                    rebuild (List.map ts ~f:(fun u -> if meets u then go u else u))
                | _, [] -> subst_here t
                | ms, others -> rebuild (others @ [ subst_here (rebuild ms) ]))
            | Leaf _ | Alts _ -> subst_here t
        in
        go tree
      in
      (* The keys are taken one at a time.  A key is allowed when no pending
         application of another key has an argument mentioning one of its
         results; among the allowed keys, in the order of their names, the
         first whose results occur only in predicate-free leaves is taken,
         else the first.  The results of a key are fixed (all its
         applications leave [pending] together), so whether a key is allowed
         is kept as a count, per key, of the pending applications of other
         keys whose arguments mention its results, decremented as keys are
         taken; and the predicate-free test reads the variables of the
         tree's other leaves once per step.  A step thus costs one traversal
         of the tree, not one per key and pending application. *)
      let key_rets = Hashtbl.Poly.create () in
      List.iter apps ~f:(fun (k, _, _, y) ->
          Hashtbl.update key_rets k.key ~f:(fun ys ->
              Set.add (Option.value ~default:Set.Poly.empty ys) y));
      let owner = Hashtbl.Poly.create () in
      List.iter apps ~f:(fun (k, _, _, y) ->
          Hashtbl.set owner ~key:y ~data:k.key);
      (* per application, the other keys one of whose results its arguments
         mention, each once *)
      let targets (k, _, args, _) =
        Set.fold (args_fvs args) ~init:Set.Poly.empty ~f:(fun acc v ->
            match Hashtbl.find owner v with
            | Some k' when not (Ident.tvar_equal k' k.key) -> Set.add acc k'
            | _ -> acc)
      in
      let blocked = Hashtbl.Poly.create () in
      let app_targets = List.map apps ~f:(fun app -> (app, targets app)) in
      List.iter app_targets ~f:(fun (_, ts) ->
          Set.iter ts ~f:(fun t ->
              Hashtbl.update blocked t ~f:(fun c -> 1 + Option.value ~default:0 c)));
      let is_allowed k =
        Option.value ~default:0 (Hashtbl.find blocked k.key) = 0
      in
      let rec loop tree pending =
        if List.is_empty pending then tree
        else
          let keys =
            List.dedup_and_sort
              ~compare:(fun a b -> Ident.tvar_compare a.key b.key)
              (List.map pending ~f:(fun ((k, _, _, _), _) -> k))
          in
          let allowed = List.filter keys ~f:is_allowed in
          let impure = impure_leaves [] tree in
          let k =
            match
              List.find allowed ~f:(fun k ->
                  let rets = Hashtbl.find_exn key_rets k.key in
                  not
                    (List.exists impure ~f:(fun t ->
                         Set.exists rets ~f:(fun y -> mem_fv y t))))
            with
            | Some k -> k
            | None -> ( match allowed with k :: _ -> k | [] -> raise Fallback)
          in
          let mine, others =
            List.partition_tf pending ~f:(fun ((k', _, _, _), _) ->
                Ident.tvar_equal k.key k'.key)
          in
          List.iter mine ~f:(fun (_, ts) ->
              Set.iter ts ~f:(fun t ->
                  Hashtbl.update blocked t ~f:(fun c ->
                      Option.value ~default:0 c - 1)));
          let ys =
            Set.Poly.of_list (List.map mine ~f:(fun ((_, _, _, y), _) -> y))
          in
          loop
            (substitute_at k
               (List.map mine ~f:(fun ((_, m, args, y), _) -> (m, args, y)))
               ys tree)
            others
      in
      let tree = loop body app_targets in
      Some (List.fold rets ~init:uni_senv ~f:Map.Poly.remove, tree)
    with Fallback -> None

  (* The nesting relation of the keys [keys] (pairwise distinct) in the
     clause [t], computed once: [order] is [NestedKeys.order ~keys t] and
     [footprint k] is the footprint of the key [k] of [keys] as stated at
     [key] above -- the names of the keys of [k]'s class, transitively under
     [nested_in a b] or [nested_in b a], and of their results, where
     [nested_in a b] holds when a result of [a] is nested in a result of [b]
     ([NestedKeys.nested_rets ~keys t (rets of b)]).  The definitions recompute
     each key's applications for every pair of keys they compare, which is
     cubic in the number of keys, each step a traversal of [t]; a clause of a
     transition system with several hundred keys then never finished.  Here
     each key's applications are read once ([NestedKeys.apps_of], one
     traversal per key), the nesting of results is reachability in the graph
     with an edge from each variable of an application's arguments to its
     result, the classes are the components of a union-find, and the order is
     the same greedy choice (the first remaining key nested in no remaining
     key, else the first remaining key) kept by a count per key of the
     remaining keys it is nested in.  Postcondition: both are equal to the
     definitions', element for element; no fresh name is drawn. *)
  let rec nesting ~keys t =
    let order, footprint, _ = nesting_with_below ~keys t in
    (order, footprint)

  (* [nesting_with_below]: [nesting], and [below k] for a key [k] of [keys]:
     the other keys of [keys] some result of which is nested, transitively,
     in a result of [k] (the keys [k]'s substitution renames with its copies),
     read off the same reachability. *)
  and nesting_with_below ~keys t =
    let keys = Array.of_list keys in
    let n = Array.length keys in
    let apps =
      Array.map keys ~f:(fun k ->
          List.map (NestedKeys.apps_of k t) ~f:(fun (args, ret) ->
              ( Set.Poly.union_list (List.map args ~f:Logic.ExtTerm.fvs_of),
                ret )))
    in
    let rets =
      Array.map apps ~f:(fun aps ->
          List.map aps ~f:snd
          |> List.dedup_and_sort ~compare:Ident.tvar_compare)
    in
    (* the keys (indices) one of whose results is [v] *)
    let owners = Hashtbl.Poly.create () in
    Array.iteri rets ~f:(fun i rs ->
        List.iter rs ~f:(fun v -> Hashtbl.add_multi owners ~key:v ~data:i));
    let owners_of v = Option.value ~default:[] (Hashtbl.find owners v) in
    (* [inside.(i)]: the keys [j <> i] some application of [i] is nested in
       a result of, i.e. whose results its arguments mention *)
    let inside =
      Array.mapi apps ~f:(fun i aps ->
          List.fold aps ~init:Int.Set.empty ~f:(fun acc (fvs, _) ->
              Set.fold fvs ~init:acc ~f:(fun acc v ->
                  List.fold (owners_of v) ~init:acc ~f:(fun acc j ->
                      if j = i then acc else Set.add acc j))))
    in
    let order =
      let containing = Array.create ~len:n [] in
      Array.iteri inside ~f:(fun i js ->
          Set.iter js ~f:(fun j -> containing.(j) <- i :: containing.(j)));
      let count = Array.map inside ~f:Set.length in
      let remove i =
        List.iter containing.(i) ~f:(fun j -> count.(j) <- count.(j) - 1)
      in
      let rec go acc remaining =
        match remaining with
        | [] -> List.rev acc
        | first :: _ ->
            let i =
              Option.value ~default:first
                (List.find remaining ~f:(fun i -> count.(i) = 0))
            in
            remove i;
            go (i :: acc) (List.filter remaining ~f:(fun j -> j <> i))
      in
      List.map (go [] (List.init n ~f:Fn.id)) ~f:(fun i -> keys.(i))
    in
    (* edges of the nesting graph: a variable of an application's arguments
       to the application's result *)
    let succ = Hashtbl.Poly.create () in
    Array.iter apps ~f:(fun aps ->
        List.iter aps ~f:(fun (fvs, ret) ->
            Set.iter fvs ~f:(fun v -> Hashtbl.add_multi succ ~key:v ~data:ret)));
    (* the variables reachable from [rs] by at least zero edges *)
    let reach rs =
      let seen = Hash_set.Poly.of_list rs in
      let rec visit = function
        | [] -> ()
        | v :: todo ->
            let next =
              List.filter (Option.value ~default:[] (Hashtbl.find succ v))
                ~f:(fun w ->
                  if Hash_set.mem seen w then false
                  else (
                    Hash_set.add seen w;
                    true))
            in
            visit (next @ todo)
      in
      visit rs;
      seen
    in
    let parent = Array.init n ~f:Fn.id in
    let rec find i =
      if parent.(i) = i then i
      else
        let r = find parent.(i) in
        parent.(i) <- r;
        r
    in
    let union i j =
      let ri = find i and rj = find j in
      if ri <> rj then parent.(ri) <- rj
    in
    let below = Array.create ~len:n Int.Set.empty in
    Array.iteri rets ~f:(fun b rs ->
        let nested = reach rs in
        List.iter rs ~f:(Hash_set.remove nested);
        Hash_set.iter nested ~f:(fun v ->
            List.iter (owners_of v) ~f:(fun j ->
                union b j;
                if j <> b then below.(b) <- Set.add below.(b) j)));
    let class_footprint = Hashtbl.Poly.create () in
    Array.iteri keys ~f:(fun i k ->
        Hashtbl.update class_footprint (find i) ~f:(fun fp ->
            Set.union
              (Option.value ~default:Set.Poly.empty fp)
              (Set.Poly.of_list (k :: rets.(i)))));
    let index = Hashtbl.Poly.create () in
    Array.iteri keys ~f:(fun i k -> Hashtbl.set index ~key:k ~data:i);
    let footprint k =
      Hashtbl.find_exn class_footprint (find (Hashtbl.find_exn index k))
    in
    let below k =
      Set.to_list below.(Hashtbl.find_exn index k)
      |> List.map ~f:(fun j -> keys.(j))
      |> Set.Poly.of_list
    in
    (order, footprint, below)

  (* [of_clause ~dedup strat_fn (uni_senv, phi)]: the clause [phi] (with its
     ranking keys already substituted) with every Skolem key of [strat_fn]
     that it mentions placed as above, [dedup params terms] giving the terms
     of a key, together with the renamed environment and the number of
     alternatives the whole-clause substitution would have made (the product
     of the term counts, saturating at 10^9; 1 for a clause with no key).
     Keys are substituted outer ones first ([NestedKeys.order]), as in the
     whole-clause substitution, so the two read one strategy the same way;
     where [one_point] applies, no result survives and no order between
     unrelated keys is needed.

     With [joint] ([joint_term_alternatives]), [joint lone] gives the units
     among the keys [lone] (those related by nesting to no other key of the
     clause): disjoint lists of at least two keys with their rows, each row a
     term per member drawn from the member's term set, every term of a
     member appearing in some row.  A unit is placed as one key whose
     alternatives are its rows, at the smallest subformula holding all its
     members' footprints.  By the identity above (the context of that
     subformula mentions no member and no member's result), the clause is
     then equivalent to the disjunction, over the vectors that choose one row
     per unit and one term per other key, of the whole-clause substitution
     of that vector; those vectors are a subset of the product of the term
     sets, so the clause implies the one placed without [joint], and is
     equivalent to it when every unit's rows are the product of its members'
     terms.  The reported whole-clause count stays the product. *)
  (* Called by [of_clause] with its arguments before it places the clause;
     it does nothing unless a test sets it, to read the clauses of a real
     solve. *)
  let clause_observer :
      (dedup:(Logic.sort_env_list -> Logic.term Set.Poly.t -> Logic.term list) ->
      (Ident.tvar, Logic.sort_env_list * Logic.term Set.Poly.t) Map.Poly.t ->
      Logic.sort_env_map * Logic.term ->
      unit)
      ref =
    ref (fun ~dedup:_ _ _ -> ())

  let of_clause ?joint ~dedup strat_fn (uni_senv, phi) =
    !clause_observer ~dedup strat_fn (uni_senv, phi);
    let fvs = Logic.ExtTerm.fvs_of phi in
    let present, footprint_of, below_of =
      Common.PhaseTime.with_phase "nesting" @@ fun () ->
      nesting_with_below
        ~keys:(Map.Poly.keys strat_fn |> List.filter ~f:(Set.mem fvs))
        phi
    in
    (* each key's footprint widened by the inner universals of its class
       ([inner_vars]), so that the placement holds every occurrence of the
       universals its copies rename apart *)
    let nnf_tree = lazy (of_nnf (Logic.ExtTerm.nnf_of phi)) in
    let is_key v = Map.Poly.mem strat_fn v in
    let heads =
      lazy (ChoiceScope.heads ~uni_senv ~is_key (Logic.ExtTerm.nnf_of phi))
    in
    let inner =
      lazy
        (if List.is_empty present then Map.Poly.empty
         else
           inner_vars ~uni_senv ~is_key ~heads:(Lazy.force heads)
             (Lazy.force nnf_tree))
    in
    let inner_of k =
      Option.value ~default:Set.Poly.empty (Map.Poly.find (Lazy.force inner) k)
    in
    let footprint_of k =
      let fp = footprint_of k in
      Set.Poly.union_list (fp :: inner_of k :: List.map (Set.to_list fp) ~f:inner_of)
    in
    (* every present key with its parameters and deduplicated terms *)
    let kept =
      Common.PhaseTime.with_phase "dedup" @@ fun () ->
      List.map present ~f:(fun key ->
          let params, terms = Map.Poly.find_exn strat_fn key in
          (key, (params, terms, dedup params terms)))
    in
    let kept_map = Map.Poly.of_alist_exn kept in
    let kept_of key = Map.Poly.find_exn kept_map key in
    (* the keys of the clause a key's results are nested in (the converse of
       [below_of]) *)
    let above_of =
      lazy
        (let above = Hashtbl.Poly.create () in
         List.iter present ~f:(fun k ->
             Set.iter (below_of k) ~f:(fun m ->
                 Hashtbl.add_multi above ~key:m ~data:k));
         fun m -> Option.value ~default:[] (Hashtbl.find above m))
    in
    (* [joint_term_alternatives]: the units of the clause's keys.  [joint]
       gives the classes of keys refined together, with their rows; a row's
       term is replaced by the term [dedup] kept for it (so that a unit offers
       no term its members would not offer alone) and repeated rows are
       dropped (a disjunction is idempotent).  Every other key is a group of
       its own whose rows are its terms.  A unit is substituted at once, its
       members' results and the results nested in them renamed per row, so a
       group must be convex in the nesting relation (no other key of the
       clause between two members: it would have to be substituted both after
       and before the group), and the groups must be orderable (no cycle of
       groups each with a member nested in the next).  A group that is not
       convex is merged with the groups of the keys between its members, and
       the first group a cycle blocks with the groups it waits for; a merged
       group's rows are the product of its parts' rows.  Every group is then
       a union of whole classes and single keys, so the clause is offered
       exactly the projection, onto its keys, of the vectors the classes
       offer, which only grows as refinements are recorded.  A group of one
       key is placed as a single key. *)
    let units =
      Common.PhaseTime.with_phase "units" @@ fun () ->
      match joint with
      | None -> []
      | Some joint -> (
          let joint_classes =
            Common.PhaseTime.with_phase "classes" @@ fun () -> joint present
          in
          Common.PhaseTime.with_phase "reps" @@ fun () ->
          let class_units =
            List.map joint_classes ~f:(fun (members, rows) ->
                let reps =
                  List.map members ~f:(fun m ->
                      let params, _, kept_terms = kept_of m in
                      fun t ->
                        if List.mem kept_terms t ~equal:JointTerms.equal_terms
                        then t
                        else
                          Option.value ~default:t
                            (List.find kept_terms ~f:(fun t' ->
                                 List.length
                                   (dedup params (Set.Poly.of_list [ t'; t ]))
                                 = 1)))
                in
                let rows =
                  List.fold rows ~init:[] ~f:(fun acc row ->
                      let row =
                        List.map2_exn reps row ~f:(fun rep t -> rep t)
                      in
                      if
                        List.mem acc row
                          ~equal:(List.equal JointTerms.equal_terms)
                      then acc
                      else row :: acc)
                  |> List.rev
                in
                (members, rows))
          in
          match class_units with
          | [] -> []
          | _ ->
              let above_of = Lazy.force above_of in
              let in_class =
                Set.Poly.of_list (List.concat_map class_units ~f:fst)
              in
              let groups =
                class_units
                @ List.filter_map present ~f:(fun k ->
                    if Set.mem in_class k then None
                    else
                      let _, _, terms = kept_of k in
                      Some ([ k ], List.map terms ~f:(fun t -> [ t ])))
              in
              let merge g1 g2 =
                ( fst g1 @ fst g2,
                  List.concat_map (snd g1) ~f:(fun r1 ->
                      List.map (snd g2) ~f:(fun r2 -> r1 @ r2)) )
              in
              let mem_group (ms, _) k = List.mem ms k ~equal:Ident.tvar_equal in
              (* the keys outside [g] between two of its members *)
              let between g =
                let ms = fst g in
                List.concat_map ms ~f:above_of
                |> List.filter ~f:(fun l ->
                    (not (mem_group g l))
                    && List.exists ms ~f:(fun m -> Set.mem (below_of m) l))
              in
              (* merge [g] with the groups holding any of the keys [ls] *)
              let absorb groups g ls =
                let others, taken =
                  List.partition_tf groups ~f:(fun h ->
                      (not (phys_equal h g))
                      && not (List.exists ls ~f:(mem_group h)))
                in
                let g' =
                  List.fold
                    (List.filter taken ~f:(fun h -> not (phys_equal h g)))
                    ~init:g ~f:merge
                in
                g' :: others
              in
              let rec settle groups =
                match List.find groups ~f:(fun g -> not (List.is_empty (between g))) with
                | Some g -> settle (absorb groups g (between g))
                | None -> (
                    (* an order of the groups: the first group, in the order
                       given, all of whose members' outer keys are in groups
                       already taken; when none is, a cycle *)
                    let rec order taken remaining =
                      match remaining with
                      | [] -> None
                      | _ -> (
                          let waits g =
                            List.concat_map (fst g) ~f:above_of
                            |> List.filter ~f:(fun k ->
                                (not (mem_group g k)) && not (Set.mem taken k))
                          in
                          match
                            List.find remaining ~f:(fun g -> List.is_empty (waits g))
                          with
                          | Some g ->
                              order
                                (List.fold (fst g) ~init:taken ~f:Set.add)
                                (List.filter remaining ~f:(fun h ->
                                     not (phys_equal h g)))
                          | None ->
                              let g = List.hd_exn remaining in
                              Some (g, waits g))
                    in
                    match order Set.Poly.empty groups with
                    | None -> groups
                    | Some (g, ls) -> settle (absorb groups g ls))
              in
              settle groups
              |> List.filter ~f:(fun (ms, _) -> List.length ms >= 2)
              |> List.map ~f:(fun (ms, rows) ->
                  (* the members in the clause's nesting order *)
                  let idx =
                    List.filter_map present ~f:(fun k ->
                        List.findi ms ~f:(fun _ m -> Ident.tvar_equal m k)
                        |> Option.map ~f:fst)
                  in
                  ( List.map idx ~f:(List.nth_exn ms),
                    List.map rows ~f:(fun row -> List.map idx ~f:(List.nth_exn row)) )))
    in
    let unit_of key =
      List.find units ~f:(fun (members, _) ->
          List.mem members key ~equal:Ident.tvar_equal)
    in
    (* each unit at the position of its first member in the nesting order,
       then (when there is a unit) the items reordered so that each comes
       after every key outside it that a member's results are nested in: the
       first item, in that order, whose such keys have all been taken is taken
       next.  Without a unit the order is the nesting order itself.  A unit is
       convex, so the order exists; were it not found, the units are given up
       and every key is placed on its own. *)
    let singles () =
      List.map present ~f:(fun key ->
          let params, _, terms = kept_of key in
          single ~key ~params ~terms ~footprint:(footprint_of key)
            ~all_keys:present)
    in
    let items =
      List.filter_map present ~f:(fun key ->
          let params, _, terms = kept_of key in
          match unit_of key with
          | None ->
              Some
                (single ~key ~params ~terms ~footprint:(footprint_of key)
                   ~all_keys:present)
          | Some (members, rows) ->
              if not (Ident.tvar_equal key (List.hd_exn members)) then None
              else (
                Atomic.incr unit_count;
                ignore (Atomic.fetch_and_add unit_rows_count (List.length rows));
                Some
                  {
                    key;
                    params;
                    terms = [];
                    footprint =
                      Set.Poly.union_list (List.map members ~f:footprint_of);
                    all_keys = present;
                    members =
                      List.map members ~f:(fun m ->
                          let ps, _, _ = kept_of m in
                          (m, ps));
                    rows;
                  }))
    in
    let ks =
      if List.is_empty units then items
      else
        let above_of = Lazy.force above_of in
        let rec go acc taken remaining =
          match remaining with
          | [] -> Some (List.rev acc)
          | _ -> (
              let ready item =
                let ms = List.map (members_of item) ~f:fst in
                List.for_all ms ~f:(fun m ->
                    List.for_all (above_of m) ~f:(fun k ->
                        Set.mem taken k || List.mem ms k ~equal:Ident.tvar_equal))
              in
              match List.findi remaining ~f:(fun _ item -> ready item) with
              | None -> None
              | Some (i, item) ->
                  go (item :: acc)
                    (List.fold (members_of item) ~init:taken ~f:(fun t (m, _) ->
                         Set.add t m))
                    (List.filteri remaining ~f:(fun j _ -> j <> i)))
        in
        match go [] Set.Poly.empty items with
        | Some ks -> ks
        | None -> singles ()
    in
    let taken =
      Set.Poly.union_list
        (fvs
        :: List.concat_map kept ~f:(fun (_, (_, _, terms)) ->
            List.map terms ~f:Logic.ExtTerm.fvs_of))
    in
    let whole =
      if List.is_empty kept then 1
      else
        List.fold kept ~init:1 ~f:(fun acc (_, (_, _, terms)) ->
            let n = List.length terms in
            if acc > 1_000_000_000 / Int.max 1 n then 1_000_000_000 else acc * n)
    in
    (* the census line of [joint_term_alternatives]'s measurements, for a
       clause of at least 50 keys: how many keys, how many have no other key
       in their footprint, the largest footprint (in keys), the units and
       their rows; nothing without the variable *)
    if
      List.length present >= 50
      && Option.is_some (Sys.getenv "COAR_MUSTRAT_JOINT_CENSUS")
    then (
      let present_set = Set.Poly.of_list present in
      let fp_keys k = Set.count (footprint_of k) ~f:(Set.mem present_set) in
      (* what [joint] would give with nesting ignored: the classes over all
         the clause's keys, and the members of each that are not lone *)
      let all_units = match joint with None -> [] | Some j -> j present in
      eprintf
        "mustrat-joint-clause keys=%d lone=%d max_footprint_keys=%d units=%d \
         rows=%d classes_all=%d members_all=%d nonlone_members_all=%d\n%!"
        (List.length present)
        (List.count present ~f:(fun k -> fp_keys k = 1))
        (List.fold present ~init:0 ~f:(fun m k -> Int.max m (fp_keys k)))
        (List.length units)
        (List.sum (module Int) units ~f:(fun (_, rows) -> List.length rows))
        (List.length all_units)
        (List.sum (module Int) all_units ~f:(fun (ms, _) -> List.length ms))
        (List.sum (module Int) all_units ~f:(fun (ms, _) ->
             List.count ms ~f:(fun k -> fp_keys k > 1))));
    (* A clause that mentions no key is kept as it is, so that it reaches the
       backend exactly as with the whole-clause substitution. *)
    if List.is_empty ks then (uni_senv, Leaf phi, whole)
    else
      let nnf_tree = Lazy.force nnf_tree in
      let heads = Lazy.force heads in
      (* The one-point rule replaces each result by its term and renames
         nothing, so it is taken only where no key has an inner universal
         to rename apart per copy. *)
      let no_inner =
        Map.Poly.for_all (Lazy.force inner) ~f:Set.is_empty
      in


      let uni_senv, tree =
        match
          if not no_inner then None
          else
            Common.PhaseTime.with_phase "one-point" @@ fun () ->
            one_point ~uni_senv ks nnf_tree
        with
        | Some placed ->
            Atomic.incr one_point_count;
            placed
        | None ->
            Common.PhaseTime.with_phase "footprints" @@ fun () ->
            place ~uni_senv ~taken
              ~inner:(Hash_set.Poly.of_list
                        (Set.to_list (Set.Poly.union_list (Map.Poly.data (Lazy.force inner)))))
              ~heads ~outside:Set.Poly.empty ks nnf_tree
      in
      (uni_senv, tree, whole)
end

module ClauseChoiceScope = struct
  (* The inner universals of every key of the clause [phi] (in negation normal
     form below), as a set to which [record] adds the names copies give
     them. *)
  let inner_of_clause ~uni_senv ~is_key ~heads phi =
    TermAlternatives.inner_vars ~uni_senv ~is_key ~heads
      (TermAlternatives.of_nnf (Logic.ExtTerm.nnf_of phi))
    |> Map.Poly.data |> Set.Poly.union_list |> Set.to_list
    |> Hash_set.Poly.of_list
end

(* Tautological clauses of a strategy check.

   A clause whose head holds an atom that its body also holds -- the same
   predicate applied to the same argument terms, compared syntactically after
   the conversion to clausal form -- is true under every interpretation, so
   removing it leaves the check's set of solutions unchanged; and a derivation
   of the remaining clauses is a derivation of the whole set, since they are a
   subset of it.  So the check with such clauses removed has the same answer,
   and every counter-play it returns is a counter-play of the original.  The
   greatest-fixpoint encoding of a ranked predicate produces such clauses
   whenever the prover may stay where it is: the stay move's two copies of the
   ranked predicate are the clause's head, once the refuter's view has
   distributed the prover's moves into clauses.  They are a third of the
   check's clauses on the elevator-signal and resource inputs, and the CHC
   backend, which is run with rule subsumption off so that its counterexample
   keeps every named decision point, does not remove them itself. *)
module TautologicalClauses = struct
  (* Precondition: none on the form of [pcsp]; a problem not in clausal form
     is converted first, as the CHC backends do.  Postcondition: the returned
     problem holds exactly the clauses of [pcsp] (without its stable clauses,
     which stay in the parameters) that have no atom both positively and
     negatively, and the count is how many were removed; the parameters are
     those of [pcsp]. *)
  let drop pcsp =
    let params = PCSP.Problem.params_of pcsp in
    let cnf =
      PCSP.Problem.clauses_of ~full_clauses:false
      @@ PCSP.Problem.to_cnf
      @@ PCSP.Problem.to_nnf pcsp
    in
    let kept =
      Set.filter cnf ~f:(fun (_, ps, ns, _) -> Set.is_empty (Set.inter ps ns))
    in
    ( Set.length cnf - Set.length kept,
      Set.length cnf,
      PCSP.Problem.of_formulas ~params (ClauseSet.to_formulas kept) )
end

(* Reading the clausal form of a check without building it, and naming the
   disjunctions whose clausal form would multiply.  The functions take the
   check's predicates [exi_senv] and a clause's universals [uni_senv]; a
   universal shadows a predicate of its name. *)
module CheckCnf = struct
  (* The head variable of [t] if [t] is an application of a predicate of
     [exi_senv]; a universal of [uni_senv] shadows a predicate of its name. *)
  let pred_app_of exi_senv uni_senv t =
    match Logic.Term.let_apps t with
    | Logic.Var (v, _), _
      when Map.Poly.mem exi_senv v && not (Map.Poly.mem uni_senv v) ->
        Some v
    | _ -> None

  let mentions_pred exi_senv uni_senv t =
    Set.exists (Logic.ExtTerm.fvs_of t) ~f:(fun v ->
        Map.Poly.mem exi_senv v && not (Map.Poly.mem uni_senv v))

  (* Does the NNF formula [t] have predicate atoms only negatively, directly
     under a [not], with only [and]/[or] above them?  Anything else that
     mentions a predicate (a quantifier, a boolean equality, an [ite]) answers
     no, so that the caller falls back rather than guesses a polarity. *)
  let rec negative_only exi_senv uni_senv t =
    (not (mentions_pred exi_senv uni_senv t))
    ||
    match Logic.Term.let_apps t with
    | Logic.Con ((Logic.BoolTerm.And | Logic.BoolTerm.Or), _), args ->
        List.for_all args ~f:(negative_only exi_senv uni_senv)
    | Logic.Con (Logic.BoolTerm.Not, _), [ a ] ->
        Option.is_some (pred_app_of exi_senv uni_senv a)
    | _ -> false

  (* An upper bound on the number of clauses the CNF conversion produces for
     the NNF formula [t], read off its structure without converting it: a
     disjunction multiplies its operands' counts, a conjunction adds them (its
     predicate-free operands merging into one clause), and anything else is
     one clause.  The conversion may produce fewer, since it deduplicates.
     It draws no fresh name and builds no clause, so it can be printed for a
     check whose conversion would not finish.  Saturates at [cnf_size_cap]. *)
  let cnf_size_cap = 1_000_000_000_000

  let cnf_mul a b =
    if a = 0 || b = 0 then 0
    else if a > cnf_size_cap / b then cnf_size_cap
    else a * b

  let cnf_add a b = Int.min cnf_size_cap (a + b)

  (* [mentions_and_size t] is [(mentions_pred t, cnf_size t)], read in one
     pass.  The count is defined as: 1 when [t] mentions no predicate;
     otherwise, for a disjunction the product of its operands' counts, for a
     conjunction the sum of its operands' counts over the operands that
     mention a predicate, plus 1 when some operand mentions none; and 1 for
     anything else.  Computed by that recursion directly, [mentions_pred] (a
     free-variable set of the whole subtree) is asked at every [and]/[or]
     node and again of every operand, so the cost grows with the formula's
     size times its depth; on the 8,816 clauses of one copy-blind check it
     took 35 s.  Here a free-variable set is built only at a node
     that is neither [and] nor [or], once.  Equal to the definition: an
     [and]/[or] node's free variables are the union of its operands' (its
     connective has none), so it mentions a predicate exactly when an operand
     does; a node that mentions none counts 1 whatever its shape; and an
     operand that mentions none counts 1 in a disjunction and is pure in a
     conjunction, as the definition reads it. *)
  let rec mentions_and_size exi_senv uni_senv t =
    match Logic.Term.let_apps t with
    | Logic.Con (Logic.BoolTerm.Or, _), args ->
        let rs = List.map args ~f:(mentions_and_size exi_senv uni_senv) in
        if not (List.exists rs ~f:fst) then (false, 1)
        else (true, List.fold rs ~init:1 ~f:(fun acc (_, c) -> cnf_mul acc c))
    | Logic.Con (Logic.BoolTerm.And, _), args ->
        let rs = List.map args ~f:(mentions_and_size exi_senv uni_senv) in
        if not (List.exists rs ~f:fst) then (false, 1)
        else
          let pure, impure = List.partition_tf rs ~f:(Fn.non fst) in
          ( true,
            List.fold impure
              ~init:(if List.is_empty pure then 0 else 1)
              ~f:(fun acc (_, c) -> cnf_add acc c) )
    | _ -> (mentions_pred exi_senv uni_senv t, 1)

  let cnf_size exi_senv uni_senv t = snd (mentions_and_size exi_senv uni_senv t)

  (* An upper bound on the total size, in term nodes, of the clauses the
     guarded clausal form of the NNF formula [t] produces, read off its
     structure as [cnf_size] reads the count: a predicate-free part or an
     atom is one clause of its own size; a disjunction's clauses are the
     concatenations of one clause of each operand, so operand [i]'s clauses
     appear once per combination of the others' ([w_i] times the product of
     the other counts); a conjunction's clauses are its operands' clauses,
     its predicate-free operands merged into one, and every clause of an
     operand holding an unknown also carries the negation of that
     predicate-free part (the guard [GuardedClauses] adds).  Returns the count
     with the size; both saturate at [cnf_size_cap].  The count alone misses
     a clause form that is short but wide: a ranking of a few hundred nodes,
     substituted at each of five moves of a step and copied by the guards
     into every one of the step's 491 clauses, made a check of about 5 MB
     whose count stayed under the naming bound. *)
  let rec cnf_weight exi_senv uni_senv t =
    let node_size t = Logic.Term.ast_size_up_to cnf_size_cap t in
    if not (mentions_pred exi_senv uni_senv t) then (1, node_size t)
    else
      match Logic.Term.let_apps t with
      | Logic.Con (Logic.BoolTerm.Or, _), args ->
          List.fold args ~init:(1, 0) ~f:(fun (c, w) a ->
              let ca, wa = cnf_weight exi_senv uni_senv a in
              (cnf_mul c ca, cnf_add (cnf_mul w ca) (cnf_mul wa c)))
      | Logic.Con (Logic.BoolTerm.And, _), args ->
          let pure, impure =
            List.partition_tf args
              ~f:(Fn.non (mentions_pred exi_senv uni_senv))
          in
          let pure_size =
            List.fold pure ~init:0 ~f:(fun acc a -> cnf_add acc (node_size a))
          in
          List.fold impure
            ~init:((if List.is_empty pure then 0 else 1), pure_size)
            ~f:(fun (c, w) a ->
              let ca, wa = cnf_weight exi_senv uni_senv a in
              (cnf_add c ca, cnf_add w (cnf_add wa (cnf_mul ca pure_size))))
      | _ -> (1, node_size t)

  (* [name_disjunctions ~fresh ~exi_senv_of uni_senv t]: the NNF formula [t]
     with the disjunctions whose clausal form would multiply replaced by
     named atoms, and the definitions of the names.  Returns [(t', defs)].

     Bottom up, at every disjunction [R_1 \/ .. \/ R_k] (its operands flattened)
     whose operands' clause counts [c_tau] ([cnf_size], with the names drawn so
     far counted as atoms) multiply to more than their sum plus one, every
     operand [R_tau] with [c_tau > 1] whose predicate atoms all occur
     negatively is replaced by [not N_tau(z_tau)], [z_tau] the universals
     [R_tau] mentions, and [N_tau(z_tau) \/ R_tau] is returned as its
     definition.  Every other operand stays.  [fresh sort] draws each
     [N_tau]; [exi_senv_of ()] is the predicates together with the names drawn
     so far.

     Exact (the argument of [name_tree], at any disjunction): [t] is built
     from literals by [and] and [or] only, so it is monotone in each operand.
     Taking [N_tau := not R_tau] (a function of [z_tau] alone) makes the
     definitions hold and turns [t'] back into [t]; conversely the definitions
     give [not N_tau => R_tau], so [t'] implies [t].  So an interpretation of
     the original predicates satisfies [t] at every value of the universals
     iff it extends to the [N_tau] so that [t'] and the definitions all hold,
     and a CHC system is satisfiable with [t] iff it is with [t'] and the
     definitions.  Each definition is a Horn clause with head [N_tau] (the
     operand's atoms are negative), and each [N_tau] is non-recursive and
     occurs elsewhere only negatively, so unfolding the [N] nodes of a
     derivation of the named system gives a derivation of the unnamed one:
     the plays read off a refutation are the same plays.

     Why: the clausal form distributes a disjunction over its operands'
     conjunctions, so a chain of guarded alternatives -- an [ite] over a
     state's cases, each case a choice among moves, each move a conjunction --
     has a number of clauses exponential in the length of the chain; one
     check of a five-floor elevator did not finish its conversion within
     3 GB.  Named, the count is the sum of the operands' counts. *)
  let name_disjunctions ~fresh ~exi_senv_of uni_senv t =
    let defs = ref [] in
    let name r =
      let zs =
        Set.to_list (Logic.ExtTerm.fvs_of r)
        |> List.filter_map ~f:(fun v ->
            Option.map (Map.Poly.find uni_senv v) ~f:(fun s -> (v, s)))
      in
      let n =
        fresh (Logic.Sort.mk_fun (List.map zs ~f:snd @ [ Logic.BoolTerm.SBool ]))
      in
      let napp =
        Logic.ExtTerm.mk_var_app n (List.map zs ~f:(fst >> Logic.ExtTerm.mk_var))
      in
      defs := (Map.Poly.of_alist_exn zs, Logic.BoolTerm.or_of [ napp; r ]) :: !defs;
      Logic.BoolTerm.neg_of napp
    in
    (* the time of the two tests asked at every node, added to the phase
       account once at the end ([PhaseTime.add_here]); [timed] only reads the
       clock around a call and returns what the call returns *)
    let mentions_secs = ref 0. and mentions_n = ref 0 in
    let size_secs = ref 0. and size_n = ref 0 in
    let timed secs n f =
      if not !Common.PhaseTime.on then f ()
      else
        let t0 = Common.PhaseTime.now () in
        let v = f () in
        secs := !secs +. (Common.PhaseTime.now () -. t0);
        incr n;
        v
    in
    let rec go t =
      if
        not
          (timed mentions_secs mentions_n (fun () ->
               mentions_pred (exi_senv_of ()) uni_senv t))
      then t
      else
        match Logic.Term.let_apps t with
        | Logic.Con (Logic.BoolTerm.And, _), _ ->
            Logic.BoolTerm.and_of
              (List.map (Logic.BoolTerm.conjuncts_of t) ~f:go)
        | Logic.Con (Logic.BoolTerm.Or, _), _ ->
            let rs = List.map (Logic.BoolTerm.disjuncts_of t) ~f:go in
            let exi_senv = exi_senv_of () in
            let sizes =
              timed size_secs size_n (fun () ->
                  List.map rs ~f:(cnf_size exi_senv uni_senv))
            in
            if
              List.fold sizes ~init:1 ~f:cnf_mul
              <= List.fold sizes ~init:0 ~f:cnf_add + 1
            then Logic.BoolTerm.or_of rs
            else
              Logic.BoolTerm.or_of
              @@ List.map2_exn rs sizes ~f:(fun r c ->
                  if c > 1 && negative_only exi_senv uni_senv r then name r
                  else r)
        | _ -> t
    in
    let t' = go t in
    Common.PhaseTime.add_here "mentions-pred" ~secs:!mentions_secs
      ~count:!mentions_n;
    Common.PhaseTime.add_here "cnf-size" ~secs:!size_secs ~count:!size_n;
    (t', List.rev !defs)

  (* [name_problem ?by_size ~bound pcsp]: [pcsp] with every formula whose
     clause count ([cnf_size] of its NNF) exceeds [bound] replaced by its
     [name_disjunctions] form and the definitions, the names added to the
     predicates as ordinary unknowns; and the number of formulas so replaced
     and of names drawn.  With [~by_size:true] a formula within the bound is
     replaced too when its named form's clauses are smaller in total
     ([cnf_weight]'s size, summed over the named formula and its
     definitions) than the formula's own; a rejected naming draws no name
     into the result.  A problem already in clausal form, and every other
     formula, is left as it is.  Equisatisfiable with [pcsp], by
     [name_disjunctions]'s argument, formula by formula, whichever formulas
     are replaced; a solution of the result restricted to [pcsp]'s
     predicates solves [pcsp]. *)
  let size_census =
    Option.is_some (Sys.getenv "COAR_MUSTRAT_SIZE_NAMING_CENSUS")

  (* The least clause count ([cnf_size]) of a formula [name_disjunctions] can
     name anything in.  It names only at a disjunction whose operands' counts
     [c_1 .. c_k] (each at least 1) multiply to more than their sum plus one,
     and the least such product is 8 ({2, 4}, {3, 3}, {2, 2, 2}; a factor 1
     adds 1 to the sum and nothing to the product, and {2, 2} and {2, 3} give
     4 <= 5 and 6 <= 6).  The first naming in a formula happens at such a
     disjunction with nothing below it named yet, whose counts are therefore
     the formula's own; and a formula's count is at least each subformula's,
     since a disjunction multiplies and a conjunction adds counts that are at
     least 1.  Names drawn for other formulas do not occur in this one (they
     avoid every free variable of the problem).  So a formula whose count is
     below 8 is returned by [name_disjunctions] with no definition, and
     [name_problem] keeps it as it is without asking. *)
  let min_multiplying_count = 8

  let name_problem ?(by_size = false) ~bound pcsp =
    if PCSP.Problem.is_cnf pcsp then (0, 0, pcsp)
    else
      let params = PCSP.Problem.params_of pcsp in
      let exi_senv = PCSP.Problem.senv_of pcsp in
      let formulas = Set.to_list (PCSP.Problem.formulas_of pcsp) in
      let taken =
        Set.Poly.union_list
          (List.concat_map formulas ~f:(fun (uni_senv, phi) ->
               [ Map.Poly.key_set uni_senv; Logic.ExtTerm.fvs_of phi ]))
      in
      let new_senv = ref Map.Poly.empty in
      (* [exi_senv] with the names drawn so far, kept up to date as each name
         is drawn.  It was rebuilt by merging the two maps at every call, and
         [name_disjunctions] asks for it at every node of every formula it
         walks: on a check of 872 named formulas and 1,745 names that one
         call took 102 s.  The bindings are the same ([exi_senv]'s, and each
         drawn name with its sort, which never collides with [exi_senv]
         since [fresh] avoids its keys), and every reader only looks keys up,
         so nothing read changes. *)
      let merged = ref exi_senv in
      let fresh sort =
        let n =
          Ident.mk_fresh_tvar_avoiding ~prefix:"Dsj_"
            ~taken:(fun v ->
              Map.Poly.mem exi_senv v || Set.mem taken v
              || Map.Poly.mem !new_senv v)
            ()
        in
        new_senv := Map.Poly.set !new_senv ~key:n ~data:sort;
        merged := Map.Poly.set !merged ~key:n ~data:sort;
        n
      in
      let exi_senv_of () = !merged in
      let replaced = ref 0 in
      let formulas =
        List.concat_map formulas ~f:(fun (uni_senv, phi) ->
            (* the steps below are phases of the account (a phase returns
               what its body returns, so they change nothing computed) *)
            let nnf =
              Common.PhaseTime.with_phase "nnf" (fun () ->
                  Logic.BoolTerm.nnf_of phi)
            in
            let counted =
              Common.PhaseTime.with_phase "count" @@ fun () ->
              try Some (cnf_size exi_senv uni_senv nnf)
              with exn when not (Common.Timer.is_async exn) -> None
            in
            let size = Option.value counted ~default:0 in
            if
              (match counted with
              | Some n -> n < min_multiplying_count
              | None -> false)
              || (size <= bound && not by_size)
            then [ (uni_senv, phi) ]
            else
              let names_before = !new_senv in
              let merged_before = !merged in
              let phi', defs =
                Common.PhaseTime.with_phase "name" (fun () ->
                    name_disjunctions ~fresh ~exi_senv_of uni_senv nnf)
              in
              let smaller () =
                Common.PhaseTime.with_phase "smaller" @@ fun () ->
                let exi = exi_senv_of () in
                let named =
                  List.fold
                    ((uni_senv, phi') :: defs)
                    ~init:0
                    ~f:(fun acc (senv, t) ->
                      cnf_add acc
                        (snd (cnf_weight exi senv (Logic.BoolTerm.nnf_of t))))
                in
                named < snd (cnf_weight exi_senv uni_senv nnf)
              in
              if List.is_empty defs then [ (uni_senv, phi) ]
              else if size > bound then (
                incr replaced;
                (uni_senv, phi') :: defs)
              else if smaller () then (
                incr replaced;
                (* one stderr line per formula named by size alone, for a
                   census of where the field acts; nothing without the
                   variable *)
                if size_census then
                  eprintf "mustrat-size-naming: clauses=%d names=%d\n%!" size
                    (List.length defs);
                (uni_senv, phi') :: defs)
              else (
                new_senv := names_before;
                merged := merged_before;
                [ (uni_senv, phi) ]))
      in
      if Map.Poly.is_empty !new_senv then (0, 0, pcsp)
      else
        let params =
          {
            params with
            PCSP.Params.senv = Map.force_merge params.PCSP.Params.senv !new_senv;
            kind_map =
              Kind.add_kinds (Map.Poly.key_set !new_senv) Kind.Ord
                params.PCSP.Params.kind_map;
          }
        in
        ( !replaced,
          Map.Poly.length !new_senv,
          PCSP.Problem.of_formulas ~params (Set.Poly.of_list formulas) )
end

(* The clausal form of a strategy check with every step clause guarded.

   A formula of the check such as [U(s) \/ (G(s) /\ not U(s'))], with [G] the
   move's predicate-free condition, has the clauses [U(s) \/ G(s)] and
   [U(s) \/ not U(s')] in the ordinary clausal form, and the second lets a
   derivation of the CHC backend step from [s] to [s'] at a state where [G(s)]
   is false, so that a counter-play read off the derivation continues past
   the end of the play.  The refinement takes every step of a counter-play as
   a move ([chain_pairs_of] asks the opponent's ranking to decrease along each
   one), so such steps ask a ranking for pairs the game never produces, and
   on an integer transition system whose exits are many states (every [x <= 0]
   of a loop guarded by [x > 0]) the rankings fitted to them never generalise.
   [Logic.BoolTerm.cnf_of_guarded] puts [not G(s)] into the step clause, which
   is exact; see its contract. *)
module GuardedClauses = struct
  (* Precondition: none on the form of [pcsp]; a problem in clausal form is
     returned unchanged.  Postcondition: a problem with the parameters of
     [pcsp] whose formulas are clauses (each a disjunction of literals and one
     predicate-free part), together equivalent to the formulas of [pcsp], and
     each clause from a conjunction that holds an unknown carries the
     negation of the conjunction's predicate-free part. *)
  let apply pcsp =
    if PCSP.Problem.is_cnf pcsp then pcsp
    else
        let params = PCSP.Problem.params_of pcsp in
        let exi_senv = PCSP.Problem.senv_of pcsp in
        PCSP.Problem.formulas_of pcsp
        |> Set.concat_map ~f:(fun (uni_senv, phi) ->
            Logic.BoolTerm.cnf_of_guarded exi_senv uni_senv
              (Logic.BoolTerm.nnf_of phi)
            |> Set.Poly.map ~f:(fun (ps, ns, phi) ->
                Clause.to_senv_formula (uni_senv, ps, ns, phi)))
        |> PCSP.Problem.of_formulas ~params
end

(* Restricted copies of a term-set strategy: the demonic question a timed-out
   strategy check falls back to ([demonic_fallback_on_undecided_check]).

   A side's term-set strategy maps each Skolem key to a set of terms, and its
   check is angelic: at every instance the side picks one term per key, so a
   counter-play must refute every pick at once -- on a loop whose two
   alternatives are refuted by a long play and a short one, Spacer has to find
   both.  A copy maps every key to ONE of its terms.  The copy's check asks for
   a play refuting that pick alone.  Since the term-set substitution is the
   disjunction of the copies' substitutions, each copy's clauses imply the
   whole strategy's: a win of a copy would carry over, but a refuted copy says
   nothing about the whole strategy.  So a copy's counter-play is a genuine
   play against the restricted strategy and serves only as a source of
   candidates for the opponent; a copy's win is read as an answer only under
   [demonic_fallback_reads_wins] ([TimeoutPath.copy_outcome]). *)
module DemonicCopies = struct
  exception Enough

  (* [copies ~max ~is_fresh strat_fn]: at most [max] maps with the keys and
     parameters of [strat_fn], each key's term set replaced by a singleton of
     one of its terms (a key with no term keeps its empty set), pairwise
     distinct; none at all when no key has two terms, since the only copy
     would be the strategy itself.
     Order: each key's terms with those satisfying [is_fresh key] first (each
     group in the set's order); tuples by ascending sum of the chosen
     positions, so the first copy takes every key's first term and the next
     ones move one key at a time; then, stably, the tuples choosing a fresh
     term for some key before those choosing none.  At most [8 max + 8]
     tuples are enumerated, so the cost does not depend on the product of the
     set sizes. *)
  let copies ~max ~is_fresh strat_fn =
    let entries =
      Map.Poly.to_alist strat_fn
      |> List.map ~f:(fun (key, (params, terms)) ->
          let fresh, old =
            List.partition_tf (Set.to_list terms) ~f:(is_fresh key)
          in
          (key, params, Array.of_list (fresh @ old), List.length fresh))
    in
    if max <= 0 || List.for_all entries ~f:(fun (_, _, a, _) -> Array.length a <= 1)
    then []
    else
      let limit = (8 * max) + 8 in
      let found = ref [] and count = ref 0 in
      let span (_, _, a, _) = Int.max 0 (Array.length a - 1) in
      (* [rest_span.(i)]: the largest sum the entries from [i] on can take *)
      let n = List.length entries in
      let rest_span = Array.create ~len:(n + 1) 0 in
      List.iteri (List.rev entries) ~f:(fun j e ->
          let i = n - 1 - j in
          rest_span.(i) <- rest_span.(i + 1) + span e);
      let rec go i s acc = function
        | [] ->
            if s = 0 then (
              found := List.rev acc :: !found;
              incr count;
              if !count >= limit then raise Enough)
        | ((_, _, a, _) as e) :: rest ->
            if s <= rest_span.(i) then
              if Array.length a = 0 then go (i + 1) s ((e, -1) :: acc) rest
              else
                for k = 0 to Int.min s (Array.length a - 1) do
                  go (i + 1) (s - k) ((e, k) :: acc) rest
                done
      in
      (try
         for s = 0 to rest_span.(0) do
           go 0 s [] entries
         done
       with Enough -> ());
      let uses_fresh t =
        List.exists t ~f:(fun ((_, _, _, nf), k) -> k >= 0 && k < nf)
      in
      let with_fresh, without =
        List.partition_tf (List.rev !found) ~f:uses_fresh
      in
      List.take (with_fresh @ without) max
      |> List.map ~f:(fun t ->
          Map.Poly.of_alist_exn
          @@ List.map t ~f:(fun ((key, params, a, _), k) ->
              ( key,
                ( params,
                  if k < 0 then Set.Poly.empty else Set.Poly.singleton a.(k) )
              )))

  (* The counter-play a copy's check returned, if any.  Every other outcome --
     a win, an undecided check, an unsatisfiable answer without a play -- is
     [None]: the copy yields nothing, and in particular no verdict. *)
  let counter_play = function
    | PCSP.Problem.Unsat (Some (PCSP.Problem.Formula cex)) -> Some cex
    | _ -> None
end

(* How a timed-out ordinary strategy check is handled: the steps, the order
   they are tried in, and how a restricted copy's answer is read.

   Each step reads only the check it asks itself: the ground split and the
   two re-asks the check's own clauses, the copy-blind re-check the side's
   whole strategy with every choice blind to the remembered copy, and the
   copies ([DemonicCopies]) single-term restrictions of the side's strategy
   with the same rankings.  None of them reads another's outcome, and the
   steps that decide hand the result to the same continuations wherever they
   stand (a counter-play to the refinement, a win to the ordinary check's win
   rules).  So the order decides which question is asked first and whether a
   later one is reached within the run's budget, never what an answer rests
   on.

   A copy's win is sound to read because the answer rules hold for any term
   map whose sets are terms over the keys' parameters, and a copy is the
   check of such a map; it is read only through [win], the ordinary check's
   win rules, so a ranking neither recorded by construction nor proved
   transitive still needs the copy-blind check of the side's whole strategy
   before a verdict is printed. *)
module TimeoutPath = struct
  type step =
    | Ground_split
    | Reask_inline
    | Reask_plain
    | Copy_blind_recheck
    | Copies
  [@@deriving eq, show { with_path = false }]

  (* The order of the steps.  The copies come last unless
     [Read_before_copy_blind]; then right before the copy-blind re-check,
     whose encoding can take seconds on a large check and which, when it
     decides nothing, leaves no budget for the copies.  The ground split is
     kept first: by default it asks the solver nothing more. *)
  let order : Config.demonic_copy_wins -> step list = function
    | Not_read | Read_after_copy_blind ->
        [ Ground_split; Reask_inline; Reask_plain; Copy_blind_recheck; Copies ]
    | Read_before_copy_blind ->
        [ Ground_split; Reask_inline; Reask_plain; Copies; Copy_blind_recheck ]

  (* [run ~ask ~win ~last steps]: the steps in order.  [ask step ~next] says
     what the step did: [`Next], nothing decided, and the next step is tried;
     [`Win], a copy's check is satisfiable and is read as a win of the
     ordinary check, by [win ()]; [`Done r], the step continued the run
     itself, possibly by calling [next] later (the copy-blind re-check does,
     when it decides nothing).  [last ()] after every step gave [`Next]. *)
  let rec run ~ask ~win ~last = function
    | [] -> last ()
    | step :: rest -> (
        match ask step ~next:(fun () -> run ~ask ~win ~last rest) with
        | `Next -> run ~ask ~win ~last rest
        | `Win -> win ()
        | `Done r -> r)

  (* How one copy's answer is read: [`Won] only for a satisfiable check, and
     only when wins are read; [`Play cex] for a counter-play against the
     copy, used only to propose the opponent's candidates; [`None] for
     anything else (a win under [Not_read] included). *)
  let copy_outcome (mode : Config.demonic_copy_wins) sol =
    match (mode, sol) with
    | (Read_after_copy_blind | Read_before_copy_blind), PCSP.Problem.Sat _ ->
        `Won
    | _, sol -> (
        match DemonicCopies.counter_play sol with
        | Some cex -> `Play cex
        | None -> `None)
end

(* The opponent's free choices of a strategy check, and the check with them
   bounded ([bounded_counterplay]).

   In the checked side's problem an opponent's Skolem key [F] (a key the
   checked side does not substitute) occurs where the opponent chooses, as
   the premise [not F(a, r)] of the step it decides, and once more as the
   formula [not F(x1, .., xn)] over distinct universals, which the Horn
   encoding turns into the fact [F(x1, .., xn)]: the opponent may answer any
   [xn] to any [x1 .. x(n-1)].  [restrict ~is_opponent ~bound fs] adds
   [xn < -bound \/ xn > bound] to each such formula of [fs] whose result is
   an integer, so the fact becomes [-bound <= xn <= bound => F(..)].

   Contract.  Every formula of the result implies the formula of [fs] it
   came from (a disjunct added to a negated premise only weakens the
   formula's Horn clause, by narrowing the instances it states), and the
   other formulas are unchanged.  Hence a derivation of the query from the
   result's clauses is one from [fs]'s, through instances of the same
   clauses, and its ground play is a play of the unbounded check; the
   converse fails, so a satisfiable result proves nothing about [fs].
   The count returned is the number of formulas restricted; with 0 the
   result is [fs]. *)
module BoundedPlay = struct
  let free_choice_result ~is_opponent (uni_senv, phi) =
    (* the formula is the negated atom, possibly in a disjunction with
       [false]s (the reduction writes [not F(..) \/ false]) *)
    match
      List.filter (Logic.ExtTerm.disjuncts_of phi) ~f:(fun t ->
          not (Logic.ExtTerm.is_false t))
    with
    | [ lit ] when Logic.ExtTerm.is_not lit ->
      let atom = Logic.ExtTerm.let_not lit in
      if not (Logic.ExtTerm.is_var_app atom) then None
      else
        let key, args = Logic.ExtTerm.let_var_app atom in
        if not (is_opponent key) then None
        else
          let vars = List.filter_map args ~f:(function
              | Logic.Var (x, _) -> Some x
              | _ -> None)
          in
          (match List.last vars with
          | Some r
            when List.length vars = List.length args
                 && (not (List.contains_dup vars ~compare:Ident.tvar_compare))
                 &&
                 match Map.Poly.find uni_senv r with
                 | Some sort -> Stdlib.(sort = Logic.IntTerm.SInt)
                 | None -> false ->
              Some r
          | _ -> None)
    | _ -> None

  (* The largest absolute value of an integer literal of [fs], at least 1. *)
  let largest_literal fs =
    Set.fold fs ~init:Z.one ~f:(fun acc (_, phi) ->
        Set.fold (Logic.IntTerm.int_consts_of phi) ~init:acc ~f:(fun acc z ->
            Z.max acc (Z.abs z)))

  let restrict ~is_opponent ~bound fs =
    let count = ref 0 in
    let fs =
      Set.Poly.map fs ~f:(fun ((uni_senv, phi) as f) ->
          match free_choice_result ~is_opponent f with
          | None -> f
          | Some r ->
              incr count;
              let v = Logic.ExtTerm.mk_var r in
              ( uni_senv,
                Logic.ExtTerm.or_of
                  [
                    phi;
                    Logic.ExtTerm.lt_of v (Logic.IntTerm.mk_int (Z.neg bound));
                    Logic.ExtTerm.gt_of v (Logic.IntTerm.mk_int bound);
                  ] ))
    in
    (fs, !count)
end

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  (* [extra_plays_inherit_lemmas]: every Spacer solve that returns a
     counterexample keeps its lemmas for the extra counter-plays asked after
     it ([SPACER.Solver.Carry]) *)
  let () =
    if config.extra_plays_inherit_lemmas && config.counter_plays_per_check > 1
    then SPACER.Solver.Carry.capturing := true

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* a verbose run also prints the environments a failed term conversion
     searched; a quiet run catches those failures silently and retries *)
  let () = if config.verbose then Atomic.set Ast.Logic.print_unbound_envs true

  (* [use_dwf = true] is MuStrat's method, not a choice a configuration makes,
     which is why it is fixed here rather than read from [config]: the rank
     unknowns this reduction makes are read back as the opponent's [DWF] keys
     (each starts as the empty relation), and a refinement disjoins a new
     piece onto a key over all the plays, so each must stand for a relation
     contained in a finite union of well-founded ones (Podelski and
     Rybalchenko's disjunctive well-foundedness), not for one well-founded
     relation.  MuVal builds the same reducer with [false]. *)
  module Reducer = MuCLP.Reducer.Make (
    struct
      let config =
        MuCLP.Reducer.Config.
          {
            verbose = config.verbose;
            use_dwf = true;
            reduction =
              Wf_reduction
                {
                  restrict_ranking_to_cycles = true;
                  record_on_head = false;
                  one_relation_per_block = false;
                };
          }
    end :
      MuCLP.Reducer.Config.ConfigType)

  module Qelim = MuCLP.Qelim.Make (
    struct
      let config =
        MuCLP.Qelim.Config.
          {
            verbose = config.verbose;
            elimination = SkolemPred;
            share_witnesses = No_witness_sharing;
          }
    end :
      MuCLP.Qelim.Config.ConfigType)

  let chc_solver () =
    let open Or_error in
    ExtFile.unwrap config.chc_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  (* The main solver of the check of a side with no strategy unknown: the
     configured replacement if there is one, else [chc_solver ()].  Only the
     solver changes; the CHC it is given and the rule its answer is read by are
     those of any other check. *)
  module type CheckSolverType = PCSPSolver.Solver.SolverType

  let empty_strategy_chc_solver () =
    let open Or_error in
    match config.empty_strategy_chc_solver with
    | None -> chc_solver ()
    | Some f ->
        ExtFile.unwrap f >>= fun cfg ->
        PCSPSolver.Solver.(
          Ok
            (module Make (struct
              let config = cfg
            end) : SolverType))

  (* The solver raced on a strategy-free check ([strategy_free_race_solver]). *)
  let strategy_free_race_solver f =
    let open Or_error in
    ExtFile.unwrap f >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  (* Budgets, in seconds, of the strategy check, each starting from
     [chc_initial_timeout].  Under [Global_doubling] both sides read the shared
     pair; under [Pass_turn_on_timeout] each side reads its own.  None is reset
     between turns: a budget only grows, and only when a check at that budget
     timed out. *)
  let chc_timeout = ref config.chc_initial_timeout
  let chc_timeout_backup = ref config.chc_initial_timeout
  let chc_timeout_primal = ref config.chc_initial_timeout
  let chc_timeout_dual = ref config.chc_initial_timeout
  let chc_timeout_backup_primal = ref config.chc_initial_timeout
  let chc_timeout_backup_dual = ref config.chc_initial_timeout

  (* Per side (index 0 primal, 1 dual), the number of tagged re-asks
     ([chain_pair_regions_free_opponent_values]) in a row that returned no
     counter-play; reset to 0 by one that returns one.  Read only by
     [freed_reask_skip_after_failures]. *)
  let freed_reask_failures = [| 0; 0 |]

  (* The budget the check of side [turn] (true = primal) uses, with the main or
     the backup CHC solver. *)
  let chc_budget ~backup turn =
    match (config.chc_timeout_policy, backup, turn) with
    | Config.Global_doubling, false, _ -> chc_timeout
    | Global_doubling, true, _ -> chc_timeout_backup
    | Pass_turn_on_timeout, false, true -> chc_timeout_primal
    | Pass_turn_on_timeout, false, false -> chc_timeout_dual
    | Pass_turn_on_timeout, true, true -> chc_timeout_backup_primal
    | Pass_turn_on_timeout, true, false -> chc_timeout_backup_dual

  let backup_chc_solver () =
    let open Or_error in
    ExtFile.unwrap config.backup_chc_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  (* The verdict-only solver of [reask_undecided_check_inline]. *)
  let reask_inline_chc_solver () =
    let open Or_error in
    ExtFile.unwrap config.reask_inline_chc_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let pcsp_solver () =
    let open Or_error in
    ExtFile.unwrap config.pcsp_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let pcsp_solver_determ () =
    let open Or_error in
    ExtFile.unwrap config.pcsp_solver_determ >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let optimizer_cfg = ExtFile.unwrap config.optimizer
  let verbose = true

  (* [validate_verdicts]: the rewrites of the input made so far by this run,
     each group a list of pairs (before, after) whose equivalence is checked
     before the strategy checks start.  Reset by [solve]. *)
  let upstream_rewrites : (string * (LogicOld.Formula.t * LogicOld.Formula.t) list) list ref =
    ref []

  let formulas_of_muclp muclp =
    muclp.query :: List.map muclp.preds ~f:(fun pred -> pred.MuCLP.Pred.body)

  let preprocess ?(id = None) ?(elim_forall = true) ?(elim_exists = true)
      ?(elim_pvar_args = true) muclp =
    let open Or_error in
    optimizer_cfg >>= fun optimizer_cfg ->
    Ok (MuCLP.Optimizer.make optimizer_cfg)
    >>= fun (module Optimizer : MuCLP.Optimizer.OptimizerType) ->
    let muclp = if config.check_problem then check_problem muclp else muclp in
    Debug.print ~id
    @@ lazy
         (sprintf "######################\nbefore optimization: %s\n"
         @@ str_of muclp);
    let simplified = simplify muclp in
    if config.validate_verdicts then
      upstream_rewrites :=
        ( "simplification",
          List.zip_exn (formulas_of_muclp muclp) (formulas_of_muclp simplified)
        )
        :: !upstream_rewrites;
    let muclp =
      Common.PhaseTime.with_phase "mustrat-optimize" @@ fun () ->
      Optimizer.f ~id ~elim_forall ~elim_exists ~elim_pvar_args simplified
    in
    Debug.print ~id
    @@ lazy
         (sprintf "after optimization: %s\n######################\n"
         @@ str_of muclp);
    Ok muclp

  (* [layout], when given, is cleared and receives, for every predicate of the
     returned problem that the reduction extended, the argument positions it
     prepended, keyed by the problem's name of the predicate ([U_P_]). *)
  let to_pfwcsp ?layout muclp =
    (* Skolemize quantifiers *)
    if verbose then
      Debug.print @@ lazy (sprintf "Input muCLP: %s\n" @@ str_of muclp);
    let muclp, univ_fns =
      Qelim.elim_exists ~conv_forall:(Config.name_universals config)
        (muclp, (Map.Poly.empty, Map.Poly.empty))
    in
    Debug.print ~id:None @@ lazy (sprintf "Skolemized: %s\n" @@ str_of muclp);
    let muclp =
      muclp |> aconv_tvar |> complete_tsort
      |> complete_psort (Kind.pred_sort_env_map_of univ_fns)
    in
    if verbose then
      Debug.print @@ lazy (sprintf "Preprocessed muCLP: %s\n" @@ str_of muclp);
    let pfwcsp, wfs =
      (* The greatest-fixpoint remembered-state encoding is not used: it
         served only the per-step facts below, which are disabled, and
         nothing else reads what it produces.  The opponent's decisions are
         still named ([conv_forall] above).  With it the first check alone
         grew by doubled arguments and a guard per recursive call, enough for
         inputs the plain encoding decides in seconds to exhaust a minute. *)
      let tbl = Hashtbl.Poly.create () in
      let res =
        Reducer.f ~id:None ~conv_nu:false ~layout:tbl ~exchange:false
          ~messenger:None muclp univ_fns
      in
      Option.iter layout ~f:(fun out ->
          Hashtbl.clear out;
          Hashtbl.iteri tbl ~f:(fun ~key ~data ->
              Hashtbl.set out
                ~key:(Ident.name_of_pvar @@ Ident.uninterp_pvar key)
                ~data));
      res
    in
    let pfwcsp =
      PCSP.Problem.add_formulas
        (* The dummy predicate variables for universal quantifiers are fixed to false *)
        (Set.Poly.filter_map
           (Map.to_set @@ fst univ_fns)
           ~f:(fun (x, s) ->
             if Kind.is_ord @@ Map.Poly.find_exn (snd univ_fns) x then
               let args =
                 Logic.mk_fresh_sort_env_list @@ Logic.Sort.args_of s
               in
               let papp =
                 Logic.ExtTerm.mk_var_app x
                   (List.map args ~f:(fst >> Logic.ExtTerm.mk_var))
               in
               Some
                 ( Map.Poly.of_alist_exn args,
                   Logic.BoolTerm.imply_of papp (Logic.BoolTerm.mk_bool false)
                 )
             else None))
        pfwcsp
    in
    Debug.print ~id:None
    @@ lazy
         (sprintf "******* Generated pfwCSP:\n%s" @@ PCSP.Problem.str_of pfwcsp);
    ( PCSP.Problem.map pfwcsp ~f:Logic.Term.refresh,
      Map.filter_keys (fst wfs) ~f:(Map.Poly.find_exn (snd wfs) >> Kind.is_ord)
    )

  (* The reading of a counter-play (a derivation the CHC backend returned)
     back into clauses and a play tree, with this check's configuration and
     trace; see [CounterPlay]. *)
  module CounterPlays = CounterPlay.Make (struct
    let config = config
    let print = Debug.print
  end)

  let let_hyper_res = CounterPlays.let_hyper_res
  let let_mp = CounterPlays.let_mp

  (* The ground play a derivation records; see [ChainRegions.play_node]. *)
  type play_node = ChainRegions.play_node = {
    pvar : Ident.pvar;
    args : LogicOld.Term.t list;
    children : play_node list;
    clause : LogicOld.Formula.t;
  }

  module StepTbl = CounterPlays.StepTbl

  let play_node_hash = ChainRegions.play_node_hash

  module PlayTbl = Stdlib.Hashtbl.Make (struct
    type t = play_node

    let equal = phys_equal
    let hash = play_node_hash
  end)

  let play_tree_of = CounterPlays.play_tree_of

  (* [validate_verdicts]: the topmost derived atoms of the derivation [cex]
     the CHC backend returned for [chc], as [VerdictValidation] reads them.
     The backend's derivation ends in its own query relation (or in [false]),
     whose premises are then the roots; a derivation ending in an atom of an
     unknown of [chc] has that atom as its one root.  Each distinct step is
     read once and a shared step gives one shared node; see
     [CounterPlay.derivation_roots] for the contract.  Raises
     [VerdictValidation.Reject] on a node whose conclusion is not an
     application of a predicate. *)
  let derivation_roots chc cex =
    CounterPlays.derivation_roots
      ~unknowns:(VerdictValidation.unknowns_of chc)
      cex

  (* The readings of a counter-play that decide whether the bounded re-ask
     is asked; see [CounterPlay]. *)
  let play_exceeds = CounterPlays.play_exceeds
  let play_outliers = CounterPlays.play_outliers
  let isolated_outlier = CounterPlays.isolated_outlier

  (* [validated what check verdict]: [verdict] when [validate_verdicts] is off
     or [check ()] succeeds; [Unknown] otherwise.  Every outcome is printed on
     stderr as a [mustrat-validate:] census line, whether or not tracing is
     on, and its reason through the trace. *)
  let validated what check verdict =
    if not config.validate_verdicts then Ok verdict
    else
      let t0 = Common.PhaseTime.now () in
      let res =
        try check ()
        with
        | VerdictValidation.Reject r -> Error r
        | exn when not (Common.Timer.is_async exn) ->
            Error ("raised " ^ Exn.to_string exn)
      in
      let secs = Common.PhaseTime.now () -. t0 in
      match res with
      | Ok () ->
          eprintf "mustrat-validate: %s validated secs=%.2f\n%!" what secs;
          Ok verdict
      | Error reason ->
          eprintf "mustrat-validate: %s refused secs=%.2f\n%!" what secs;
          Debug.print
          @@ lazy
               (sprintf "### The %s is not validated (answering unknown): %s"
                  what reason);
          Ok Unknown

  (* For the opponent's ranking key [WF_P_], the pairs of ground states its
     ranking must contain for the checked side's derivation to be a play the
     opponent wins.  The opponent's least-fixpoint predicate [P] is visited at
     every node whose conclusion is an application of [U_P_] (the reduction's
     name for [P] in the checked side's clauses); along a root-to-leaf path the
     visits are in play order, root first.  Because the reduction lets the
     checked side keep any earlier visit as the remembered state, the ranking
     must contain EVERY pair (s_i, s_j) with i < j on a path, not only the
     consecutive ones -- Podelski and Rybalchenko's transition-invariant
     condition.  The state is the last [n] arguments of the conclusion, [n]
     being half the key's arity, since the reduction puts the remembered copy
     (and, for a predicate called from outside its component, a flag) first.
     The chain is RESET at a visit to a predicate of lower index (an outer
     equation of the hierarchical system), as in Kura and Unno's disjunctively
     well-founded game (Def. 6.4): the ranking of [P] need only decrease between
     visits to [P] with no outer predicate visited in between.  Without the
     reset the pairs would span outer visits, and on a play that returns to the
     same [P]-state through an outer predicate no ranking contains them, which
     is how a refinement came out unsatisfiable on every turn of an input whose
     outer least-fixpoint predicate shares a component with inner ones.
     [pred_index] maps the reduction's name for each predicate ([U_Q_]) to its
     position in the equation list; a name it does not hold (the query, the
     Skolem dummies) neither extends nor resets a chain. *)
  let pred_index : (string, int) Hashtbl.t = Hashtbl.create (module String)

  let set_pred_index muclp =
    Hashtbl.clear pred_index;
    List.iteri muclp.MuCLP.Problem.preds ~f:(fun i pred ->
        Hashtbl.set pred_index
          ~key:(Ident.name_of_pvar @@ Ident.uninterp_pvar pred.MuCLP.Pred.name)
          ~data:i)

  (* The argument positions the reduction prepended to each predicate, one
     table for the primal problem and one for the dual, keyed by the problem's
     name of the predicate ([U_P_]; see [MuCLP.Reducer.prefix_entry]).  Filled
     by [solve] from the reduction itself and read only under
     [copy_blind_choices]; a predicate absent from its side's table carries no
     copy. *)
  let copy_layout_primal : (string, MuCLP.Reducer.prefix_entry list) Hashtbl.t
      =
    Hashtbl.create (module String)

  let copy_layout_dual : (string, MuCLP.Reducer.prefix_entry list) Hashtbl.t =
    Hashtbl.create (module String)

  (* Chain pairs and their regions, with this check's predicate positions,
     trace and configuration; see [ChainRegions]. *)
  let rank_target_of = ChainRegions.rank_target_of
  let repair_log = ChainRegions.repair_log

  let chain_pairs_of ?nearest_only tree ~wf_key ~arity =
    ChainRegions.chain_pairs_of ?nearest_only ~print:Debug.print ~pred_index
      ~splice_chain_revisits:config.splice_chain_revisits tree ~wf_key ~arity

  let chain_regions_of ?passed ?by_mbp ?problem_sides_only ?multiphase_depth
      ?window ?window_min_pairs ?bind_decision ?bind_step ?observe ~decisions
      tree ~wf_key ~arity =
    ChainRegions.chain_regions_of ~print:Debug.print ~pred_index
      ~drop_implied:config.chain_pair_region_drop_implied
      ~window_key:config.chain_pair_segments_window_key ?passed ?by_mbp
      ?problem_sides_only ?multiphase_depth ?window ?window_min_pairs
      ?bind_decision ?bind_step ?observe ~decisions tree ~wf_key ~arity

  (* The plays the last refinement read (the first play, then the extra
     ones), kept for [JointWall], which reads them only when its variable is
     set. *)
  let last_refinement_plays = ref []

  (* The clauses of the check [chc], as [JointWall] reads the ranked side's
     choices between disjuncts off them (old-style clauses, as
     [PassedChoices] takes them): all of a clausal check's; of a check still
     stated as formulas, those of each formula whose conversion
     [CheckCnf.cnf_size]
     bounds by [joint_wall_cnf_max] clauses, the others skipped.  Converting
     such a check whole need not finish (the solving path names its
     multiplying disjunctions first), and a skipped formula only hides
     alternatives from the instrument.  Read by the instrument alone. *)
  let joint_wall_cnf_max = 1000

  let joint_wall_clauses chc =
    let exi_senv = PCSP.Problem.senv_of chc in
    let clauses =
      if PCSP.Problem.is_cnf chc then Set.to_list (PCSP.Problem.clauses_of chc)
      else
        List.concat_map (Set.to_list (PCSP.Problem.formulas_of chc))
          ~f:(fun (uni_senv, phi) ->
            if CheckCnf.cnf_size exi_senv uni_senv phi > joint_wall_cnf_max then []
            else
              Set.to_list
                (ClauseSet.of_formulas exi_senv
                   (Set.Poly.singleton (uni_senv, phi))))
    in
    List.map clauses ~f:(fun c ->
        let senv, ps, ns, phi = Clause.to_old_clause exi_senv c in
        (Logic.to_old_sort_env_map senv, ps, ns, phi))

  (* The EXITS of the play [tree] from the chains the opponent's rankings
     cover, as the atoms to block, per predicate name: its arity and its
     ground argument tuples.  A node is on a chain path when it is the root,
     or an application of a predicate some key of [wf_strat] ranks, or has
     such an application below it; an exit is a child of an on-path node that
     is not itself on a path -- a side premise of the query, or the premise by
     which a chain ends (the base case under its last visit).  Blocking the
     exits and nothing on the paths leaves the chains themselves available, so
     the next derivation has to reach the query by another side premise or
     continue a chain past the state where the previous one stopped, which is
     what lengthens the chain pairs.  Blocking the ranked states instead
     removes the chain a counter-play is forced through and leaves no play.
     A node defining a checked-side strategy value ([FreedValues]) is part of
     its parent's clause, the value the strategy decides there, and is never
     an exit.  Empty when the play visits no ranked predicate. *)
  let exits_of tree wf_strat =
    let targets =
      Set.Poly.of_list @@ List.filter_map ~f:rank_target_of
      @@ Map.Poly.keys wf_strat
    in
    let is_target node = Set.mem targets (Ident.name_of_pvar node.pvar) in
    (* A play shares a node used by several parents ([play_tree_of]), and
       both walks below visit each node once.  Being on a path is a function
       of the node alone, and so is the set of exits a node's children add;
       the result is read as a set (deduplicated and sorted per name), so
       visiting a node once per path, as a tree walk does, adds nothing but
       repetitions, and on a play with millions of paths never ended. *)
    let on_path_memo = PlayTbl.create 256 in
    let rec on_path node =
      match PlayTbl.find_opt on_path_memo node with
      | Some b -> b
      | None ->
          let b = is_target node || List.exists node.children ~f:on_path in
          PlayTbl.replace on_path_memo node b;
          b
    in
    let exits = ref [] in
    let visited = PlayTbl.create 256 in
    let rec go node =
      if not (PlayTbl.mem visited node) then (
        PlayTbl.replace visited node ();
        List.iter node.children ~f:(fun child ->
            if on_path child then go child
            else if
              (not (String.is_empty (Ident.name_of_pvar child.pvar)))
              && not (FreedValues.is_tag (Ident.name_of_pvar child.pvar))
            then
              exits := (Ident.name_of_pvar child.pvar, child.args) :: !exits))
    in
    if not (on_path tree) then Map.Poly.empty
    else (
      go tree;
      List.fold !exits ~init:Map.Poly.empty ~f:(fun acc (name, args) ->
          Map.Poly.update acc name ~f:(function
            | None -> (List.length args, [ args ])
            | Some (n, argss) -> (n, args :: argss)))
      |> Map.Poly.map ~f:(fun (n, argss) ->
             (n, List.dedup_and_sort ~compare:Stdlib.compare argss)))

  (* The checked CHC [chc] with the atoms [blocked] (per predicate name, the
     arity and the ground argument tuples) excluded as PREMISES: every
     negative occurrence of [P(t)] becomes [P(t) /\ t <> a_1 /\ ..].  A negative
     occurrence made smaller makes its formula larger, so each blocked formula
     is implied by the original and the blocked system is a weakening: when it
     is unsatisfiable so is the original, and every clause instance its
     derivation uses is an instance of the original clause, so the derivation
     is a counter-play of the checked strategy.  Head occurrences are left
     alone (a guard there would add a goal rather than remove a derivation).
     Formulas mentioning no blocked predicate are passed through unconverted.
     [None] when no occurrence was blocked. *)
  let block_states chc blocked =
    let open LogicOld in
    let exi_senv = PCSP.Problem.senv_of chc in
    let blocked_names = Set.Poly.of_list @@ Map.Poly.keys blocked in
    let changed = ref false in
    let phis =
      Set.Poly.map (PCSP.Problem.formulas_of chc) ~f:(fun (uni_senv, phi) ->
          if
            not
              (Set.exists (Logic.Term.fvs_of phi) ~f:(fun v ->
                   Set.mem blocked_names (Ident.name_of_tvar v)))
          then (uni_senv, phi)
          else
            let phi' =
              Formula.map_atom_polarity
                (Logic.ExtTerm.to_old_fml exi_senv uni_senv phi)
                true
                ~f:(fun polarity atom ->
                  match atom with
                  | Atom.App (Predicate.Var (pvar, _), ts, _) when not polarity
                    -> (
                      match Map.Poly.find blocked (Ident.name_of_pvar pvar) with
                      | Some (n, states) when List.length ts >= n ->
                          let st = List.drop ts (List.length ts - n) in
                          let guards =
                            List.filter_map states ~f:(fun s ->
                                if List.length s = n then
                                  Some
                                    (Formula.mk_neg @@ Formula.and_of
                                    @@ List.map2_exn st s ~f:Formula.eq)
                                else None)
                          in
                          if List.is_empty guards then Formula.mk_atom atom
                          else (
                            changed := true;
                            Formula.and_of (Formula.mk_atom atom :: guards))
                      | _ -> Formula.mk_atom atom)
                  | _ -> Formula.mk_atom atom)
            in
            (uni_senv, Logic.ExtTerm.of_old_formula phi'))
    in
    if !changed then
      Some (PCSP.Problem.of_formulas ~params:(PCSP.Problem.params_of chc) phis)
    else None

  (* Under [extra_plays_budget_factor]: when the ask of the current check
     started ([Common.PhaseTime.now]; for an answer of a copy continuing the
     check, when that copy started), and the seconds from then until its
     answer was read -- the time the check that returned the first play
     took, before any re-ask of it.  Only budgets of extra counter-plays read
     them. *)
  let ask_started = ref 0.

  let play_check_secs = ref None

  (* Up to [counter_plays_per_check - 1] further counter-plays of the check
     [chc] beyond the one [cex] records, each asked of [solver] at [budget]
     seconds with the exits of every play found so far blocked ([exits_of],
     [block_states]), so that each answer is a different play.  Collection
     stops at the first query that does not return a counter-play, when a play
     adds no state to block, or on any failure but an asynchronous one; the
     plays found until then are kept.  So the check takes at most
     [counter_plays_per_check] times its budget.  Nothing here decides an
     answer: the plays only feed the opponent's ranking refinement. *)
  let extra_counter_plays (module S : CheckSolverType) ~budget wf_strat chc
      cex =
    let k = config.counter_plays_per_check in
    if k <= 1 || not (Config.chain_pairs_from_play config) then []
    else
      let found = ref [] in
      let merge m1 m2 =
        Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
          | `Left v | `Right v -> Some v
          | `Both ((n, a), (_, b)) ->
              Some (n, List.dedup_and_sort ~compare:Stdlib.compare (a @ b)))
      in
      let same m1 m2 =
        Map.Poly.equal (fun (n1, a) (n2, b) -> n1 = n2 && Stdlib.( = ) a b) m1 m2
      in
      let count m =
        Map.Poly.fold m ~init:0 ~f:(fun ~key:_ ~data:(_, sts) acc ->
            acc + List.length sts)
      in
      (* [extra_plays_inherit_lemmas]: Spacer's lemmas from the solve that
         returned the previous play, when it was a Spacer solve of the
         system this query strengthens ([SPACER.Solver.Carry]); [None]
         otherwise, and then the query is asked from nothing as before *)
      let carry =
        ref
          (if config.extra_plays_inherit_lemmas then
             SPACER.Solver.Carry.take_for chc
           else None)
      in
      let rec loop blocked tree i =
        if i < k then
          let blocked' = merge blocked (exits_of tree wf_strat) in
          if not (same blocked blocked') then
            match block_states chc blocked' with
            | None -> ()
            | Some chc' -> (
                Debug.print
                @@ lazy
                     (sprintf
                        "### Asking for counter-play %d of %d (%d sec.) with %d \
                         exit atom(s) blocked: %s"
                        (i + 1) k budget (count blocked')
                        (String.concat_map_list ~sep:"; "
                           (Map.Poly.to_alist blocked') ~f:(fun (p, (_, argss)) ->
                             String.concat_map_list ~sep:" " argss ~f:(fun ts ->
                                 sprintf "%s(%s)" p
                                   (String.concat_map_list ~sep:","
                                      ~f:LogicOld.Term.str_of ts)))));
                let outcome_of = function
                  | Ok (PCSP.Problem.Unsat (Some _), _) -> "play"
                  | Ok (PCSP.Problem.Timeout, _) -> "timeout"
                  | Ok (PCSP.Problem.Sat _, _) -> "none"
                  | Ok _ -> "other"
                  | Error _ -> "error"
                in
                let t0 = Common.PhaseTime.now () in
                let carried = Option.value_map !carry ~default:0 ~f:SPACER.Solver.Carry.size in
                SPACER.Solver.Carry.seed_next !carry;
                (* a seed left unconsumed (a solver other than Spacer) must
                   not reach a later solve of a system it does not
                   over-approximate *)
                let r =
                  Exn.protect
                    ~f:(fun () -> S.solve ~timeout:(Some budget) chc')
                    ~finally:(fun () -> SPACER.Solver.Carry.seed_next None)
                in
                (* a play's solve was asked of a strengthening of [chc'] next *)
                carry :=
                  if config.extra_plays_inherit_lemmas then
                    SPACER.Solver.Carry.take_for chc'
                  else None;
                if LoopPhase.timeline then
                  eprintf
                    "mustrat-extra-play: n=%d budget=%d secs=%.2f carried=%d \
                     seeded=%d capture=%.2f first=%s outcome=%s\n%!"
                    (i + 1) budget
                    (Common.PhaseTime.now () -. t0)
                    carried !SPACER.Solver.Carry.last_seeded
                    !SPACER.Solver.Carry.last_capture_secs
                    (match !play_check_secs with
                    | Some s -> sprintf "%.2f" s
                    | None -> "-")
                    (outcome_of r);
                (* A diagnostic, with COAR_MUSTRAT_CARRY_AB set: a query that
                   was seeded is asked once more from nothing, at the same
                   budget, and both times and outcomes are printed
                   ([mustrat-carry-ab:]); the seeded answer is the one used *)
                if
                  carried > 0
                  && Option.is_some (Sys.getenv "COAR_MUSTRAT_CARRY_AB")
                then (
                  let secs = Common.PhaseTime.now () -. t0 in
                  let seeded = !SPACER.Solver.Carry.last_seeded in
                  let t1 = Common.PhaseTime.now () in
                  let r' = S.solve ~timeout:(Some budget) chc' in
                  eprintf
                    "mustrat-carry-ab: n=%d budget=%d seeded=%d seeded_secs=%.2f \
                     seeded_outcome=%s fresh_secs=%.2f fresh_outcome=%s\n%!"
                    (i + 1) budget seeded secs (outcome_of r)
                    (Common.PhaseTime.now () -. t1)
                    (outcome_of r'));
                match r with
                | Ok (PCSP.Problem.Unsat (Some (PCSP.Problem.Formula cex')), _)
                  ->
                    let hres, _, _ = let_mp cex' in
                    let tree' = play_tree_of hres in
                    found := tree' :: !found;
                    Debug.print
                    @@ lazy (sprintf "### Counter-play %d found" (i + 1));
                    loop blocked' tree' (i + 1)
                | Ok (sol, _) ->
                    Debug.print
                    @@ lazy
                         (sprintf "### No counter-play %d: %s" (i + 1)
                            (PCSP.Problem.str_of_sol_with_witness sol))
                | Error err ->
                    Debug.print
                    @@ lazy
                         (sprintf "### No counter-play %d: %s" (i + 1)
                            (Error.to_string_hum err)))
      in
      (try
         let hres, _, _ = let_mp cex in
         loop Map.Poly.empty (play_tree_of hres) 1
       with exn when not (Common.Timer.is_async exn) ->
         Debug.print
         @@ lazy
              (sprintf "### Extra counter-plays stopped (%s)"
                 (Exn.to_string exn)));
      List.rev !found

  exception NoRefinement

  (* Raised by [refine_strat] under [bound_last_refinement] when the
     refinement's final answer is the constraint solver's [Timeout]: the
     bounded last form ran out of its budget.  Read by the turn loop as
     [StallRule.Last_form_expired], not as a failed refinement. *)
  exception RefinementBudgetExpired

  (* Under [demonic_fallback_on_undecided_check]: per side ([true] the primal)
     and key name, the term set the side's strategy had at its last check and
     the terms that set added over the one checked before it.  Updated only
     when the set changes, so a retried check of the same strategy keeps the
     record of what was new.  It only orders the restricted copies. *)
  let checked_terms :
      (bool * string, Logic.term Set.Poly.t * Logic.term Set.Poly.t) Hashtbl.Poly.t =
    Hashtbl.Poly.create ()

  let note_checked_terms turn strat_fn =
    Map.Poly.iteri strat_fn ~f:(fun ~key ~data:(_, terms) ->
        let k = (turn, Ident.name_of_tvar key) in
        match Hashtbl.find checked_terms k with
        | Some (last, _) when Set.equal last terms -> ()
        | Some (last, _) ->
            Hashtbl.set checked_terms ~key:k ~data:(terms, Set.diff terms last)
        | None -> Hashtbl.set checked_terms ~key:k ~data:(terms, Set.Poly.empty))

  let is_fresh_term turn key term =
    match Hashtbl.find checked_terms (turn, Ident.name_of_tvar key) with
    | Some (_, fresh) -> Set.mem fresh term
    | None -> false

  (* Consecutive turns on which a refinement added nothing (every failed
     refinement passes the turn and is counted here).  A refinement that adds nothing leaves the
     strategies as they were, so the next check returns the same derivation and
     the alternation would repeat forever; two such turns in a row (one per side)
     end the run with [unknown].  The verdicts themselves do not depend on this:
     [valid] and [invalid] come only from an exact check of one side's strategy
     against every behaviour of the other.  Reset at each [solve]. *)
  (* [COAR_MUSTRAT_REASK_CENSUS] set: each re-ask of
     [reask_undecided_check_inline] prints one line with its outcome. *)
  let reask_census =
    Option.is_some (Sys.getenv "COAR_MUSTRAT_REASK_CENSUS")

  (* Census lines of the demonic fallback on stderr (whether or not tracing
     is on): one per copy asked, with its answer, and one per fallback, with
     where it was asked and what it gave. *)
  let copies_census =
    Option.is_some (Sys.getenv "COAR_MUSTRAT_COPIES_CENSUS")

  (* [race_check_plain_spacer]: how long the process waits, after its own
     check timed out, for the raced copy (same budget, started a moment
     later) to say what it found before killing it.  It bounds what a
     timed-out check costs beyond its budget with the race on. *)
  let race_timeout_grace_ms = 2000

  let split_census =
    Option.is_some (Sys.getenv "COAR_MUSTRAT_ALT_SPLIT_CENSUS")

  (* Whether each WF read-back prints which ranking keys
     [resynthesise_only_on_new_pairs] keeps, or would keep (a counter that
     also shows the field was read). *)
  let rulem_census =
    Option.is_some (Sys.getenv "COAR_MUSTRAT_RULEM_CENSUS")

  (* Whether some smallest-derivation exploration of a split in this [solve]
     ran out of the configured attempt budget [split_ground_alternative_budget]
     after the small budget of [split_ground_budget_after_cut] had been cut
     too.  Reset at each [solve]. *)
  let split_cut_seen = ref false

  (* [split_ground_goals_first], read through the gate of
     [split_ground_goals_first_integer_only]: whether the input passed it is
     set at each [solve]. *)
  let split_first_gate = ref true

  let split_first_on () = config.split_ground_goals_first && !split_first_gate

  (* The height ([GroundGoals.height]) of the derivation the last split
     that derived a counter-play returned; read by
     [freed_reask_after_split_max_height] right after the split asked before
     the solver derived one, so it is that split's.  [0] before any. *)
  let last_split_height = ref 0

  (* the number of splits dumped under [COAR_GROUND_SPLIT_DUMP] *)
  let split_dump_count = ref 0

  (* [split_ground_goals chc], under [split_ground_alternative_goals]: a
     counter-play of the check [chc] composed from separate derivations of the
     ground atoms its goals conjoin ([GroundGoals]), in the form Spacer
     reports one, or [None] when [chc] is not of that shape or some goal's
     atoms were not all derived.  [None] proves nothing. *)
  let rec split_ground_goals ?prove ?budget chc =
    match split_ground_goals_outcome ?prove ?budget chc with
    | `Counter_play cex -> Some cex
    | `Won | `Nothing -> None

  (* [split_ground_goals_outcome chc]: as [split_ground_goals], with a third
     outcome [`Won] when the split proves the query not derivable: by
     [split_ground_goals_first]'s smallest search ([GroundGoals.Won]), or by
     [prove], the leaf proofs of [split_ground_prove_leaves]
     ([GroundGoals.Underivable]). *)
  and split_ground_goals_outcome ?prove ?budget chc =
    match (budget, config.split_ground_budget_after_cut) with
    | Some budget, _ -> split_ground_goals_once ?prove ~budget chc
    | None, None ->
        split_ground_goals_once ?prove
          ~budget:config.split_ground_alternative_budget chc
    | None, Some small ->
        (* [split_ground_budget_after_cut]: asked at the small budget first,
           and at the configured one only when that left the split undecided
           with some exploration cut, and no exploration at the configured
           budget has been cut in this [solve].  Before such a cut the
           outcome kind is the configured budget's: a leaf derived or proved
           underivable within fewer tries is so within more (the exploration
           is the same up to the smaller budget), and an undecided split with
           no cut explored as far as any budget would. *)
        let large = config.split_ground_alternative_budget in
        let cuts0 = !GroundGoals.smallest_cuts in
        let escapes0 = !GroundGoals.smallest_escapes in
        (* [split_ground_large_pass_literal_box]: the first pass records the
           explorations that leave the clauses' literal box, the second is not
           asked after one did and stops each exploration at its first atom
           outside the box.  A pass not asked or stopped is a search given up
           on, handled as [`Nothing] already is. *)
        let box = config.split_ground_large_pass_literal_box in
        let r =
          split_ground_goals_once ?prove
            ?literal_box:(if box then Some `Record else None)
            ~budget:(Int.min small large) chc
        in
        (match r with
        | `Nothing
          when !GroundGoals.smallest_cuts > cuts0
               && (not !split_cut_seen) && large > small ->
            if box && !GroundGoals.smallest_escapes > escapes0 then (
              if split_census then
                eprintf "mustrat-alt-split: large-pass-skipped escaped\n%!";
              Debug.print
              @@ lazy
                   "### Ground alternative split: second pass not asked (an \
                    atom left the literal box)";
              `Nothing)
            else
              let cuts1 = !GroundGoals.smallest_cuts in
              let r' =
                split_ground_goals_once ?prove ~budget_after_cut:small
                  ?literal_box:(if box then Some `Stop else None)
                  ~budget:large chc
              in
              if !GroundGoals.smallest_cuts > cuts1 then split_cut_seen := true;
              r'
        | r -> r)

  and split_ground_goals_once ?prove ?budget_after_cut ?literal_box ~budget chc
      =
    let t0 = Common.Clock.now_float () in
    (* Z3 is asked for at most [split_ground_alternative_max_asks] clause
       instances over the whole split; the count is reported. *)
    let ask, asks =
      GroundGoals.bounded_ask ?max:config.split_ground_alternative_max_asks
        GroundGoals.ask_z3
    in
    let escapes0 = !GroundGoals.smallest_escapes in
    let census outcome =
      let outcome =
        match literal_box with
        | None -> sprintf "%s budget=%d" outcome budget
        | Some _ ->
            sprintf "%s budget=%d escaped=%d" outcome budget
              (!GroundGoals.smallest_escapes - escapes0)
      in
      let msg =
        sprintf "%s asks=%d secs=%.2f" outcome !asks
          (Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) t0))
      in
      if split_census then eprintf "mustrat-alt-split: %s\n%!" msg;
      Debug.print @@ lazy (sprintf "### Ground alternative split: %s" msg)
    in
    match GroundGoals.clauses_of_problem chc with
    | None ->
        census "not-clausal";
        `Nothing
    | Some clauses -> (
        (* [COAR_GROUND_SPLIT_DUMP=DIR]: each split's clauses are written to
           [DIR/split_<n>_b<budget>[_c<budget after a cut>].smt2], for a
           replay outside the run *)
        (match Sys.getenv "COAR_GROUND_SPLIT_DUMP" with
        | Some dir ->
            incr split_dump_count;
            GroundGoals.dump_smt2
              (sprintf "%s/split_%03d_b%d%s.smt2" dir !split_dump_count budget
                 (match budget_after_cut with
                 | Some b -> sprintf "_c%d" b
                 | None -> ""))
              clauses
        | None -> ());
        match
          GroundGoals.split
            ~stop_when_doomed:config.split_ground_alternative_stop_when_doomed
            ~smallest:(split_first_on ())
            ~stop_at_root:
              (split_first_on () && config.split_ground_smallest_stop_at_root)
            ?budget_after_cut ?literal_box
            ?prove:(Option.map prove ~f:(fun prove -> prove chc))
            ~ask
            ~budget clauses
        with
        | GroundGoals.Not_shape ->
            census "not-shape";
            `Nothing
        | Undecided { leaves; derived; tried } ->
            census
              (sprintf "undecided leaves=%d derived=%d tried=%d%s" leaves
                 derived tried
                 (if split_first_on () then
                    let atoms, unknown, cut = !GroundGoals.last_smallest_stats in
                    sprintf " last-explored=%d unknown-tries=%d cut=%b" atoms
                      unknown cut
                  else ""));
            `Nothing
        | Won { leaves; proved } ->
            census (sprintf "won leaves=%d proved=%d" leaves proved);
            `Won
        | Underivable { leaves; proven; asked } ->
            census
              (sprintf "underivable leaves=%d proven=%d asked=%d" leaves proven
                 asked);
            `Won
        | Derived { leaves; derived; root } ->
            last_split_height := GroundGoals.height root;
            census
              (sprintf
                 "derived leaves=%d derived=%d nodes=%d distinct=%d height=%d"
                 leaves derived (GroundGoals.size root)
                 (GroundGoals.shared_size root) !last_split_height);
            `Counter_play
              (GroundGoals.to_cex ~own_heads:config.split_ground_clause_heads
                 root))

  let stalls = ref 0

  (* The last ordinary check built by [solve_primal_dual], with what it was
     built from: the checked side ([true] the primal), both sides'
     strategies (rankings, then term sets; the checked side's first) and the
     checked side's problem, all compared by physical equality.  A check
     asked again for the same strategies (after a timeout) reuses it under
     [reuse_check_on_retry].  Reset at each [solve]. *)
  let last_check = ref None

  (* The key ([last_check]'s) of the last check whose bounded check was
     asked ([bounded_counterplay]), so that a retry of the same
     strategies does not ask it again.  Reset at each [solve]. *)
  let last_bounded_ask = ref None

  (* The last copy-blind check built by [solve_primal_dual] (under
     [copy_blind_on_timeout], [untransitive_win]'s re-check,
     [copy_blind_first] or [copy_blind_choices]), keyed as [last_check]:
     the checked side, both sides' strategies and the checked side's
     problem, compared by physical equality.  It holds the outcome of
     [copy_blind_chc] and, once built, the check made from it.  Under
     [reuse_check_on_retry] a copy-blind check asked again for the same
     strategies (each rung of the doubling re-checks a timed-out side
     copy-blind) reuses both instead of encoding again: the encoding and
     the build read only the strategies, the checked side's problem, the
     side's copy layout and predicate index (fixed for the whole [solve])
     and the configuration, so a rebuild differs only in fresh names and in
     which equivalent terms a solver-backed deduplication merged -- the
     argument of [reuse_check_on_retry].  Kept apart from [last_check] so
     that building one kind of check does not discard the other.  Reset at
     each [solve]. *)
  let last_copy_blind_check = ref None

  (* Under [copy_blind_recheck_once]: the key (as [last_check]'s, compared
     by physical equality) of the last check whose copy-blind re-check after
     a timeout gave neither a win nor a counter-play.  Written only by the
     re-check's own neither-arm, read only by the guard of the re-check step
     of the timeout path; a retry of that same check (the doubling passes the
     very maps and problem back) then skips the re-check.  Holding one key is
     enough: a check of other strategies has another key and is re-checked,
     and the doubling retries only the check that just timed out.  Reset at
     each [solve]. *)
  let copy_blind_recheck_spent = ref None

  (* Under [copy_blind_recheck_continued]: the check (keyed as
     [continuation], compared by physical equality) whose copy-blind
     re-check a forked copy is asking with no budget, and that copy's race.
     Invariant: [Some] only while this process has not finished that race,
     or while the race was inherited at a fork (its [owner] is another
     process); an inherited race is a sibling's and is forgotten, never
     finished, as [ask_aside]'s copy forgets the continued check's.  Reset
     at each [solve]. *)
  let cb_continuation = ref None

  (* Stop the copy of [cb_continuation], if this process started it; forget
     an inherited one.  Never returns when that copy has already claimed the
     run. *)
  let drop_cb_continuation () =
    match !cb_continuation with
    | None -> ()
    | Some (_, _, _, _, _, _, t) ->
        cb_continuation := None;
        if Pid.equal t.PCSatCommon.ParallelRace.owner (Core_unix.getpid ())
        then PCSatCommon.ParallelRace.finish t

  (* Under [continue_check_in_copy]: the ordinary check whose in-process ask
     ran out of its budget while a forked copy goes on asking it, with what
     it was built from (as in [last_check], compared by physical equality),
     the race of that copy and the time the copy started
     ([Common.PhaseTime.now]).  Invariant: [Some] only while that race has
     not been finished by the process; whoever sets it back to [None] has
     finished the race or is about to.  Reset at each [solve]. *)
  let continuation = ref None

  let continue_census msg =
    (* stamped with the monotonic clock and the process id, so that the lines
       of the process and of its copy can be put on one time line *)
    if reask_census then
      eprintf "mustrat-continue: %.3f pid=%d %s\n%!" (Common.PhaseTime.now ())
        (Pid.to_int (Core_unix.getpid ()))
        msg

  (* Stop the copy of [continuation], if any: kill and reap it.  When the copy
     has already claimed the run this never returns (the process exits with
     the copy's status), which is what a process that has lost the run must
     do before it would compute or print anything else. *)
  let drop_continuation () =
    match !continuation with
    | None -> ()
    | Some (_, _, _, _, _, _, t, _) ->
        continuation := None;
        continue_census "dropped";
        PCSatCommon.ParallelRace.finish t

  (* Under [strategy_free_race_solver]: per side ([true] the primal), the race
     of the copy that asks the side's strategy-free check of the raced solver.
     Invariant: a side has an entry only while its race has not been
     finished by this process; a race inherited at a fork (its [owner] is another process, the
     copy that now runs being a sibling of its copy) is not this process's and
     is forgotten, never finished, so that the sibling is left alone and the
     run's present process may start a race of its own.  Reset at each
     [solve]. *)
  let strategy_free_races : (bool, PCSatCommon.ParallelRace.t) Hashtbl.t =
    Hashtbl.Poly.create ()

  (* [strategy_free_race_running turn]: whether this process has a race of
     [turn]'s strategy-free check running; forgets an inherited one *)
  let strategy_free_race_running turn =
    match Hashtbl.find strategy_free_races turn with
    | None -> false
    | Some t ->
        if Pid.equal t.PCSatCommon.ParallelRace.owner (Core_unix.getpid ())
        then true
        else (
          Hashtbl.remove strategy_free_races turn;
          false)

  (* Stop every strategy-free race of this process: kill and reap its copy.
     As [drop_continuation], this never returns when a copy has already
     claimed the run. *)
  let drop_strategy_free_races () =
    let races = Hashtbl.to_alist strategy_free_races in
    Hashtbl.clear strategy_free_races;
    List.iter races ~f:(fun (_, t) ->
        if Pid.equal t.PCSatCommon.ParallelRace.owner (Core_unix.getpid ())
        then PCSatCommon.ParallelRace.finish t)

  (* [complement_solution sol]: [P |-> \xs. not (sol P)(xs)] for every
     predicate of [sol].  A solution of a problem's co-CHC form
     ([PCSP.Problem.cochc_to_chc] applied to it) complemented is a solution
     of the problem: the form replaces every predicate by its complement. *)
  let complement_solution sol =
    Map.Poly.map sol ~f:(fun t ->
        let params, body = Logic.Term.let_lam t in
        Logic.Term.mk_lambda params (Logic.BoolTerm.neg_of body))

  (* Under [resynthesise_wf_rankings]: per ranking key (by name), every chain
     pair an accepted refinement of it has asked for.  A key names the ranking
     of one fixpoint predicate on the side where that predicate is a least
     fixpoint, so primal and dual keys never share a name.  Reset at each
     [solve]. *)
  let wf_rank_pairs :
      (string, (LogicOld.Term.t list * LogicOld.Term.t list) list) Hashtbl.t =
    Hashtbl.create (module String)

  (* Under [skolem_term_window]: per Skolem key (by name), its terms, most
     recently added first.  Invariant: the key's term set in the strategy is
     the set of this list's elements, whenever the key has been refined
     since the last [solve]; a key not in the table still has the term set
     it was initialised with.  Reset at each [solve]. *)
  let skolem_term_order : (string, Logic.term list) Hashtbl.t =
    Hashtbl.create (module String)

  (* Under [joint_term_alternatives]: per Skolem key (by name), the history
     [JointTerms] reads -- its initial terms (the term set it held when a
     refinement first touched it, extended at each check by any term of its
     set that no refinement proposed) and, newest first, each refinement that
     touched it with the terms it proposed.  Refinements are numbered by
     [joint_refinement_id], one number per read-back.  A key absent from the
     tables has not been refined.  Reset at each [solve]. *)
  let joint_initial : (string, Logic.term list) Hashtbl.t =
    Hashtbl.create (module String)

  let joint_refinements : (string, (int * Logic.term list) list) Hashtbl.t =
    Hashtbl.create (module String)

  let joint_refinement_id = ref 0

  (* [relative_completeness]: the offer and the probes.

     Per side (index 0 the primal side, 1 the dual): how many turns it has
     had; a cursor over the vectors of terms offered to its Skolem keys (one
     term per key, layer by layer, [RelComplete.Vectors]); a cursor over the
     tuples of ranking-function relations of its ranking keys
     ([RelComplete.Rankings]) with every tuple produced so far, so that the
     probes can visit each tuple infinitely often (probe [q] takes the tuple
     at position [n], where [q = m (m + 1) / 2 + n] with [n <= m]); the
     probes that were not decided in their budget, to be asked again with
     twice the budget; and, with a cap, the pass over the capped layer's
     rankings made once every capped term has been offered, with how many of
     its probes are still undecided.  Reset at each [solve]. *)
  type rc_strat_fn =
    (Ident.tvar, Logic.sort_env_list * Logic.term Set.Poly.t) Map.Poly.t

  type rc_side = {
    mutable rc_turns : int;
    mutable offer_cursor : (Ident.tvar list * RelComplete.Vectors.t) option;
    mutable offers_done : bool;
    mutable rank_cursor :
      (Ident.tvar list * RelComplete.Rankings.key list * RelComplete.Rankings.cursor)
      option;
    rank_items : (Ident.tvar * Logic.term) list Queue.t;
    mutable rank_cursor_done : bool;
    mutable probe_count : int;
    retries : (rc_strat_fn * (Ident.tvar * Logic.term) list * int * bool) Queue.t;
    mutable final_cursor : RelComplete.Rankings.cursor option;
    mutable final_done : bool;
    mutable final_undecided : int;
  }

  let rc_fresh_side () =
    {
      rc_turns = 0;
      offer_cursor = None;
      offers_done = false;
      rank_cursor = None;
      rank_items = Queue.create ();
      rank_cursor_done = false;
      probe_count = 0;
      retries = Queue.create ();
      final_cursor = None;
      final_done = false;
      final_undecided = 0;
    }

  let rc_sides = [| rc_fresh_side (); rc_fresh_side () |]

  let rc_reset () =
    rc_sides.(0) <- rc_fresh_side ();
    rc_sides.(1) <- rc_fresh_side ()

  let rc_on () =
    match config.relative_completeness with Rc_off -> false | _ -> true

  let rc_cap () =
    match config.relative_completeness with Capped l -> Some l | _ -> None

  (* Under [relative_completeness], a run is never ended by stalls. *)
  let gives_up_on_stalls stalls = (not (rc_on ())) && StallRule.gives_up stalls

  (* Under [relative_completeness] the refinement's last form is bounded as
     under [bound_last_refinement]: the guarantee needs every turn to end,
     and an unbounded refinement can hold a turn for the whole run (a
     refinement whose selection did not apply sent the problem to the
     constraint solver, which had not returned 200 s later, so no offer
     after it was made).  An expired budget passes the turn at the doubled
     budget, as that field's rule does. *)
  let bound_last_refinement () = config.bound_last_refinement || rc_on ()

  (* The slot of a Skolem key with parameters [args] (its result last): terms
     of the result's sort over the parameters of that sort; [None] for a key
     whose result is neither an integer nor a real. *)
  let rc_slot_of_key (args : Logic.sort_env_list) =
    match List.rev args with
    | (_, sret) :: rev ->
        let params = List.rev rev in
        let of_sort s =
          Array.of_list
            (List.filter_map params ~f:(fun (x, s') ->
                 if Stdlib.(s' = s) then Some x else None))
        in
        if Stdlib.(sret = Logic.IntTerm.SInt) then
          Some (RelComplete.int_slot (of_sort Logic.IntTerm.SInt))
        else if Stdlib.(sret = Logic.RealTerm.SReal) then
          Some (RelComplete.real_slot (of_sort Logic.RealTerm.SReal))
        else None
    | [] -> None

  (* [rc_offer side strat_fn]: [strat_fn] with the next offered vector added,
     one term per key with a slot, as the key's equation [y = t]; [strat_fn]
     itself when the offers are over (with a cap) or no key has a slot.
     Under [joint_term_alternatives] the vector is recorded as one
     refinement of every key it touches, so that it is one row of their
     joint offer, as a refinement's proposal is.  Post: every key's term set
     only grows. *)
  let rc_offer side (strat_fn : rc_strat_fn) =
    let st = rc_sides.(side) in
    let keys, cursor =
      match st.offer_cursor with
      | Some kc -> kc
      | None ->
          let keyed =
            Map.Poly.to_alist strat_fn
            |> List.filter_map ~f:(fun (k, (args, _)) ->
                   Option.map (rc_slot_of_key args) ~f:(fun s -> (k, s)))
            |> List.sort ~compare:(fun (a, _) (b, _) -> Ident.tvar_compare a b)
          in
          let kc =
            ( List.map keyed ~f:fst,
              RelComplete.Vectors.create (Array.of_list (List.map keyed ~f:snd)) )
          in
          st.offer_cursor <- Some kc;
          kc
    in
    if st.offers_done || List.is_empty keys then (
      st.offers_done <- true;
      strat_fn)
    else
      match RelComplete.Vectors.next cursor with
      | Some v
        when match rc_cap () with
             | Some l -> cursor.RelComplete.Vectors.layer <= l
             | None -> true ->
          incr joint_refinement_id;
          let joint_id = !joint_refinement_id in
          let strat_fn, shown =
            List.foldi keys ~init:(strat_fn, []) ~f:(fun i (strat_fn, shown) k ->
                let args, terms = Map.Poly.find_exn strat_fn k in
                let y, sret = List.last_exn args in
                let fresh =
                  Logic.BoolTerm.eq_of sret (Logic.Term.mk_var y)
                    (Logic.ExtTerm.of_old_term v.(i))
                in
                if config.joint_term_alternatives then (
                  let name = Ident.name_of_tvar k in
                  if not (Hashtbl.mem joint_initial name) then
                    Hashtbl.set joint_initial ~key:name ~data:(Set.to_list terms);
                  Hashtbl.update joint_refinements name ~f:(fun rs ->
                      (joint_id, [ fresh ]) :: Option.value ~default:[] rs));
                ( Map.Poly.set strat_fn ~key:k ~data:(args, Set.add terms fresh),
                  (Ident.name_of_tvar k ^ " := " ^ LogicOld.Term.str_of v.(i))
                  :: shown ))
          in
          Debug.print
          @@ lazy
               (sprintf "### Offered (layer %d): %s"
                  cursor.RelComplete.Vectors.layer
                  (String.concat ~sep:", " (List.rev shown)));
          (* one stderr line per offer, for a census of how the term sets
             grow; nothing without the variable *)
          if Option.is_some (Sys.getenv "COAR_MUSTRAT_RC_CENSUS") then
            eprintf "mustrat-rc: offer side=%d layer=%d keys=%d terms=%d t=%.2f\n%!"
              side cursor.RelComplete.Vectors.layer (List.length keys)
              (Map.Poly.fold strat_fn ~init:0 ~f:(fun ~key:_ ~data:(_, ts) n ->
                   n + Set.length ts))
              (Common.PhaseTime.now ());
          strat_fn
      | _ ->
          st.offers_done <- true;
          Debug.print @@ lazy "### Every offer of the capped layers made";
          strat_fn

  (* The ranking tuples of a side as maps from its ranking keys to lambdas:
     [rc_rank_keys wf] with a cursor built on first use. *)
  let rc_rank_cursor_for side (strat_wf : (Ident.tvar, Logic.term) Map.Poly.t) =
    let st = rc_sides.(side) in
    match st.rank_cursor with
    | Some kc -> kc
    | None ->
        let keys =
          Map.Poly.keys strat_wf |> List.sort ~compare:Ident.tvar_compare
        in
        let rk =
          List.map keys ~f:(fun k ->
              let args, _ = Logic.Term.let_lam (Map.Poly.find_exn strat_wf k) in
              let n = List.length args / 2 in
              let old = List.map args ~f:(fun (x, s) -> (x, Logic.ExtTerm.to_old_sort s)) in
              RelComplete.Rankings.key_of ~earlier:(List.take old n)
                ~later:(List.drop old n))
        in
        let kc = (keys, rk, RelComplete.Rankings.cursor rk) in
        st.rank_cursor <- Some kc;
        kc

  let rc_lambdas strat_wf keys formulas =
    List.map2_exn keys formulas ~f:(fun k phi ->
        let args, _ = Logic.Term.let_lam (Map.Poly.find_exn strat_wf k) in
        (k, Logic.Term.mk_lambda args (Logic.ExtTerm.of_old_formula phi)))

  (* the next ranking tuple of the cursor, within the cap if any *)
  let rc_next_rank cursor =
    match RelComplete.Rankings.next cursor with
    | Some fs
      when match rc_cap () with
           | Some l -> cursor.RelComplete.Rankings.layer <= l
           | None -> true ->
        Some fs
    | _ -> None

  (* The ranking tuple the next probe of [side] tries, before the capped
     pass: the dovetailed visit of every tuple produced so far, each
     infinitely often; [None] when the side has none. *)
  let rc_dovetail side strat_wf =
    let st = rc_sides.(side) in
    let keys, _, cursor = rc_rank_cursor_for side strat_wf in
    let q = st.probe_count in
    st.probe_count <- q + 1;
    let m = ref 0 in
    while ((!m + 1) * (!m + 2) / 2) <= q do incr m done;
    let n = q - (!m * (!m + 1) / 2) in
    while (not st.rank_cursor_done) && Queue.length st.rank_items <= n do
      match rc_next_rank cursor with
      | Some fs -> Queue.enqueue st.rank_items (rc_lambdas strat_wf keys fs)
      | None -> st.rank_cursor_done <- true
    done;
    let len = Queue.length st.rank_items in
    if len = 0 then None else Some (Queue.get st.rank_items (n mod len))

  (* [rc_run_probes ~side ~strat_wf ~strat_fn ~ask]: this turn's probes of
     [side]: the oldest undecided probe asked again at its doubled budget,
     then one new probe -- the next tuple of the capped pass once every
     capped offer has been made, otherwise the dovetailed tuple (none for a
     side without ranking keys, whose ordinary check is its probe).  [ask wf
     strat_fn budget] asks the check of [strat_fn] with the rankings [wf].
     [true] when a probe was won.  A won probe's rankings are
     ranking-function relations, well-founded and transitive whatever their
     components, so the win is an answer as a win with rankings proved
     transitive is; a lost or undecided probe is no fact about anything but
     its own candidate, and nothing is refined from it. *)
  let rc_run_probes ~side ~strat_wf ~strat_fn ~ask =
    let st = rc_sides.(side) in
    let wf_of items = Map.Poly.of_alist_exn items in
    let initial = config.chc_initial_timeout in
    let retried =
      match Queue.dequeue st.retries with
      | None -> false
      | Some (fn, items, budget, final) -> (
          match ask (wf_of items) fn budget with
          | `Won -> true
          | `Lost ->
              if final then st.final_undecided <- st.final_undecided - 1;
              false
          | `Undecided ->
              Queue.enqueue st.retries (fn, items, 2 * budget, final);
              false)
    in
    if retried then true
    else
      let candidate =
        match rc_cap () with
        | Some _ when st.offers_done ->
            if st.final_done then None
            else
              let keys, rk, _ = rc_rank_cursor_for side strat_wf in
              let cursor =
                match st.final_cursor with
                | Some c -> c
                | None ->
                    let c = RelComplete.Rankings.cursor rk in
                    st.final_cursor <- Some c;
                    c
              in
              (match rc_next_rank cursor with
              | Some fs -> Some (rc_lambdas strat_wf keys fs, true)
              | None ->
                  st.final_done <- true;
                  None)
        | _ ->
            if Map.Poly.is_empty strat_wf then None
            else
              Option.map (rc_dovetail side strat_wf) ~f:(fun items ->
                  (items, false))
      in
      match candidate with
      | None -> false
      | Some (items, final) -> (
          match ask (wf_of items) strat_fn initial with
          | `Won -> true
          | `Lost -> false
          | `Undecided ->
              if final then st.final_undecided <- st.final_undecided + 1;
              Queue.enqueue st.retries (strat_fn, items, 2 * initial, final);
              false)

  (* With a cap: both sides have been offered every capped term and every
     capped ranking tuple has been probed and lost after that. *)
  let rc_exhausted () =
    Option.is_some (rc_cap ())
    && Array.for_all rc_sides ~f:(fun st ->
           st.offers_done && st.final_done && st.final_undecided = 0)

  (* The units of [TermAlternatives.of_clause]'s [joint] argument for the
     strategy [strat_fn], over the keys [lone] (each a key of [strat_fn]). *)
  let joint_units strat_fn lone =
    let term_set k = snd (Map.Poly.find_exn strat_fn k) in
    List.iter lone ~f:(fun k ->
        let name = Ident.name_of_tvar k in
        match Hashtbl.find joint_initial name with
        | None -> ()
        | Some initial ->
            Hashtbl.set joint_initial ~key:name
              ~data:
                (JointTerms.initial_closed ~term_set:(term_set k) ~initial
                   ~refinements:
                     (Option.value ~default:[]
                        (Hashtbl.find joint_refinements name))));
    JointTerms.units ~min_keys:config.joint_term_alternatives_min_keys
      ~distinct:config.joint_rows_distinct_terms ~term_set
      ~initial:(fun k -> Hashtbl.find joint_initial (Ident.name_of_tvar k))
      ~refinements:(fun k ->
        Option.value ~default:[]
          (Hashtbl.find joint_refinements (Ident.name_of_tvar k)))
      lone

  (* Per ranking key (by name), the ranking last produced by re-synthesis as
     one [WF]-kind template instance, which is well-founded whatever the
     template's parameters.  Compared with the strategy's current term by
     physical equality, so a ranking changed in any other way (a disjoined
     piece) is never taken for one of these.  Reset at each [solve]. *)
  let wf_by_construction : (string, Logic.term) Hashtbl.t =
    Hashtbl.create (module String)

  (* Under [generalise_chain_pairs]: per ranking key (by name), the regions
     (see [chain_regions_of]) of the refinements whose generalised problem
     was the one solved, each as its variables (the two states, in the key's
     parameter order) and a formula over them.  Every later generalised
     re-synthesis of the key asks its copy to contain all of them again, as
     [wf_rank_pairs] does for the ground pairs.  Each region keeps the
     certificate [chain_regions_of] gave it, by position over the copy's
     state, so it needs no renaming.  Reset at each [solve]. *)
  let wf_rank_regions :
      ( string,
        (LogicOld.sort_env_list
        * LogicOld.Formula.t
        * (int * (Z.t list * Z.t) list) option)
        list )
      Hashtbl.t =
    Hashtbl.create (module String)

  (* Under [chain_pair_regions_by_mbp]: per ranking key (by name), the one
     variable list every region of the key is renamed onto, so that two
     regions are the same constraint exactly when their formulas are
     structurally equal.  Created at the key's first region and reset at each
     [solve]. *)
  let wf_region_vars : (string, LogicOld.sort_env_list) Hashtbl.t =
    Hashtbl.create (module String)

  (* [canonical_regions key regions]: [regions] (each its variables, a
     quantifier-free formula over them and its certificate, as
     [chain_regions_of] returns them; the certificate is carried unchanged),
     renamed onto [key]'s canonical variables, simplified, with repetitions
     removed (first occurrence kept, order otherwise preserved).
     Pre: every region's variables have the key's arity and sorts, in the
     key's parameter order.  Post: each result is a region of the input up to
     a renaming of its variables, which are the canonical ones; no two
     results are structurally equal. *)
  let canonical_regions key regions =
    let open LogicOld in
    match regions with
    | [] -> []
    | (vars0, _, _) :: _ ->
        let cvars =
          Hashtbl.find_or_add wf_region_vars key ~default:(fun () ->
              List.map vars0 ~f:(fun (_, s) ->
                  (Ident.mk_fresh_tvar ~prefix:(Some "GR_") (), s)))
        in
        List.filter_map regions ~f:(fun (vars, region, cert) ->
            if List.length vars <> List.length cvars then None
            else
              Some
                ( cvars,
                  Evaluator.simplify
                  @@ Formula.rename
                       (Map.Poly.of_alist_exn
                       @@ List.map2_exn vars cvars ~f:(fun (v, _) (c, _) ->
                           (v, c)))
                       region,
                  cert ))
        |> List.fold ~init:([], Set.Poly.empty)
             ~f:(fun (acc, seen) (cv, r, cert) ->
               let k = Formula.str_of r in
               if Set.mem seen k then (acc, seen)
               else ((cv, r, cert) :: acc, Set.add seen k))
        |> fst |> List.rev

  let region_holds_at = RankCandidate.region_holds_at

  (* The largest absolute integer literal of the game [solve] was last given
     (after its binder normalisation), at least 1; set by [solve] and read
     only by the LP candidate's literal rung
     ([chain_pair_lex_candidate_const_ladder]). *)
  let game_largest_literal = ref Z.one

  (* The LP and certificate ranking candidates, with this check's
     configuration, trace and repair log; see [RankCandidate]. *)
  module RankCandidates = RankCandidate.Make (struct
    let config = config
    let print = Debug.print
    let repair_log = repair_log
    let literal_bound () = !game_largest_literal
  end)

  let multiphase_candidate = RankCandidates.multiphase_candidate
  let lex_candidate = RankCandidates.lex_candidate

  (* [ranking_contains ranking (a, b)]: whether the ranking [ranking] (a
     lambda over the two states' positions) holds at the ground pair [(a, b)],
     decided by substituting the pair and simplifying.  True only when the
     simplified formula is [true]; a ranking of another arity, a formula the
     simplifier leaves undecided, or a failed conversion answers false, the
     answer that lets the caller change the ranking. *)
  let ranking_contains ranking (a, b) =
    let args, body = Logic.Term.let_lam ranking in
    let pair = a @ b in
    if List.length args <> List.length pair then false
    else
      try
        let sub =
          Map.Poly.of_alist_exn
            (List.map2_exn args pair ~f:(fun (x, _) t ->
                 (x, Logic.ExtTerm.of_old_term t)))
        in
        LogicOld.Formula.is_true @@ Evaluator.simplify
        @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
             (Map.Poly.of_alist_exn args)
             (Logic.ExtTerm.subst sub body)
      with exn when not (Common.Timer.is_async exn) -> false

  (* Whether the directed graph of the ground pairs [pairs] has a cycle.  A
     relation containing a cycle is not well-founded, and a finite acyclic set
     of pairs is contained in its transitive closure, a finite strict order,
     which is well-founded; so this decides whether SOME well-founded relation
     contains the pairs (whether the ranking template can express one is a
     separate question).  States are compared as [chain_pairs_of] compares
     them. *)
  let pairs_cyclic pairs =
    let succs =
      List.fold pairs ~init:Map.Poly.empty ~f:(fun m (a, b) ->
          Map.Poly.update m a ~f:(function None -> [ b ] | Some l -> b :: l))
    in
    (* 1 on the current path, 2 finished *)
    let colour = ref Map.Poly.empty in
    let rec visit s =
      match Map.Poly.find !colour s with
      | Some 1 -> true
      | Some _ -> false
      | None ->
          colour := Map.Poly.set !colour ~key:s ~data:1;
          let found =
            List.exists
              (Option.value ~default:[] (Map.Poly.find succs s))
              ~f:visit
          in
          colour := Map.Poly.set !colour ~key:s ~data:2;
          found
    in
    List.exists pairs ~f:(fun (a, _) -> visit a)

  (* Compared on the simplified first-order form, as [print_strat] shows it: a
     refinement that joins a ranking already present grows the term
     syntactically ([or] of the old and the new) without changing it, and a
     comparison of the raw terms would count that as progress.  A ranking is
     a lambda over its parameters; a Skolem key's term is a body over the
     key's parameters, which are therefore passed for it (read without them,
     every such term failed the conversion as an unbound variable and fell
     back to the raw comparison). *)
  let strat_str_body params body t =
    try
      LogicOld.Formula.str_of @@ Evaluator.simplify
      @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
           (Map.Poly.of_alist_exn params) body
    with exn when not (Common.Timer.is_async exn) -> Logic.ExtTerm.str_of t

  let same_strategy (wf1, fn1, _) (wf2, fn2, _) =
    let str_body = strat_str_body in
    let str t =
      let args, body = Logic.Term.let_lam t in
      str_body args body t
    in
    Map.Poly.equal (fun t1 t2 -> String.(str t1 = str t2)) wf1 wf2
    && Map.Poly.equal
         (fun (ps1, ts1) (ps2, ts2) ->
           Set.equal
             (Set.Poly.map ts1 ~f:(fun t -> str_body ps1 t t))
             (Set.Poly.map ts2 ~f:(fun t -> str_body ps2 t t)))
         fn1 fn2

  (* Whether the joint offer is the one the checks use: [joint_units] is read
     only by the placed-tree encoding with named alternatives. *)
  let joint_offer_in_use () =
    config.joint_term_alternatives && config.miniscope_term_alternatives
    && config.name_term_alternatives

  (* A snapshot of the joint history, taken before a refinement so that
     [joint_offer_grew] can ask what the check before it offered. *)
  let joint_snapshot () =
    (!joint_refinement_id, Hashtbl.copy joint_initial,
     Hashtbl.copy joint_refinements)

  (* [joint_offer_grew (since, initial0, refinements0) strat_fn]: whether a
     refinement recorded after the snapshot proposed a tuple the joint offer
     of the snapshot did not hold, [strat_fn] being the Skolem strategy the
     snapshot was taken with.  Under the joint offer a class of keys refined
     together is offered its rows, not the product of its term sets, so a
     refinement whose terms each are already in their key's term set can
     still offer a new combination: [same_strategy], which compares term sets
     only, calls such a refinement unchanged although the next check of the
     opponent offers one more alternative.  (Measured: the opponent's check
     offered the rows (0,0,0,0) and (-1,1,0,-1) of a four-key class, the
     refinement proposed (0,0,0,-1), and the run answered [unknown] on that
     stall.)

     A record is the tuple block one read-back proposed: per key it touched,
     its distinct terms.  It is new when, over the keys it touched and with
     the snapshot's classes ([JointTerms.units] over those keys, as for a
     clause holding exactly them), some vector of the record's block is not
     offered: a key in no class is offered its term set alone, a class its
     rows, and keys of different classes are combined freely.  Terms are
     compared in the simplified form [same_strategy] uses.  A class's block
     larger than its distinct rows holds a vector outside them (rows are
     distinct vectors), so a block is enumerated only when it is no larger
     than rows already built.  [false] when the joint offer is not in use:
     the product is offered, and a recombination of held terms is offered
     already; and [false] under [unchanged_reads_joint_offer = false], which
     restores the term-set-only test. *)
  let joint_offer_grew (since, initial0, refinements0) strat_fn =
    config.unchanged_reads_joint_offer && joint_offer_in_use ()
    &&
    let by_name =
      Map.Poly.fold strat_fn ~init:String.Map.empty
        ~f:(fun ~key ~data m ->
          Map.set m ~key:(Ident.name_of_tvar key) ~data:(key, data))
    in
    let str (params, _) t = strat_str_body params t t in
    let dedup = List.dedup_and_sort ~compare:String.compare in
    let records =
      Hashtbl.fold joint_refinements ~init:Int.Map.empty
        ~f:(fun ~key:name ~data:rs acc ->
          match Map.find by_name name with
          | None -> acc
          | Some (k, entry) ->
              List.fold rs ~init:acc ~f:(fun acc (r, ts) ->
                  if r <= since then acc
                  else
                    Map.add_multi acc ~key:r
                      ~data:(k, dedup (List.map ts ~f:(str entry)))))
    in
    let entry_of k = snd (Map.find_exn by_name (Ident.name_of_tvar k)) in
    Map.exists records ~f:(fun block ->
        let keys = List.map block ~f:fst in
        let proposed k =
          snd
            (List.find_exn block ~f:(fun (k', _) -> Ident.tvar_equal k k'))
        in
        let classes =
          JointTerms.units ~min_keys:config.joint_term_alternatives_min_keys
            ~distinct:config.joint_rows_distinct_terms
            ~term_set:(fun k -> snd (entry_of k))
            ~initial:(fun k -> Hashtbl.find initial0 (Ident.name_of_tvar k))
            ~refinements:(fun k ->
              Option.value ~default:[]
                (Hashtbl.find refinements0 (Ident.name_of_tvar k)))
            keys
        in
        let in_class k =
          List.exists classes ~f:(fun (members, _) ->
              List.mem members k ~equal:Ident.tvar_equal)
        in
        List.exists keys ~f:(fun k ->
            (not (in_class k))
            &&
            let entry = entry_of k in
            let held = Set.Poly.map (snd entry) ~f:(str entry) in
            List.exists (proposed k) ~f:(fun s -> not (Set.mem held s)))
        || List.exists classes ~f:(fun (members, rows) ->
               let entries = List.map members ~f:entry_of in
               let rows =
                 List.dedup_and_sort
                   ~compare:(List.compare String.compare)
                   (List.map rows ~f:(fun row ->
                        List.map2_exn entries row ~f:str))
               in
               let lists = List.map members ~f:proposed in
               let size =
                 List.fold lists ~init:1 ~f:(fun acc l ->
                     if acc > List.length rows then acc
                     else acc * List.length l)
               in
               size > List.length rows
               || List.exists (JointTerms.product lists) ~f:(fun v ->
                      not (List.mem rows v ~equal:(List.equal String.equal)))))

  let solspace =
    ref
      (Map.Poly.of_alist_exn
         [
           (SolSpace.ND, Some 1);
           (SolSpace.NC, Some 1);
           (SolSpace.NP, Some 1);
           (SolSpace.NDC, Some 1);
           (SolSpace.NL, Some 1);
         ])

  let refine_solspace wf fn =
    let f = function
      | None -> None
      | Some None -> Some 1
      | Some (Some n) -> Some (n + 1)
    in
    if fn then
      solspace :=
        Map.Poly.update ~f
          (Map.Poly.update ~f !solspace SolSpace.ND)
          SolSpace.NC;
    if wf then
      solspace :=
        Map.Poly.update ~f
          (Map.Poly.update ~f
             (Map.Poly.update ~f !solspace SolSpace.NP)
             SolSpace.NDC)
          SolSpace.NL

  let use_solspace = false

  let print_strat key args phi' =
    Debug.print
    @@ lazy
         (sprintf "%s(%s) := %s" (Ident.name_of_tvar key)
            (String.concat_map_list ~sep:"," args
               ~f:(fst >> Ident.name_of_tvar))
            (LogicOld.Formula.str_of @@ Evaluator.simplify
            @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                 (Map.Poly.of_alist_exn args)
                 phi'))

  let z3_solve =
    let module Z3interface =
      Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
    fun senv phi ->
      Common.PhaseTime.with_phase "fresh-ctx-check" (fun () ->
          Z3interface.check_sat [ phi ] senv (Z3.mk_context []))

  (* [Some sol] when the refinement problem is a pure existential over its
     Skolem unknowns and [SkolemTerms.solve] solves it; [None] sends the
     caller to the constraint solver.  Any exception but an asynchronous one
     (a timeout must reach the timer) is a fallback too: the selection is an
     optimisation and must never be the reason a refinement fails. *)
  (* Under [select_initial_atom_rows]: the further rows of the keys with no
     argument that the last call of [select_skolem_solution] found, each a map
     from such a key's copy to a constant function ([SkolemTerms.
     InitialAtomRows]).  Set by every call of [select_skolem_solution] (empty
     when it found none or declined), read by the refinement's read-back. *)
  let selected_extra_rows : (Ident.tvar, Logic.term) Map.Poly.t list ref =
    ref []

  (* the most rows one refinement adds under [select_initial_atom_rows] *)
  let initial_atom_rows_max = 8

  (* [cav24_labels p]: a solution of the losing system [p] of
     [refine_guards = Cav24_sound], by the engine [refine_labels] names, or
     [None] (no solution, an error, or an exception other than a timeout).
     Forward propagation computes the least solution and does not read the
     goal; [Cav24Guards.run] then finds no winning value at the root when
     the goal fails, so its answer is never trusted alone. *)
  let cav24_labels pcsp =
    try
      match config.refine_labels with
      | Labels_forward | Labels_regions -> (
          match PCSP.ForwardPropagate.solve pcsp with
          | Ok (PCSP.Problem.Sat sol) -> Some sol
          | _ -> None)
      | Labels_spacer -> (
          match ExtFile.unwrap config.refine_labels_spacer_solver with
          | Error _ -> None
          | Ok cfg -> (
              let module S = PCSPSolver.Solver.Make (struct
                let config = cfg
              end) in
              match S.solve pcsp with
              | Ok (PCSP.Problem.Sat sol, _) -> Some sol
              | _ -> None))
    with exn when not (Common.Timer.is_async exn) -> None

  let select_skolem_solution ?origin_of ?snap ?pinned ?eq_result ?joint pfwcsp =
    selected_extra_rows := [];
    (* [mentioned_only] of [Terms_select]: a presolved copy, declared and
       mentioned by no formula, does not keep the problem from selection *)
    let pfwcsp, restricted =
      if
        match config.refine_terms with
        | Terms_select { mentioned_only; _ } -> mentioned_only
        | Terms_pcsat -> false
      then (
        let pfwcsp', removed = SkolemTerms.mentioned_only pfwcsp in
        if removed then
          repair_log
            (sprintf "selection asked on %d of %d unknowns"
               (Map.Poly.length (PCSP.Problem.senv_of pfwcsp'))
               (Map.Poly.length (PCSP.Problem.senv_of pfwcsp)));
        (pfwcsp', removed))
      else (pfwcsp, false)
    in
    let note outcome =
      if restricted then repair_log ("selection on the restricted problem: " ^ outcome)
    in
    Array.fill SkolemTerms.InitialAtomRows.last_counts ~pos:0 ~len:7 0;
    try
      let policy = ref [] in
      let rows_out = ref [] in
      let labels =
        match (config.refine_guards, origin_of) with
        | Cav24_sound, Some _ -> Some cav24_labels
        | _ -> None
      in
      let sol, inverted, guarded =
        SkolemTerms.solve ?origin_of ?labels
          ~label_regions:
            (match config.refine_labels with
            | Labels_regions -> true
            | Labels_forward | Labels_spacer -> false)
          ?snap ?pinned ?eq_result ?joint
          ~prefer_bound:config.select_prefer_bound
          ~mixed_sorts:config.select_skolem_mixed_sorts
          ~atom_rows:
            (if config.select_initial_atom_rows then initial_atom_rows_max
             else 0)
          ~rows_out
          ~report:(fun line -> policy := line :: !policy)
          pfwcsp
      in
      selected_extra_rows := !rows_out;
      (* one stderr line per note of the guard step (what each key's copies
         became), for a census of where a guard alternative acts; printed at
         once since a run stopped at its budget runs no exit handler *)
      if Option.is_some (Sys.getenv "COAR_MUSTRAT_GUARD_CENSUS") then
        List.iter guarded ~f:(fun (k, what) ->
            eprintf "mustrat-guards: %s: %s\n%!" (Ident.name_of_tvar k) what);
      if not (List.is_empty !rows_out) then
        Debug.print
        @@ lazy
             (sprintf "## %d further initial row(s) of the keys with no argument:\n%s"
                (List.length !rows_out)
                (String.concat_map_list ~sep:"\n" !rows_out ~f:(fun row ->
                     String.concat_map_list ~sep:", " (Map.Poly.to_alist row)
                       ~f:(fun (k, t) ->
                         Ident.name_of_tvar k ^ " := " ^ Logic.ExtTerm.str_of t))));
      if Option.is_some (Sys.getenv "COAR_MUSTRAT_ATOM_ROWS_CENSUS") then
        eprintf
          "mustrat-atom-rows: rows=%d nullary=%d atoms=%d targets=%d asked=%d \
           sat=%d new=%d valid=%d\n%!"
          (List.length !rows_out)
          SkolemTerms.InitialAtomRows.last_counts.(0)
          SkolemTerms.InitialAtomRows.last_counts.(1)
          SkolemTerms.InitialAtomRows.last_counts.(2)
          SkolemTerms.InitialAtomRows.last_counts.(3)
          SkolemTerms.InitialAtomRows.last_counts.(4)
          SkolemTerms.InitialAtomRows.last_counts.(5)
          SkolemTerms.InitialAtomRows.last_counts.(6);
      Debug.print
      @@ lazy
           (sprintf "## Skolem terms by model-guided selection%s:\n%s%s%s"
              (if List.is_empty !policy then ""
               else " (" ^ String.concat ~sep:"; " (List.rev !policy) ^ ")")
              (String.concat_map_list ~sep:"\n" (Map.Poly.to_alist sol)
                 ~f:(fun (k, t) ->
                   Ident.name_of_tvar k ^ " := " ^ Logic.ExtTerm.str_of t))
              (String.concat_map_list inverted ~f:(fun (k, what) ->
                   sprintf "\n## argument of %s %s" (Ident.name_of_tvar k)
                     what))
              (String.concat_map_list guarded ~f:(fun (k, what) ->
                   sprintf "\n## guards for the copies of %s: %s"
                     (Ident.name_of_tvar k) what)));
      note "solved";
      Some sol
    with
    | SkolemTerms.Shape_mismatch reason ->
        note ("refused (" ^ reason ^ ")");
        Debug.print
        @@ lazy
             (sprintf "## Skolem term selection does not apply (%s); asking PCSat"
                reason);
        None
    | exn when not (Common.Timer.is_async exn) ->
        note "failed";
        Debug.print
        @@ lazy
             (sprintf "## Skolem term selection failed (%s); asking PCSat"
                (Exn.to_string exn));
        None

  (* [Some (skolem_part, ranking_part)] when [pfwcsp] mixes Skolem keys
     ([FN]) with ranking copies ([WF]/[DWF]) and its formulas split into those
     mentioning a ranking copy and the rest with no unknown shared between the
     two groups; [None] otherwise.  Each part keeps the whole problem's
     parameters with its unknowns restricted to the ones it mentions.  Sharing
     no unknown, the two parts are independent: a solution of each is a
     solution of the whole, and a solution of the whole restricts to one of
     each.  On the refinement problems built here the ranking copies are
     constrained by ground chain-pair facts alone, so the split is the
     separation of the ranking fit from the Skolem part.  Measured on three
     games: the split replaced 13 to 19 template terms per refinement by one
     to four selected terms, and the check that followed timed out as before,
     so the term count was not what made that check slow. *)
  let split_mixed_refinement pfwcsp =
    let params = PCSP.Problem.params_of pfwcsp in
    let senv = params.PCSP.Params.senv in
    let kind x = PCSP.Problem.kind_of pfwcsp x in
    let is_rank x = Kind.is_wf (kind x) || Kind.is_dwf (kind x) in
    let unknowns_of (_, t) =
      Set.filter (Logic.Term.fvs_of t) ~f:(Map.Poly.mem senv)
    in
    let rank_fs, rest_fs =
      Set.partition_tf (PCSP.Problem.formulas_of pfwcsp) ~f:(fun f ->
          Set.exists (unknowns_of f) ~f:is_rank)
    in
    let unknowns fs =
      Set.Poly.union_list (List.map (Set.to_list fs) ~f:unknowns_of)
    in
    let rank_us = unknowns rank_fs and rest_us = unknowns rest_fs in
    if
      Set.is_empty rank_fs || Set.is_empty rest_fs
      || (not (Set.is_empty (Set.inter rank_us rest_us)))
      || not (Set.exists rest_us ~f:(fun x -> Kind.is_fn (kind x)))
    then None
    else
      let part fs us =
        PCSP.Problem.of_formulas
          ~params:
            {
              params with
              PCSP.Params.senv = Map.Poly.filter_keys senv ~f:(Set.mem us);
              (* already among [formulas_of]'s formulas *)
              stable_clauses = Set.Poly.empty;
            }
          fs
      in
      Some (part rest_fs rest_us, part rank_fs rank_us)

  (* A diagnostic, never a decision: re-check the kind constraints of an
     accepted refinement's solution [sol] of [pfwcsp] -- each ranking copy is
     declared [DWF], and it passes when [sol] lies inside the decrease relation
     of the ranking certificate [certs] records for it, so that every piece is
     well-founded -- and print the tally.  Nothing it finds changes the
     refinement; a failure is printed prominently so that it is seen.  A
     ranking with no recorded certificate (an answer that did not come from
     the ranking template) is counted unchecked. *)
  let check_refinement_kinds pfwcsp sol ~certs =
    let module W = PCSat.WitnessChecker in
    match
      try
        Ok
          (W.check_kind_constraints ~id:(PCSP.Problem.id_of pfwcsp) ~certs
             pfwcsp sol W.empty)
      with exn_ when not (Common.Timer.is_async exn_) -> Error exn_
    with
    | Ok r ->
        Debug.print @@ lazy (W.str_of_report "refinement-kind" r);
        if not (List.is_empty r.W.failed) then
          Debug.print
          @@ lazy
               (sprintf
                  "!!!!!!!! REFINEMENT KIND CHECK FAILED (%d): an accepted \
                   ranking is not certified well-founded by its recorded \
                   certificate; the refinement is used unchanged !!!!!!!!"
                  (List.length r.W.failed))
    | Error exn_ ->
        Debug.print
        @@ lazy
             (sprintf
                "(refinement-kind-check (passed 0) (unchecked 1) (failed 0)\n\
                \ (unchecked \"the checker raised: %s\" 1))"
                (String.substr_replace_all ~pattern:"\"" ~with_:"'"
                   (Exn.to_string exn_)))

  (* What the plays demand of one ranking key's fresh copy, and what the
     ranking seam built for it ([rank_demand], [rank_candidate] inside
     [refine_strat]); polymorphic in the pair, fact and region types so that the
     records state the shape without repeating those types. *)
  type ('pair, 'fact, 'region) rank_demand = {
    rd_key : Ident.tvar;  (** the ranking key *)
    rd_args : Logic.sort_env_list;  (** its parameters *)
    rd_copy : Ident.tvar;  (** the fresh copy the refinement solves *)
    rd_pairs : 'pair list;  (** the chain pairs asked of the copy *)
    rd_sort : Logic.Sort.t;  (** the copy's sort *)
    rd_facts : 'fact Set.Poly.t;  (** the pairs as ground facts of the copy *)
    rd_regions : 'region region_demand option;
        (** [Some] exactly when regions are asked of the copy *)
  }

  and 'region region_demand = {
    rg_stored : 'region list;  (** regions accepted refinements asked *)
    rg_fresh : 'region list;  (** regions read off this refinement's plays *)
    rg_uncertified : 'region list;
        (** the stored and fresh regions that hold no certificate *)
  }

  type 'region rank_candidate = {
    rc_ranking : Logic.term option;  (** a ranking built for the demand *)
    rc_asked : 'region list;  (** the regions the problem asks of the copy *)
  }

  (* [solve_certs], when given, is [solve] returning the kind certificates of
     a [Sat] answer as well; it is used in place of [solve] only under
     [check_refinement_kinds], to re-check an accepted refinement's rankings.
     The answer it gives is the one [solve] gives. *)
  let refine_strat ?(extra_plays = []) ?check ?solve_certs ?solve_wf solve
      cex (dual_strat_wf, dual_strat_fn, dual_nu_wfs) =
    let open Ast.LogicOld in
    (* Under [chain_pair_regions_with_passed_choices] (read only with
       [generalise_chain_pairs] or [chain_pair_regions_by_mbp]): the losing conditions of the alternatives
       the ranked side passed over at a node of the play, read from the
       clauses of the check [check] that returned the play
       ([PassedChoices]), computed once per predicate and kept here.  They
       narrow the chain-pair regions and nothing else; without [check] or
       with the field off, no condition.  Under
       [passed_choices_at_ranked_visits_only] they are taken only at the
       visits of the ranked predicate ([PassedChoices.at_node]). *)
    let passed =
      match check with
      | Some chc
        when (config.generalise_chain_pairs || config.chain_pair_regions_by_mbp)
             && config.chain_pair_regions_with_passed_choices ->
          let clauses =
            lazy
              (try
                 let exi_senv = PCSP.Problem.senv_of chc in
                 PCSP.Problem.clauses_of (PCSP.Problem.to_cnf chc)
                 |> Set.to_list
                 |> List.map ~f:(fun c ->
                     let senv, ps, ns, phi = Clause.to_old_clause exi_senv c in
                     (Logic.to_old_sort_env_map senv, ps, ns, phi))
               with exn when not (Common.Timer.is_async exn) ->
                 Debug.print
                 @@ lazy
                      (sprintf "## passed-choice conditions unavailable: %s"
                         (Exn.to_string exn));
                 [])
          in
          let cache = Hashtbl.create (module String) in
          let qelim phi =
            Z3Smt.Z3interface.qelim ~timeout:(Some 1000) ~id:None
              ~fenv:(get_fenv ()) phi
          in
          let visits_only = config.passed_choices_at_ranked_visits_only in
          fun ~visit (node : play_node) xs ->
            if (visits_only && not visit) || List.is_empty xs || String.is_empty (Ident.name_of_pvar node.pvar)
            then []
            else
              let params, conds =
                Hashtbl.find_or_add cache (Ident.name_of_pvar node.pvar)
                  ~default:(fun () ->
                    let params =
                      List.map xs ~f:(fun (_, s) ->
                          (Ident.mk_fresh_tvar ~prefix:(Some "PCP_") (), s))
                    in
                    let conds =
                      PassedChoices.losing_conditions ~qelim
                        (Lazy.force clauses) node.pvar params
                    in
                    Debug.print
                    @@ lazy
                         (sprintf
                            "## passed-choice condition(s) of %s over (%s): %s"
                            (Ident.name_of_pvar node.pvar)
                            (String.concat_map_list ~sep:"," params
                               ~f:(fst >> Ident.name_of_tvar))
                            (if List.is_empty conds then "none"
                             else
                               String.concat_map_list ~sep:"; " conds
                                 ~f:Formula.str_of));
                    (params, conds))
              in
              if List.is_empty conds || List.length params <> List.length xs
                 || List.length node.args <> List.length xs
              then []
              else
                PassedChoices.at_node ~visits_only ~visit conds params
                  ~point:node.args ~vars:xs
      | _ -> fun ~visit:_ _ _ -> []
    in
    let orig_keys_wf = Map.Poly.key_set dual_strat_wf in
    let orig_keys_fn = Map.Poly.key_set dual_strat_fn in
    (* the counter-play read back: its play tree, its clauses (built when
       read) and whether they can hold a copy of a refined key; see
       [CounterPlay.read_counter_play] *)
    let read = CounterPlays.read_counter_play ~orig_keys_wf ~orig_keys_fn cex in
    let play = read.CounterPlays.play in
    if Lazy.force JointWall.enabled then
      last_refinement_plays := Option.to_list play @ extra_plays;
    let module Preprocessor = Preprocessor.Make (struct
      (* [refine_preprocessor], loaded with the configuration; the calls below
         pass [Eliminate_keeping], since this clause set is not asked whether
         it is satisfiable (its strategy predicates are placeholders to be
         synthesised anew, and it may be unsatisfiable as it stands) *)
      let config = ExtFile.unwrap_or_abort config.refine_preprocessor
    end) in
    let copies = CounterPlays.key_copies ~orig_keys_wf ~orig_keys_fn read in
    let { CounterPlays.keys_wf; keys_fn; senv_problem } = copies in
    let problem =
      CounterPlays.refinement_clauses read copies
        ~preprocess:(fun ~keep p ->
          snd
          @@ Preprocessor.preprocess p
               ~purpose:
                 (Preprocessing.Preprocessor.Purpose.Eliminate_keeping keep))
    in
    (* The refinement problem for the plays [plays] (the first play, then any
       extra ones): the clauses read off the first play's derivation, and, per
       ranking key, one fresh copy constrained by the chain pairs of all the
       plays together, so that one ranking has to cover every play. *)
    (* Under [~wf_mode] (only with [resynthesise_wf_rankings]), a key whose
       ranking is constrained by chain-pair facts alone gets its fresh copy
       declared [WF] and constrained by every pair accepted refinements have
       asked of it as well as the new ones, unless those contain a cycle; its
       solution then REPLACES the ranking (see the read-back below).  What the
       last build asked, per key, and which copies it declared [WF], are left
       in these two references for the read-back. *)
    let last_asked = ref [] in
    let last_wf_copies = ref Set.Poly.empty in
    (* Under [~generalise] (only with [generalise_chain_pairs]): the regions
       the last build read off the plays, per key whose copy it declared [WF],
       and how many region clauses (stored and new) it added in all. *)
    let last_regions = ref [] in
    let last_region_clauses = ref 0 in
    (* Under [chain_pair_region_multiphase_depth]: the copies the last build
       solved itself, each with its solution (see [multiphase_candidate]);
       such a copy is declared but constrained by nothing in the problem, and
       its solution is put into the constraint solver's answer. *)
    let presolved = ref [] in
    let decisions =
      Set.Poly.map orig_keys_fn ~f:Ident.name_of_tvar
    in
    let has_derivation_copy key =
      Set.exists keys_wf ~f:(fun x ->
          String.is_prefix (Ident.name_of_tvar x)
            ~prefix:(Ident.name_of_tvar key ^ "$"))
    in
    let by_mbp = config.chain_pair_regions_by_mbp in
    (* Boundary 2 of the refinement, the ranking seam under
       [refine_rankings = Separate]: per ranking key, [rank_demand] reads
       what the plays demand of a fresh copy of the key, [rank_candidate]
       tries to meet that demand by a ranking built here, and
       [rank_constraints] states what is left as the copy's constraints.
       [build_pfwcsp] only declares the copy and joins those constraints.
       The three are called in this order once per key, and their effects on
       the build's bookkeeping ([last_asked], [last_wf_copies],
       [last_regions], [last_region_clauses], [presolved]) are the ones the
       read-back after the solve relies on. *)
    (* [rank_demand ~wf_mode ~generalise trees ~key ~args]: [None] when the
       plays [trees] give the ranking key [key] (of parameters [args]) no
       chain pair, with no effect but a trace line.  Otherwise [Some d]:
       - [d.rd_copy] is a fresh variable named [key$...];
       - [d.rd_pairs] are the pairs asked of it: the plays' pairs
         ([chain_pairs_of], deduplicated and sorted), or under [wf_mode], for
         a key with no copy in the derivation, every pair asked of [key] by
         an accepted refinement so far together with them when that union is
         acyclic (transitively reduced under
         [chain_pair_transitive_reduction]), in which case the copy is to be
         declared [WF];
       - [d.rd_sort] is the copy's sort and [d.rd_facts] the pairs as ground
         facts [copy(a @ b)];
       - [d.rd_regions] is [Some] exactly when [generalise] holds and the
         copy is to be declared [WF]: the regions stored for [key], the new
         regions read off the plays ([chain_regions_of]; under [by_mbp]
         renamed onto the key's canonical variables, those equal to another
         or to a stored one dropped), and the stored and new ones holding no
         certificate.
       Effects, in this order: [(key, plays' pairs)] pushed on [last_asked];
       the copy added to [last_wf_copies] when it is to be declared [WF];
       [(key, new regions)] pushed on [last_regions] when [d.rd_regions] is
       [Some].  Asks no Z3 question beyond those [chain_regions_of] and
       [canonical_regions] ask. *)
    let rank_demand ~wf_mode ~generalise trees ~key ~args =
      let pairs =
        List.concat_map trees ~f:(fun tree ->
            chain_pairs_of
              ~nearest_only:config.chain_pairs_nearest_visits_only tree
              ~wf_key:key ~arity:(List.length args))
        |> ChainPairs.dedup_and_sort
      in
      if not (List.is_empty extra_plays) then
        Debug.print
        @@ lazy
             (sprintf "## chain pairs of %s from %d play(s): %s"
                (Ident.name_of_tvar key) (List.length trees)
                (String.concat_map_list ~sep:"; " pairs
                   ~f:(fun (a, b) ->
                     sprintf "(%s) -> (%s)"
                       (String.concat_map_list ~sep:","
                          ~f:LogicOld.Term.str_of a)
                       (String.concat_map_list ~sep:","
                          ~f:LogicOld.Term.str_of b))));
      if List.is_empty pairs then None
      else
        let copy =
          Ident.mk_fresh_tvar
            ~prefix:(Some (Ident.name_of_tvar key ^ "$"))
            ()
        in
        last_asked := (key, pairs) :: !last_asked;
        let pairs =
          if wf_mode && not (has_derivation_copy key) then
            let all =
              Option.value ~default:[]
                (Hashtbl.find wf_rank_pairs
                   (Ident.name_of_tvar key))
              @ pairs
              |> ChainPairs.dedup_and_sort
            in
            (* [chain_pair_transitive_reduction]: the reduction and the
               cycle test read one numbering of the states
               ([ChainPairs.reduce_if_acyclic] is [None] exactly when
               [pairs_cyclic] holds) *)
            let reduced =
              if config.chain_pair_transitive_reduction then
                `Reduced (ChainPairs.reduce_if_acyclic all)
              else `Not_asked
            in
            if
              match reduced with
              | `Reduced r -> Option.is_none r
              | `Not_asked -> pairs_cyclic all
            then (
              Debug.print
              @@ lazy
                   (sprintf
                      "## the chain pairs asked of %s so far \
                       contain a cycle; it is refined by a \
                       disjoined piece"
                      (Ident.name_of_tvar key));
              pairs)
            else (
              last_wf_copies := Set.add !last_wf_copies copy;
              Debug.print
              @@ lazy
                   (sprintf
                      "## re-synthesising %s as one WF relation \
                       over %d chain pair(s)"
                      (Ident.name_of_tvar key) (List.length all));
              (* [chain_pair_transitive_reduction]: [all] is
                 acyclic here, and every relation the copy can
                 be given (a template instance) is transitive,
                 so the reduction asks the same of it *)
              match reduced with
              | `Reduced reduced ->
                let reduced = Option.value_exn reduced in
                ChainPairs.log
                  (sprintf "reduce key=%s all=%d kept=%d"
                     (Ident.name_of_tvar key) (List.length all)
                     (List.length reduced));
                Debug.print
                @@ lazy
                     (sprintf
                        "## %s: %d of the %d chain pair(s) left \
                         by transitive reduction"
                        (Ident.name_of_tvar key)
                        (List.length reduced) (List.length all));
                reduced
              | `Not_asked -> all)
          else pairs
        in
        (* built here, before the regions, as the build always built them:
           the order of term constructions is kept, not only the order of
           effects *)
        let sort =
          Logic.Sort.mk_fun (List.map args ~f:snd @ [ Logic.BoolTerm.SBool ])
        in
        let facts =
          Set.Poly.of_list
          @@ List.map pairs ~f:(fun (a, b) ->
              ( Map.Poly.empty,
                Logic.Term.mk_var_app copy
                  (List.map (a @ b) ~f:Logic.ExtTerm.of_old_term) ))
        in
        let regions =
          if generalise && Set.mem !last_wf_copies copy then (
            let regions =
              List.concat_map trees ~f:(fun tree ->
                  chain_regions_of ~passed ~by_mbp
                    ~problem_sides_only:
                      config.chain_pair_regions_by_mbp_problem_sides_only
                    ~multiphase_depth:
                      config.chain_pair_region_multiphase_depth
                    ~window:config.chain_pair_region_window
                    ~window_min_pairs:
                      config.chain_pair_region_window_min_pairs
                    ~decisions tree
                    ~wf_key:key
                    ~arity:(List.length args))
              |> List.stable_sort ~compare:(fun (p1, _) (p2, _) ->
                  Stdlib.compare p1 p2)
              |> List.remove_consecutive_duplicates
                   ~equal:(fun (p1, _) (p2, _) ->
                     Stdlib.( = ) p1 p2)
              |> List.map ~f:snd
            in
            let stored =
              Option.value ~default:[]
                (Hashtbl.find wf_rank_regions
                   (Ident.name_of_tvar key))
            in
            (* [by_mbp]: the new regions renamed onto the key's
               canonical variables, without the ones equal to
               each other or to a stored one (stored regions are
               canonical already) *)
            let regions =
              if by_mbp then
                let n_stored = List.length stored in
                List.drop
                  (canonical_regions (Ident.name_of_tvar key)
                     (stored @ regions))
                  n_stored
              else regions
            in
            last_regions := (key, regions) :: !last_regions;
            (* A region holding a certificate has no linear
               ranking; it is asked only through a candidate
               built from the certificates.  With no candidate
               accepted those regions are left out, and what is
               asked is what is asked without certificates. *)
            let uncertified =
              List.filter (stored @ regions) ~f:(fun (_, _, cert) ->
                  Option.is_none cert)
            in
            Debug.print
            @@ lazy
                 (sprintf
                    "## %s: %d region(s) from the plays, %d \
                     stored:\n%s"
                    (Ident.name_of_tvar key) (List.length regions)
                    (List.length stored)
                    (String.concat_map_list ~sep:"\n" regions
                       ~f:(fun (vars, region, cert) ->
                         sprintf "  (%s) : %s%s"
                           (String.concat_map_list ~sep:","
                              vars ~f:(fst >> Ident.name_of_tvar))
                           (LogicOld.Formula.str_of region)
                           (match cert with
                           | None -> ""
                           | Some (len, fs) ->
                               sprintf
                                 " [multiphase %s, %d step(s)]"
                                 (RankingCheck.str_of_components
                                    fs)
                                 len))));
            Some
              {
                rg_stored = stored;
                rg_fresh = regions;
                rg_uncertified = uncertified;
              })
          else None
        in
        Some
          {
            rd_key = key;
            rd_args = args;
            rd_copy = copy;
            rd_pairs = pairs;
            rd_sort = sort;
            rd_facts = facts;
            rd_regions = regions;
          }
    in
    (* [rank_candidate ~wf_mode d]: a ranking for the demand [d] built here,
       by LP or certificates rather than by the constraint solver, and the
       regions the problem asks of the copy.
       - With regions ([d.rd_regions = Some r]): under
         [chain_pair_region_multiphase_depth > 1] the multiphase candidate
         over every region and pair ([multiphase_candidate]); failing that the
         lexicographic one over the uncertified regions and the pairs
         ([lex_candidate]).  [rc_asked] is every region when a multiphase
         candidate is found, the uncertified ones otherwise.
       - Without regions, under [wf_mode] for a copy declared [WF] and
         [chain_pair_lex_candidate_depth > 0]: the lexicographic candidate
         over the pairs alone; [rc_asked] empty.
       - Otherwise no candidate and [rc_asked] empty.
       Post (from the candidates' own contracts): a returned ranking is a
       template instance whose order contains [d.rd_pairs] and every region
       of [rc_asked] ([order_covers]), so the copy's demands are discharged.
       No effect on the build's bookkeeping; the candidates' memos only. *)
    let rank_candidate ~wf_mode d =
      match d.rd_regions with
      | Some r ->
          let multiphase =
            if config.chain_pair_region_multiphase_depth <= 1
            then None
            else
              Option.map ~f:snd
              @@ multiphase_candidate
                   ~key:(Ident.name_of_tvar d.rd_key) ~args:d.rd_args
                   (r.rg_stored @ r.rg_fresh) d.rd_pairs
          in
          (* [chain_pair_lex_candidate_depth]: when no
             certificate is accepted, a candidate built over
             the regions the problem would ask and the pairs *)
          let candidate =
            match multiphase with
            | Some _ -> multiphase
            | None ->
                Option.map ~f:snd
                @@ lex_candidate ~key:(Ident.name_of_tvar d.rd_key)
                     ~args:d.rd_args r.rg_uncertified d.rd_pairs
          in
          let asked =
            match multiphase with
            | Some _ -> r.rg_stored @ r.rg_fresh
            | None -> r.rg_uncertified
          in
          { rc_ranking = candidate; rc_asked = asked }
      | None ->
          if
            wf_mode
            && Set.mem !last_wf_copies d.rd_copy
            && config.chain_pair_lex_candidate_depth > 0
          then
            (* the re-synthesis over the ground pairs alone: the
               same candidate, built over the pairs *)
            {
              rc_ranking =
                Option.map ~f:snd
                @@ lex_candidate ~key:(Ident.name_of_tvar d.rd_key)
                     ~args:d.rd_args [] d.rd_pairs;
              rc_asked = [];
            }
          else { rc_ranking = None; rc_asked = [] }
    in
    (* [rank_constraints d c]: the constraints of the copy [d.rd_copy] the
       problem keeps.  A candidate [c.rc_ranking = Some lam] discharges the
       demand: the copy is pushed on [presolved] with [lam] and asked
       nothing.  Otherwise the pairs [d.rd_pairs] as ground facts, and with
       regions, each region [(vars, region)] of [c.rc_asked] as the clause
       [forall vars. region => copy(vars)] (the ground facts stay, so the
       problem only gains constraints; under [by_mbp] a pair some asked
       region holds at is implied by it and not asked again).  With regions
       the number of regions asked is added to [last_region_clauses] whether
       or not a candidate was found.  Asks Z3 only through
       [region_holds_at]. *)
    let rank_constraints d c =
      let copy = d.rd_copy and pairs = d.rd_pairs and facts = d.rd_facts in
      match d.rd_regions with
      | Some _ -> (
          let asked = c.rc_asked in
          last_region_clauses :=
            !last_region_clauses + List.length asked;
          match c.rc_ranking with
          | Some lam ->
              (* the copy's demands are discharged by [lam]:
                 it is declared, asked nothing, and solved by
                 [lam] *)
              presolved := (copy, lam) :: !presolved;
              Set.Poly.empty
          | None ->
          (* [by_mbp]: a ground pair some region holds at is
             implied by that region's clause, so it is not
             asked again as a fact *)
          let facts =
            if by_mbp then
              Set.Poly.of_list
              @@ List.filter_map pairs ~f:(fun (a, b) ->
                  if
                    List.exists asked ~f:(fun (vars, r, _) ->
                        region_holds_at (vars, r) (a, b))
                  then None
                  else
                    Some
                      ( Map.Poly.empty,
                        Logic.Term.mk_var_app copy
                          (List.map (a @ b)
                             ~f:Logic.ExtTerm.of_old_term) ))
            else facts
          in
          Debug.print
          @@ lazy
               (sprintf
                  "## %s: %d of %d ground pair(s) asked as facts"
                  (Ident.name_of_tvar d.rd_key) (Set.length facts)
                  (List.length pairs));
          Set.union facts
          @@ Set.Poly.of_list
          @@ List.map asked ~f:(fun (vars, region, _) ->
              ( Logic.of_old_sort_env_map
                  (Map.Poly.of_alist_exn vars),
                Logic.BoolTerm.imply_of
                  (Logic.ExtTerm.of_old_formula region)
                  (Logic.Term.mk_var_app copy
                     (List.map vars
                        ~f:(fst >> Logic.Term.mk_var))) )))
      | None -> (
          match c.rc_ranking with
          | Some lam ->
              presolved := (copy, lam) :: !presolved;
              Set.Poly.empty
          | None -> facts)
    in
    (* [~src] and [~extra_fn] serve the lifted counter-play only: the clauses
       read, and further unknowns of kind [FN] (the tag predicates kept as
       variables) treated as the key copies are.  With their defaults the
       build is the one used without the field. *)
    let build_pfwcsp ?(wf_mode = false) ?(generalise = false) ?(src = problem)
        ?(extra_fn = Map.Poly.empty) plays =
      let senv_build = Map.force_merge senv_problem extra_fn in
      let keys_build =
        Set.union (Set.union keys_fn keys_wf) (Map.key_set extra_fn)
      in
      last_asked := [];
      last_wf_copies := Set.Poly.empty;
      last_regions := [];
      last_region_clauses := 0;
      presolved := [];
      let pfwcsp =
        let fsenvs, cs =
          PCSP.Problem.clauses_of src
          |> Set.Poly.filter_map ~f:(fun (uni_senv, pos, neg, phi) ->
              let pos =
                Set.filter pos
                  ~f:
                    (Logic.Term.pvar_of_atom
                    >> Set.mem keys_build
                    >> not)
              in
              if Set.is_empty neg && Set.is_empty pos then None
              else
                let senv1, (senv2, fsenv, phi) =
                  Tuple2.map_snd
                    ~f:
                      (Logic.ExtTerm.neg_of
                      >> Logic.ExtTerm.to_old_fml senv_build uni_senv
                      >> Evaluator.simplify
                      >> (fun phi ->
                      if false then
                        print_endline
                          ("before: " ^ LogicOld.Formula.str_of @@ snd
                          @@ LogicOld.Formula.quantify_except ~exists:true
                               Set.Poly.empty phi);
                      phi)
                      >> LogicOld.Formula.negate >> Evaluator.simplify
                      >> Tuple2.curry
                           (Ast.Qelim.elim_free_univ_vars_old Map.Poly.empty
                              senv_build)
                           uni_senv
                      >> snd >> LogicOld.Formula.negate >> Evaluator.simplify
                      >> LogicOld.Formula.quantify_except ~exists:true
                           Set.Poly.empty
                      >> snd
                      >> (fun phi ->
                      if false then
                        print_endline ("after: " ^ LogicOld.Formula.str_of phi);
                      phi)
                      >> LogicOld.Formula.skolemize ~uni_senv:Map.Poly.empty
                           ~use_fn_pred:true ~only_impure:true)
                  @@ Clause.to_senv_formula (uni_senv, pos, neg, phi)
                in
                Some
                  ( fsenv,
                    Logic.ExtTerm.of_old
                      ( Map.force_merge (Logic.to_old_sort_env_map senv1) senv2,
                        phi ) ))
          |> Set.unzip
        in
        (* With the opponent's decisions named, the derivation is a complete
           play and the pairs its rankings must cover are read off it (see
           [chain_pairs_of]); each key gets a fresh copy constrained by those
           pairs as facts, joined into the key's strategy like any other copy.
           This is the ranking seam ([refine_rankings]): [Separate], the one
           value, constrains each ranking copy by the play's pairs alone,
           independently of how the Skolem terms are then chosen; per key
           the demand, the candidate and the constraints left are
           [rank_demand], [rank_candidate] and [rank_constraints], and the
           build only declares the copy.  A joint alternative adds its arm
           here. *)
        let pair_senv, pair_cs =
          match (config.refine_rankings, plays) with
          | _, [] -> (Map.Poly.empty, Set.Poly.empty)
          | (Config.Separate | Config.Joint_guided | Config.Joint_steered _), trees ->
              (* [Joint_guided] and [Joint_steered] ask the ranking as [Separate] does; they
                 differ only in how the terms are then selected
                 ([joint_selection]) *)
              Map.Poly.fold dual_strat_wf
                ~init:(Map.Poly.empty, Set.Poly.empty)
                ~f:(fun ~key ~data (senv, cs) ->
                  let args, _ = Logic.Term.let_lam data in
                  match rank_demand ~wf_mode ~generalise trees ~key ~args with
                  | None -> (senv, cs)
                  | Some d ->
                      let c = rank_candidate ~wf_mode d in
                      ( Map.Poly.set senv ~key:d.rd_copy ~data:d.rd_sort,
                        Set.union cs (rank_constraints d c) ))
        in
        let cs = Set.union cs pair_cs in
        let params =
          let fsenv =
            Map.force_merge_list @@ Set.to_list
            @@ Set.Poly.map ~f:Logic.of_old_sort_env_map fsenvs
          in
          let kind_map =
            Kind.add_kinds !last_wf_copies Kind.WF
            @@ Kind.add_kinds keys_wf Kind.DWF
                 (Kind.add_kinds
                    (Set.diff (Map.key_set pair_senv) !last_wf_copies)
                    Kind.DWF
                    (Kind.add_kinds keys_fn Kind.FN
                       (Kind.add_kinds (Map.key_set extra_fn) Kind.FN
                          (Kind.add_kinds (Map.key_set fsenv) Kind.FN
                             Map.Poly.empty))))
          in
          PCSP.Params.make ~kind_map
            (Map.force_merge_list [ senv_build; fsenv; pair_senv ])
        in
        PCSP.Problem.normalize @@ PCSP.Problem.of_formulas ~params cs
      in
      if use_solspace then
        PCSP.Problem.set_params_sol_space pfwcsp
          (Map.of_set_exn
          @@ Set.Poly.map (Set.union keys_wf keys_fn) ~f:(fun key ->
              (key, !solspace)))
      else pfwcsp
    in
    (* the kind certificates of the latest refinement solved, read by the
       check of an accepted refinement; empty when the answer did not come
       from a call that records them *)
    let last_certs = ref Map.Poly.empty in
    let solve_unbounded =
      match solve_certs with
      | Some solve_certs when config.check_refinement_kinds ->
          fun pfwcsp ->
            Or_error.map (solve_certs pfwcsp) ~f:(fun (sol, n, certs) ->
                last_certs := certs;
                (sol, n))
      | _ -> solve
    in
    (* The re-synthesis attempt is bounded ([solve_wf], the check's budget)
       so that the refinement asked without it is always reached.  Under
       [bound_last_refinement] that last form (every build that declared no
       [WF] copy) is bounded the same way, so that a refinement no ranking of
       the template class meets ends too; it then gives no kind certificates,
       as the bounded attempts never do, and an expired budget is the
       solver's [Timeout], raised below as [RefinementBudgetExpired]. *)
    let solve pfwcsp =
      match solve_wf with
      | Some solve_wf when not (Set.is_empty !last_wf_copies) ->
          solve_wf pfwcsp
      | Some solve_wf when bound_last_refinement () -> solve_wf pfwcsp
      | _ -> solve_unbounded pfwcsp
    in
    (* A lifted [refine_counter_play]: the Skolem part of this refinement
       solved by model-guided selection on the play with the checked side's
       ground values kept as variables, or [None].

       The counter-play is read from the check whose checked-side values are
       tag predicates, each defined by one fact [T(c)] when the value is a
       ground constant.  Resolving those facts away (as the ordinary build
       does) writes the constant into every key argument that was the
       opponent's move, so the selection can only return a constant for such
       a key.  Here each such tag is kept: its fact becomes the universal fact
       [T(v)] (so that no preprocessing reads the tag as empty), the tag is an
       extra unknown of kind [FN] of the build, and the selection is asked
       with the tag pinned to its definition [v = c], which enters the
       selection's model and not the formula it selects from.  The answer is
       checked valid with the tags pinned, which is the refinement problem
       with the values inlined; so it beats the same play.  Built with no
       chain-pair play, its formulas are the Skolem part of the ordinary
       build (a ranking copy constrained by pairs shares no unknown with
       them), and the key copies keep their names, which is what the
       read-back uses.  The build's bookkeeping of ranking copies is restored
       afterwards, so the ordinary build that follows is unaffected.
       Computed at most once per refinement. *)
    let lifted_memo = ref None in
    (* whether the memoised selection was asked on the generalised goal *)
    let lifted_general = ref false in
    let lifted_selection_raw ?origin_of ?snap () =
      match !lifted_memo with
      | Some r -> r
      | None ->
          let started = Common.PhaseTime.now () in
          let r =
            if
              not
                (Config.selects_terms config.refine_terms
               && Config.lifts_play config.refine_counter_play)
            then None
            else
              try
                (* [refine_counter_play = Lifted_free_goal]: the play with
                   its goal instance generalised, when it has a ground
                   argument *)
                let src, general = CounterPlays.lifted_source read in
                if general then lifted_general := true;
                match CounterPlays.lift_tags src with
                | None -> None
                | Some { CounterPlays.single; pinned; extra_fn; lifted_raw } ->
                  let lifted =
                    snd
                    @@ Preprocessor.preprocess lifted_raw
                         ~purpose:
                           (Preprocessing.Preprocessor.Purpose
                            .Eliminate_keeping
                              (Set.union
                                 (Map.Poly.key_set senv_problem)
                                 (Map.Poly.key_set extra_fn)))
                  in
                  let saved =
                    ( !last_asked,
                      !last_wf_copies,
                      !last_regions,
                      !last_region_clauses,
                      !presolved )
                  in
                  let pfwcsp =
                    Exn.protect
                      ~f:(fun () -> build_pfwcsp ~src:lifted ~extra_fn [])
                      ~finally:(fun () ->
                        let a, b, c, d, e = saved in
                        last_asked := a;
                        last_wf_copies := b;
                        last_regions := c;
                        last_region_clauses := d;
                        presolved := e)
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "## selection on the lifted play (%d value(s) kept \
                           as variables):\n%s\n"
                          (Map.Poly.length single)
                          (PCSP.Problem.str_of pfwcsp));
                  let all_fn p =
                    Map.Poly.for_alli (PCSP.Problem.senv_of p)
                      ~f:(fun ~key ~data:_ ->
                        Kind.is_fn (PCSP.Problem.kind_of p key))
                  in
                  let part =
                    if all_fn pfwcsp then Some pfwcsp
                    else
                      Option.map (split_mixed_refinement pfwcsp) ~f:fst
                  in
                  Option.bind part ~f:(fun part ->
                      select_skolem_solution ?origin_of ?snap
                        ~pinned:(Map.Poly.find pinned)
                        ~eq_result:
                          (Config.frees_goal config.refine_counter_play)
                        part)
              with exn when not (Common.Timer.is_async exn) ->
                Debug.print
                @@ lazy
                     (sprintf "## selection on the lifted play failed (%s)"
                        (Exn.to_string exn));
                None
          in
          Debug.print
          @@ lazy
               (if Option.is_some r then
                  "## selection on the lifted play gave the Skolem part"
                else "## no selection on the lifted play; the ordinary one");
          (* one stderr line per lifted selection asked, for a census of where
             the field acts and what it costs; nothing without the variable *)
          if
            Config.lifts_play config.refine_counter_play
            && Option.is_some (Sys.getenv "COAR_MUSTRAT_LIFTED_CENSUS")
          then
            eprintf "mustrat-lifted: outcome=%s secs=%.2f%s\n%!"
              (if Option.is_some r then "gave" else "none")
              (Common.PhaseTime.now () -. started)
              (match r with
              | None -> ""
              | Some sol ->
                  " terms="
                  ^ String.concat_map_list ~sep:"; " (Map.Poly.to_alist sol)
                      ~f:(fun (k, t) ->
                        Ident.name_of_tvar k ^ ":=" ^ Logic.ExtTerm.str_of t));
          lifted_memo := Some r;
          r
    in
    (* [lifted_selection ~against]: the lifted selection, for the refinement
       problem [against] (the Skolem part of the build being solved).  Asked
       on the generalised goal, the lifted play is weaker than [against]: its
       goal arguments are existential in the refinement, so an answer valid
       on it need not beat the play the CHC backend returned.  The answer is
       then kept only as a proposal for the key copies: [against] is asked
       with every copy the answer solves pinned to that solution and only
       its other unknowns (Skolem constants of its own) selected, and the
       result, checked valid on [against] by the selection itself, is the
       solution; [None] when that fails, and the ordinary selection follows.
       Pre: [against]'s key copies carry the names the lifted build gave
       them (both are read off the same play).  Post: [Some sol] solves
       [against]. *)
    let lifted_selection ?origin_of ?snap ~against () =
      match lifted_selection_raw ?origin_of ?snap () with
      | Some sol when !lifted_general ->
          let senv = PCSP.Problem.senv_of against in
          let proposal =
            Map.Poly.filter_keys sol ~f:(Map.Poly.mem senv)
          in
          let rows = !selected_extra_rows in
          let r =
            if Map.Poly.is_empty proposal then None
            else if Map.Poly.for_alli senv ~f:(fun ~key ~data:_ ->
                        Map.Poly.mem proposal key)
            then
              (* every unknown proposed: one validity check per formula *)
              if
                (try SkolemTerms.valid_solution against proposal
                 with exn when not (Common.Timer.is_async exn) -> false)
              then Some proposal
              else None
            else
              (* the others (Skolem constants of [against] alone) selected
                 with the proposal pinned; the selection checks the whole *)
              select_skolem_solution ~pinned:(Map.Poly.find proposal) against
          in
          selected_extra_rows := rows;
          Debug.print
          @@ lazy
               (if Option.is_some r then
                  "## the lifted play's answer (goal generalised) checked \
                   valid on the refinement"
                else
                  "## the lifted play's answer (goal generalised) not \
                   checked valid on the refinement; the ordinary selection");
          if Option.is_some (Sys.getenv "COAR_MUSTRAT_LIFTED_CENSUS") then
            eprintf "mustrat-lifted: free-goal valid=%b\n%!" (Option.is_some r);
          r
      | r -> r
    in
    (* Boundary 3, the term seam's selection ([refine_terms = Terms_select]):
       [select_terms ?origin_of ?snap ~lifted_first p] asks first, when
       [lifted_first], the selection on the lifted play against [p]
       ([lifted_selection], which answers [None] unless
       [refine_counter_play] lifts the play), and otherwise, or when that
       gives nothing, model-guided selection on [p] itself
       ([select_skolem_solution]).  Boundary 4, the guards
       ([SkolemTerms.guard_terms]), is applied inside either selection to
       the copies [origin_of] groups; without [origin_of] it is the
       identity ([refine_guards = Unguarded]).
       Assumes: [p] is a refinement problem built from this counter-play
       (its key copies named [key$...] as [build_pfwcsp] names them).
       Guarantees: [Some sol] passed the validity check of the selection that
       returned it -- on [p] for [select_skolem_solution] and for a lifted
       answer on a generalised goal, and on the lifted play with its tags
       pinned (the play's values inlined) otherwise; [None] when neither
       selection applies, and the caller falls back to the constraint solver.
       Effects: [selected_extra_rows] as the selection that ran last left it;
       the lifted selection is computed at most once per refinement. *)
    let select_terms ?origin_of ?snap ~lifted_first p =
      match
        if lifted_first then lifted_selection ?origin_of ?snap ~against:p ()
        else None
      with
      | Some sol -> Some sol
      | None -> select_skolem_solution ?origin_of ?snap p
    in
    (* [refine_rankings = Joint_guided]: the counter-play's clauses with the
       state at each visit of a ranked predicate observed, built once per
       refinement.  Each clause whose head is a copy [p$N] of a predicate a
       ranking key ranks gains the premise [V(s)], [V] a fresh unknown of
       kind [FN] (an observer: it asks nothing, the selection reads its
       argument terms), [s] the head's last [n] arguments, [n] the key's
       state width.  The clauses are then preprocessed as the refinement's
       are, the observers kept with the key copies, so after the derivation's
       predicates are resolved away each observer's arguments are the visit's
       state as a term of the selection's formula.  Also kept: the copy tree
       (each copy's premises' copies), the observer of each copy, and the
       counter-play's ground state at each copy.  [None] when the clauses
       hold no ranked visit. *)
    let joint_observed ~raw ~extra_fn ~pinned =
        (let _, model, _ = Lazy.force read.CounterPlays.expanded in
         let raw_senv = PCSP.Problem.senv_of raw in
         let orig_of name =
           match String.lsplit2 name ~on:'$' with
           | Some (p, _) -> p
           | None -> name
         in
         (* ranked predicate name -> state width *)
         let widths =
           Map.Poly.fold dual_strat_wf ~init:Map.Poly.empty
             ~f:(fun ~key ~data acc ->
               match rank_target_of key with
               | Some t ->
                   Map.Poly.set acc ~key:t
                     ~data:(List.length (fst (Logic.Term.let_lam data)) / 2)
               | None -> acc)
         in
         let observers = Hashtbl.create (module String) in
         let children = Hashtbl.create (module String) in
         let has_parent = Hash_set.create (module String) in
         let roots = ref [] in
         (* each formula of the counter-play is one clause (CounterPlay's
            implication, its premises' copies fresh): in negation normal
            form its top disjuncts are the head (a positive predicate atom)
            and the premises (negated ones) *)
         let pvar_app phi =
           match phi with
           | LogicOld.Formula.Atom
               (LogicOld.Atom.App (LogicOld.Predicate.Var (p, sorts), ts, _), _)
             ->
               Some (p, sorts, ts)
           | _ -> None
         in
         let formulas =
           List.map (Set.to_list (PCSP.Problem.formulas_of raw))
             ~f:(fun (uni_senv, phi) ->
               let ophi =
                 LogicOld.Formula.nnf_of
                 @@ Logic.ExtTerm.to_old_fml raw_senv uni_senv phi
               in
               let ds = LogicOld.Formula.disjuncts_list_of ophi in
               let heads = List.filter_map ds ~f:pvar_app in
               let bodies =
                 List.filter_map ds ~f:(function
                   | LogicOld.Formula.UnaryOp (LogicOld.Formula.Not, a, _) ->
                       Option.map (pvar_app a) ~f:(fun (p, _, _) ->
                           Ident.name_of_pvar p)
                   | _ -> None)
               in
               (match heads with
               | [] -> roots := bodies @ !roots
               | _ ->
                   List.iter heads ~f:(fun (h, _, _) ->
                       Hashtbl.add_multi children ~key:(Ident.name_of_pvar h)
                         ~data:bodies;
                       List.iter bodies ~f:(Hash_set.add has_parent)));
               let tags =
                 List.filter_map heads ~f:(fun (p, sorts, args) ->
                     let name = Ident.name_of_pvar p in
                     match Map.Poly.find widths (orig_of name) with
                     | Some n
                       when n > 0
                            && List.length args >= n
                            && not (Hashtbl.mem observers name) ->
                         let drop = List.length args - n in
                         let state = List.drop args drop
                         and ssorts = List.drop sorts drop in
                         let v =
                           Ident.mk_fresh_tvar ~prefix:(Some "JointVisit_") ()
                         in
                         Hashtbl.set observers ~key:name
                           ~data:
                             ( v,
                               Logic.Sort.mk_fun
                                 (List.map ssorts ~f:Logic.ExtTerm.of_old_sort
                                 @ [ Logic.BoolTerm.SBool ]) );
                         Some
                           (LogicOld.Formula.mk_neg
                           @@ LogicOld.Formula.mk_atom
                           @@ LogicOld.Atom.mk_pvar_app
                                (Ident.tvar_to_pvar v) ssorts state)
                     | _ -> None)
               in
               ( Logic.to_old_sort_env_map uni_senv,
                 if List.is_empty tags then ophi
                 else LogicOld.Formula.or_of (ophi :: tags) ))
         in
         if Hashtbl.is_empty observers then (
           Debug.print
           @@ lazy
                (sprintf
                   "## the joint selection: no visit of a ranked predicate \
                    (%s) heads a clause of the counter-play's %d clause(s) \
                    (heads: %s)"
                   (String.concat ~sep:"," (Map.Poly.keys widths))
                   (List.length formulas)
                   (String.concat ~sep:","
                      (List.dedup_and_sort ~compare:String.compare
                         (List.map (Hashtbl.keys children) ~f:orig_of))));
           None)
         else
           let obs_senv =
             Hashtbl.fold observers ~init:Map.Poly.empty
               ~f:(fun ~key:_ ~data:(v, sort) acc ->
                 Map.Poly.set acc ~key:v ~data:sort)
           in
           let params = PCSP.Problem.params_of raw in
           let tagged =
             PCSP.Problem.of_old_formulas
               ~params:
                 {
                   params with
                   PCSP.Params.senv =
                     Map.force_merge params.PCSP.Params.senv obs_senv;
                   (* [senv] within [kind_map]'s keys: an observer is an
                      ordinary predicate until the build declares it [FN] *)
                   kind_map =
                     Kind.add_kinds (Map.Poly.key_set obs_senv) Kind.Ord
                       params.PCSP.Params.kind_map;
                 }
               (Set.Poly.of_list formulas)
           in
           let pre =
             snd
             @@ Preprocessor.preprocess tagged
                  ~purpose:
                    (Preprocessing.Preprocessor.Purpose.Eliminate_keeping
                       (Set.Poly.union_list
                          [
                            Map.Poly.key_set senv_problem;
                            Map.Poly.key_set extra_fn;
                            Map.Poly.key_set obs_senv;
                          ]))
           in
           let saved =
             ( !last_asked,
               !last_wf_copies,
               !last_regions,
               !last_region_clauses,
               !presolved )
           in
           let pfwcsp =
             Exn.protect
               ~f:(fun () ->
                 build_pfwcsp ~src:pre
                   ~extra_fn:(Map.force_merge obs_senv extra_fn)
                   [])
               ~finally:(fun () ->
                 let a, b, c, d, e = saved in
                 last_asked := a;
                 last_wf_copies := b;
                 last_regions := c;
                 last_region_clauses := d;
                 presolved := e)
           in
           let ground =
             Set.fold model ~init:Map.Poly.empty ~f:(fun acc (p, ts) ->
                 Map.Poly.set acc ~key:(Ident.name_of_pvar p) ~data:ts)
           in
           Some
             ( pfwcsp,
               observers,
               (fun name -> Option.value ~default:[] (Hashtbl.find children name)),
               List.dedup_and_sort ~compare:String.compare
                 (!roots
                 @ List.filter (Hashtbl.keys children) ~f:(fun h ->
                       not (Hash_set.mem has_parent h))),
               orig_of,
               ground,
               pinned ))
    in
    (* The clauses the joint selection reads, in the order asked: under a
       lifted [refine_counter_play], the lifted play's (the checked side's
       values kept as pinned tags, the goal generalised under
       [Lifted_free_goal]), on which a visit's state stays a variable where
       the ordinary clauses fix it to the play's constant; then the ordinary
       counter-play's.  Each built once per refinement, when first asked.
       Under [Joint_steered] the ordinary clauses alone, the check's own:
       every model of them is a play of the check (its root the query's
       instance, the checked side's moves its strategy's values), which is
       what a ranking met at such a model may be relied on for; a model of
       the lifted clauses with the goal generalised can be a play from
       another goal instance, at which a ranking can be met while the terms
       lose from the real one.  ([SteerAudit]'s test mutant reads the
       lifted clauses instead.) *)
    let joint_lifted =
      lazy
        (if
           not
             (Config.selects_terms config.refine_terms
             && Config.lifts_play config.refine_counter_play)
         then None
         else
           let src, _ = CounterPlays.lifted_source read in
           match CounterPlays.lift_tags src with
           | None -> None
           | Some { CounterPlays.pinned; extra_fn; lifted_raw; _ } ->
               joint_observed ~raw:lifted_raw ~extra_fn ~pinned:(Some pinned))
    in
    let joint_ordinary =
      lazy
        (joint_observed
           ~raw:(Lazy.force read.CounterPlays.raw_problem)
           ~extra_fn:Map.Poly.empty ~pinned:None)
    in
    let steered = match config.refine_rankings with
      | Config.Joint_steered _ -> true
      | Config.Separate | Config.Joint_guided -> false
    in
    let joint_sources =
      if steered then
        if SteerAudit.mutant_is SteerAudit.Generalised_source then
          [ ("lifted", joint_lifted) ]
        else [ ("ordinary", joint_ordinary) ]
      else [ ("lifted", joint_lifted); ("ordinary", joint_ordinary) ]
    in
    let force_source (source, lz) =
      try Lazy.force lz
      with exn when not (Common.Timer.is_async exn) ->
        Debug.print
        @@ lazy
             (sprintf "## the joint selection's %s clauses failed (%s)"
                source (Exn.to_string exn));
        None
    in
    (* [joint_pair_names ~kids ~roots ~orig_of target]: the chain pairs of
       the copy tree ([kids] each copy's premises' copies, [roots] the
       query's) for the ranked predicate [target], as pairs of copy names:
       two visits of [target] on one path with no visit of a predicate ranked
       below it between them, as [chain_pairs_of] reads them on the play,
       without the revisit cut. *)
    let joint_pair_names ~kids ~roots ~orig_of target =
      let target_index = Hashtbl.find pred_index target in
      let module N = struct
        type t = { name : string; mutable kids : t list }
      end in
      let nodes = Hashtbl.create (module String) in
      let rec node name =
        match Hashtbl.find nodes name with
        | Some n -> n
        | None ->
            let n = { N.name; kids = [] } in
            Hashtbl.set nodes ~key:name ~data:n;
            n.N.kids <- List.map (List.concat (kids name)) ~f:node;
            n
      in
      let root = { N.name = ""; kids = List.map roots ~f:node } in
      ChainPairs.pairs
        ~children:(fun n -> n.N.kids)
        ~hash:(fun n -> String.hash n.N.name)
        ~state_of:(fun n ->
          if String.(orig_of n.N.name = target) then Some n.N.name else None)
        ~resets:(fun n ->
          match
            (target_index, Hashtbl.find pred_index (orig_of n.N.name))
          with
          | Some ti, Some i -> i < ti
          | _ -> false)
        root
    in
    (* the ranking key a copy [key$N] was made from *)
    let ranking_key_of copy =
      Set.find orig_keys_wf ~f:(fun key ->
          String.is_prefix (Ident.name_of_tvar copy)
            ~prefix:(Ident.name_of_tvar key ^ "$"))
    in
    let joint_census_on () =
      Lazy.force JointWall.enabled
      || Option.is_some (Sys.getenv "COAR_MUSTRAT_JOINT_CENSUS")
    in
    (* [joint_select ~source ~data ~rankings ~pins ~against]: the selection
       on the observed clauses [data] (one of [joint_sources]) with the
       decrease of every chain pair under each fixed ranking of [rankings]
       (each [(key, ranked predicate, ranking)]) conjoined, the model asked
       first at the states [pins] gives a copy (the counter-play's own
       states, or a steered resolution's).
       Guarantees: [Some (sol, recorded)] only when [sol] passed the
       selection's validity check on the observed clauses, the selection's
       final model satisfies them and every stated pair's decrease, and
       [sol] also solves [against] ([SkolemTerms.satisfied_by]: with the key
       copies set to [sol], some values of [against]'s own Skolem constants
       satisfy every formula), the acceptance guard an ordinary selection
       meets.  Under [Joint_steered] moreover every chain pair of every
       ranking is stated (none left out for want of a visit's state), and
       [recorded] is, per ranking key, the ground chain pairs of the play at
       the model the selection started from and at the model it ended at,
       both contained in the key's ranking (the decrease held at both);
       otherwise [recorded] is empty.
       Effects: the trace and [selected_extra_rows] (the selection's). *)
    let joint_select ~source ~data ~rankings ~pins ~against ?origin_of ?snap
        () =
      let open LogicOld in
      let jp, observers, kids, roots, orig_of, _ground, pinned = data in
      let obs_copy = Hashtbl.create (module String) in
      Hashtbl.iteri observers ~f:(fun ~key ~data:(v, _) ->
          Hashtbl.set obs_copy ~key:(Ident.name_of_tvar v) ~data:key);
      let named =
        List.map rankings ~f:(fun (key, target, lam) ->
            (key, lam, joint_pair_names ~kids ~roots ~orig_of target))
      in
      let state_of_copy observed name =
        Option.bind (Hashtbl.find observers name) ~f:(fun (v, _) ->
            List.Assoc.find observed v ~equal:Ident.tvar_equal)
      in
      let n_pairs = ref 0 and n_unstated = ref 0 in
      let dec observed =
        n_pairs := 0;
        n_unstated := 0;
        Formula.and_of
        @@ List.concat_map named ~f:(fun (_, lam, names) ->
            List.filter_map names ~f:(fun (v, w) ->
                match (state_of_copy observed v, state_of_copy observed w) with
                | Some sv, Some sw -> (
                    match JointWall.ranking_at lam (sv @ sw) with
                    | Some phi ->
                        incr n_pairs;
                        Some phi
                    | None ->
                        incr n_unstated;
                        None)
                | _ ->
                    incr n_unstated;
                    None))
      in
      let at_m observed =
        Formula.and_of
        @@ List.concat_map observed ~f:(fun (v, state) ->
            match
              Option.bind (Hashtbl.find obs_copy (Ident.name_of_tvar v)) ~f:pins
            with
            | Some ts when List.length ts >= List.length state ->
                List.map2_exn state
                  (List.drop ts (List.length ts - List.length state))
                  ~f:Formula.eq
            | _ -> [])
      in
      let recorded = ref None in
      let joint =
        {
          SkolemTerms.observer =
            (fun x -> Hashtbl.mem obs_copy (Ident.name_of_tvar x));
          dec;
          at_m;
          record =
            (if steered then
               Some (fun ~start ~moved -> recorded := Some (start, moved))
             else None);
        }
      in
      Debug.print
      @@ lazy
           (sprintf
              "## the joint selection on the %s clauses (%d visit(s) \
               observed, the ranking of %d copy fixed):\n\
               %s\n"
              source (Hashtbl.length observers) (List.length rankings)
              (PCSP.Problem.str_of jp));
      let r =
        match pinned with
        | None -> select_skolem_solution ?origin_of ?snap ~joint jp
        | Some pinned ->
            select_skolem_solution ?origin_of ?snap ~joint
              ~pinned:(Map.Poly.find pinned)
              ~eq_result:(Config.frees_goal config.refine_counter_play)
              jp
      in
      (* the acceptance guard, on the refinement problem itself *)
      let r =
        Option.bind r ~f:(fun sol ->
            let ok =
              try SkolemTerms.satisfied_by against sol
              with exn when not (Common.Timer.is_async exn) -> false
            in
            if not ok then
              Debug.print
              @@ lazy
                   "## the joint answer not checked on the refinement \
                    problem; the ordinary dispatch";
            if ok then Some sol else None)
      in
      (* [Joint_steered]: every pair stated, and the play's pairs at the
         start and at the end of the selection, read off the observed
         states *)
      let r =
        if not steered then Option.map r ~f:(fun sol -> (sol, []))
        else
          Option.bind r ~f:(fun sol ->
              match !recorded with
              | _ when !n_unstated > 0 ->
                  Debug.print
                  @@ lazy
                       (sprintf
                          "## the steered answer left %d chain pair(s) \
                           unstated; not used"
                          !n_unstated);
                  None
              | None -> None
              | Some (start, moved) -> (
                  let ground_of states name =
                    Option.bind (Hashtbl.find observers name) ~f:(fun (v, _) ->
                        List.Assoc.find states v ~equal:Ident.tvar_equal)
                  in
                  let pairs_at states names =
                    Option.all
                    @@ List.map names ~f:(fun (v, w) ->
                        match (ground_of states v, ground_of states w) with
                        | Some a, Some b -> Some (a, b)
                        | _ -> None)
                  in
                  match
                    Option.all
                    @@ List.map named ~f:(fun (key, lam, names) ->
                        match (pairs_at start names, pairs_at moved names) with
                        | Some ps, Some qs ->
                            Some (key, lam, ps, qs)
                        | _ -> None)
                  with
                  | None -> None
                  | Some per_key ->
                      SteerAudit.answer ~source
                        ~own:(fun () ->
                          (* the moved states and [sol] as one resolution of
                             the check's own clauses, the observers matched
                             by the copy they observe *)
                          match force_source ("ordinary", joint_ordinary) with
                          | None -> None
                          | Some (own_jp, own_obs, _, _, _, _, _) ->
                              Option.map
                                (Option.all
                                   (List.map moved ~f:(fun (v, ts) ->
                                        Option.bind
                                          (Hashtbl.find obs_copy
                                             (Ident.name_of_tvar v))
                                          ~f:(fun copy ->
                                            Option.map
                                              (Hashtbl.find own_obs copy)
                                              ~f:(fun (v', _) -> (v', ts))))))
                                ~f:(fun states ->
                                  SkolemTerms.resolution_at own_jp ~states sol))
                        ~contained:(fun () ->
                          List.for_all per_key ~f:(fun (_, lam, _, qs) ->
                              List.for_all qs ~f:(ranking_contains lam)))
                        (List.map per_key ~f:(fun (key, _, _, qs) ->
                             (Ident.name_of_tvar key, qs)));
                      Some
                        ( sol,
                          List.map per_key ~f:(fun (key, _, ps, qs) ->
                              ( key,
                                List.dedup_and_sort ~compare:Stdlib.compare
                                  (ps @ qs) )) )))
      in
      (r, !n_pairs, !n_unstated)
    in
    (* [record_joint_pairs recorded]: [Joint_steered]'s recording, the pairs
       of the joint answer's own play joined to what this refinement asks of
       each key ([last_asked]), so that, once the refinement is accepted,
       they join the pairs every later ranking of the key must contain
       ([wf_rank_pairs]).  ([SteerAudit]'s test mutant records nothing.) *)
    let record_joint_pairs recorded =
      if not (SteerAudit.mutant_is SteerAudit.Drop_record) then
        List.iter recorded ~f:(fun (key, pairs) ->
            if not (List.is_empty pairs) then
              last_asked := (key, pairs) :: !last_asked)
    in
    (* [joint_selection ?origin_of ?snap pfwcsp]: under [refine_rankings =
       Joint_guided] or [Joint_steered], when every ranking copy of [pfwcsp]
       (the problem the last build made) was solved by the build itself
       ([presolved], the ranking fixed before the terms), the Skolem keys
       selected on the counter-play's clauses with the decrease of every
       chain pair under those rankings conjoined ([joint_select]), the model
       asked at the counter-play's own states first.
       Guarantees: [Some sol] passed [joint_select]'s checks; under
       [Joint_steered] the answer's own pairs have been added to
       [last_asked]; [None] when the field is [Separate], a ranking copy is
       not presolved, the clauses hold no ranked visit, or the selection
       declines, and the dispatcher continues as under [Separate].
       Effects: the trace, one census line under [COAR_MUSTRAT_JOINT_WALL]
       or [COAR_MUSTRAT_JOINT_CENSUS] (the line alone, no instrument);
       the build's bookkeeping is restored after the observed build. *)
    let joint_selection ?origin_of ?snap pfwcsp =
      match config.refine_rankings with
      | Config.Separate -> None
      | Config.Joint_guided | Config.Joint_steered _ -> (
          let senv = PCSP.Problem.senv_of pfwcsp in
          let pre = !presolved in
          let non_fn =
            Map.Poly.keys senv
            |> List.filter ~f:(fun x ->
                   not (Kind.is_fn (PCSP.Problem.kind_of pfwcsp x)))
          in
          let census outcome =
            if joint_census_on () then
              eprintf "mustrat-joint-%s: %s\n%!"
                (if steered then "steered" else "guided")
                outcome
          in
          (* per presolved copy: its key, the key's ranked predicate and the
             ranking; under [Joint_steered] every copy must have them, since
             a ranking left out of the decrease would be installed without
             its pairs being stated *)
          let rankings =
            List.map pre ~f:(fun (copy, lam) ->
                Option.bind (ranking_key_of copy) ~f:(fun key ->
                    Option.map (rank_target_of key) ~f:(fun t -> (key, t, lam))))
          in
          let rankings =
            if steered then Option.all rankings
            else Some (List.filter_map rankings ~f:Fn.id)
          in
          match rankings with
          | _
            when List.is_empty pre
                 || not
                      (List.for_all non_fn ~f:(fun x ->
                           List.exists pre ~f:(fun (c, _) ->
                               Ident.tvar_equal c x))) ->
              census "outcome=none reason=ranking-not-fixed";
              None
          | None ->
              census "outcome=none reason=ranking-not-read";
              None
          | Some rankings ->
              let against, _ = SkolemTerms.mentioned_only pfwcsp in
              List.find_map joint_sources ~f:(fun (source, lz) ->
                  match force_source (source, lz) with
                  | None ->
                      census
                        (sprintf "outcome=none source=%s reason=no-ranked-visit"
                           source);
                      None
                  | Some data -> (
                      let _, _, _, _, _, ground, _ = data in
                      let pins name =
                        Option.map (Map.Poly.find ground name)
                          ~f:
                            (List.map ~f:(fun t ->
                                 Logic.ExtTerm.to_old_term Map.Poly.empty
                                   Map.Poly.empty t []))
                      in
                      let r, n_pairs, n_unstated =
                        joint_select ~source ~data ~rankings ~pins ~against
                          ?origin_of ?snap ()
                      in
                      Option.iter r ~f:(fun (_, recorded) ->
                          record_joint_pairs recorded);
                      let _, observers, _, _, _, _, _ = data in
                      census
                        (sprintf
                           "outcome=%s source=%s pairs=%d unstated=%d \
                            observers=%d%s"
                           (if Option.is_some r then "gave" else "none")
                           source n_pairs n_unstated
                           (Hashtbl.length observers)
                           (match r with
                           | None -> ""
                           | Some (sol, recorded) ->
                               (if steered then
                                  sprintf " recorded=%d"
                                    (List.sum (module Int) recorded
                                       ~f:(fun (_, ps) -> List.length ps))
                                else "")
                               ^ " terms="
                               ^ String.concat_map_list ~sep:"; "
                                   (Map.Poly.to_alist sol) ~f:(fun (k, t) ->
                                     Ident.name_of_tvar k ^ ":="
                                     ^ Logic.ExtTerm.str_of t)));
                      Option.map r ~f:fst)))
    in

    (* Boundary 5, the dispatcher over the refinement's seams, for the
       problem [pfwcsp] the last build made (the copies it presolved are
       [solve_refinement]'s): [refine_terms] chooses between the constraint
       solver alone ([Terms_pcsat]) and selection ([Terms_select], boundary
       3) with the constraint solver as the fallback, the problem split into
       its Skolem and ranking parts first under [split_mixed]; [refine_guards]
       is read here as the grouping [origin_of] that boundary 4 combines
       ([Separation]) or its absence ([Unguarded]); [refine_counter_play]
       is read by the lifted selection; [refine_rankings] was read by the
       build ([rank_demand]).
       Guarantees: an [Ok (Sat sol, _)] is the constraint solver's answer, a
       checked selection (boundary 3's guarantee), or under the split the
       union of a checked selection of the Skolem part and the constraint
       solver's answer of the ranking part, which share no unknown.
       Effects: [last_certs] reset, then set by the constraint solver's call
       when it records certificates; [selected_extra_rows] emptied when a
       split's ranking part fails, since those rows belong to an answer not
       returned. *)
    let solve_refinement_unpresolved pfwcsp =
    last_certs := Map.Poly.empty;
    (*if verbose then*)
    Debug.print
    @@ lazy
         (sprintf "## pfwCSP for ranking and Skolem function synthesis:\n%s\n"
         @@ PCSP.Problem.str_of pfwcsp);
      match config.refine_terms with
      | Terms_select { split_mixed; _ } -> (
        (* the guard seam's grouping: the key a copy was made from, by the
           naming rule the solution is read back with below; a copy matching
           no key, or more than one, is not grouped *)
        let origin_of =
          if
            match config.refine_guards with
            | Separation | Cav24_sound -> true
            | Unguarded -> false
          then
            Some
              (fun x ->
                match
                  Set.to_list
                  @@ Set.filter (Set.union orig_keys_wf orig_keys_fn)
                       ~f:(fun key ->
                         String.is_prefix (Ident.name_of_tvar x)
                           ~prefix:(Ident.name_of_tvar key ^ "$"))
                with
                | [ key ] when Set.mem orig_keys_fn key -> Some key
                | _ -> None)
          else None
        in
        (* [select_snap_constant_keys]: for a copy, the closed results of the
           terms its opponent key holds, so that an argument-free copy can
           take one of them again (the copy-to-key rule as above) *)
        let snap =
          if config.select_snap_constant_keys then
            Some
              (fun x ->
                match
                  Set.to_list
                  @@ Set.filter orig_keys_fn ~f:(fun key ->
                         String.is_prefix (Ident.name_of_tvar x)
                           ~prefix:(Ident.name_of_tvar key ^ "$"))
                with
                | [ key ] ->
                    let args, terms = Map.Poly.find_exn dual_strat_fn key in
                    Some
                      (List.filter_map (Set.to_list terms)
                         ~f:(SnapConstants.closed_result args))
                | _ -> None)
          else None
        in
        let all_fn =
          Map.Poly.for_alli (PCSP.Problem.senv_of pfwcsp) ~f:(fun ~key ~data:_ ->
              Kind.is_fn (PCSP.Problem.kind_of pfwcsp key))
        in
        match
          match joint_selection ?origin_of ?snap pfwcsp with
          | Some sol -> Some sol
          | None -> select_terms ?origin_of ?snap ~lifted_first:all_fn pfwcsp
        with
        | Some sol -> Result.Ok (PCSP.Problem.Sat sol, 0)
        | None -> (
            match
              if split_mixed then
                split_mixed_refinement pfwcsp
              else None
            with
            | None -> solve pfwcsp
            | Some (skolem_part, ranking_part) -> (
                match
                  select_terms ?origin_of ?snap ~lifted_first:true skolem_part
                with
                | None -> solve pfwcsp
                | Some sol_skolem -> (
                    match solve ranking_part with
                    | Result.Ok (PCSP.Problem.Sat sol_ranking, n) ->
                        Debug.print
                        @@ lazy
                             "## the refinement split: Skolem terms by \
                              selection, rankings by PCSat";
                        Result.Ok
                          ( PCSP.Problem.Sat
                              (Map.force_merge sol_skolem sol_ranking),
                            n )
                    | _ ->
                        Debug.print
                        @@ lazy
                             "## the ranking part of the split refinement \
                              was not solved; asking PCSat for the whole";
                        (* the rows were found for the selection's answer,
                           which is not the one returned *)
                        selected_extra_rows := [];
                        solve pfwcsp))))
      | Terms_pcsat -> solve pfwcsp
    in
    (* [solve_refinement pfwcsp]: the refinement [pfwcsp] the last build made,
       solved, with the copies that build solved itself ([presolved], the
       ranking seam's candidates) set to their solutions.  A problem left
       with no constraint at all is answered by those solutions alone;
       otherwise the dispatcher ([solve_refinement_unpresolved]) solves it
       and the presolved copies, which no constraint mentions, are
       overwritten in its answer.  Without presolved copies, exactly the
       dispatcher's answer.  Effects: [selected_extra_rows] emptied first, so
       only rows found while solving this problem are read back. *)
    let solve_refinement pfwcsp =
      (* only rows found while solving this problem are read back *)
      selected_extra_rows := [];
      match !presolved with
      | [] -> solve_refinement_unpresolved pfwcsp
      | pre ->
          let set sol =
            List.fold pre ~init:sol ~f:(fun sol (copy, lam) ->
                Map.Poly.set sol ~key:copy ~data:lam)
          in
          if Set.is_empty (PCSP.Problem.formulas_of pfwcsp) then (
            last_certs := Map.Poly.empty;
            Result.Ok (PCSP.Problem.Sat (set Map.Poly.empty), 0))
          else
            match solve_refinement_unpresolved pfwcsp with
            | Result.Ok (PCSP.Problem.Sat sol, n) ->
                Result.Ok (PCSP.Problem.Sat (set sol), n)
            | r -> r
    in
    let first_plays = Option.to_list play in
    (* [wf_attempts plays]: the re-synthesis attempts over [plays], over the
       regions first and then over the ground chain pairs, each bounded by
       [solve_wf]; [Some] the first that succeeds, [None] when neither does
       (or neither applies). *)
    let wf_attempts plays =
      (* The generalised attempt: the re-synthesis problem with each key's
         regions added.  Skipped when it would add no region clause, since it
         would then be the plain attempt below asked twice. *)
      let gen_attempt =
        if
          config.resynthesise_wf_rankings
          && (config.generalise_chain_pairs || config.chain_pair_regions_by_mbp)
        then (
          let pfwcsp =
            build_pfwcsp ~wf_mode:true ~generalise:true plays
          in
          if Set.is_empty !last_wf_copies || !last_region_clauses = 0 then None
          else
            match solve_refinement pfwcsp with
            | Result.Ok (PCSP.Problem.Sat _, _) as result ->
                Debug.print
                @@ lazy
                     (sprintf
                        "## re-synthesis over %d region clause(s) succeeded"
                        !last_region_clauses);
                Some (pfwcsp, result)
            | _ ->
                Debug.print
                @@ lazy
                     "## re-synthesis over the regions did not succeed; \
                      asking it over the ground chain pairs";
                None)
        else None
      in
      let wf_attempt =
        if Option.is_some gen_attempt then gen_attempt
        else if config.resynthesise_wf_rankings then (
          let pfwcsp = build_pfwcsp ~wf_mode:true plays in
          if Set.is_empty !last_wf_copies then None
          else
            match solve_refinement pfwcsp with
            | Result.Ok (PCSP.Problem.Sat _, _) as result ->
                Some (pfwcsp, result)
            | _ ->
                Debug.print
                @@ lazy
                     "## re-synthesis as WF relations did not succeed";
                None)
        else None
      in
      wf_attempt
    in
    (* [first_play_wf_resynthesis]: the re-synthesis attempts over the first
       play alone, asked when those over every play fail, before the disjoined
       form.  The further plays are found by blocking the first play's exits,
       so they may take moves of the ranked side the first play did not, and
       their pairs together may admit no ranking at all while the first
       play's alone do.  A refinement only selects the next strategy, so this
       changes no answer rule. *)
    let pfwcsp, result =
      match wf_attempts (first_plays @ extra_plays) with
      | Some r -> r
      | None -> (
          let first_alone =
            if
              FirstPlayWf.asks ~enabled:config.first_play_wf_resynthesis
                ~resynthesise:config.resynthesise_wf_rankings
                ~first_plays:(List.length first_plays)
                ~extra_plays:(List.length extra_plays)
                ~wf_copies:(Set.length !last_wf_copies)
            then (
              Debug.print
              @@ lazy
                   "## re-synthesis over all the counter-plays did not \
                    succeed; asking it over the first play alone";
              (* one stderr line per firing, for a census of where the field
                 acts; nothing without the variable *)
              if Option.is_some (Sys.getenv "COAR_MUSTRAT_FIRST_PLAY_CENSUS")
              then eprintf "mustrat-first-play: asked\n%!";
              let r = wf_attempts first_plays in
              if
                Option.is_some r
                && Option.is_some (Sys.getenv "COAR_MUSTRAT_FIRST_PLAY_CENSUS")
              then eprintf "mustrat-first-play: solved\n%!";
              r)
            else None
          in
          match first_alone with
          | Some r -> r
          | None ->
              Debug.print
              @@ lazy "## asking the refinement with disjoined pieces";
              let pfwcsp = build_pfwcsp (first_plays @ extra_plays) in
              (pfwcsp, solve_refinement pfwcsp))
    in
    (* The extra plays only add chain pairs, and pairs from different plays
       can be more than one ranking covers (the checked side's strategy may
       let the plays cycle through each other's states).  So a refinement
       that does not succeed with them is asked again with the first play's
       pairs alone -- exactly the problem built with no extra play -- and the
       extra plays can never be the reason a refinement fails. *)
    let pfwcsp, result =
      match result with
      | Result.Ok (PCSP.Problem.Sat _, _) -> (pfwcsp, result)
      | _ when List.is_empty extra_plays || List.is_empty first_plays ->
          (pfwcsp, result)
      | _ ->
          Debug.print
          @@ lazy
               "## refinement with the extra counter-plays did not succeed; \
                asking again with the first play alone";
          let pfwcsp = build_pfwcsp first_plays in
          (pfwcsp, solve_refinement pfwcsp)
    in
    (* [refine_rankings = Joint_steered k]: a refinement every form above
       failed to solve is steered: the steered refinement that records its
       own play, selecting on the check's own clauses only.  The
       build over the first play with the re-synthesis's demand
       ([wf_mode]: per key, the pairs accepted refinements asked and the
       played pairs) is made once more for its bookkeeping and its Skolem
       part; each ranking copy the build could not fix (no ranking it
       builds contains the played pairs) is steered:
       - a resolution of the check's own clauses is asked
         ([SkolemTerms.observed_resolution]: every key's result free) in
         which no chain pair joins two equal states (no irreflexive relation
         contains such a pair), every fixed ranking decreases on its pairs,
         and the visit states differ from the played ones and from every
         resolution tried before;
       - for each steered key a ranking is built ([rank_candidate]) over the
         pairs accepted refinements asked of it and the regions stored for
         it, with that resolution's own pairs added; a ranking it returns
         contains all of them ([order_covers]);
       - the joint selection ([joint_select]) is asked with those rankings
         and the model pinned at the resolution's states first.
       The first resolution for which both succeed is the answer: its
       rankings are installed as built here (as presolved copies, each
       replacing its key's ranking, which it may, since it contains every
       pair and region asked of the key), its terms as selected, and what
       the refinement asks of a steered key is the selection's own play's
       pairs (at the model it started from and the model it ended at) in
       place of the played pairs, which the ranking need not contain.  At
       most [k] resolutions are asked.
       Guarantees: [Some (pfwcsp, Ok (Sat sol, 0))] only with every ranking
       of [sol] a template instance containing the key's whole recorded
       demand together with this answer's own pairs, and the terms passing
       the acceptance guard [joint_select] states on the problem's Skolem
       part; [None] otherwise, with the build's bookkeeping restored. *)
    let steer k =
      let saved =
        ( !last_asked,
          !last_wf_copies,
          !last_regions,
          !last_region_clauses,
          !presolved )
      in
      let restore () =
        let a, b, c, d, e = saved in
        last_asked := a;
        last_wf_copies := b;
        last_regions := c;
        last_region_clauses := d;
        presolved := e
      in
      let census outcome =
        if joint_census_on () then
          eprintf "mustrat-joint-steered: steer %s\n%!" outcome
      in
      let decline reason =
        census ("outcome=none reason=" ^ reason);
        restore ();
        None
      in
      let pfwcsp = build_pfwcsp ~wf_mode:true first_plays in
      let pre = !presolved in
      let is_rank x = not (Kind.is_fn (PCSP.Problem.kind_of pfwcsp x)) in
      let rank_copies =
        List.filter (Map.Poly.keys (PCSP.Problem.senv_of pfwcsp)) ~f:is_rank
      in
      let failed =
        List.filter rank_copies ~f:(fun c ->
            not (List.exists pre ~f:(fun (c', _) -> Ident.tvar_equal c c')))
      in
      let read_copy copy =
        Option.bind (ranking_key_of copy) ~f:(fun key ->
            if has_derivation_copy key then None
            else Option.map (rank_target_of key) ~f:(fun t -> (copy, key, t)))
      in
      if List.is_empty failed then decline "no-failed-ranking"
      else
        match
          ( Option.all (List.map failed ~f:read_copy),
            Option.all
              (List.map pre ~f:(fun (copy, lam) ->
                   Option.map (read_copy copy) ~f:(fun (_, key, t) ->
                       (key, t, lam)))) )
        with
        | None, _ | _, None -> decline "ranking-not-read"
        | Some failed, Some fixed -> (
            match
              force_source
                (if SteerAudit.mutant_is SteerAudit.Generalised_source then
                   ("lifted", joint_lifted)
                 else ("ordinary", joint_ordinary))
            with
            | None -> decline "no-ranked-visit"
            | Some data -> (
                let source =
                  if SteerAudit.mutant_is SteerAudit.Generalised_source then
                    "lifted"
                  else "ordinary"
                in
                let jp, observers, kids, roots, orig_of, ground, _ = data in
                let open LogicOld in
                let obs_copy = Hashtbl.create (module String) in
                Hashtbl.iteri observers ~f:(fun ~key ~data:(v, _) ->
                    Hashtbl.set obs_copy ~key:(Ident.name_of_tvar v) ~data:key);
                let observer x = Hashtbl.mem obs_copy (Ident.name_of_tvar x) in
                let names_of target = joint_pair_names ~kids ~roots ~orig_of target in
                let fixed_named =
                  List.map fixed ~f:(fun (_, t, lam) -> (lam, names_of t))
                in
                let failed_named =
                  List.map failed ~f:(fun (copy, key, t) ->
                      (copy, key, t, names_of t))
                in
                let all_names =
                  List.concat_map fixed_named ~f:snd
                  @ List.concat_map failed_named ~f:(fun (_, _, _, ns) -> ns)
                in
                let state_of_copy observed name =
                  Option.bind (Hashtbl.find observers name) ~f:(fun (v, _) ->
                      List.Assoc.find observed v ~equal:Ident.tvar_equal)
                in
                (* the observed states equal, copy by copy, to the ground
                   states [pins] gives *)
                let at observed pins =
                  Formula.and_of
                  @@ List.concat_map observed ~f:(fun (v, state) ->
                      match
                        Option.bind
                          (Hashtbl.find obs_copy (Ident.name_of_tvar v))
                          ~f:pins
                      with
                      | Some ts when List.length ts >= List.length state ->
                          List.map2_exn state
                            (List.drop ts (List.length ts - List.length state))
                            ~f:Formula.eq
                      | _ -> [])
                in
                let played name =
                  Option.map (Map.Poly.find ground name)
                    ~f:
                      (List.map ~f:(fun t ->
                           Logic.ExtTerm.to_old_term Map.Poly.empty
                             Map.Poly.empty t []))
                in
                let extra tried observed =
                  Formula.and_of
                    ((* no chain pair joins two equal states *)
                     List.filter_map all_names ~f:(fun (v, w) ->
                         match
                           (state_of_copy observed v, state_of_copy observed w)
                         with
                         | Some sv, Some sw when List.length sv = List.length sw
                           ->
                             Some
                               (Formula.mk_neg
                                  (Formula.and_of (List.map2_exn sv sw ~f:Formula.eq)))
                         | _ -> None)
                    @ (* every fixed ranking decreases on its pairs *)
                    List.concat_map fixed_named ~f:(fun (lam, names) ->
                        List.filter_map names ~f:(fun (v, w) ->
                            match
                              (state_of_copy observed v, state_of_copy observed w)
                            with
                            | Some sv, Some sw -> JointWall.ranking_at lam (sv @ sw)
                            | _ -> None))
                    @ (* away from the played states and those tried *)
                    List.map (played :: tried) ~f:(fun pins ->
                        let phi = at observed pins in
                        if Formula.is_true phi then Formula.mk_true ()
                        else Formula.mk_neg phi))
                in
                let against =
                  fst
                  @@ SkolemTerms.mentioned_only
                  @@ PCSP.Problem.of_formulas
                       ~params:
                         {
                           (PCSP.Problem.params_of pfwcsp) with
                           PCSP.Params.stable_clauses = Set.Poly.empty;
                         }
                       (Set.filter (PCSP.Problem.formulas_of pfwcsp)
                          ~f:(fun (_, t) ->
                            not
                              (Set.exists (Logic.Term.fvs_of t) ~f:(fun x ->
                                   List.mem rank_copies x ~equal:Ident.tvar_equal))))
                in
                let rec loop i tried =
                  if i > k then decline (sprintf "tried=%d" (i - 1))
                  else
                    match
                      SkolemTerms.observed_resolution ~observer
                        ~extra:(extra tried) jp
                    with
                    | None -> decline (sprintf "no-resolution tried=%d" (i - 1))
                    | Some states -> (
                        let by_copy =
                          Hashtbl.create (module String)
                        in
                        List.iter states ~f:(fun (v, ts) ->
                            Option.iter
                              (Hashtbl.find obs_copy (Ident.name_of_tvar v))
                              ~f:(fun copy -> Hashtbl.set by_copy ~key:copy ~data:ts));
                        let pins = Hashtbl.find by_copy in
                        let candidate (copy, key, t, names) =
                          match
                            Option.all
                              (List.map names ~f:(fun (v, w) ->
                                   match (pins v, pins w) with
                                   | Some a, Some b -> Some (a, b)
                                   | _ -> None))
                          with
                          | None -> None
                          | Some own ->
                              let name = Ident.name_of_tvar key in
                              let pairs =
                                Option.value ~default:[]
                                  (Hashtbl.find wf_rank_pairs name)
                                @ own
                                |> List.dedup_and_sort ~compare:Stdlib.compare
                              in
                              if pairs_cyclic pairs then None
                              else
                                let args, _ =
                                  Logic.Term.let_lam
                                    (Map.Poly.find_exn dual_strat_wf key)
                                in
                                let stored =
                                  Option.value ~default:[]
                                    (Hashtbl.find wf_rank_regions name)
                                in
                                last_wf_copies := Set.add !last_wf_copies copy;
                                let d =
                                  {
                                    rd_key = key;
                                    rd_args = args;
                                    rd_copy = copy;
                                    rd_pairs = pairs;
                                    rd_sort =
                                      Logic.Sort.mk_fun
                                        (List.map args ~f:snd
                                        @ [ Logic.BoolTerm.SBool ]);
                                    rd_facts = Set.Poly.empty;
                                    rd_regions =
                                      (if List.is_empty stored then None
                                       else
                                         Some
                                           {
                                             rg_stored = stored;
                                             rg_fresh = [];
                                             rg_uncertified =
                                               List.filter stored
                                                 ~f:(fun (_, _, cert) ->
                                                   Option.is_none cert);
                                           });
                                  }
                                in
                                Option.map (rank_candidate ~wf_mode:true d).rc_ranking
                                  ~f:(fun lam -> (copy, key, t, lam))
                        in
                        match Option.all (List.map failed_named ~f:candidate) with
                        | None ->
                            census (sprintf "resolution=%d ranking=none" i);
                            loop (i + 1) (pins :: tried)
                        | Some built -> (
                            let rankings =
                              fixed
                              @ List.map built ~f:(fun (_, key, t, lam) ->
                                  (key, t, lam))
                            in
                            let r, _, _ =
                              joint_select ~source ~data ~rankings ~pins ~against
                                ()
                            in
                            match r with
                            | None ->
                                census (sprintf "resolution=%d selection=none" i);
                                loop (i + 1) (pins :: tried)
                            | Some (sol, recorded) ->
                                let steered_keys =
                                  List.map built ~f:(fun (_, key, _, _) -> key)
                                in
                                let is_steered key =
                                  List.mem steered_keys key ~equal:Ident.tvar_equal
                                in
                                (* the played pairs are not this answer's
                                   demand for a steered key; its own play's
                                   are *)
                                last_asked :=
                                  List.filter !last_asked ~f:(fun (key, _) ->
                                      not (is_steered key));
                                last_regions :=
                                  List.filter !last_regions ~f:(fun (key, _) ->
                                      not (is_steered key));
                                record_joint_pairs recorded;
                                presolved :=
                                  List.map built ~f:(fun (copy, _, _, lam) ->
                                      (copy, lam))
                                  @ pre;
                                last_certs := Map.Poly.empty;
                                census
                                  (sprintf
                                     "outcome=gave resolution=%d recorded=%d \
                                      terms=%s"
                                     i
                                     (List.sum (module Int) recorded
                                        ~f:(fun (_, ps) -> List.length ps))
                                     (String.concat_map_list ~sep:"; "
                                        (Map.Poly.to_alist sol) ~f:(fun (x, t) ->
                                          Ident.name_of_tvar x ^ ":="
                                          ^ Logic.ExtTerm.str_of t)));
                                Some
                                  ( pfwcsp,
                                    Result.Ok
                                      ( PCSP.Problem.Sat
                                          (List.fold !presolved ~init:sol
                                             ~f:(fun sol (copy, lam) ->
                                               Map.Poly.set sol ~key:copy
                                                 ~data:lam)),
                                        0 ) )))
                in
                try loop 1 []
                with exn when not (Common.Timer.is_async exn) ->
                  decline ("raised " ^ Exn.to_string exn)))
    in
    let pfwcsp, result =
      match (result, config.refine_rankings) with
      | Result.Ok (PCSP.Problem.Sat _, _), _ -> (pfwcsp, result)
      | _, Config.Joint_steered k
        when (not (List.is_empty first_plays)) && config.resynthesise_wf_rankings
        -> (
          match steer k with Some r -> r | None -> (pfwcsp, result))
      | _ -> (pfwcsp, result)
    in
    match result with
    | Result.Ok (PCSP.Problem.Sat sol, _) ->
        if config.check_refinement_kinds then
          (* a presolved copy has no certificate and no constraint in
             [pfwcsp]; its order is well-founded by construction *)
          check_refinement_kinds pfwcsp
            (List.fold !presolved ~init:sol ~f:(fun sol (copy, _) ->
                 Map.Poly.remove sol copy))
            ~certs:!last_certs;
        (* [last_regions] is non-empty only when the problem solved is the
           generalised one, since every later build resets it. *)
        List.iter !last_regions ~f:(fun (key, regions) ->
            if not (List.is_empty regions) then
              Hashtbl.update wf_rank_regions (Ident.name_of_tvar key)
                ~f:(fun old -> Option.value ~default:[] old @ regions));
        if config.resynthesise_wf_rankings then
          List.iter !last_asked ~f:(fun (key, pairs) ->
              Hashtbl.update wf_rank_pairs (Ident.name_of_tvar key)
                ~f:(fun old ->
                  Option.value ~default:[] old @ pairs
                  |> ChainPairs.dedup_and_sort));
        (* [resynthesise_only_on_new_pairs]: the ranking keys whose ranking
           is kept as it is, because every chain pair this refinement asked
           of the key evaluates to true in the current ranking.
           Postcondition: a key outside this set is refined as without the
           field; a key inside it keeps its term, and with it its record in
           [wf_by_construction], and still contains every pair asked of it
           (those were just added to [wf_rank_pairs]), so the ranking still
           covers every pair any accepted refinement has asked.  A key that
           was asked no pair is never kept. *)
        let kept_rankings =
          if
            config.resynthesise_wf_rankings
            && config.resynthesise_only_on_new_pairs
          then
            Map.Poly.key_set dual_strat_wf
            |> Set.filter ~f:(fun key ->
                let asked =
                  List.concat_map !last_asked ~f:(fun (k, pairs) ->
                      if Ident.tvar_equal k key then pairs else [])
                in
                (not (List.is_empty asked))
                && List.for_all asked
                     ~f:(ranking_contains (Map.Poly.find_exn dual_strat_wf key)))
          else Set.Poly.empty
        in
        (* Census (environment [COAR_MUSTRAT_RULEM_CENSUS]): one stderr line
           per read-back with the field's value, the keys asked a pair, the
           keys whose every asked pair the current ranking contains (those
           the field keeps, whether or not it is on) and the keys kept.  It
           reads only, so a run with it is the run without it. *)
        if rulem_census && config.resynthesise_wf_rankings then begin
          let asked_keys =
            Map.Poly.key_set dual_strat_wf
            |> Set.filter ~f:(fun key ->
                List.exists !last_asked ~f:(fun (k, pairs) ->
                    Ident.tvar_equal k key && not (List.is_empty pairs)))
          in
          let coverable =
            Set.filter asked_keys ~f:(fun key ->
                List.for_all
                  (List.concat_map !last_asked ~f:(fun (k, pairs) ->
                       if Ident.tvar_equal k key then pairs else []))
                  ~f:(ranking_contains (Map.Poly.find_exn dual_strat_wf key)))
          in
          let names s =
            Set.to_list s |> List.map ~f:Ident.name_of_tvar
            |> String.concat ~sep:","
          in
          eprintf
            "mustrat-rulem: field=%b asked=%d covered=%d kept=%d covered-keys=[%s]\n%!"
            config.resynthesise_only_on_new_pairs (Set.length asked_keys)
            (Set.length coverable) (Set.length kept_rankings) (names coverable)
        end;
        Set.iter kept_rankings ~f:(fun key ->
            Debug.print
            @@ lazy
                 (sprintf
                    "## every chain pair asked of %s is in its current ranking; the ranking is kept"
                    (Ident.name_of_tvar key)));
        let rev_ren =
          Map.Poly.mapi
            (Map.force_merge senv_problem
               (Map.Poly.filter (PCSP.Problem.senv_of pfwcsp) ~f:(fun _ -> true)
               (* a presolved copy is read back even if the problem, which
                  asks nothing of it, does not keep it declared *)
               |> (fun senv ->
               List.fold !presolved ~init:senv ~f:(fun senv (copy, _) ->
                   Map.Poly.set senv ~key:copy ~data:Logic.BoolTerm.SBool))
               |> Map.Poly.filter_keys ~f:(fun x ->
                   (not (Map.Poly.mem senv_problem x))
                   && Set.exists orig_keys_wf ~f:(fun key ->
                       String.is_prefix (Ident.name_of_tvar x)
                         ~prefix:(Ident.name_of_tvar key ^ "$")))))
            ~f:(fun ~key:x ~data:_ ->
              Set.find_exn (Set.union orig_keys_wf orig_keys_fn) ~f:(fun key ->
                  String.is_prefix (Ident.name_of_tvar x)
                    ~prefix:(Ident.name_of_tvar key ^ "$")))
        in
        (* this read-back's number, for [joint_term_alternatives] *)
        incr joint_refinement_id;
        let joint_id = !joint_refinement_id in
        let strat =
        Map.Poly.fold rev_ren ~init:(dual_strat_wf, dual_strat_fn, dual_nu_wfs)
          ~f:(fun ~key ~data (dual_strat_wf, dual_strat_fn, dual_nu_wfs) ->
            match Map.Poly.find sol key with
            | None -> (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
            | Some _ when Set.mem kept_rankings data ->
                (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
            | Some _ ->
                if Set.mem orig_keys_wf data then (
                  let args, term =
                    Logic.Term.let_lam @@ Map.Poly.find_exn dual_strat_wf data
                  in
                  let piece =
                    Logic.ExtTerm.subst sol
                    @@ Logic.Term.mk_var_app key
                         (List.map args ~f:(fst >> Logic.Term.mk_var))
                  in
                  (* A copy declared [WF] holds every pair asked of the key so
                     far, so it replaces the ranking; any other copy is one
                     more piece of a union.  A presolved copy is declared
                     [WF] too, and its order is recorded as built by
                     construction on the same ground: it is the ranking
                     template's relation with one piece, a trivially true
                     discriminator and the certificate as lexicographic
                     components, or the two-piece instance the linear
                     programs build, well-founded for any coefficients.  (A
                     one-piece order is also transitive, so the transitivity
                     test would certify it without the record; a two-piece
                     one need not be.) *)
                  let replaces = Set.mem !last_wf_copies key in
                  let term' =
                    if replaces then piece else Logic.BoolTerm.or_of [ term; piece ]
                  in
                  Debug.print @@ lazy "## Refined the wf strategy of the side whose counter-play won the check:";
                  print_strat data args term';
                  let lam = Logic.Term.mk_lambda args term' in
                  if replaces then
                    Hashtbl.set wf_by_construction
                      ~key:(Ident.name_of_tvar data) ~data:lam
                  else Hashtbl.remove wf_by_construction (Ident.name_of_tvar data);
                  SteerAudit.install ~key:(Ident.name_of_tvar data)
                    ~contains:(ranking_contains lam)
                    ~demand:
                      (Option.value ~default:[]
                         (Hashtbl.find wf_rank_pairs (Ident.name_of_tvar data)));
                  ( Map.Poly.set dual_strat_wf ~key:data ~data:lam,
                    dual_strat_fn,
                    dual_nu_wfs ))
                else if Set.mem orig_keys_fn data then (
                  let args, terms = Map.Poly.find_exn dual_strat_fn data in
                  let fresh =
                    Logic.ExtTerm.subst sol
                    @@ Logic.Term.mk_var_app key
                         (List.map args ~f:(fst >> Logic.Term.mk_var))
                  in
                  if config.joint_term_alternatives then (
                    let name = Ident.name_of_tvar data in
                    if not (Hashtbl.mem joint_initial name) then
                      Hashtbl.set joint_initial ~key:name
                        ~data:(Set.to_list terms);
                    Hashtbl.update joint_refinements name ~f:(function
                      | Some ((r, ts) :: rest) when r = joint_id ->
                          (r, ts @ [ fresh ]) :: rest
                      | rs -> (joint_id, [ fresh ]) :: Option.value ~default:[] rs));
                  let terms' =
                    match config.skolem_term_window with
                    | None -> Set.add terms fresh
                    | Some n ->
                        (* the window: [fresh] first, then the key's earlier
                           terms newest first (the initial ones, in set
                           order, the oldest), cut at [n] *)
                        let name = Ident.name_of_tvar data in
                        let order =
                          match Hashtbl.find skolem_term_order name with
                          | Some order -> order
                          | None -> List.rev (Set.to_list terms)
                        in
                        let order =
                          SkolemTermWindow.update ~n
                            ~equal:(fun t1 t2 ->
                              try Stdlib.( = ) t1 t2
                              with exn when not (Common.Timer.is_async exn) ->
                                false)
                            order fresh
                        in
                        Hashtbl.set skolem_term_order ~key:name ~data:order;
                        if Set.length (Set.add terms fresh) > max 1 n then (
                          Debug.print
                          @@ lazy
                               (sprintf
                                  "## %s keeps its %d most recent term(s)"
                                  name (max 1 n));
                          (* one stderr line per firing, for a census of
                             where the window acts; nothing without the
                             variable *)
                          if
                            Option.is_some
                              (Sys.getenv "COAR_MUSTRAT_WINDOW_CENSUS")
                          then
                            eprintf "skolem-term-window fired %s\n%!" name);
                        Set.Poly.of_list order
                  in
                  Debug.print @@ lazy "## Refined the fn strategy of the side whose counter-play won the check:";
                  Set.iter terms' ~f:(print_strat data args);
                  ( dual_strat_wf,
                    Map.Poly.set dual_strat_fn ~key:data ~data:(args, terms'),
                    dual_nu_wfs ))
                else (dual_strat_wf, dual_strat_fn, dual_nu_wfs))
        in
        (* [select_initial_atom_rows]: each further row of the keys with no
           argument is read back as a refinement of its own, so that under
           [joint_term_alternatives] its values form one tuple of the class's
           offer rather than entering the product of the keys' terms within
           the refinement above.  A row only adds terms to term sets, the
           invariant the joint offer's monotonicity rests on.  Not read under
           [skolem_term_window], whose term lists keep a bounded number of
           terms that a row would push out. *)
        if Option.is_some config.skolem_term_window then strat
        else
          List.fold !selected_extra_rows ~init:strat
            ~f:(fun (dual_strat_wf, dual_strat_fn, dual_nu_wfs) row ->
              incr joint_refinement_id;
              let row_id = !joint_refinement_id in
              let dual_strat_fn =
                Map.Poly.fold row ~init:dual_strat_fn
                  ~f:(fun ~key ~data:_ dual_strat_fn ->
                    match Map.Poly.find rev_ren key with
                    | Some data when Set.mem orig_keys_fn data -> (
                        match Map.Poly.find dual_strat_fn data with
                        | None -> dual_strat_fn
                        | Some (args, terms) ->
                            let fresh =
                              Logic.ExtTerm.subst row
                              @@ Logic.Term.mk_var_app key
                                   (List.map args ~f:(fst >> Logic.Term.mk_var))
                            in
                            if config.joint_term_alternatives then (
                              let name = Ident.name_of_tvar data in
                              if not (Hashtbl.mem joint_initial name) then
                                Hashtbl.set joint_initial ~key:name
                                  ~data:(Set.to_list terms);
                              Hashtbl.update joint_refinements name ~f:(function
                                | Some ((r, ts) :: rest) when r = row_id ->
                                    (r, ts @ [ fresh ]) :: rest
                                | rs ->
                                    (row_id, [ fresh ])
                                    :: Option.value ~default:[] rs));
                            Debug.print
                            @@ lazy
                                 (sprintf
                                    "## Initial row %d of the dual fn strategy:"
                                    row_id);
                            print_strat data args fresh;
                            Map.Poly.set dual_strat_fn ~key:data
                              ~data:(args, Set.add terms fresh))
                    | _ -> dual_strat_fn)
              in
              (dual_strat_wf, dual_strat_fn, dual_nu_wfs))
    | Result.Ok (PCSP.Problem.Unsat _, _) -> raise NoRefinement
    | Result.Ok (PCSP.Problem.Timeout, _) when bound_last_refinement () ->
        (* every form tried before the last one either succeeded (and was
           returned above) or fell through, so a final [Timeout] is the last
           form's own expired budget *)
        Debug.print
        @@ lazy "## the last form of the refinement ran out of its budget";
        (* one stderr line per expiry, for a census in a plain run; nothing
           without the variable *)
        if Option.is_some (Sys.getenv "COAR_MUSTRAT_LASTREF_CENSUS") then
          eprintf "mustrat-lastref: expired\n%!";
        raise RefinementBudgetExpired
    | Result.Ok ((PCSP.Problem.(Unknown | Timeout) as sol), _) ->
        Debug.print @@ lazy (PCSP.Problem.str_of_sol_with_witness sol);
        (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
    | Result.Ok ((PCSP.Problem.OutSpace xs as sol), _) ->
        Debug.print @@ lazy (PCSP.Problem.str_of_sol_with_witness sol);
        refine_solspace
          (List.exists xs ~f:(Map.Poly.mem dual_strat_wf))
          (List.exists xs ~f:(Map.Poly.mem dual_strat_fn));
        (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
    | Result.Error _ ->
        Debug.print @@ lazy "error";
        (dual_strat_wf, dual_strat_fn, dual_nu_wfs (*failwith "refine_strat"*))

  let subst_strat primal_strat_wf primal_strat_fn (uni_senv, phi) =
    let uni_senv', phi' =
      if false then
        ( uni_senv,
          Logic.ExtTerm.subst
            (Map.Poly.map primal_strat_fn ~f:(fun (args, terms) ->
                 Logic.ExtTerm.mk_lambda args
                 @@ Logic.ExtTerm.or_of @@ Set.to_list terms))
          @@ Logic.ExtTerm.subst primal_strat_wf phi )
      else
        (* Keys are substituted outer ones first, and each copy renames apart
           the results of the key's applications and of the applications
           nested in them ([NestedKeys]). *)
        let phi0 = Logic.ExtTerm.subst primal_strat_wf phi in
        let keys = Map.Poly.keys primal_strat_fn in
        let heads =
          ChoiceScope.heads ~uni_senv
            ~is_key:(Map.Poly.mem primal_strat_fn)
            (Logic.ExtTerm.nnf_of phi0)
        in
        let inner = ClauseChoiceScope.inner_of_clause ~uni_senv
            ~is_key:(Map.Poly.mem primal_strat_fn) ~heads phi0 in
        List.fold (NestedKeys.order ~keys phi0) ~init:(uni_senv, phi0)
          ~f:(fun (uni_senv, phi) key ->
            let params, terms = Map.Poly.find_exn primal_strat_fn key in
            if Set.mem (Logic.ExtTerm.fvs_of phi) key then
              let rets = NestedKeys.rets_of key phi in
              let local = rets @ NestedKeys.nested_rets ~keys phi rets in
              (* with two terms or more, also the universals the choice may
                 not depend on ([ChoiceScope]) *)
              let local =
                if Set.length terms < 2 then local
                else
                  local
                  @ ChoiceScope.renamed ~inner ~keys:[ key ] ~all_keys:keys ~heads
                      ~outside:Set.Poly.empty ~local phi
              in
              let phi_fvs = Logic.ExtTerm.fvs_of phi in
              let uni_senvs, phis =
                List.unzip @@ Set.to_list
                @@ Set.Poly.map terms ~f:(fun term ->
                    (* The return variable is renamed into the clause's
                       universals, where [Map.rename_keys_map] overwrites any
                       entry of the same name, so the new name must be absent
                       from the clause's environment and from the free
                       variables of the formula and of the substituted term;
                       otherwise two universals of the clause would become
                       one. *)
                    let term_fvs = Logic.ExtTerm.fvs_of term in
                    let ren =
                      NestedKeys.renaming local ~taken:(fun v ->
                          Map.Poly.mem uni_senv v || Set.mem phi_fvs v
                          || Set.mem term_fvs v)
                    in
                    ChoiceScope.record ~inner ren;
                    let phi' =
                      Logic.ExtTerm.rename ren
                      @@ Logic.ExtTerm.subst
                           (Map.Poly.singleton key
                              (Logic.ExtTerm.mk_lambda params term))
                           phi
                    in
                    let uni_senv' = Map.rename_keys_map ren uni_senv in
                    if false then
                      Debug.print
                      @@ lazy
                           (sprintf "renamed: %s\n" (Logic.ExtTerm.str_of phi'));
                    (uni_senv', phi'))
              in
              (Map.force_merge_list uni_senvs, Logic.ExtTerm.or_of phis)
            else (uni_senv, phi))
    in
    if false then
      Debug.print
      @@ lazy
           (sprintf "### Formula converted:\n%s\n=>\n%s\n"
              (Logic.ExtTerm.str_of phi)
              (Logic.ExtTerm.str_of phi'));
    (uni_senv', phi')

  (* ---------------------------------------------------------------------
     The named encoding of term alternatives ([name_term_alternatives]).

     [subst_strat] above substitutes each term of a key's term set into the
     whole formula and joins the copies with [or]; the CNF of that join is the
     product of the copies' clause counts.  The functions below compute the
     same copies as a LIST (the alternatives), so that the CHC can name each
     one by a fresh predicate instead of distributing the join.  Nothing here
     is reached with the field off. *)

  (* [dedup_terms params terms]: [terms] with every term dropped that is
     equivalent to one kept before it under every value of [params], the
     key's parameters.  Exact: the alternatives are joined by a disjunction,
     which is idempotent.  Equivalence is decided syntactically on the
     simplified first-order form and, failing that, by asking Z3 whether the
     biconditional is valid within [dedup_timeout_ms]; any answer other than
     valid (a timeout or an exception included) keeps both terms, which is
     the encoding without deduplication and therefore still exact.  Two
     entries of a refuter's set that print alike ([x1 = 0] twice) doubled the
     alternatives of every clause mentioning the key. *)
  let dedup_timeout_ms = 1000

  let dedup_terms params terms =
    let senv = Map.Poly.of_alist_exn params in
    let old_of term =
      try
        Some
          (Evaluator.simplify
          @@ Logic.ExtTerm.to_old_fml Map.Poly.empty senv term)
      with exn when not (Common.Timer.is_async exn) -> None
    in
    let equivalent (t1, f1) (t2, f2) =
      Stdlib.(t1 = t2)
      ||
      match (f1, f2) with
      | Some f1, Some f2 -> (
          (try Stdlib.(f1 = f2)
           with exn when not (Common.Timer.is_async exn) -> false)
          ||
          let iff = LogicOld.Formula.mk_iff f1 f2 in
          if Z3Smt.Z3interface.may_not_return iff then false
          else
            try
              match
                Z3Smt.Z3interface.check_valid ~timeout:(Some dedup_timeout_ms)
                  ~id:None (LogicOld.get_fenv ()) iff
              with
              | `Valid -> true
              | _ -> false
            with exn when not (Common.Timer.is_async exn) -> false)
      | _ -> false
    in
    Set.to_list terms
    |> List.fold ~init:[] ~f:(fun kept term ->
        let entry = (term, old_of term) in
        if List.exists kept ~f:(equivalent entry) then kept else entry :: kept)
    |> List.rev_map ~f:fst

  (* [subst_strat_alternatives]: the alternatives [subst_strat] joins, as a
     list, with each key's term set deduplicated.
     Contract: [or_of] of the returned alternatives, under the returned
     environment, is equivalent to [subst_strat]'s formula under its
     environment (up to the names of the fresh result universals).  An
     alternative that does not mention a key is kept once rather than copied
     per term, by idempotence. *)
  let subst_strat_alternatives primal_strat_wf primal_strat_fn (uni_senv, phi)
      =
    let phi0 = Logic.ExtTerm.subst primal_strat_wf phi in
    let keys = Map.Poly.keys primal_strat_fn in
    let heads =
      ChoiceScope.heads ~uni_senv
        ~is_key:(Map.Poly.mem primal_strat_fn)
        (Logic.ExtTerm.nnf_of phi0)
    in
    let inner = ClauseChoiceScope.inner_of_clause ~uni_senv
        ~is_key:(Map.Poly.mem primal_strat_fn) ~heads phi0 in
    List.fold (NestedKeys.order ~keys phi0) ~init:(uni_senv, [ phi0 ])
      ~f:(fun (uni_senv, alts) key ->
        let params, terms = Map.Poly.find_exn primal_strat_fn key in
        let mentions alt = Set.mem (Logic.ExtTerm.fvs_of alt) key in
        match List.filter alts ~f:mentions with
        | [] -> (uni_senv, alts)
        | mentioning ->
            let whole = Logic.BoolTerm.or_of mentioning in
            let rets = NestedKeys.rets_of key whole in
            let local = rets @ NestedKeys.nested_rets ~keys whole rets in
            let deduped = dedup_terms params terms in
            (* with two terms or more, also the universals the choice may not
               depend on ([ChoiceScope]); an alternative not mentioning the
               key is not copied, so its variables are shared *)
            let local =
              match deduped with
              | _ :: _ :: _ ->
                  local
                  @ ChoiceScope.renamed ~inner ~keys:[ key ] ~all_keys:keys ~heads
                      ~outside:
                        (Set.Poly.union_list
                           (List.filter_map alts ~f:(fun alt ->
                                if mentions alt then None
                                else Some (Logic.ExtTerm.fvs_of alt))))
                      ~local whole
              | _ -> local
            in
            let alts_fvs =
              Set.Poly.union_list (List.map alts ~f:Logic.ExtTerm.fvs_of)
            in
            (* As in [subst_strat]: the result variable is renamed into the
               clause's universals, so the new name must be absent from the
               environment and from the free variables of every alternative
               and of the substituted term. *)
            let copies =
              List.map deduped ~f:(fun term ->
                  let term_fvs = Logic.ExtTerm.fvs_of term in
                  let ren =
                    NestedKeys.renaming local ~taken:(fun v ->
                        Map.Poly.mem uni_senv v || Set.mem alts_fvs v
                        || Set.mem term_fvs v)
                  in
                  ChoiceScope.record ~inner ren;
                  (term, ren))
            in
            let uni_senv' =
              Map.force_merge_list
              @@ List.map copies ~f:(fun (_, ren) ->
                  Map.rename_keys_map ren uni_senv)
            in
            let alts' =
              List.concat_map alts ~f:(fun alt ->
                  if mentions alt then
                    List.map copies ~f:(fun (term, ren) ->
                        Logic.ExtTerm.rename ren
                        @@ Logic.ExtTerm.subst
                             (Map.Poly.singleton key
                                (Logic.ExtTerm.mk_lambda params term))
                             alt)
                  else [ alt ])
            in
            (uni_senv', alts'))

  include CheckCnf

  (* The bound above summed over a problem's formulas, and the largest. *)
  let cnf_size_of_problem pcsp =
    let exi_senv = PCSP.Problem.senv_of pcsp in
    Set.fold (PCSP.Problem.formulas_of pcsp) ~init:(0, 0)
      ~f:(fun (total, largest) (uni_senv, phi) ->
        let n =
          try cnf_size exi_senv uni_senv (Logic.ExtTerm.nnf_of phi)
          with exn when not (Common.Timer.is_async exn) -> 1
        in
        (cnf_add total n, Int.max largest n))

  (* [name_alternatives ~fresh exi_senv (uni_senv, alts)]: the named encoding
     of the CHC formula [or_of alts] (each alternative already in CHC form),
     or [None] when it does not apply and the disjunction is to be kept.

     It applies when there are at least two alternatives; each alternative's
     NNF is [H \/ R_tau] with [H] the same single positive predicate atom in
     every alternative, or absent from all of them (a goal clause); every
     [R_tau] has its predicate atoms only negatively; and the product of the
     CNF sizes [c_tau] of the [R_tau] exceeds their sum plus one, so that
     naming is smaller.  The result is the clause [H \/ not N_1(z_1) \/ .. \/
     not N_k(z_k)] and, per alternative, the definition [N_tau(z_tau) \/
     R_tau], [z_tau] being the universals [R_tau] mentions; [fresh sort]
     draws each [N_tau].

     Exact: an interpretation of the original predicates satisfies [H \/
     \/_tau R_tau] iff it extends to the [N_tau] so that the new formulas all
     hold (take [N_tau := not R_tau]; conversely, where [H] fails some
     [N_tau] is false and its definition gives [R_tau]).  Each [N_tau] is
     non-recursive and defined by its definition only, so unfolding the [N]
     nodes of a derivation of the new system gives one of the old. *)
  let name_alternatives ~fresh exi_senv (uni_senv, alts) =
    if List.length alts < 2 then None
    else
      let split alt =
        let heads, rest =
          List.partition_tf
            (Logic.BoolTerm.disjuncts_of (Logic.ExtTerm.nnf_of alt))
            ~f:(fun d -> Option.is_some (pred_app_of exi_senv uni_senv d))
        in
        (heads, Logic.BoolTerm.or_of rest)
      in
      let splits = List.map alts ~f:split in
      let heads = fst (List.hd_exn splits) in
      let same_heads =
        List.length heads <= 1
        && List.for_all splits ~f:(fun (hs, _) ->
            try Stdlib.(hs = heads)
            with exn when not (Common.Timer.is_async exn) -> false)
      in
      let rests = List.map splits ~f:snd in
      if
        (not same_heads)
        || not (List.for_all rests ~f:(negative_only exi_senv uni_senv))
      then None
      else
        let sizes = List.map rests ~f:(cnf_size exi_senv uni_senv) in
        let product = List.fold sizes ~init:1 ~f:cnf_mul in
        let sum = List.fold sizes ~init:0 ~f:cnf_add in
        if product <= sum + 1 then None
        else
          let named =
            List.map rests ~f:(fun r ->
                let zs =
                  Set.to_list (Logic.ExtTerm.fvs_of r)
                  |> List.filter_map ~f:(fun v ->
                      Option.map (Map.Poly.find uni_senv v) ~f:(fun s -> (v, s)))
                in
                let n =
                  fresh
                    (Logic.Sort.mk_fun
                       (List.map zs ~f:snd @ [ Logic.BoolTerm.SBool ]))
                in
                let napp =
                  Logic.ExtTerm.mk_var_app n
                    (List.map zs ~f:(fst >> Logic.ExtTerm.mk_var))
                in
                ( napp,
                  (Map.Poly.of_alist_exn zs, Logic.BoolTerm.or_of [ napp; r ])
                ))
          in
          let clause =
            ( uni_senv,
              Logic.BoolTerm.or_of
                (heads @ List.map named ~f:(fst >> Logic.BoolTerm.neg_of)) )
          in
          Some (clause :: List.map named ~f:snd)

  (* How [name_tree] puts a leaf into CHC form: the co-CHC substitution maps
     each predicate [P] to [fun xs -> not (P xs)].  [Logic.Term.subst] reduces
     each application of such a lambda one argument at a time and renames
     every binder it passes with a traversal of the body below it, so an
     application to n arguments costs about n^2/2 traversals, and every
     quantifier of the leaf is renamed too; on checks whose predicates take a
     few dozen arguments this was nearly all of the check's construction.
     [subst_rename_on_capture] reduces an application in one step and renames
     a binder only where it could capture.  Its result is alpha-equivalent to
     [subst]'s on a beta-normal leaf (a placed leaf is one), so the check asks
     the same question with other bound names; it also draws fewer fresh
     names, which moves the names drawn after it.
     [COAR_MUSTRAT_NAME_SUBST_RENAME_ALL] selects [subst]; with
     COAR_EXACT_CROSSCHECK both are computed and a pair that is not
     alpha-equivalent is reported on stderr. *)
  module NameSubst = struct
    let rename_all =
      Option.is_some (Sys.getenv "COAR_MUSTRAT_NAME_SUBST_RENAME_ALL")

    (* alpha-equivalence of two terms: bound variables are compared by the
       depth of their binder, free ones by name; [info] is ignored *)
    let alpha_equiv t1 t2 =
      let open Logic in
      let rec index x = function
        | [] -> None
        | y :: ys ->
            if Ident.tvar_equal x y then Some 0
            else Option.map (index x ys) ~f:(( + ) 1)
      in
      let rec eq b1 b2 t1 t2 =
        match (t1, t2) with
        | Var (x, _), Var (y, _) -> (
            match (index x b1, index y b2) with
            | Some i, Some j -> i = j
            | None, None -> Ident.tvar_equal x y
            | _ -> false)
        | Con (c1, _), Con (c2, _) -> Stdlib.(c1 = c2)
        | App (f1, a1, _), App (f2, a2, _) -> eq b1 b2 f1 f2 && eq b1 b2 a1 a2
        | Bin (k1, v1, s1, u1, _), Bin (k2, v2, s2, u2, _) ->
            Stdlib.(k1 = k2) && Stdlib.(s1 = s2) && eq (v1 :: b1) (v2 :: b2) u1 u2
        | Let (v1, s1, d1, u1, _), Let (v2, s2, d2, u2, _) ->
            Stdlib.(s1 = s2) && eq b1 b2 d1 d2 && eq (v1 :: b1) (v2 :: b2) u1 u2
        | TyApp (u1, s1, _), TyApp (u2, s2, _) ->
            Stdlib.(s1 = s2) && eq b1 b2 u1 u2
        | TyLam (v1, u1, _), TyLam (v2, u2, _) ->
            Stdlib.(v1 = v2) && eq b1 b2 u1 u2
        | _ -> false
      in
      eq [] [] t1 t2

    let checked = Stdlib.Atomic.make 0

    let () =
      if Ast.PropLogic.Formula.crosscheck then
        Stdlib.at_exit (fun () ->
            eprintf "exact-crosscheck: %d naming substitutions compared\n%!"
              (Stdlib.Atomic.get checked))

    (* [apply sub] is the leaf conversion for [sub], to be applied to every
       leaf of every tree of one check.  Partially applied once: given its
       substitution, [subst_rename_on_capture] first computes the variables
       free in the substitution's range (a union over every predicate of
       the problem), which does not depend on the leaf; recomputing it for
       each leaf was most of the naming step once the reduction itself was
       linear.  The function returned is the same one, so each leaf is
       converted to the same term with the same fresh names drawn. *)
    let apply sub =
      if rename_all then fun t -> Logic.ExtTerm.subst sub t
      else
        let subst = Logic.Term.subst_rename_on_capture sub in
        fun t ->
        let r = subst t in
        if Ast.PropLogic.Formula.crosscheck then (
          let n = 1 + Stdlib.Atomic.fetch_and_add checked 1 in
          if n mod 1000 = 0 then
            eprintf "exact-crosscheck: %d naming substitutions compared\n%!" n;
          if not (alpha_equiv r (Logic.ExtTerm.subst sub t)) then
            eprintf "exact-crosscheck: MuStrat naming substitution NOT ALPHA-EQUIVALENT\n%!");
        r
  end

  (* [name_tree ~fresh ~exi_senv_of leaf (uni_senv, tree)]: the CHC form of a
     clause placed by [TermAlternatives.of_clause] ([leaf] is
     [NameSubst.apply sub], [sub] the substitution [cochc_to_chc] applies,
     made once per check and applied to each leaf), with every [Alts] node
     that meets [name_alternatives]'s conditions -- at least two alternatives, each with
     predicate atoms only negatively, the product of their CNF sizes above
     their sum plus one -- replaced by [not N_1(z_1) \/ .. \/ not N_k(z_k)],
     returned with the definitions [N_tau(z_tau) \/ R_tau], [z_tau] the
     universals [R_tau] mentions.  Inner nodes are named first, so an outer
     alternative may mention an inner name, negatively.  An [Alts] node that
     does not meet the conditions stays a disjunction.  [exi_senv_of ()] is
     the problem's predicates together with the names drawn so far, so that
     an inner name counts as an atom when an outer node is sized.

     Exact at any position, not only at the top of the clause: an [Alts] node
     sits under [and] and [or] only, so the clause is monotone in it.  Taking
     [N_tau := not R_tau] turns the named clause back into the clause; and the
     definitions give [not N_tau => R_tau], so by monotonicity the named clause
     implies the clause.  So an interpretation of the original predicates
     satisfies the clause iff it extends to the [N_tau] satisfying the named
     clause and the definitions.  Each [N_tau] is non-recursive and defined
     only by its definition, so unfolding the [N] nodes of a derivation of the
     named system gives a derivation of the unnamed one. *)
  let name_tree ~fresh ~exi_senv_of leaf (uni_senv, tree) =
    let defs = ref [] in
    let rec go = function
      | TermAlternatives.Leaf t -> leaf t
      | TermAlternatives.And ts -> Logic.BoolTerm.and_of (List.map ts ~f:go)
      | TermAlternatives.Or ts -> Logic.BoolTerm.or_of (List.map ts ~f:go)
      | TermAlternatives.Alts ts ->
          let rs = List.map ts ~f:(go >> Logic.ExtTerm.nnf_of) in
          let exi_senv = exi_senv_of () in
          let sizes = List.map rs ~f:(cnf_size exi_senv uni_senv) in
          if
            List.length rs < 2
            || (not (List.for_all rs ~f:(negative_only exi_senv uni_senv)))
            || List.fold sizes ~init:1 ~f:cnf_mul
               <= List.fold sizes ~init:0 ~f:cnf_add + 1
          then Logic.BoolTerm.or_of rs
          else
            Logic.BoolTerm.or_of
            @@ List.map rs ~f:(fun r ->
                let zs =
                  Set.to_list (Logic.ExtTerm.fvs_of r)
                  |> List.filter_map ~f:(fun v ->
                      Option.map (Map.Poly.find uni_senv v) ~f:(fun s -> (v, s)))
                in
                let n =
                  fresh
                    (Logic.Sort.mk_fun
                       (List.map zs ~f:snd @ [ Logic.BoolTerm.SBool ]))
                in
                let napp =
                  Logic.ExtTerm.mk_var_app n
                    (List.map zs ~f:(fst >> Logic.ExtTerm.mk_var))
                in
                defs :=
                  (Map.Poly.of_alist_exn zs, Logic.BoolTerm.or_of [ napp; r ])
                  :: !defs;
                Logic.BoolTerm.neg_of napp)
    in
    let phi = go tree in
    ((uni_senv, phi), List.rev !defs)

  (* The check's CHC under [name_term_alternatives]: [subst_strat]'s
     formulas, each formula's alternatives converted to CHC form one by one
     (by the substitution [cochc_to_chc] applies) and then named where
     [name_alternatives] applies.  The new predicates are ordinary and are
     drawn fresh against the problem's predicates, every universal and free
     variable of every formula, and every strategy key [keys]: a derivation
     node's copy is named [<pred>$<n>] and the refinement recognises a key's
     copy by the prefix [<key>$], so a new predicate must not be named as a
     key. *)
  let named_chc ?(joint = `Default) ~params ~keys primal_strat_wf
      primal_strat_fn primal =
    (* [joint_term_alternatives]'s units: by default from the history of
       [primal_strat_fn]'s own terms; [`Units f] when the caller translates
       them ([freed_named_chc]); [`None] for the product *)
    let joint =
      match joint with
      | `None -> None
      | `Units f -> Some f
      | `Default ->
          if config.joint_term_alternatives then
            Some (joint_units primal_strat_fn)
          else None
    in
    let pcsp0 = PCSP.Problem.of_formulas ~params Set.Poly.empty in
    let sub = PCSP.Problem.cochc_subst_of pcsp0 in
    let chc_params =
      PCSP.Problem.params_of (PCSP.Problem.cochc_to_chc pcsp0)
    in
    let exi_senv = chc_params.PCSP.Params.senv in
    let clauses = Set.to_list (PCSP.Problem.formulas_of primal) in
    (* Either each formula's whole-clause alternatives in CHC form, or (with
       [miniscope_term_alternatives]) each formula's placed tree, still in
       co-CHC form: [name_tree] converts its leaves. *)
    let placing_start = Common.Clock.now_ns () in
    let formulas, trees =
      LoopPhase.phase "place" @@ fun () ->
      if config.miniscope_term_alternatives then
        ( [],
          List.map clauses ~f:(fun (uni_senv, phi) ->
              TermAlternatives.of_clause ?joint ~dedup:dedup_terms
                primal_strat_fn
                (uni_senv, Logic.ExtTerm.subst primal_strat_wf phi)) )
      else
        ( List.map clauses ~f:(fun (uni_senv, phi) ->
              let uni_senv, alts =
                subst_strat_alternatives primal_strat_wf primal_strat_fn
                  (uni_senv, phi)
              in
              (uni_senv, List.map alts ~f:(Logic.ExtTerm.subst sub))),
          [] )
    in
    let placing_secs =
      Time_ns.Span.to_sec (Time_ns.diff (Common.Clock.now_ns ()) placing_start)
    in
    let input_names =
      Set.Poly.union_list
      @@ List.concat_map formulas ~f:(fun (uni_senv, alts) ->
          Map.Poly.key_set uni_senv :: List.map alts ~f:Logic.ExtTerm.fvs_of)
      @ List.concat_map trees ~f:(fun (uni_senv, tree, _) ->
          [ Map.Poly.key_set uni_senv; TermAlternatives.fvs_of tree ])
    in
    let new_senv = ref Map.Poly.empty in
    let fresh sort =
      let n =
        Ident.mk_fresh_tvar_avoiding ~prefix:"Alt_"
          ~taken:(fun v ->
            Map.Poly.mem exi_senv v || Set.mem input_names v || Set.mem keys v
            || Map.Poly.mem !new_senv v)
          ()
      in
      new_senv := Map.Poly.set !new_senv ~key:n ~data:sort;
      n
    in
    let named = ref 0 in
    let phis =
      LoopPhase.phase "name" @@ fun () ->
      List.concat_map formulas ~f:(fun (uni_senv, alts) ->
          match name_alternatives ~fresh exi_senv (uni_senv, alts) with
          | Some phis ->
              incr named;
              phis
          | None -> [ (uni_senv, Logic.BoolTerm.or_of alts) ])
      @
      let leaf = NameSubst.apply sub in
      List.concat_map trees ~f:(fun (uni_senv, tree, _) ->
          let clause, defs =
            name_tree ~fresh
              ~exi_senv_of:(fun () -> Map.force_merge exi_senv !new_senv)
              leaf (uni_senv, tree)
          in
          if not (List.is_empty defs) then incr named;
          clause :: defs)
    in
    (* one stderr line per check built, for a census of the placed
       alternatives; nothing without the variable *)
    if
      config.miniscope_term_alternatives
      && Option.is_some (Sys.getenv "COAR_MUSTRAT_JOINT_CENSUS")
    then (
      let placed, whole =
        List.fold trees ~init:(0, 0) ~f:(fun (p, w) (_, tree, n) ->
            let a = TermAlternatives.num_alternatives tree in
            if a = 0 then (p, w) else (p + a, w + n))
      in
      eprintf
        "mustrat-joint-census joint=%b placed=%d whole=%d units_so_far=%d unit_rows_so_far=%d secs=%.3f\n%!"
        (Option.is_some joint) placed whole
        (Atomic.get TermAlternatives.unit_count)
        (Atomic.get TermAlternatives.unit_rows_count)
        placing_secs);
    if config.miniscope_term_alternatives then
      Debug.print
      @@ lazy
           (let placed, whole =
              List.fold trees ~init:(0, 0) ~f:(fun (p, w) (_, tree, n) ->
                  let a = TermAlternatives.num_alternatives tree in
                  if a = 0 then (p, w) else (p + a, w + n))
            in
            sprintf
              "### Term alternatives placed at subformulas: %d alternative(s) \
               where the whole-clause substitution makes %d (clauses \
               placed by the one-point rule so far: %d), placed in %.3f s"
              placed whole
              (Atomic.get TermAlternatives.one_point_count)
              placing_secs);
    Debug.print
    @@ lazy
         (sprintf
            "### Term alternatives named in %d formula(s) by %d new \
             predicate(s)"
            !named (Map.Poly.length !new_senv));
    let params =
      {
        chc_params with
        PCSP.Params.senv = Map.force_merge chc_params.PCSP.Params.senv !new_senv;
        kind_map =
          Kind.add_kinds (Map.Poly.key_set !new_senv) Kind.Ord
            chc_params.PCSP.Params.kind_map;
      }
    in
    PCSP.Problem.of_formulas ~params (Set.Poly.of_list phis)

  (* [freed_named_chc]: [named_chc] with the checked side's strategy values
     kept as variables ([chain_pair_regions_free_opponent_values]): every key
     of [primal_strat_fn] that [FreedValues.tag] accepts has its terms
     replaced by tag applications, the tags are declared to [named_chc] with
     a kind the conversion to CHC form does not negate (so that each stays a
     body premise), and the result is the check with the tags made ordinary
     predicates and their definitions added.  Exact: the definitions make
     each tag the relation its term states (see [FreedValues]).  [None]
     when no key is tagged: the check would be [named_chc]'s. *)
  let freed_named_chc ~params ~keys primal_strat_wf primal_strat_fn primal =
    let formulas = Set.to_list (PCSP.Problem.formulas_of primal) in
    let names =
      Set.Poly.union_list
        (List.concat_map formulas ~f:(fun (uni_senv, phi) ->
             [ Map.Poly.key_set uni_senv; Logic.ExtTerm.fvs_of phi ]))
    in
    let strat_fn, defs, tag_senv, translation =
      FreedValues.tag_with_translation
        ~query_keys:
          (Config.selects_terms config.refine_terms
          && Config.frees_goal config.refine_counter_play)
        ~dedup:dedup_terms
        ~taken:(fun v ->
          Map.Poly.mem params.PCSP.Params.senv v || Set.mem names v
          || Set.mem keys v)
        ~is_pred:(fun v ->
          (* the predicates [PCSP.Problem.cochc_subst_of] negates: the
             ordinary ones of the check's environment, keys and rankings
             excluded (they are substituted before the conversion) *)
          Map.Poly.mem params.PCSP.Params.senv v
          && (not (Map.Poly.mem primal_strat_fn v))
          && (not (Map.Poly.mem primal_strat_wf v))
          && (not (Set.mem keys v))
          && Kind.is_ord
               (Option.value ~default:Kind.Ord
                  (Map.Poly.find params.PCSP.Params.kind_map v)))
        formulas primal_strat_fn
    in
    if Map.Poly.is_empty tag_senv then None
    else
      let tag_names = Map.Poly.key_set tag_senv in
      let params' =
        {
          params with
          PCSP.Params.senv = Map.force_merge params.PCSP.Params.senv tag_senv;
          kind_map = Kind.add_kinds tag_names Kind.FN params.PCSP.Params.kind_map;
        }
      in
      (* [joint_term_alternatives]: the units of the strategy's own terms,
         each row's term of a tagged key replaced by the tag application that
         replaced it (or that replaced the term [dedup_terms] kept for it).
         A tag stands for its term exactly (its least interpretation is the
         term's relation), so the tagged check under these rows is the
         untagged check under the same offer.  A unit with a term no tag
         stands for is offered as a product. *)
      let joint =
        if not config.joint_term_alternatives then `None
        else
          `Units
            (fun lone ->
              let translate key t =
                match Map.Poly.find translation key with
                | None -> Some t (* not tagged: its terms are unchanged *)
                | Some pairs -> (
                    match
                      List.find pairs ~f:(fun (t', _) ->
                          JointTerms.equal_terms t t')
                    with
                    | Some (_, app) -> Some app
                    | None ->
                        let params, _ = Map.Poly.find_exn primal_strat_fn key in
                        List.find_map pairs ~f:(fun (t', app) ->
                            if
                              List.length
                                (dedup_terms params (Set.Poly.of_list [ t'; t ]))
                              = 1
                            then Some app
                            else None))
              in
              List.filter_map (joint_units primal_strat_fn lone)
                ~f:(fun (members, rows) ->
                  Option.map
                    (Option.all
                       (List.map rows ~f:(fun row ->
                            Option.all (List.map2_exn members row ~f:translate))))
                    ~f:(fun rows -> (members, rows))))
      in
      let chc =
        named_chc ~joint ~params:params' ~keys primal_strat_wf strat_fn primal
      in
      let p = PCSP.Problem.params_of chc in
      Debug.print
      @@ lazy
           (sprintf
              "### Kept the checked side's strategy values as variables by %d \
               defined predicate(s)"
              (Set.length tag_names));
      FreedValues.log (sprintf "check tags=%d" (Set.length tag_names));
      Option.some
      @@ PCSP.Problem.of_formulas
        ~params:
          {
            p with
            PCSP.Params.kind_map =
              Set.fold tag_names ~init:p.PCSP.Params.kind_map
                ~f:(fun m n -> Map.Poly.set m ~key:n ~data:Kind.Ord);
          }
        (Set.union (PCSP.Problem.formulas_of chc) (Set.Poly.of_list defs))

  (* ---------------------------------------------------------------------
     Choices that do not read the remembered copy ([copy_blind_choices]).

     The disjunctively well-founded reduction gives a least-fixpoint predicate
     [P] and the members of its component a copy [c] of an earlier visit to
     [P], and the check is satisfiable exactly when the reduced
     greatest-fixpoint system holds at the query.  A choice the checked side
     leaves open in such a body -- a disjunct, or a term of a key's term set,
     which the join of [subst_strat] makes a disjunct -- is then resolved
     pointwise in [c]: at one position the check may take one alternative for
     one copy value and another for another, which no strategy on the original
     game can do, and on an invalid input with a union of two well-founded
     rankings the check becomes satisfiable.

     The encoding below makes every such choice a function of the body's
     variables other than the copy.  In a CHC-form body, a choice node
     [K \/ D_1 \/ .. \/ D_k] ([k >= 2]; the [D_tau] are the disjuncts that
     mention a fixpoint predicate or the copy, [K] the others) becomes
     [K \/ not N_1(v_1) \/ .. \/ not N_k(v_k)], each [v_tau] holding no copy
     variable, with the Horn definition

       N_tau(v_tau) <= Reach_X(c, x) /\ Pi /\ not D_tau

     ([X(c, x)] the body's head, [Pi] the conditions under which the node is
     reached inside the body).  [N_tau(v)] reads "alternative [tau] loses at
     some copy at which the position [x] is reachable", so the head is
     derivable at [(c, x)] only when every alternative loses at some reachable
     copy, and a solution fixes, per value of [v], one alternative that wins at
     every reachable copy.  [Reach_Y] is the forward reachability of each
     fixpoint predicate from the query, over-approximated by the Horn clauses

       Reach_Y(t) <= Reach_X(p) /\ Pi_atom        (one per call Y(t) in X's body)
       Reach_Y(t) <= Pi_atom                      (one per call in the query)

     with [Pi_atom] the pure conjuncts beside the call and the negated pure
     disjuncts around it.  Without the reachability guard every alternative
     that calls [P] would have to win at the copy equal to the callee's state,
     where the comparison of a well-founded ranking fails, so every such answer
     would be lost. *)

  exception Unreadable of string

  (* A leaf of a body's connective tree, read against [exi_senv] (the check's
     predicates), [uni_senv] (the formula's universals, which shadow a
     predicate of their name) and [tracked] (the fixpoint predicates).
     [`Unreadable] is a leaf that mentions a fixpoint predicate other than as
     one application, positive or negated; [`Opaque] a leaf that mentions only
     other predicates (the dummies naming the opponent's decisions). *)
  let cb_leaf ~exi_senv ~uni_senv ~tracked t =
    let app t =
      match Logic.Term.let_apps t with
      | Logic.Var (v, _), args
        when Map.Poly.mem exi_senv v && not (Map.Poly.mem uni_senv v) ->
          Some (v, args)
      | _ -> None
    in
    let mentions_tracked t =
      Set.exists (Logic.ExtTerm.fvs_of t) ~f:(fun v ->
          Set.mem tracked v && not (Map.Poly.mem uni_senv v))
    in
    if not (mentions_pred exi_senv uni_senv t) then `Pure
    else
      match app t with
      | Some (v, args) when Set.mem tracked v ->
          if List.exists args ~f:mentions_tracked then `Unreadable
          else `Tracked_pos (v, args)
      | Some _ when not (mentions_tracked t) -> `Opaque_pos
      | _ -> (
          match Logic.Term.let_apps t with
          | Logic.Con (Logic.BoolTerm.Not, _), [ a ] -> (
              match app a with
              | Some (v, args)
                when Set.mem tracked v
                     && not (List.exists args ~f:mentions_tracked) ->
                  `Tracked_neg (v, args)
              | _ -> if mentions_tracked t then `Unreadable else `Opaque)
          | _ -> if mentions_tracked t then `Unreadable else `Opaque)

  (* The operands of an [Or] or [Alts] node, with nested nodes of the same
     connective spliced in: an [Or] inside an [Or], an [Alts] inside an
     [Alts].  An [Alts] inside an [Or], or an [Or] (a term alternative's copy
     of a disjunction) inside an [Alts], stays one operand.  Keeping each
     term alternative's copy apart keeps its own kept disjuncts (among them
     the copy's result guard) out of the premises of the other copies'
     choices: spliced into one node, every copy's kept disjuncts became a
     premise of every other copy's choice definitions and reachability
     clauses, and every copy's renamed result an argument of every choice
     predicate, so a node of [n] term alternatives emitted about [n^2]
     premise literals. *)
  let cb_disjuncts = function
    | TermAlternatives.Or ts ->
        let rec go = function
          | TermAlternatives.Or ts -> List.concat_map ts ~f:go
          | t -> [ t ]
        in
        List.concat_map ts ~f:go
    | TermAlternatives.Alts ts ->
        let rec go = function
          | TermAlternatives.Alts ts -> List.concat_map ts ~f:go
          | t -> [ t ]
        in
        List.concat_map ts ~f:go
    | t -> [ t ]

  (* Every leaf reached from the root through [Or] and [Alts] nodes only: the
     candidates for a formula's head, which may sit inside each term
     alternative's copy when a key's footprint spans the whole clause. *)
  let rec cb_frontier = function
    | TermAlternatives.Or ts | TermAlternatives.Alts ts ->
        List.concat_map ts ~f:cb_frontier
    | t -> [ t ]

  exception Too_large of int

  (* [copy_blind_chc ~params ~layout ~keys strat_wf strat_fn primal]: the part
     of the check [copy_blind_choices] encodes itself, [`Not_needed] when no
     formula of [primal] (the checked side's co-CHC) is the body of a
     predicate that carries a copy, in which case the check is built as
     without the field, or [`Too_large n] when the clauses emitted reached
     [n] premise literals and choice-predicate arguments, above
     [copy_blind_max_premises], and the encoding was abandoned.  [params]
     are the check's parameters (the checked side's keys relabelled
     ordinary), [layout] the checked side's table of prepended positions,
     [keys] every strategy key of both sides.

     Otherwise the result is [`Built (rest, added, new_senv, established)]:
     - [rest], the formulas of [primal] to be encoded as without the field
       (every formula that is not a copy-carrying body, and a copy-carrying
       body this encoding cannot read);
     - [added], CHC-form formulas: each readable copy-carrying body with its
       choices named as described above, the definitions of the names, and the
       reachability clauses of every formula of [primal];
     - [new_senv], the new predicates ([Choice_*], [Reach_*]), all ordinary;
     - [established], false when some formula mentions a fixpoint predicate in
       a way this encoding cannot read, so that the reachability predicates may
       miss a call or a copy-carrying choice stayed open: a satisfiable check
       is then no evidence that the checked side wins.

     Precondition: the formulas of [primal] are co-CHC (every fixpoint
     predicate positive except the one head of a body, with the checked side's
     keys still unsubstituted), as [to_pfwcsp] produces them.
     Postcondition: every formula of [added] is Horn after the substitution of
     the check's ordinary predicates by their negations has been applied to
     the part that came from [primal]; [added] mentions the choice and
     reachability predicates only as described, so each [Choice_*] and each
     [Reach_*] is defined by its own clauses alone. *)
  let cb_census = Option.is_some (Sys.getenv "COAR_MUSTRAT_CB_CENSUS")

  let copy_blind_chc ~params ~layout ~keys primal_strat_wf primal_strat_fn
      primal =
    let exi_senv = PCSP.Problem.senv_of primal in
    let tracked =
      Map.Poly.key_set exi_senv
      |> Set.filter ~f:(fun v -> Hashtbl.mem pred_index (Ident.name_of_tvar v))
    in
    (* Decided on the reduction's own record rather than on the heads found,
       so that a copy-carrying body whose head cannot be read is reported as
       not established instead of passing unencoded.  Decided before the
       term alternatives are placed, since it reads only the record and the
       check's predicates: placing them for a check that needs no copy-blind
       encoding took several seconds per call on large term sets, for a
       result that was then discarded. *)
    let any_copy =
      Hashtbl.existsi layout ~f:(fun ~key ~data ->
          Map.Poly.mem exi_senv (Ident.Tvar key)
          && List.exists data ~f:(function
               | MuCLP.Reducer.Copy -> true
               | MuCLP.Reducer.Flag -> false))
    in
    if not any_copy then `Not_needed
    else
    let sub =
      PCSP.Problem.cochc_subst_of (PCSP.Problem.of_formulas ~params Set.Poly.empty)
    in
    (* Each formula with its ranking keys substituted and its Skolem keys'
       term alternatives placed at subformulas, as a connective tree. *)
    let trees =
      LoopPhase.phase "cb-trees" @@ fun () ->
      List.map (Set.to_list (PCSP.Problem.formulas_of primal))
        ~f:(fun (uni_senv, phi) ->
          let uni_senv', tree, _ =
            TermAlternatives.of_clause ~dedup:dedup_terms primal_strat_fn
              (uni_senv, Logic.ExtTerm.subst primal_strat_wf phi)
          in
          let tree =
            match tree with
            | TermAlternatives.Leaf l ->
                TermAlternatives.of_nnf (Logic.ExtTerm.nnf_of l)
            | t -> t
          in
          ((uni_senv, phi), uni_senv', tree))
    in
    (* The head of a formula (its one negated application of a fixpoint
       predicate, among the top-level disjuncts) and the formula's copy
       variables, read off the head's prepended positions. *)
    let head_of uni_senv tree =
      let leaf t = cb_leaf ~exi_senv ~uni_senv ~tracked t in
      let heads =
        List.filter_map (cb_frontier tree) ~f:(function
          | TermAlternatives.Leaf l -> (
              match leaf l with `Tracked_neg (v, args) -> Some (v, args) | _ -> None)
          | _ -> None)
        |> List.dedup_and_sort ~compare:(fun (v1, a1) (v2, a2) ->
               match Ident.tvar_compare v1 v2 with
               | 0 -> (
                   try Stdlib.compare a1 a2
                   with exn when not (Common.Timer.is_async exn) -> -1)
               | c -> c)
      in
      match heads with
      | [] -> Ok None
      | [ (v, args) ] ->
          let entries =
            Option.value ~default:[]
              (Hashtbl.find layout (Ident.name_of_tvar v))
          in
          let n = List.length entries in
          if n > List.length args then Error "a head shorter than its prefix"
          else
            let prefix, _ = List.split_n args n in
            let copies =
              List.map2_exn entries prefix ~f:(fun e a ->
                  match (e, a) with
                  | MuCLP.Reducer.Copy, Logic.Var (x, _) -> Ok (Some x)
                  | MuCLP.Reducer.Copy, _ -> Error "a copy argument that is not a variable"
                  | MuCLP.Reducer.Flag, _ -> Ok None)
              |> Result.all
            in
            Result.map copies ~f:(fun cs ->
                let copies = Set.Poly.of_list (List.filter_opt cs) in
                Some
                  ( v,
                    args,
                    copies,
                    Set.diff
                      (Set.Poly.union_list (List.map args ~f:Logic.ExtTerm.fvs_of))
                      copies ))
      | _ -> Error "two heads"
    in
    let parsed =
      LoopPhase.phase "cb-heads" @@ fun () ->
      List.map trees ~f:(fun (orig, uni_senv, tree) ->
          (orig, uni_senv, tree, head_of uni_senv tree))
    in
      let taken =
        LoopPhase.phase "cb-taken" @@ fun () ->
        Set.Poly.union_list
          (Map.Poly.key_set exi_senv :: keys
          :: List.concat_map parsed ~f:(fun (_, uni_senv, tree, _) ->
              [ Map.Poly.key_set uni_senv; TermAlternatives.fvs_of tree ]))
      in
      let new_senv = ref Map.Poly.empty in
      let fresh prefix sort =
        let n =
          Ident.mk_fresh_tvar_avoiding ~prefix
            ~taken:(fun v -> Set.mem taken v || Map.Poly.mem !new_senv v)
            ()
        in
        new_senv := Map.Poly.set !new_senv ~key:n ~data:sort;
        n
      in
      let reach_names = Hashtbl.Poly.create () in
      let reach_app v args =
        let r =
          Hashtbl.find_or_add reach_names v ~default:(fun () ->
              fresh "Reach_" (Map.Poly.find_exn exi_senv v))
        in
        Logic.ExtTerm.mk_var_app r args
      in
      let established = ref true in
      let unread = ref [] in
      (* A predicate of the check that carries a copy but is not tracked:
         [head_of] finds heads among tracked predicates only, so a body
         headed by it would be read as having no head and go to the
         ordinary encoding, its choices resolved pointwise in the copy.
         Every predicate with a copy is tracked when the reduction and
         [pred_index] were computed from the same problem; if one is not,
         the encoding is marked not established, so that a satisfiable
         check is not taken as a win. *)
      let untracked_copy_preds =
        Hashtbl.fold layout ~init:[] ~f:(fun ~key ~data acc ->
            if
              Map.Poly.mem exi_senv (Ident.Tvar key)
              && (not (Set.mem tracked (Ident.Tvar key)))
              && List.exists data ~f:(function
                   | MuCLP.Reducer.Copy -> true
                   | MuCLP.Reducer.Flag -> false)
            then key :: acc
            else acc)
      in
      if not (List.is_empty untracked_copy_preds) then (
        Debug.print
        @@ lazy
             (sprintf
                "### Copy-blind choices: predicate(s) %s carry a copy but are not tracked"
                (String.concat ~sep:", " untracked_copy_preds));
        established := false;
        unread := "a copy-carrying predicate that is not tracked" :: !unread);
      let rest = ref [] in
      let added = ref [] in
      let nodes = ref 0 in
      let cb_choices = ref 0 in
      (* the lifted kept operands added under [copy_blind_lift_kept] *)
      let lifted = ref 0 in
      (* The premise literals and choice-predicate arguments emitted so far,
         against [copy_blind_max_premises]. *)
      let emitted = ref 0 in
      let charge n =
        emitted := !emitted + n;
        if !emitted > config.copy_blind_max_premises then
          raise (Too_large !emitted)
      in
      (* Read from the free variables rather than by filtering [uni_senv]: a
         formula with many term alternatives has one renamed result per
         alternative in [uni_senv], and each of its clauses mentions few. *)
      let clause_of uni_senv phi =
        let fvs = Logic.ExtTerm.fvs_of phi in
        ( Set.fold fvs ~init:Map.Poly.empty ~f:(fun acc v ->
              match Map.Poly.find uni_senv v with
              | Some s -> Map.Poly.set acc ~key:v ~data:s
              | None -> acc),
          phi )
      in
      match
      LoopPhase.phase "cb-emit" @@ fun () ->
      List.iter parsed ~f:(fun (orig, uni_senv, tree, head) ->
          let leaf t = cb_leaf ~exi_senv ~uni_senv ~tracked t in
          let to_term = TermAlternatives.to_term in
          let is_pure t =
            not (mentions_pred exi_senv uni_senv (to_term t))
          in
          let copies, premise, head_leaf, visible =
            match head with
            | Ok (Some (v, args, copies, visible)) ->
                ( copies,
                  Some (reach_app v args),
                  Some
                    (Logic.BoolTerm.neg_of (Logic.ExtTerm.mk_var_app v args)),
                  visible )
            | _ -> (Set.Poly.empty, None, None, Set.Poly.empty)
          in
          (* A disjunct kept outside the alternatives: it mentions neither a
             fixpoint predicate nor the copy, so resolving it reads only what
             the position shows. *)
          let is_kept t =
            let fvs = TermAlternatives.fvs_of t in
            Set.are_disjoint fvs copies
            && not
                 (Set.exists fvs ~f:(fun v ->
                      Set.mem tracked v && not (Map.Poly.mem uni_senv v)))
          in
          (* What is known when a sibling of a node's operand does not hold
             ([Or]) or holds ([And]), as a CHC-world premise: a pure formula,
             or a positive application of an untracked predicate, whose
             co-CHC occurrence is its negation.  Anything else yields nothing,
             which only weakens the premise. *)
          let neg_premise k =
            if is_pure k then Some (Logic.BoolTerm.neg_of (to_term k))
            else
              match k with
              | TermAlternatives.Leaf l -> (
                  match leaf l with `Opaque_pos -> Some l | _ -> None)
              | _ -> None
          in
          (* The operands of an [Or]/[Alts] node: the kept disjuncts, and the
             alternatives, in which every pure disjunct (one that mentions the
             copy but no predicate) is merged into one.  Pure disjuncts make no
             move between them: whichever holds, no call is followed, so
             choosing among them is only testing their disjunction, and a
             node whose alternatives are all pure is a test rather than a
             choice.  Naming each pure disjunct separately would demand one of
             them to hold at every reachable copy, which a substituted ranking
             (a disjunction over the copy) rarely satisfies.  A pure disjunct
             beside a call is still an alternative of its own node, since it
             lets the branch stop at one copy and continue at another. *)
          (* [copy_blind_lift_kept]: the lifted kept disjunct of a node of
             term alternatives whose alternatives (its spliced operands that
             are not kept) are [ts], or [None].  [results] are the formula's
             renamed result variables (its universals the placement of term
             alternatives introduced).  Each alternative that is a disjunction
             contributes its kept disjuncts but its guards, with each result
             [r] that has a guard [r <> t] among them (a kept disjunct
             [not (r = t)] or [r <> t], [r] not in [t]) replaced by [t].  An
             alternative with no other kept disjunct contributes nothing.
             Contract: at every assignment of the formula's variables the
             result implies the node, so adding it as a disjunct leaves the
             formula's meaning unchanged.  For one alternative: where each
             substituted result equals the value of its term, the contribution
             evaluates as the alternative's own kept disjuncts, which imply the
             alternative; where one differs, its guard, a disjunct of the
             alternative, holds.  This needs no quantifier over the results,
             so a contribution that still mentions a result (one with no guard
             in that alternative, or an enclosing node's) is as sound as one
             that does not.  The result is returned only when it is kept and
             pure (no copy, no predicate), so that it is a kept operand in the
             sense [is_kept] tests: if the lifted form mentioned the copy it
             would not be kept, and it is dropped. *)
          let lifted_kept ts =
            let results =
              Set.diff (Map.Poly.key_set uni_senv) (Map.Poly.key_set (fst orig))
            in
            let guard_of l =
              let side a b =
                match a with
                | Logic.Var (r, _)
                  when Set.mem results r
                       && not (Set.mem (Logic.ExtTerm.fvs_of b) r) ->
                    Some (r, b)
                | _ -> None
              in
              let eq_sides t =
                match Logic.Term.let_apps t with
                | Logic.TyApp (Logic.Con (Logic.BoolTerm.Eq, _), _, _), [ a; b ]
                  ->
                    Some (a, b)
                | _ -> None
              in
              let pair =
                match Logic.Term.let_apps l with
                | Logic.TyApp (Logic.Con (Logic.BoolTerm.Neq, _), _, _), [ a; b ]
                  ->
                    Some (a, b)
                | Logic.Con (Logic.BoolTerm.Not, _), [ e ] -> eq_sides e
                | _ -> None
              in
              Option.bind pair ~f:(fun (a, b) ->
                  match side a b with Some g -> Some g | None -> side b a)
            in
            let lift c =
              match c with
              | TermAlternatives.Or _ -> (
                  let ks = List.filter (cb_disjuncts c) ~f:is_kept in
                  let guards, others =
                    List.partition_map ks ~f:(fun k ->
                        match k with
                        | TermAlternatives.Leaf l -> (
                            match guard_of l with
                            | Some g -> First g
                            | None -> Second k)
                        | _ -> Second k)
                  in
                  let sub =
                    List.fold guards ~init:Map.Poly.empty
                      ~f:(fun m (r, t) ->
                        if Map.Poly.mem m r then m
                        else Map.Poly.set m ~key:r ~data:t)
                  in
                  match others with
                  | [] -> None
                  | _ ->
                      Some
                        (Logic.ExtTerm.subst sub
                           (Logic.BoolTerm.or_of (List.map others ~f:to_term))))
              | _ -> None
            in
            match List.filter_map ts ~f:lift with
            | [] -> None
            | ds ->
                let k = TermAlternatives.Leaf (Logic.BoolTerm.or_of ds) in
                if is_kept k && is_pure k then Some k else None
          in
          let operands t =
            let disjuncts = cb_disjuncts t in
            let kept, alts = List.partition_tf disjuncts ~f:is_kept in
            let kept =
              match t with
              | TermAlternatives.Alts _ when config.copy_blind_lift_kept -> (
                  match lifted_kept alts with
                  | Some k ->
                      incr lifted;
                      kept @ [ k ]
                  | None -> kept)
              | _ -> kept
            in
            let pure_alts, calls = List.partition_tf alts ~f:is_pure in
            let merged =
              match pure_alts with
              | [] -> []
              | [ d ] -> [ d ]
              | ds ->
                  [ TermAlternatives.Leaf
                      (Logic.BoolTerm.or_of (List.map ds ~f:to_term)) ]
            in
            (kept, merged @ calls)
          in
          (* A pure sibling at an [And] is a premise of the other operands.
             That is sound because a pure subtree contains no choice node (every
             node in it has at most its one merged pure alternative), so it is
             its own CHC form and holds in a solution of the check exactly when
             it holds.  A pure sibling whose truth at a copy were established
             only through named alternatives could not be assumed: two such
             conjuncts would each be assumed while justifying the other, and at
             a reachable copy where both fail no definition would fire. *)
          let pos_premise t = if is_pure t then Some (to_term t) else None in
          let siblings ts i =
            List.filter_mapi ts ~f:(fun j t -> if i = j then None else pos_premise t)
          in
          let rec reach ~pi = function
            | TermAlternatives.Leaf l -> (
                match leaf l with
                | `Tracked_pos (v, args) ->
                    charge (List.length pi + 2);
                    added :=
                      clause_of uni_senv
                        (Logic.BoolTerm.or_of
                           (reach_app v args
                           :: (Option.to_list premise @ pi
                              |> List.map ~f:Logic.BoolTerm.neg_of)))
                      :: !added
                | `Tracked_neg _ -> raise (Unreadable "a negated call in a body")
                | `Unreadable -> raise (Unreadable "an unreadable call")
                | `Pure | `Opaque_pos | `Opaque -> ())
            | TermAlternatives.And ts ->
                List.iteri ts ~f:(fun i t -> reach ~pi:(pi @ siblings ts i) t)
            | (TermAlternatives.Or _ | TermAlternatives.Alts _) as t ->
                let kept, alts = operands t in
                let pi = pi @ List.filter_map kept ~f:neg_premise in
                List.iter alts ~f:(reach ~pi)
          in
          let rec transform ~pi = function
            | TermAlternatives.Leaf l -> (
                match leaf l with
                | `Tracked_neg _ -> raise (Unreadable "a negated call in a body")
                | `Unreadable -> raise (Unreadable "an unreadable call")
                | _ -> l)
            | TermAlternatives.And ts ->
                Logic.BoolTerm.and_of
                  (List.mapi ts ~f:(fun i t ->
                       transform ~pi:(pi @ siblings ts i) t))
            | (TermAlternatives.Or _ | TermAlternatives.Alts _) as t ->
                let kept, alts = operands t in
                let pi = pi @ List.filter_map kept ~f:neg_premise in
                let alts' = List.map alts ~f:(transform ~pi) in
                let kept' = List.map kept ~f:to_term in
                if List.length alts' <= 1 then Logic.BoolTerm.or_of (kept' @ alts')
                else (
                  incr nodes;
                  let reach_head =
                    match premise with
                    | Some p -> p
                    | None -> raise (Unreadable "a choice outside a body")
                  in
                  let pi_fvs =
                    Set.Poly.union_list (List.map pi ~f:Logic.ExtTerm.fvs_of)
                  in
                  Logic.BoolTerm.or_of
                    (kept'
                    @ List.map alts' ~f:(fun d ->
                        let vs =
                          Set.Poly.union_list
                            [ Logic.ExtTerm.fvs_of d; pi_fvs; visible ]
                          |> Set.filter ~f:(fun v ->
                                 Map.Poly.mem uni_senv v && not (Set.mem copies v))
                        in
                        let zs =
                          List.map (Set.to_list vs) ~f:(fun v ->
                              (v, Map.Poly.find_exn uni_senv v))
                        in
                        charge (List.length pi + List.length zs + 2);
                        incr cb_choices;
                        let n =
                          fresh "Choice_"
                            (Logic.Sort.mk_fun
                               (List.map zs ~f:snd @ [ Logic.BoolTerm.SBool ]))
                        in
                        let napp =
                          Logic.ExtTerm.mk_var_app n
                            (List.map zs ~f:(fst >> Logic.ExtTerm.mk_var))
                        in
                        added :=
                          clause_of uni_senv
                            (Logic.BoolTerm.or_of
                               ((napp :: Logic.BoolTerm.neg_of reach_head
                                 :: List.map pi ~f:Logic.BoolTerm.neg_of)
                               @ [ Logic.ExtTerm.subst sub d ]))
                          :: !added;
                        Logic.BoolTerm.neg_of napp)))
          in
          (* The body: the top-level disjuncts but the head.  [head_of]
             found one head at most (up to repetition), so every negated call
             among them is that head. *)
          let body_of tree =
            let is_head = function
              | TermAlternatives.Leaf l -> (
                  match leaf l with `Tracked_neg _ -> true | _ -> false)
              | _ -> false
            in
            (* The head removed wherever [cb_frontier] can reach it, the
               [Or]/[Alts] structure kept: in [H \/ Alts (A_1 .. A_k)] with
               [H] a disjunct of every [A_tau] this is exact, since [\/] is
               associative and idempotent. *)
            let rec strip = function
              | TermAlternatives.Or ts ->
                  TermAlternatives.Or
                    (List.filter_map ts ~f:(fun t ->
                         if is_head t then None else Some (strip t)))
              | TermAlternatives.Alts ts ->
                  TermAlternatives.Alts
                    (List.map ts ~f:(fun t ->
                         if is_head t then TermAlternatives.Or [] else strip t))
              | t -> t
            in
            match head_leaf with
            | None -> tree
            | Some _ -> (
                match tree with
                | TermAlternatives.Or _ | TermAlternatives.Alts _ ->
                    TermAlternatives.Or [ strip tree ]
                | t -> TermAlternatives.Or (if is_head t then [] else [ t ]))
          in
          let saved = !added in
          match
            (match head with
            | Error msg -> raise (Unreadable msg)
            | Ok _ -> ());
            let body = body_of tree in
            reach ~pi:[] body;
            if Set.is_empty copies then None
            else
              let h = Option.value_exn head_leaf in
              Some
                ( uni_senv,
                  Logic.ExtTerm.subst sub
                    (Logic.BoolTerm.or_of [ h; transform ~pi:[] body ]) )
          with
          | None -> rest := orig :: !rest
          | Some main -> added := main :: !added
          | exception Unreadable msg ->
              added := saved;
              established := false;
              unread := msg :: !unread;
              rest := orig :: !rest)
      with
      | exception Too_large n ->
          Debug.print
          @@ lazy
               (sprintf
                  "### Copy-blind choices: abandoned after %d premise \
                   literal(s), above the bound of %d"
                  n config.copy_blind_max_premises);
          `Too_large n
      | () ->
      if cb_census then
        eprintf
          "mustrat-copy-blind-census: formulas=%d nodes=%d choices=%d \
           emitted=%d added=%d\n%!"
          (List.length parsed) !nodes !cb_choices !emitted (List.length !added);
      Debug.print
      @@ lazy
           (sprintf
              "### Copy-blind choices: %d choice node(s) named by %d \
               predicate(s), %d reachability predicate(s), %d formula(s) left \
               to the ordinary encoding, %d lifted kept operand(s)%s"
              !nodes
              (Map.Poly.length !new_senv - Hashtbl.length reach_names)
              (Hashtbl.length reach_names) (List.length !rest) !lifted
              (if !established then ""
               else
                 sprintf "; NOT established (%s): a satisfiable check is not a win"
                   (String.concat ~sep:", "
                      (List.dedup_and_sort ~compare:String.compare !unread))));
      `Built (List.rev !rest, List.rev !added, !new_senv, !established)

  (* [copy_blind_now]: encode this one check copy-blind, whatever
     [copy_blind_choices] says; set by [untransitive_win]'s re-check of a win
     whose rankings are not proved transitive, and with [for_refinement] on
     the copy-blind check of a timed-out check. *)
  (* [for_refinement]: set only on the copy-blind check of strategies whose
     ordinary check timed out ([copy_blind_on_timeout]).  A win or a
     counter-play of this check is handled as usual, and any outcome that
     yields neither runs [for_refinement], the ordinary check's own handling
     of its timeout. *)
  (* [cb_first_done]: set on the ordinary check that [copy_blind_first] runs
     after its copy-blind check yielded neither a win nor a counter-play, so
     that the ordinary check neither starts another copy-blind check first nor
     repeats it on a timeout. *)
  let rec solve_primal_dual ?(copy_blind_now = false) ?for_refinement
      ?(cb_first_done = false) turn
      ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
      ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual) =
    if
      config.copy_blind_first && (not copy_blind_now) && (not cb_first_done)
      && (not config.copy_blind_choices)
      && Option.is_none for_refinement
      && not
           (Map.Poly.is_empty primal_strat_wf && Map.Poly.is_empty primal_strat_fn)
    then (
      (* [copy_blind_first]: the copy-blind encoding is a fraction of the
         ordinary one and is sometimes decided where the ordinary check times
         out; its win is an answer and its counter-play refines the opponent,
         exactly as after a timeout.  Anything else falls back to the ordinary
         check, at the same budget. *)
      Debug.print
      @@ lazy
           (sprintf "### Checking the %s strategies copy-blind first"
              (if turn then "primal" else "dual"));
      solve_primal_dual ~copy_blind_now:true
        ~for_refinement:(fun () ->
          solve_primal_dual ~cb_first_done:true turn
            ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual))
        turn
        ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
        ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual))
    else
    (* [relative_completeness]: on a side's own turn (not a re-check of the
       same strategies), every [offer_every]-th turn makes an offer here and
       a probe below.  With a cap, the run ends with [unknown] once both
       sides have exhausted the capped space. *)
    let rc_side_ix = if turn then 0 else 1 in
    let rc_entry =
      rc_on () && (not copy_blind_now) && Option.is_none for_refinement
      && (not cb_first_done) && not config.copy_blind_choices
    in
    let rc_probe_turn =
      rc_entry
      &&
      let st = rc_sides.(rc_side_ix) in
      st.rc_turns <- st.rc_turns + 1;
      (st.rc_turns - 1) mod Int.max 1 config.offer_every = 0
    in
    let primal_strat_fn =
      if rc_probe_turn then rc_offer rc_side_ix primal_strat_fn
      else primal_strat_fn
    in
    if rc_entry && rc_exhausted () then (
      Debug.print
      @@ lazy
           "### Both sides have exhausted the capped hypothesis space: unknown\n";
      Ok Unknown)
    else
    let open Or_error.Monad_infix in
    let use_copy_blind = config.copy_blind_choices || copy_blind_now in
    (* [continue_check_in_copy]: a copy still asking a check of these very
       strategies goes on through the questions its timeout asks (they are
       about the same strategies) and its retries; any other check means the
       run has moved on, and the copy is stopped. *)
    let same_continued (turn', pwf, pfn, dwf, dfn, problem, _, _) =
      Bool.equal turn turn' && phys_equal pwf primal_strat_wf
      && phys_equal pfn primal_strat_fn && phys_equal dwf dual_strat_wf
      && phys_equal dfn dual_strat_fn && phys_equal problem primal
    in
    (match !continuation with
    | Some c when same_continued c -> ()
    | Some _ -> drop_continuation ()
    | None -> ());
    (* [copy_blind_recheck_continued]: likewise for a copy still asking the
       copy-blind re-check of a check of other strategies *)
    let same_cb_continued (turn', pwf, pfn, dwf, dfn, problem, _) =
      same_continued (turn', pwf, pfn, dwf, dfn, problem, (), ())
    in
    (match !cb_continuation with
    | Some c when same_cb_continued c -> ()
    | Some _ -> drop_cb_continuation ()
    | None -> ());
    chc_solver () >>= fun (module CHCSolver) ->
    backup_chc_solver () >>= fun (module CHCSolverBackUp) ->
    pcsp_solver () >>= fun (module PCSPSolver) ->
    let params =
      let params = PCSP.Problem.params_of primal in
      {
        params with
        kind_map =
          Map.Poly.map params.kind_map ~f:(function
            | Kind.FN | Kind.DWF -> Kind.Ord
            | k -> k);
      }
    in
    let keys =
      Set.Poly.union_list
        [
          Map.Poly.key_set primal_strat_wf;
          Map.Poly.key_set primal_strat_fn;
          Map.Poly.key_set dual_strat_wf;
          Map.Poly.key_set dual_strat_fn;
        ]
    in
    (* Under [copy_blind_choices], the copy-carrying bodies (and the
       reachability clauses) are encoded by [copy_blind_chc]; the formulas it
       leaves go through the encoding below as without the field. *)
    let same_ask (turn', pwf, pfn, dwf, dfn, problem) =
      Bool.equal turn turn' && phys_equal pwf primal_strat_wf
      && phys_equal pfn primal_strat_fn && phys_equal dwf dual_strat_wf
      && phys_equal dfn dual_strat_fn && phys_equal problem primal
    in
    let ask_key =
      (turn, primal_strat_wf, primal_strat_fn, dual_strat_wf, dual_strat_fn,
       primal)
    in
    (* [reuse_check_on_retry]: the copy-blind encoding and check of these very
       strategies, when the last copy-blind check was built for them. *)
    let reused_copy_blind =
      match !last_copy_blind_check with
      | Some (key, outcome, built)
        when use_copy_blind && config.reuse_check_on_retry && same_ask key ->
          Some (outcome, built)
      | _ -> None
    in
    let copy_blind =
      if use_copy_blind then
        match
          match reused_copy_blind with
          | Some (outcome, _) ->
              Debug.print
              @@ lazy
                   "### Reusing the copy-blind encoding built for the same \
                    strategies";
              outcome
          | None ->
              let outcome =
                LoopPhase.phase "mustrat-copy-blind-encode" @@ fun () ->
                copy_blind_chc ~params
                  ~layout:(if turn then copy_layout_primal else copy_layout_dual)
                  ~keys primal_strat_wf primal_strat_fn primal
              in
              last_copy_blind_check := Some (ask_key, outcome, ref None);
              outcome
        with
        | `Built b -> Some b
        | `Not_needed -> None
        | `Too_large _ when Option.is_some for_refinement ->
            (* A re-check after a timeout: skipped, and the timeout is
               handled as without the re-check. *)
            None
        | `Too_large _ ->
            (* Every formula through the ordinary encoding, and the check
               not established: a satisfiable answer is then no win. *)
            Some
              ( Set.to_list (PCSP.Problem.formulas_of primal),
                [],
                Map.Poly.empty,
                false )
      else None
    in
    let checked =
      match copy_blind with
      | None -> primal
      | Some (rest, _, _, _) ->
          PCSP.Problem.of_formulas ~params:(PCSP.Problem.params_of primal)
            (Set.Poly.of_list rest)
    in
    let copy_blind_established =
      match copy_blind with None -> true | Some (_, _, _, e) -> e
    in
    match for_refinement, copy_blind with
    | Some ordinary, None ->
        (* No copy-carrying body on this side: the re-check would be the
           ordinary check again. *)
        ordinary ()
    | _ ->
    (* The check of [strat_fn] (the checked side's term sets; its rankings
       are always [primal_strat_wf]): built for the strategy itself below, and
       for its restricted copies by [demonic_fallback]. *)
    (* With [~freed:true] (only under [chain_pair_regions_free_opponent_values]
       and [name_term_alternatives]): the tagged check of [freed_named_chc],
       [None] when no key is tagged; otherwise always [Some]. *)
    (* [~problem]: the side's problem the check is built from, [checked]
       unless the bounded check ([bounded_counterplay]) is built. *)
    let build_chc_opt ?(freed = false) ?(wf = primal_strat_wf)
        ?(problem = checked) strat_fn =
    let base =
      if config.name_term_alternatives then
        if freed then
          freed_named_chc ~params ~keys wf strat_fn problem
        else Some (named_chc ~params ~keys wf strat_fn problem)
      else
      Option.some
      @@ (problem |> PCSP.Problem.formulas_of
      |> Set.Poly.map ~f:(subst_strat wf strat_fn)
      |> PCSP.Problem.of_formulas ~params
      |> PCSP.Problem.cochc_to_chc
      |>
      (* The facts below assumed that the opponent's ranking covers every
         greatest-fixpoint step.  That named the steps but let a derivation end
         after one step in an arbitrary direction, so refinements covered single
         pairs and did not generalise.  They are not used: the check stays exact,
         the derivation is a complete play, and the pairs are read off it
         ([chain_pairs_of]). *)
      if true then Fn.id
      else
        PCSP.Problem.add_formulas
          (Set.Poly.map (Map.to_set primal_nu_wfs) ~f:(fun (x, s) ->
               let args =
                 Logic.mk_fresh_sort_env_list @@ Logic.Sort.args_of s
               in
               let papp =
                 Logic.ExtTerm.mk_var_app x
                   (List.map args ~f:(fst >> Logic.ExtTerm.mk_var))
               in
               (Map.Poly.of_alist_exn args, papp))))
    in
    Option.map base ~f:(fun chc ->
    let chc =
      match copy_blind with
      | None -> chc
      | Some (_, added, new_senv, _) ->
          let p = PCSP.Problem.params_of chc in
          PCSP.Problem.of_formulas
            ~params:
              {
                p with
                PCSP.Params.senv = Map.force_merge p.PCSP.Params.senv new_senv;
                kind_map =
                  Kind.add_kinds (Map.Poly.key_set new_senv) Kind.Ord
                    p.PCSP.Params.kind_map;
              }
            (Set.union (PCSP.Problem.formulas_of chc) (Set.Poly.of_list added))
    in
    let chc =
      if config.name_large_check_disjunctions then (
        let replaced, names, chc =
          LoopPhase.phase "name-disjunctions" @@ fun () ->
          CheckCnf.name_problem
            ~by_size:config.name_check_disjunctions_by_size ~bound:1000 chc
        in
        if replaced > 0 && LoopPhase.timeline then
          eprintf "mustrat-named-disjunctions: formulas=%d names=%d\n%!"
            replaced names;
        if replaced > 0 then
          Debug.print
          @@ lazy
               (sprintf
                  "### Named the multiplying disjunctions of %d formula(s) \
                   of the check by %d new predicate(s)"
                  replaced names);
        chc)
      else chc
    in
    let chc = LoopPhase.phase "guard" @@ fun () -> GuardedClauses.apply chc in
    let chc =
      if config.drop_tautological_check_clauses then (
        let dropped, total, chc = TautologicalClauses.drop chc in
        Debug.print
        @@ lazy
             (sprintf
                "### Dropped %d tautological clause(s) of the check's %d"
                dropped total);
        chc)
      else chc
    in
    chc)
    in
    let build_chc strat_fn = Option.value_exn (build_chc_opt strat_fn) in
    let chc =
      match (!last_check, reused_copy_blind) with
      | _, Some (_, { contents = Some chc }) ->
          (* [use_copy_blind]: the check built from the reused encoding *)
          if LoopPhase.timeline then eprintf "mustrat-reuse: copy-blind\n%!";
          Debug.print
          @@ lazy "### Reusing the copy-blind check built for the same strategies";
          chc
      | Some (key, chc), _
        when config.reuse_check_on_retry && (not use_copy_blind)
             && same_ask key ->
          if LoopPhase.timeline then eprintf "mustrat-reuse: ordinary\n%!";
          Debug.print
          @@ lazy "### Reusing the check built for the same strategies";
          chc
      | _ ->
          let chc =
            LoopPhase.phase
              (if use_copy_blind then "mustrat-build-check-copy-blind"
               else "mustrat-build-check")
            @@ fun () -> build_chc primal_strat_fn
          in
          (if use_copy_blind then
             (* the encoding was just made or reused for this very key *)
             match !last_copy_blind_check with
             | Some (key, _, built) when same_ask key -> built := Some chc
             | _ -> ()
           else last_check := Some (ask_key, chc));
          chc
    in
    (* The check whose counter-play the refinement reads: [chc], or the
       tagged check when [freed_reask] replaced the counter-play by one of
       it, so that the play and the clauses it is read against agree. *)
    (* A diagnostic, with COAR_MUSTRAT_TIMELINE and
       COAR_MUSTRAT_NORMALIZE_PROBE both set: the check's size, and the time
       the CHC backend's normalisation takes on it, outside the check's
       budget (the backend normalises it again inside the budget, so a check
       whose normalisation alone outlasts the budget times out before the
       solver is asked).  It doubles that cost; nothing reads its result. *)
    if
      LoopPhase.timeline
      && Option.is_some (Sys.getenv "COAR_MUSTRAT_NORMALIZE_PROBE")
    then (
      let t = Common.PhaseTime.now () in
      let n = PCSP.Problem.normalize chc in
      eprintf
        "mustrat-normalize-probe: formulas=%d chars=%d normalized_chars=%d secs=%.2f\n%!"
        (Set.length (PCSP.Problem.formulas_of chc))
        (String.length (PCSP.Problem.str_of chc))
        (String.length (PCSP.Problem.str_of n))
        (Common.PhaseTime.now () -. t));
    let played_chc = ref chc in
    if config.demonic_fallback_on_undecided_check && not use_copy_blind then
      note_checked_terms turn primal_strat_fn;
    Debug.print
    @@ lazy
         (sprintf
            "\n\
             ### Checking whether the current %s strategy is winning via CHC \
             solving (%d sec.)"
            (if turn then "primal" else "dual")
            !(chc_budget ~backup:false turn));
    if verbose then
      Debug.print @@ lazy (sprintf "%s\n" @@ PCSP.Problem.str_of chc);
    Debug.print
    @@ lazy
         (let total, largest = cnf_size_of_problem chc in
          sprintf
            "### CNF size of the check (a bound from the formula structure): \
             %d clause(s) over %d formula(s), the largest formula %d"
            total
            (Set.length (PCSP.Problem.formulas_of chc))
            largest);
    (* Every ranking the checked side substitutes is known well-founded:
       produced by re-synthesis as one [WF] template instance (and unchanged
       since), or proved transitive, a transitive finite union of
       well-founded relations being well-founded.  The reason for each one
       that is neither is printed. *)
    let rankings_transitive () =
      Map.Poly.for_alli primal_strat_wf ~f:(fun ~key ~data ->
          match Hashtbl.find wf_by_construction (Ident.name_of_tvar key) with
          | Some t when phys_equal t data -> true
          | _ ->
          match
            RankingCheck.check ~direct:config.validate_verdicts data
          with
          | Ok () -> true
          | Error reason ->
              Debug.print
              @@ lazy (sprintf "### %s: %s" (Ident.name_of_tvar key) reason);
              false)
    in
    (* [demonic_fallback ()], under [demonic_fallback_on_undecided_check] and
       after this side's ordinary check timed out: the checks of the
       strategy's restricted copies ([DemonicCopies]), in their order, each at
       [demonic_fallback_timeout].  [`Refined r] when a copy's counter-play
       refined the opponent to a different strategy: [r] is the run continued
       with the opponent's turn, exactly as after an ordinary counter-play
       (the budget is not doubled, as after a copy-blind counter-play).
       [`Copy_won] (only under [demonic_fallback_reads_wins]) when a copy's
       check, asked before any copy refined the opponent, is satisfiable: the
       caller reads it as the ordinary check's win.  [`Nothing] when neither
       happened -- every copy was undecided, returned no play, won with the
       field off, or its refinement left the opponent unchanged -- and the
       timeout is then handled as without the field.  A copy's counter-play
       is a play against the restricted strategy only, so it enters the run
       only through the opponent's refinement. *)
    let demonic_fallback () =
      if not (config.demonic_fallback_on_undecided_check && not use_copy_blind)
      then `Nothing
      else
        let copies =
          DemonicCopies.copies ~max:config.demonic_fallback_max_copies
            ~is_fresh:(is_fresh_term turn) primal_strat_fn
        in
        (* printed when the fallback's outcome is known, before the run
           continues from it, so that a run cut by its budget still counts *)
        let census outcome =
          if copies_census then
            eprintf "mustrat-demonic-fallback: %s copies=%d %s\n%!"
              (match config.demonic_fallback_reads_wins with
              | Read_before_copy_blind -> "early"
              | Not_read | Read_after_copy_blind -> "late")
              (List.length copies) outcome
        in
        Debug.print
        @@ lazy
             (sprintf
                "### Demonic fallback: the %s check timed out; asking %d \
                 restricted cop%s at %d sec. each"
                (if turn then "primal" else "dual")
                (List.length copies)
                (if List.length copies = 1 then "y" else "ies")
                config.demonic_fallback_timeout);
        let refine_from chc' cex =
          let wf_records =
            Map.Poly.mapi dual_strat_wf ~f:(fun ~key ~data:_ ->
                Hashtbl.find wf_by_construction (Ident.name_of_tvar key))
          in
          let restore () =
            Map.Poly.iteri wf_records ~f:(fun ~key ~data ->
                match data with
                | Some t ->
                    Hashtbl.set wf_by_construction
                      ~key:(Ident.name_of_tvar key) ~data:t
                | None ->
                    Hashtbl.remove wf_by_construction (Ident.name_of_tvar key))
          in
          let current = (dual_strat_wf, dual_strat_fn, dual_nu_wfs) in
          let joint0 = joint_snapshot () in
          try
            let refined =
              refine_strat ~check:chc'
                ~solve_wf:
                  (PCSPSolver.solve
                     ~timeout:(Some !(chc_budget ~backup:false turn))
                     ~bpvs:Set.Poly.empty)
                ~solve_certs:
                  (PCSPSolver.solve_with_kind_certificates ~timeout:None
                     ~bpvs:Set.Poly.empty)
                PCSPSolver.solve cex current
            in
            if
              same_strategy refined current
              && not (joint_offer_grew joint0 dual_strat_fn)
            then (
              restore ();
              None)
            else Some refined
          with
          | NoRefinement | RefinementBudgetExpired ->
              restore ();
              None
          | exn when not (Common.Timer.is_async exn) ->
              Debug.print
              @@ lazy
                   (sprintf "### Demonic fallback: refinement failed (%s)"
                      (Exn.to_string exn));
              restore ();
              None
        in
        let rec go i = function
          | [] ->
              census "nothing";
              Debug.print
              @@ lazy "### Demonic fallback: no copy refined the opponent";
              `Nothing
          | strat_fn' :: rest -> (
              let outcome =
                try
                  let chc' = build_chc strat_fn' in
                  match
                    LoopPhase.phase "mustrat-demonic-fallback" (fun () ->
                        CHCSolver.solve
                          ~timeout:(Some config.demonic_fallback_timeout) chc')
                  with
                  | Ok (sol, _) ->
                      Debug.print
                      @@ lazy
                           (sprintf "### Demonic fallback: copy %d: %s" i
                              (match sol with
                              | PCSP.Problem.Sat _ -> "the copy wins"
                              | Unsat (Some (Formula _)) -> "a counter-play"
                              | sol -> PCSP.Problem.str_of_sol_with_witness sol));
                      if copies_census then
                        eprintf "mustrat-demonic-copy: %s\n%!"
                          (match sol with
                          | PCSP.Problem.Sat _ -> "sat"
                          | Unsat (Some (Formula _)) -> "counter-play"
                          | _ -> "none");
                      (* the check of the single-term strategy [strat_fn']
                         with the side's rankings: a win is read only when
                         [demonic_fallback_reads_wins] says so *)
                      (match
                         TimeoutPath.copy_outcome
                           config.demonic_fallback_reads_wins sol
                       with
                      | `Won -> `Won
                      | `Play cex -> `Play (chc', cex)
                      | `None -> `None)
                  | Error err ->
                      Debug.print
                      @@ lazy
                           (sprintf "### Demonic fallback: copy %d: %s" i
                              (Error.to_string_hum err));
                      `None
                with exn when not (Common.Timer.is_async exn) ->
                  Debug.print
                  @@ lazy
                       (sprintf "### Demonic fallback: copy %d: %s" i
                          (Exn.to_string exn));
                  `None
              in
              match outcome with
              | `None -> go (i + 1) rest
              | `Won ->
                  census "won";
                  `Copy_won
              | `Play (chc', cex) -> (
                  match refine_from chc' cex with
                  | None -> go (i + 1) rest
                  | Some dual_strat ->
                      census "refined";
                      stalls := 0;
                      Debug.print
                      @@ lazy
                           (sprintf
                              "### Demonic fallback: copy %d refined the \
                               opponent; pass the turn to %s\n"
                              i
                              (if turn then "dual" else "primal"));
                      `Refined
                        ( solve_primal_dual (not turn) (dual_strat, dual)
                            ((primal_strat_wf, primal_strat_fn, primal_nu_wfs),
                             primal)
                        >>= fun s -> Ok (Verdict.flip s) )))
        in
        go 1 copies
    in
    (* [prove_leaves ~budget chc] under [split_ground_prove_leaves]: the
       [prove] argument of [GroundGoals.split] for the check [chc].  A leaf
       [atom] is proven not derivable when the check's clauses without its
       goal clauses, with the one goal [atom => false] instead, are answered
       satisfiable (a model of the clauses with [atom] false, so [atom] is not
       in their least model) by the check's own solver.  Rounds give each leaf
       1, 2, 4, .. seconds, and every ask is cut so that all of them together
       take at most [budget] seconds, the budget the check itself just ran out
       of; a cut ask and any other answer prove nothing.  [deadline] and
       [left ()] read the one monotonic clock ([Common.Clock]), so [left ()]
       is the budget minus the time elapsed, no time-of-day step included. *)
    let prove_leaves ~budget chc =
      let deadline = Time_float.add (Common.Clock.now_float ()) (Time_float.Span.of_sec (Float.of_int budget)) in
      let left () =
        Time_float.Span.to_sec (Time_float.diff deadline (Common.Clock.now_float ()))
      in
      let rest =
        lazy
          (let cnf = PCSP.Problem.to_cnf chc in
           ( PCSP.Problem.params_of cnf,
             Set.filter (PCSP.Problem.clauses_of cnf) ~f:(Fn.non Clause.is_goal)
           ))
      in
      let prove (p, sorts, vals) secs =
        let secs = Int.min secs (Float.iround_down_exn (left ())) in
        secs >= 1
        &&
        try
          let params, rest = Lazy.force rest in
          let goal =
            Clause.of_old_clause
              ( Map.Poly.empty,
                Set.Poly.empty,
                Set.Poly.singleton (LogicOld.Atom.mk_pvar_app p sorts vals),
                LogicOld.Formula.mk_false () )
          in
          let chc' =
            PCSP.Problem.of_clauses
              ~params:{ params with PCSP.Params.stable_clauses = Set.Poly.empty }
              (Set.add rest goal)
          in
          let proven =
            match CHCSolver.solve ~timeout:(Some secs) chc' with
            | Ok (PCSP.Problem.Sat _, _) -> true
            | _ -> false
          in
          Debug.print
          @@ lazy
               (sprintf "### Leaf %s %s within %d sec."
                  (LogicOld.Formula.str_of (LogicOld.Formula.mk_atom (LogicOld.Atom.mk_pvar_app p sorts vals)))
                  (if proven then "proven not derivable" else "not proven")
                  secs);
          proven
        with exn when not (Common.Timer.is_async exn) -> false
      in
      let rounds i =
        if i > 30 || Float.(left () < 1.) then None else Some (1 lsl i)
      in
      (prove, rounds)
    in
    (* [reask_inline ()] under [reask_undecided_check_inline]: the check
       asked once more, at the budget it just timed out at, of the verdict-only
       solver with Z3's rule transformations on.  [true] only for a win (the
       query not derivable); every other outcome, a counter-play included, is
       [false] and is discarded: the transformed rules' derivation is not read,
       and a counter-play claimed through them is not used. *)
    let reask_inline retry =
      let budget = !(chc_budget ~backup:retry turn) in
      Debug.print
      @@ lazy
           (sprintf
              "### The %s check timed out; asking it again with Z3's rule \
               inlining on (%d sec.), reading only a win"
              (if turn then "primal" else "dual")
              budget);
      let won =
        ReaskInline.won (fun () ->
            reask_inline_chc_solver () >>= fun (module S) ->
            S.solve ~timeout:(Some budget) chc)
      in
      (* A census line, on stderr whether or not tracing is on, so that a
         plain run (tracing slows the check it would observe) can be counted. *)
      if reask_census then
        eprintf "mustrat-reask-inline: %s\n%!" (if won then "win" else "no-win");
      Debug.print
      @@ lazy
           (if won then "### The re-ask with inlining is a win"
            else "### The re-ask with inlining gave no win; discarded");
      won
    in
    (* [reask_plain retry] under [reask_undecided_check_plain_spacer]: the
       check asked once more, at the budget it just timed out at, of
       [backup_chc_solver] (Spacer without global guidance).  [Some r] for a
       win or a counter-play with its derivation, read as the ordinary
       check's; [None] for anything else, which is discarded.  A
       counter-play goes through [freed_reask], defined below with the
       solver the check was asked of, hence the forward reference. *)
    let freed_reask_fwd = ref Fn.id in
    let reask_plain () =
      let budget = !(chc_budget ~backup:false turn) in
      Debug.print
      @@ lazy
           (sprintf
              "### The %s check timed out; asking it again of the plain \
               Spacer (%d sec.)"
              (if turn then "primal" else "dual")
              budget);
      let res =
        LoopPhase.phase "mustrat-reask-plain" (fun () ->
            ReaskInline.answer (fun () ->
                CHCSolverBackUp.solve ~timeout:(Some budget) chc))
      in
      let outcome =
        match res with
        | Some (PCSP.Problem.Sat _, _) -> "win"
        | Some _ -> "counter-play"
        | None -> "none"
      in
      if reask_census then eprintf "mustrat-reask-plain: %s\n%!" outcome;
      Debug.print
      @@ lazy (sprintf "### The re-ask of the plain Spacer: %s" outcome);
      Option.map res ~f:(fun r -> !freed_reask_fwd r)
    in
    (* [split_ground_goals_first]: set when the split asked before the solver
       derived nothing for this very check, so that the solver's timeout does
       not ask it again (the split reads nothing but the check, and asks Z3
       nothing under [split_ground_alternative_max_asks = Some 0], so a second
       split of the same check would derive nothing either). *)
    let split_first_undecided = ref false in
    let rec f ?(plain_reasked = false) retry res =
      match res with
      | ( ( PCSP.Problem.Timeout | Unknown
          | Unsat (None | Some (Proof _ | External _ | Counterexample _)) ),
          _ )
        when Option.is_some for_refinement ->
          Debug.print
          @@ lazy
               "### The copy-blind check gave neither a win nor a \
                counter-play; handling the ordinary check's timeout";
          if config.copy_blind_recheck_once then
            copy_blind_recheck_spent := Some ask_key;
          (Option.value_exn for_refinement) ()
      | PCSP.Problem.Sat _, _
        when Option.is_some for_refinement && not copy_blind_established ->
          Debug.print
          @@ lazy
               "### The copy-blind check is satisfiable but not established; \
                handling the ordinary check's timeout";
          if config.copy_blind_recheck_once then
            copy_blind_recheck_spent := Some ask_key;
          (Option.value_exn for_refinement) ()
      | Timeout, _ when (not use_copy_blind) && Option.is_none for_refinement
        ->
          (* The steps of [TimeoutPath.order], each tried once; a step that
             decides nothing passes to the next, and after the last the
             timeout is handled by [f_timeout] (the turn passes or the check
             is retried).  [plain_reasked]: the plain Spacer was already asked
             this check (the race), so it is not asked again. *)
          let has_strategy =
            not
              (Map.Poly.is_empty primal_strat_wf
              && Map.Poly.is_empty primal_strat_fn)
          in
          let ask (step : TimeoutPath.step) ~next =
            match step with
            | Ground_split
              when config.split_ground_alternative_goals
                   && not !split_first_undecided -> (
                (* A counter-play composed from separate derivations of the
                   goals' ground atoms is a derivation of the check's own
                   clauses, so it is handled as the ordinary check's
                   counter-play; anything else is the timeout, handled as
                   without the field. *)
                let prove =
                  if config.split_ground_prove_leaves then
                    Some (prove_leaves ~budget:!(chc_budget ~backup:retry turn))
                  else None
                in
                match
                  LoopPhase.phase "mustrat-ground-split" @@ fun () ->
                  split_ground_goals_outcome ?prove chc
                with
                | `Counter_play cex ->
                    (* [split_ground_goals_first]: the check is decided here,
                       so a copy still asking it ([continue_check_in_copy])
                       could only return another answer to it later and take
                       the run over from the refinement this answer starts *)
                    if split_first_on () then drop_continuation ();
                    `Done
                      (f_ordinary ~split:true retry
                         (PCSP.Problem.Unsat (Some (PCSP.Problem.Formula cex)), -1))
                | `Won when config.validate_verdicts ->
                    (* [validate_verdicts]: the split's win carries no
                       solution to validate, so it is no verdict; the timeout
                       is handled as when the split decides nothing *)
                    eprintf "mustrat-validate: split win without a certificate\n%!";
                    `Next
                | `Won ->
                    (* [split_ground_prove_leaves] (or the smallest search):
                       the query is not derivable.  Handled as a win of the
                       ordinary check, as the inlined re-ask's win is: the
                       copy-blind certification of a ranking not proved
                       transitive still runs, and no arm of [f_ordinary] reads
                       a win's solution.  The check is decided, so a copy
                       still asking it is dropped. *)
                    `Win
                | `Nothing -> `Next)
            | Reask_inline when config.reask_undecided_check_inline ->
                if reask_inline retry then
                  (* Handled as a win of the ordinary check, so the copy-blind
                     certification of a ranking not proved transitive still
                     runs.  The empty solution map is never read: no arm of
                     [f_ordinary] reads a win's solution. *)
                  `Done (f_ordinary retry (PCSP.Problem.Sat Map.Poly.empty, -1))
                else `Next
            | Reask_plain
              when config.reask_undecided_check_plain_spacer
                   && (not plain_reasked) && not retry -> (
                match reask_plain () with
                | Some res' -> `Done (f_ordinary retry res')
                | None -> `Next)
            (* [copy_blind_recheck_once]: a check whose re-check already
               gave nothing is not re-checked again at the doubled budget;
               the step passes, as the catch-all below passes a step that
               is off.  Sound: the re-check only adds a chance of a win
               (an answer only on an established encoding) or of a
               counter-play (which only feeds a refinement); a skipped
               re-check leaves the timeout to the steps after it and to
               the doubling, exactly as with [copy_blind_on_timeout] off,
               so it can lose or gain an answer but never change one. *)
            | Copy_blind_recheck
              when config.copy_blind_on_timeout && (not cb_first_done)
                   && has_strategy
                   && not
                        (config.copy_blind_recheck_once
                        &&
                        match !copy_blind_recheck_spent with
                        | Some key -> same_ask key
                        | None -> false) ->
                Debug.print
                @@ lazy
                     (sprintf
                        "### The %s check timed out; checking the same \
                         strategies with copy-blind choices"
                        (if turn then "primal" else "dual"));
                (* when the re-check decides nothing, the steps after this
                   one are tried ([next]) *)
                `Done
                  (solve_primal_dual ~copy_blind_now:true ~for_refinement:next
                     turn
                     ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
                     ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual))
            | Copies -> (
                match demonic_fallback () with
                | `Refined r -> `Done r
                | `Copy_won ->
                    (* [demonic_fallback_reads_wins]: read by the ordinary
                       check's win rules, as the split's win is *)
                    `Win
                | `Nothing -> `Next)
            | Ground_split | Reask_inline | Reask_plain | Copy_blind_recheck ->
                `Next
          in
          TimeoutPath.run ~ask
            ~win:(fun () ->
              (* decided, so a copy still asking the whole check is dropped;
                 the win arms of [f_ordinary] read no solution *)
              drop_continuation ();
              f_ordinary retry (PCSP.Problem.Sat Map.Poly.empty, -1))
            ~last:(fun () -> f_timeout retry)
            (TimeoutPath.order config.demonic_fallback_reads_wins)
      | res -> f_ordinary retry res
    and f_ordinary ?(split = false) retry = function
      | PCSP.Problem.Sat _, _
        when Config.rechecks_copy_blind config.untransitive_win
             && (not use_copy_blind)
             && not (rankings_transitive ()) ->
          (* A win with a ranking not proved transitive may rest on choices
             that read the remembered copy.  The same strategies are checked
             again with every such choice made blind to the copy, and that
             check decides: a win there is an answer, a counter-play there
             refines the opponent as any counter-play does. *)
          Debug.print
          @@ lazy
               (sprintf
                  "### Current %s strategy wins the check, but a ranking is \
                   not proved transitive; checking again with copy-blind \
                   choices"
                  (if turn then "primal" else "dual"));
          solve_primal_dual ~copy_blind_now:true turn
            ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
      | PCSP.Problem.Sat _, _ when not copy_blind_established ->
          (* The copy-blind encoding could not read every formula, so the
             reachability predicates may miss a call or a choice may still read
             the copy: a satisfiable check proves nothing.  Pass the turn as a
             failed refinement does, ending the run with [unknown] after two
             such turns in a row. *)
          incr stalls;
          if gives_up_on_stalls !stalls then (
            Debug.print
            @@ lazy
                 "### Copy-blind encoding not established and no progress: \
                  unknown\n";
            Ok Unknown)
          else (
            Debug.print
            @@ lazy
                 (sprintf
                    "### The %s check is satisfiable but the copy-blind \
                     encoding is not established; pass the turn to %s\n"
                    (if turn then "primal" else "dual")
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
      | PCSP.Problem.Sat _, _
        when Config.untransitive_win_inconclusive ~copy_blind:use_copy_blind
               config.untransitive_win
             && not (rankings_transitive ()) ->
          (* A win with a ranking not proved transitive may rest on choices
             that read the remembered copy, so it is not an answer.  An
             ordinary win reaches this arm only when the mode does not
             re-check it, and every such mode makes it inconclusive here. *)
          incr stalls;
          if gives_up_on_stalls !stalls then (
            Debug.print
            @@ lazy
                 "### A win with a ranking not proved transitive, twice in a \
                  row: unknown\n";
            Ok Unknown)
          else (
            Debug.print
            @@ lazy
                 (sprintf
                    "### Current %s strategy wins the check, but a ranking is \
                     not proved transitive; pass the turn to %s\n"
                    (if turn then "primal" else "dual")
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
      | PCSP.Problem.Sat sol, _
        when match
               VerdictValidation.solution_refuted
                 ~timeout_ms:config.validate_verdicts_timeout_ms chc sol
             with
             | None -> false
             | Some reason ->
                 if reask_census then
                   eprintf "mustrat-win-refuted: %s\n%!"
                     (if turn then "primal" else "dual");
                 Debug.print
                 @@ lazy
                      (sprintf
                         "### The %s check's win is refuted by its own \
                          solution (%s); read as the solver's unknown"
                         (if turn then "primal" else "dual")
                         reason);
                 true ->
          (* Every win read as the check's verdict reaches this arm, from
             whichever ask produced it (the process's, a continued copy's, a
             raced or re-asked solver's); the arms above read a win only to
             choose the next check (a copy-blind re-check, a pass of the
             turn), so a wrong win there changes the run's course, never an
             answer.  The arm below reads the win as the check's
             satisfiability on the solver's word.  A win whose own solution
             violates a formula of [chc] at a concrete point is a wrong
             answer of the solver, not a win, and is read as the solver's
             [unknown] (through [f], so that a copy-blind re-check hands it
             to the timeout's next step as any undecided re-check does).
             Only a refuted certificate is discarded: a win without one (a
             verdict-only re-ask, the ground split) or one Z3 cannot check is
             read as before.  [unknown] is never a verdict, so the guard adds
             no answer rule; it can discard a correct win only if the
             solution was decoded wrongly from a correct answer, and it costs
             one validity question per formula of [chc] at each such win. *)
          f retry (PCSP.Problem.Unknown, -1)
      | PCSP.Problem.Sat sol, _ ->
          Debug.print
          @@ lazy
               (sprintf "### Current %s strategy is winning\n"
                  (if turn then "primal" else "dual"));
          validated "win"
            (fun () ->
              VerdictValidation.solution_validates
                ~timeout_ms:config.validate_verdicts_timeout_ms chc sol)
            Valid
      | Unsat (Some (Formula cex)), _ ->
          if
            Map.Poly.is_empty primal_strat_wf
            && Map.Poly.is_empty primal_strat_fn
          then
            (* The checked side has no ranking key and no Skolem key, so it
               makes no decision: there is no strategy to refine, and an
               unsatisfiable check refutes the side's input outright.
               Contract: with no ranking key no least-fixpoint predicate of
               the side reaches itself, and with no Skolem key no arithmetic
               existential is left, so the reduction adds no copy and no
               guard and reads each least fixpoint as a greatest one (a
               predicate that does not reach itself has one fixpoint).  The
               check is then the Horn encoding of a system of greatest
               fixpoints, solvable exactly when the query holds at the
               greatest solution, since that solution is the union of all
               post-fixpoints (Tarski, Pacific J. Math. 5, 1955, Theorem 1);
               the named opponent decisions, the named disjunctions and the
               guarded clausal form each preserve solvability.  So an
               unsatisfiable check -- the solver's answer, or a counter-play
               composed from derivations of the goals' ground atoms -- means
               the side's input is invalid, provided the solver's
               unsatisfiability is sound.  The caller flips a dual side's
               verdict, which needs the dual system to be the negation.
               Without the shortcut the run refines only the opponent and
               can end only by synthesising the opponent's whole winning
               strategy. *)
            validated "refutation"
              (fun () ->
                VerdictValidation.refutation_validates
                  ~timeout_ms:config.validate_verdicts_timeout_ms !played_chc
                  (derivation_roots !played_chc cex))
              Invalid
          else (
            (* the checked side ([turn]) lost; what the counter-play refines
               is its opponent's strategy (the side whose play won the
               check), which then takes the turn *)
            Debug.print
            @@ lazy
                 (sprintf
                    "### Counter strategy found! The current %s strategy \
                     lost the check; refining the %s strategy via pfwCSP \
                     solving"
                    (if turn then "primal" else "dual")
                    (if turn then "dual" else "primal"));
            try
              let primal_strat =
                (primal_strat_wf, primal_strat_fn, primal_nu_wfs)
              in
              let extra_plays =
                LoopPhase.phase "mustrat-extra-plays" @@ fun () ->
                extra_counter_plays
                  (if split then
                     (* the further plays of a composed counter-play are asked
                        of the same search, Spacer having just timed out *)
                     (module struct
                       include CHCSolver

                       let solve ?timeout:_ ?bpvs:_ ?print_sol:_ ?preds:_
                           ?copreds:_ chc =
                         Ok
                           ( (match
                                split_ground_goals
                                  ?budget:
                                    config.split_ground_extra_play_budget
                                  chc
                              with
                             | Some cex ->
                                 PCSP.Problem.Unsat
                                   (Some (PCSP.Problem.Formula cex))
                             | None -> PCSP.Problem.Unknown),
                             0 )
                     end : CheckSolverType)
                   else if retry then (module CHCSolverBackUp : CheckSolverType)
                   else (module CHCSolver : CheckSolverType))
                  ~budget:
                    (let budget = !(chc_budget ~backup:retry turn) in
                     match (config.extra_plays_budget_factor, !play_check_secs) with
                     | Some c, Some secs ->
                         (* [extra_plays_budget_factor]: the time this check
                            took, scaled, instead of the shared budget that
                            only grows *)
                         Int.min budget
                           (Int.max 1 (Float.iround_up_exn (c *. secs)))
                     | _ ->
                         if config.extra_plays_at_initial_budget then
                           Int.min config.chc_initial_timeout budget
                         else budget)
                  dual_strat_wf !played_chc cex
              in
              (* The records of [wf_by_construction] for the keys about to
                 be refined, restored if the refinement is rejected as
                 unchanged: the read-back of an accepted PCSat answer sets a
                 key's record to the term it produced, and when that
                 strategy is then rejected because it equals the current one
                 in simplified form, the current term stays and must keep the
                 record it had.  Restoring only returns each key to its state
                 before this refinement, so a ranking has a record only when
                 re-synthesis produced that very term (the record is compared
                 by physical equality) and it is well-founded as a [WF]
                 template instance; the one effect is that a later win with
                 that ranking is accepted as having well-founded rankings
                 instead of going to the transitivity test and the copy-blind
                 re-check, which is sound for the same reason the record is. *)
              let wf_records =
                Map.Poly.mapi dual_strat_wf ~f:(fun ~key ~data:_ ->
                    Hashtbl.find wf_by_construction (Ident.name_of_tvar key))
              in
              let restore_wf_records () =
                Map.Poly.iteri wf_records ~f:(fun ~key ~data ->
                    match data with
                    | Some t ->
                        Hashtbl.set wf_by_construction
                          ~key:(Ident.name_of_tvar key) ~data:t
                    | None ->
                        Hashtbl.remove wf_by_construction
                          (Ident.name_of_tvar key))
              in
              let joint0 = joint_snapshot () in
              let dual_strat =
                LoopPhase.phase "mustrat-refine" @@ fun () ->
                refine_strat ~extra_plays ~check:!played_chc
                  ~solve_wf:
                    (PCSPSolver.solve
                       ~timeout:(Some !(chc_budget ~backup:false turn))
                       ~bpvs:Set.Poly.empty)
                  ~solve_certs:(PCSPSolver.solve_with_kind_certificates
                                  ~timeout:None ~bpvs:Set.Poly.empty)
                  PCSPSolver.solve cex
                  (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
              in
              if
                Config.detect_unchanged_refinement config
                && same_strategy dual_strat
                     (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
                && not (joint_offer_grew joint0 dual_strat_fn)
              then (
                restore_wf_records ();
                raise NoRefinement);
              stalls := 0;
              JointWall.report ~plays:!last_refinement_plays
                ~clauses:
                  (let chc = !played_chc in
                   lazy (joint_wall_clauses chc))
                ~chain_pairs:(fun tree -> chain_pairs_of tree)
                ~chain_regions:(fun ?bind_decision ?bind_step ~observe tree
                                    ~wf_key ~arity ->
                  ignore
                  @@ chain_regions_of ?bind_decision ?bind_step ~observe
                       ~decisions:
                         (Set.Poly.map (Map.Poly.key_set dual_strat_fn)
                            ~f:Ident.name_of_tvar)
                       tree ~wf_key ~arity)
                ~before:(dual_strat_wf, dual_strat_fn)
                ~after:(let wf, fn, _ = dual_strat in (wf, fn));
              Debug.print
              @@ lazy
                   (sprintf "\n### Strategy refined and pass the turn to %s\n"
                      (if turn then "dual" else "primal"));
              solve_primal_dual (not turn) (dual_strat, dual)
                (primal_strat, primal)
              >>= fun s -> Ok (Verdict.flip s)
            with
            | RefinementBudgetExpired ->
              (* [bound_last_refinement]: the last form of the refinement ran
                 out of the check's budget.  Neither a loss of the checked
                 side nor a failed refinement: the stall count is left as it
                 is, the side's check budget is doubled (the refinement's
                 bounded forms read the same budget, so they get the doubled
                 one next time too), and the turn passes, as on a
                 failed refinement -- an expired budget is never read as
                 [invalid].  No answer comes from here. *)
              let failure = StallRule.Last_form_expired in
              stalls := StallRule.after ~stalls:!stalls failure;
              if StallRule.doubles_budget failure then (
                let budget = chc_budget ~backup:false turn in
                budget := !budget * 2);
              Debug.print
              @@ lazy
                   (sprintf
                      "### The last refinement form ran out of its budget; \
                       the check budget is now %d sec.; pass the turn to %s\n"
                      !(chc_budget ~backup:false turn)
                      (if turn then "dual" else "primal"));
              solve_primal_dual (not turn)
                ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
                ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
              >>= fun s -> Ok (Verdict.flip s)
            | NoRefinement ->
              (* A failed refinement always passes the turn, and two in a row
                 (one per side) answer [unknown].  An unsatisfiable refinement
                 problem says only that no assignment of the opponent's key
                 copies on the nodes of this counter-play reproduces it: a fact
                 about one play and the strategy encoding, not a proof that the
                 checked side loses against every strategy of the other, so it
                 never yields [invalid].  The same holds a fortiori under
                 [copy_blind_choices], whose check also restricts the checked
                 side's choices.  [valid] and [invalid] come only from an
                 exact check. *)
              stalls := StallRule.after ~stalls:!stalls StallRule.Refinement_failed;
              if gives_up_on_stalls !stalls then (
                Debug.print
                @@ lazy "### Neither side's refinement made progress: unknown\n";
                Ok Unknown)
              else (
                Debug.print
                @@ lazy
                     (sprintf "### No refinement found; pass the turn to %s\n"
                        (if turn then "dual" else "primal"));
                solve_primal_dual (not turn)
                  ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
                  ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
                >>= fun s -> Ok (Verdict.flip s)))
      | Unsat (None | Some (Proof _ | External _ | Counterexample _)), _ ->
          if
            Map.Poly.is_empty primal_strat_wf
            && Map.Poly.is_empty primal_strat_fn
          then
            (* The checked side has no ranking key and no Skolem key, so it
               makes no decision: there is no strategy to refine, and an
               unsatisfiable check refutes the side's input outright.
               Contract: with no ranking key no least-fixpoint predicate of
               the side reaches itself, and with no Skolem key no arithmetic
               existential is left, so the reduction adds no copy and no
               guard and reads each least fixpoint as a greatest one (a
               predicate that does not reach itself has one fixpoint).  The
               check is then the Horn encoding of a system of greatest
               fixpoints, solvable exactly when the query holds at the
               greatest solution, since that solution is the union of all
               post-fixpoints (Tarski, Pacific J. Math. 5, 1955, Theorem 1);
               the named opponent decisions, the named disjunctions and the
               guarded clausal form each preserve solvability.  So an
               unsatisfiable check -- the solver's answer, or a counter-play
               composed from derivations of the goals' ground atoms -- means
               the side's input is invalid, provided the solver's
               unsatisfiability is sound.  The caller flips a dual side's
               verdict, which needs the dual system to be the negation.
               Without the shortcut the run refines only the opponent and
               can end only by synthesising the opponent's whole winning
               strategy. *)
            validated "refutation"
              (fun () -> Error "the backend gave no derivation")
              Invalid
          else (
            Debug.print
            @@ lazy
                 (sprintf
                    "### Current %s strategy is not winning (no cex obtained) \
                     and pass the turn to %s\n"
                    (if turn then "primal" else "dual")
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
      | Unknown, _ ->
          if retry then (
            Debug.print
            @@ lazy
                 (sprintf "### Unknown result and pass the turn to %s\n"
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
          else (
            Debug.print
            @@ lazy
                 (sprintf
                    "\n\
                     ### Checking again whether the current %s strategy is \
                     winning via CHC solving (%d sec.)"
                    (if turn then "primal" else "dual")
                    !(chc_budget ~backup:true turn));
            LoopPhase.phase "mustrat-check-backup" (fun () ->
                CHCSolverBackUp.solve
                  ~timeout:(Some !(chc_budget ~backup:true turn))
                  chc)
            >>= f true)
      | Timeout, _ ->
          (* An ordinary check's timeout is handled by [f]'s steps, the
             copies among them; this arm is reached by a copy-blind check's
             own timeout, for which no step applies *)
          f_timeout retry
      | OutSpace _, _ -> failwith "out of space" (* TODO *)
    and f_timeout retry =
          (* A timeout is not a verdict.  Both policies only choose which
             check runs next -- this side again, or the other side, with the
             strategies unchanged -- and with what budget; neither reads the
             timeout as a win or a loss.  Every answer is still produced by
             one of the other arms of this function, from a check that
             returned, by the same rule as under the other policy, and passing
             the turn is what an [unknown] from the backup solver already
             does.  So the policy changes whether and when a run answers, not
             which rule an answer rests on: as long as those rules are sound,
             no schedule can produce both answers, since the sides' claims are
             each other's negation. *)
          let budget = chc_budget ~backup:retry turn in
          budget := !budget * 2;
          let has_strategy =
            not
              (Map.Poly.is_empty primal_strat_wf
              && Map.Poly.is_empty primal_strat_fn)
          in
          (match config.chc_timeout_policy with
          | Config.Global_doubling
            when config.pass_turn_on_strategy_timeout && has_strategy ->
            (* [pass_turn_on_strategy_timeout]: the shared budget doubled as
               under [Global_doubling], and the turn passed as under
               [Pass_turn_on_timeout], resetting the stall count for the same
               reason.  A side with no strategy unknown is retried as under
               [Global_doubling]: its check is the whole question and its
               timeout says nothing the other side's check can answer. *)
            stalls := 0;
            if LoopPhase.timeline then
              eprintf "mustrat-pass-turn: to=%s budget=%d at=%.2f\n%!"
                (if turn then "dual" else "primal")
                !budget
                (Common.PhaseTime.now () -. Common.PhaseTime.t0);
            Debug.print
            @@ lazy
                 (sprintf "timeout and pass the turn to %s (budget %d sec.)\n"
                    (if turn then "dual" else "primal")
                    !budget);
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s)
          | Config.Global_doubling ->
            Debug.print @@ lazy (sprintf "timeout and retry\n");
            solve_primal_dual turn
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
            >>= fun s -> Ok s
          | Pass_turn_on_timeout ->
            (* The stall rule answers [unknown] after both sides failed to
               refine in a row.  A side whose check timed out has not tried,
               so the run of failures is broken here; otherwise a failed
               refinement, this timeout, and a second failed refinement of the
               same side would end the run without the other side ever having
               been checked to an answer. *)
            stalls := 0;
            Debug.print
            @@ lazy
                 (sprintf "timeout and pass the turn to %s\n"
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
    in
    (* A side without a strategy unknown answers from the check alone (the two
       [Unsat] arms above return [Invalid] before reading any counterexample),
       so its main solver may be one that returns none. *)
    (if
       Map.Poly.is_empty primal_strat_wf && Map.Poly.is_empty primal_strat_fn
     then (
       if Option.is_some config.empty_strategy_chc_solver then
         Debug.print
         @@ lazy
              "### No strategy unknown on this side: the check goes to \
               empty_strategy_chc_solver\n";
       empty_strategy_chc_solver ())
     else Ok (module CHCSolver : CheckSolverType))
    >>= fun (module MainSolver) ->
    let rc_probe_won =
      rc_probe_turn && (not use_copy_blind)
      && rc_run_probes ~side:rc_side_ix ~strat_wf:primal_strat_wf
           ~strat_fn:primal_strat_fn ~ask:(fun wf strat_fn budget ->
             try
               match
                 LoopPhase.phase "mustrat-rc-probe" @@ fun () ->
                 build_chc_opt ~wf strat_fn
               with
               | None -> `Undecided
               | Some chc_p -> (
                   Debug.print
                   @@ lazy
                        (sprintf "### Probe of the %s side with ranking(s) %s (%d sec.)"
                           (if turn then "primal" else "dual")
                           (String.concat_map_list ~sep:"; "
                              (Map.Poly.to_alist wf) ~f:(fun (k, t) ->
                                Ident.name_of_tvar k ^ " := "
                                ^ Logic.ExtTerm.str_of t))
                           budget);
                   let t0 = Common.PhaseTime.now () in
                   let outcome =
                     match
                       LoopPhase.phase "mustrat-rc-probe" @@ fun () ->
                       MainSolver.solve ~timeout:(Some budget) chc_p
                     with
                     | Ok (PCSP.Problem.Sat _, _) -> `Won
                     | Ok (PCSP.Problem.Unsat _, _) -> `Lost
                     | _ -> `Undecided
                   in
                   if Option.is_some (Sys.getenv "COAR_MUSTRAT_RC_CENSUS") then
                     eprintf "mustrat-rc: probe side=%d outcome=%s secs=%.2f\n%!"
                       rc_side_ix
                       (match outcome with
                       | `Won -> "won"
                       | `Lost -> "lost"
                       | `Undecided -> "undecided")
                       (Common.PhaseTime.now () -. t0);
                   outcome)
             with exn when not (Common.Timer.is_async exn) ->
               Debug.print
               @@ lazy (sprintf "### Probe failed (%s)" (Exn.to_string exn));
               `Undecided)
    in
    if rc_probe_won then (
      Debug.print
      @@ lazy
           (sprintf
              "### A probe of the %s side won with ranking-function relations: \
               the %s strategy is winning\n"
              (if turn then "primal" else "dual")
              (if turn then "primal" else "dual"));
      Ok Valid)
    else
    (* [freed_reask res] ([chain_pair_regions_free_opponent_values]): when the
       ordinary check [chc] returned a counter-play, the same check with the
       checked side's strategy values kept as defined predicates
       ([freed_named_chc]) is asked, at the check's budget but never above
       its initial one ([chc_initial_timeout], as the extra counter-plays
       are), and its counter-play,
       if it returns one, replaces [res] (and [played_chc] becomes that check),
       so that the regions read from it leave those values free.  Anything
       else it returns is discarded and [res] stands.

       Why the ordinary check is asked first.  The two checks have the same
       answer (the tagged one is the check with each strategy value named by
       a predicate its definition makes exactly that value), so only the
       counter-play differs, and only a lost check has one to read.  The
       tagged check is the harder one for the CHC backend: a named value is a
       variable bounded by a premise where the ordinary check has a constant,
       and a tagged key is out of the one-point placement of term
       alternatives.  On an integer transition system whose checked side
       decides hundreds of nondeterministic draws, the tagged check
       was not decided at 8, 16 and 32 s where the ordinary one is decided in
       well under its first budget, so asking it in place of the ordinary
       check lost a verdict the default finds in seconds.  Asked only after a
       loss and only for its play, it costs at most one initial budget per
       lost check, and a win or a timeout of the ordinary check is
       untouched.

       Exact: the verdict read is the ordinary check's, and a counter-play of
       the tagged check is a counter-play of the check (it unfolds into one
       by resolving each tag leaf with its definition).

       [freed_reask_timeout] caps the re-ask's budget further, and
       [freed_reask_skip_after_failures] stops asking it on a side once that
       many re-asks of that side in a row returned no counter-play.  Both
       only change which counter-play the refinement reads (the ordinary one
       stands), never a verdict.

       [~after_split:true] says the ordinary counter-play is the ground
       split's ([split_ground_goals_first]); under
       [freed_reask_after_split_max_height] the re-ask is then not asked when
       that derivation ([last_split_height]) is higher than the bound. *)
    (* the checked side's problem of the bounded check ([bounded_counterplay])
       once its counter-play is read, so that the tagged re-ask below keeps
       the bound *)
    let bounded_problem = ref None in
    (* [ask_bounded ~bound ~why]: the check with the opponent's free choices
       bounded ([BoundedPlay]), asked once per strategies of a side, and its
       counter-play, when it returns one; [None] for anything else, or when it
       is not asked.  A counter-play of it is a counter-play of the check, made
       of instances of the check's own clauses, so the caller hands it on
       exactly as the check's counter-play (the extra plays, the tagged re-ask
       and the refinement then read the bounded clauses: [played_chc],
       [bounded_problem]).  No verdict comes from the bounded check: a win
       under the bound may rest on a choice beyond it.  Why: a counter-play
       choosing a value past every literal of the problem makes the
       refinement offer a constant past it, and on a program with a guard at
       a large capacity the next check was then decided by neither the ground
       split nor the solver, where a counter-play with small choices led to
       checks decided in seconds. *)
    let bound_of fs = function
      | Config.Fixed n -> Z.of_int (Int.max 0 n)
      | Largest_literal -> BoundedPlay.largest_literal fs
    in
    let ask_bounded ~bound ~why =
      let has_strategy =
        not
          (Map.Poly.is_empty primal_strat_wf && Map.Poly.is_empty primal_strat_fn)
      in
      let asked_before =
        match !last_bounded_ask with Some key -> same_ask key | None -> false
      in
      if
        use_copy_blind || Option.is_some for_refinement || (not has_strategy)
        || asked_before
        || Map.Poly.is_empty dual_strat_fn
      then None
      else (
        last_bounded_ask := Some ask_key;
        let fs = PCSP.Problem.formulas_of checked in
        let bound = bound_of fs bound in
        let fs', count =
          BoundedPlay.restrict ~is_opponent:(Map.Poly.mem dual_strat_fn) ~bound
            fs
        in
        if count = 0 then (
          Debug.print
          @@ lazy
               (sprintf
                  "### No free choice of the opponent in the %s check to \
                   bound"
                  (if turn then "primal" else "dual"));
          None)
        else
          let problem =
            PCSP.Problem.of_formulas ~params:(PCSP.Problem.params_of checked) fs'
          in
          match
            try
              LoopPhase.phase "mustrat-build-check-bounded" @@ fun () ->
              build_chc_opt ~problem primal_strat_fn
            with exn when not (Common.Timer.is_async exn) -> None
          with
          | None -> None
          | Some bounded -> (
              let budget =
                Int.min config.chc_initial_timeout
                  !(chc_budget ~backup:false turn)
              in
              let started = Common.PhaseTime.now () in
              let res =
                LoopPhase.phase "mustrat-check-bounded" @@ fun () ->
                MainSolver.solve ~timeout:(Some budget) bounded
              in
              let outcome =
                match res with
                | Ok (PCSP.Problem.Unsat (Some (Formula _)), _) ->
                    "counter-play"
                | Ok (PCSP.Problem.Sat _, _) -> "win (discarded)"
                | Ok (PCSP.Problem.Timeout, _) -> "timeout"
                | _ -> "other"
              in
              if LoopPhase.timeline then
                eprintf
                  "mustrat-bounded-play: %s %s side=%s bound=%s facts=%d \
                   budget=%d %.2fs\n%!"
                  why outcome
                  (if turn then "primal" else "dual")
                  (Z.to_string bound) count budget
                  (Common.PhaseTime.now () -. started);
              Debug.print
              @@ lazy
                   (sprintf
                      "### The %s check with the opponent's free choices \
                       bounded by %s (%d fact(s), %s): %s"
                      (if turn then "primal" else "dual")
                      (Z.to_string bound) count why outcome);
              match res with
              | Ok ((PCSP.Problem.Unsat (Some (Formula _)), _) as r) ->
                  played_chc := bounded;
                  bounded_problem := Some problem;
                  Some r
              | _ -> None))
    in
    (* [bounded_counterplay = Reask_beyond _]: a counter-play of the check
       whose play gives a free choice of the opponent a value above the bound
       is replaced by the bounded check's counter-play when it has one; every
       other answer stands.  A run whose plays stay within the bound asks
       nothing more. *)
    let bounded_reask res =
      match (config.bounded_counterplay, res) with
      | ( (Config.Reask_beyond bound | Config.Reask_isolated_outlier bound),
          (PCSP.Problem.Unsat (Some (Formula cex)), _) )
        when Option.is_none !bounded_problem ->
          let b = bound_of (PCSP.Problem.formulas_of checked) bound in
          let names =
            Set.Poly.map (Map.Poly.key_set dual_strat_fn) ~f:Ident.name_of_tvar
          in
          let is_opponent n = Set.mem names n in
          let outliers () = play_outliers ~is_opponent ~bound:b cex in
          let fire =
            match config.bounded_counterplay with
            | Reask_isolated_outlier _ ->
                let os = outliers () in
                if LoopPhase.timeline && not (List.is_empty os) then
                  eprintf "mustrat-bounded-outliers: side=%s bound=%s %s\n%!"
                    (if turn then "primal" else "dual")
                    (Z.to_string b)
                    (String.concat ~sep:" "
                       (List.map os ~f:(fun (r, m) ->
                            Z.to_string r ^ "/"
                            ^ Option.value_map m ~default:"-" ~f:Z.to_string)));
                isolated_outlier os
            | _ -> play_exceeds ~is_opponent ~bound:b cex
          in
          if fire then
            match ask_bounded ~bound ~why:"reask" with
            | Some r -> r
            | None -> res
          else res
      | _ -> res
    in
    let side = if turn then 0 else 1 in
    let freed_reask ?(after_split = false) res =
      play_check_secs := Some (Common.PhaseTime.now () -. !ask_started);
      let res0 = res in
      let res = bounded_reask res in
      (* the split's own counter-play, not one a bounded re-ask replaced it by *)
      let after_split = after_split && phys_equal res res0 in
      match res with
      | PCSP.Problem.Unsat (Some (Formula _)), _
        when config.chain_pair_regions_free_opponent_values
             && config.name_term_alternatives
             && Option.is_none for_refinement && not use_copy_blind
             &&
             (match config.freed_reask_skip_after_failures with
             | Some n when freed_reask_failures.(side) >= n ->
                 FreedValues.log "reask skipped";
                 false
             | _ -> true)
             &&
             (match config.freed_reask_after_split_max_height with
             | Some h when after_split && !last_split_height > h ->
                 FreedValues.log
                   (sprintf "reask skipped split-height=%d" !last_split_height);
                 false
             | _ -> true) -> (
          match
            try
              LoopPhase.phase "mustrat-build-check-freed"
              @@ fun () ->
              build_chc_opt ~freed:true ?problem:!bounded_problem
                primal_strat_fn
            with exn when not (Common.Timer.is_async exn) -> None
          with
          | None -> res
          | Some tagged -> (
              let budget =
                Int.min config.chc_initial_timeout
                  !(chc_budget ~backup:false turn)
              in
              let budget =
                match config.freed_reask_timeout with
                | Some cap -> Int.max 1 (Int.min cap budget)
                | None -> budget
              in
              Debug.print
              @@ lazy
                   (sprintf
                      "### The %s check was lost; asking it again with the                        checked side's strategy values named, for its                        counter-play (%d sec.)"
                      (if turn then "primal" else "dual")
                      budget);
              let started = Common.Clock.now_float () in
              let elapsed () =
                sprintf " %.2fs budget=%d"
                  (Time_float.Span.to_sec
                     (Time_float.diff (Common.Clock.now_float ()) started))
                  budget
              in
              match
                LoopPhase.phase "mustrat-check-freed" @@ fun () ->
                MainSolver.solve ~timeout:(Some budget) tagged
              with
              | Ok ((PCSP.Problem.Unsat (Some (Formula _)), _) as res') ->
                  FreedValues.log ("reask counter-play" ^ elapsed ());
                  freed_reask_failures.(side) <- 0;
                  played_chc := tagged;
                  res'
              | _ ->
                  FreedValues.log ("reask no-counter-play" ^ elapsed ());
                  freed_reask_failures.(side) <-
                    freed_reask_failures.(side) + 1;
                  Debug.print
                  @@ lazy
                       "### The named re-ask gave no counter-play; the                         ordinary one is read";
                  res))
      | _ -> res
    in
    (freed_reask_fwd := fun res -> freed_reask res);
    (* [split_ground_goals_first]: the ground split asked before the solver.
       A derived counter-play is the check's, read as the timeout path reads
       one ([f_ordinary ~split:true]), and any copy still asking this check
       is stopped; otherwise the check is asked below exactly as without the
       field.  Not for a copy-blind check or re-check, whose clauses are not
       the ones the split reads. *)
    let split_first =
      if
        split_first_on ()
        && config.split_ground_alternative_goals
        && (not use_copy_blind)
        && Option.is_none for_refinement
      then (
        match
          LoopPhase.phase "mustrat-ground-split-first" @@ fun () ->
          split_ground_goals_outcome chc
        with
        | `Won when config.validate_verdicts ->
            (* [validate_verdicts]: the split's win carries no solution to
               validate, so the check is asked of the solver as when the
               split decides nothing, and the solver's solution decides *)
            eprintf "mustrat-validate: split win without a certificate\n%!";
            split_first_undecided := true;
            `Nothing
        | (`Counter_play _ | `Won) as r -> r
        | `Nothing ->
            split_first_undecided := true;
            `Nothing)
      else `Nothing
    in
    match split_first with
    | `Counter_play cex ->
        drop_continuation ();
        let res = (PCSP.Problem.Unsat (Some (PCSP.Problem.Formula cex)), -1) in
        (* [split_first_freed_reask]: the split's counter-play is a lost check
           like the solver's, so the tagged re-ask with the checked side's
           values freed is asked as after the solver's loss; a counter-play it
           returns replaces the split's (and the extra plays then come from
           the solver, as on the ordinary path), anything else leaves the
           split's.  The verdict read is the same lost check either way. *)
        let res' =
          if config.split_first_freed_reask then
            freed_reask ~after_split:true res
          else res
        in
        if phys_equal res' res then f_ordinary ~split:true false res
        else f_ordinary false res'
    | `Won ->
        (* the query of this very check is not derivable: the check is won,
           and handled as a win of the ordinary check (so the copy-blind
           certification of a ranking not proved transitive still runs).  The
           empty solution map is never read: no arm of [f_ordinary] reads a
           win's solution. *)
        drop_continuation ();
        Debug.print
        @@ lazy
             (sprintf
                "### The ground split proved the %s check's query underivable"
                (if turn then "primal" else "dual"));
        f_ordinary false (PCSP.Problem.Sat Map.Poly.empty, -1)
    | `Nothing ->
    (* [bounded_counterplay = Bounded_first _]: the bounded check
       ([ask_bounded]) asked before the check itself, once per strategies of a
       side; its counter-play goes on as the check's would, anything else
       leaves the check to be asked below as without the field. *)
    let bounded_first =
      match config.bounded_counterplay with
      | Config.Bounded_first bound -> ask_bounded ~bound ~why:"first"
      | No_bound | Reask_beyond _ | Reask_isolated_outlier _ -> None
    in
    match bounded_first with
    | Some res -> f false (freed_reask res)
    | None ->
    (* [race_check_plain_spacer]: the check asked of [backup_chc_solver] (Spacer
       without global guidance) in a forked copy beside the in-process check,
       at the same budget.

       Why the copy takes the run over rather than sending its answer back: a
       counter-play is a formula of the term language, whose constructors are
       extensible variants, and such a value does not survive [Marshal]; the
       copy, forked at this very point, holds the whole state of the run, so
       it continues from its answer exactly as this process would have
       continued from the same answer of the ordinary check
       ([PCSatCommon.ParallelRace]: one atomic claim, the process then exits
       with the copy's status).  So a win and a counter-play are both taken,
       and nothing is serialised.

       Exactly one of the two continues: the process keeps its own answer only
       through [finish], which claims the race first (killing the copy), and a
       copy that claimed it first makes [finish] never return.  Only the
       ordinary check of the main solver is raced -- not a retry of the
       backup, not a copy-blind check or re-check -- the checks
       [reask_undecided_check_plain_spacer] re-asks.

       Under [race_check_plain_spacer_after_first_rung] alone, only a check
       whose budget has grown past [chc_initial_timeout] is raced: a budget
       grows only when a check at it ran out, so a run whose checks all
       decide at their first budget never forks.  A check not raced is asked
       exactly as without either field, and a raced one exactly as under
       [race_check_plain_spacer]; the choice reads the budget alone, never
       an answer. *)
    let budget = !(chc_budget ~backup:false turn) in
    let race_fields =
      config.race_check_plain_spacer
      || config.race_check_plain_spacer_after_first_rung
    in
    let race_this_rung =
      RaceRung.races ~every_rung:config.race_check_plain_spacer
        ~after_first_rung:config.race_check_plain_spacer_after_first_rung
        ~initial:config.chc_initial_timeout ~budget
    in
    let race =
      if
        race_this_rung && (not use_copy_blind)
        && Option.is_none for_refinement
        && Common.ForkGuard.fits
             ~growth:(Common.ForkGuard.peak_excess_bytes ())
             ()
      then
        PCSatCommon.ParallelRace.start ~reads:`None (fun () ->
            let started = Common.PhaseTime.now () in
            let res =
              ReaskInline.answer (fun () ->
                  CHCSolverBackUp.solve ~timeout:(Some budget) chc)
            in
            (* in the copy: when it has nothing, the census line is its only
               trace (its answer, when it has one, is printed by the copy that
               continues below) *)
            if reask_census && Option.is_none res then
              eprintf "mustrat-race-plain: copy none %.1fs budget=%d\n%!"
                (Common.PhaseTime.now () -. started)
                budget;
            res)
      else `Not_started
    in
    (* [continue_check_in_copy]: the ordinary check asked so that its work
       survives its budget.

       Why a copy at all: every check makes a solver context of its own and
       drops it on return, so the solver's state at a timeout is lost and the
       doubled-budget retry repeats the first budget's work from nothing,
       after the timeout's other questions.  The context cannot be kept
       across the timeout's handling in this process (the solver call has
       returned), but a forked copy that never stopped asking keeps it.

       Rule.  With no copy of this check running: fork a copy asking the
       check of [MainSolver] with no budget, ask the check here at [budget]
       as without the field.  Here decided (anything but a timeout): stop
       the copy and go on with that answer.  Here timed out: leave the copy
       running ([continuation]) and handle the timeout as without the field.
       With a copy of this check running (the retry at a doubled budget):
       ask nothing; wait until the copy has run [budget] seconds, the
       retry's own budget; if it is still asking, this rung timed out;
       if it ended without an answer (an [unknown], an error), stop
       waiting for it and ask the check here as without the field.  A copy
       that decides, at any time, takes the run over from its answer (see
       [PCSatCommon.ParallelRace]); before the in-process ask's budget has
       run out it holds its answer back, so that the process, which
       decides the same question by the same solver at about the same time,
       keeps its own answer and the run does not move into the copy for
       nothing.  The copy then sets the check's budget to the rung at which
       the doubling schedule would have decided the check, as the retries
       without the field would have left it.

       Exactness: every answer read is a win or a counter-play with its
       derivation of the very check, from the very solver, that the process
       asks without the field; only the time at which it is read changes. *)
    (* [strategy_free_race_solver]: the check of a side with no strategy
       unknown is the side's whole question and does not change while the run
       goes on (nothing is substituted into it), so one copy asking it of the
       raced solver, with no budget, serves every later check of that side.
       Started at the side's first ordinary check, before anything else is
       asked; the process then goes on exactly as without the field.

       Exactness: the copy asks [cochc_to_chc chc], which replaces every
       predicate of [chc] (all of kind [Ord]: the check is handed to a CHC
       solver) by its complement, so [S] solves it exactly when
       [complement_solution S] solves [chc].  A [Sat] is read as [chc]'s win
       with that solution, an [Unsat] as [chc]'s refutation without a
       derivation, which the arms of [f] read for a side without strategy
       unknowns as they read Spacer's (they test the emptiness before
       reading any counterexample).  So every answer read is an answer of the
       very check the process asks, by a solver sound for satisfiability and
       unsatisfiability; only which solver decides it, and when, changes. *)
    let strategy_free_won =
      match config.strategy_free_race_solver with
      | Some sf_file
        when (not use_copy_blind) && Option.is_none for_refinement
             && Map.Poly.is_empty primal_strat_wf
             && Map.Poly.is_empty primal_strat_fn
             && not (strategy_free_race_running turn) -> (
          match strategy_free_race_solver sf_file with
          | Error _ -> None
          | Ok (module SF : CheckSolverType) -> (
              let co = PCSP.Problem.cochc_to_chc chc in
              let started = Common.PhaseTime.now () in
              match
                PCSatCommon.ParallelRace.start ~reads:`None (fun () ->
                    match SF.solve ~timeout:None co with
                    | Ok (PCSP.Problem.Sat sol, _) ->
                        Some (PCSP.Problem.Sat (complement_solution sol), -1)
                    | Ok (PCSP.Problem.Unsat _, _) ->
                        Some (PCSP.Problem.Unsat None, -1)
                    | Ok _ | Error _ -> None
                    | exception exn when not (Common.Timer.is_async exn) -> None)
              with
              | `Won res' ->
                  (* in the copy, which now is the run: the races it inherited
                     are its siblings', forgotten here, never stopped *)
                  continuation := None;
                  Hashtbl.clear strategy_free_races;
                  if LoopPhase.timeline then
                    eprintf "mustrat-strategy-free-race: %s %s after %.1fs\n%!"
                      (if turn then "primal" else "dual")
                      (match res' with
                      | PCSP.Problem.Sat _, _ -> "win"
                      | _ -> "refutation")
                      (Common.PhaseTime.now () -. started);
                  Debug.print
                  @@ lazy
                       (sprintf
                          "### The raced solver decided the %s side's \
                           strategy-free check after %.1f sec.; the copy \
                           continues the run"
                          (if turn then "primal" else "dual")
                          (Common.PhaseTime.now () -. started));
                  Some (f false res')
              | `Not_started -> None
              | `Racing t ->
                  if LoopPhase.timeline then
                    eprintf "mustrat-strategy-free-race: %s started\n%!"
                      (if turn then "primal" else "dual");
                  Hashtbl.set strategy_free_races ~key:turn ~data:t;
                  None))
      | _ -> None
    in
    let ask_here () =
      LoopPhase.phase
        (if use_copy_blind then "mustrat-check-copy-blind" else "mustrat-check")
        (fun () -> MainSolver.solve ~timeout:(Some budget) chc)
      >>= fun res -> f false (freed_reask res)
    in
    let continue_field =
      config.continue_check_in_copy || config.check_in_copy_only
    in
    let continue_on =
      continue_field
      && (not race_fields)
      && (not use_copy_blind) && Option.is_none for_refinement
    in
    let start_continued () =
      if
        not
          (Common.ForkGuard.fits
             ~growth:(Common.ForkGuard.peak_excess_bytes ())
             ())
      then (
        continue_census "not-started (memory)";
        ask_here ())
      else
        let started = Common.PhaseTime.now () in
        match
          PCSatCommon.ParallelRace.start ~reads:`None (fun () ->
              match
                ReaskInline.answer (fun () ->
                    if config.continued_check_flat_and_or then
                      Z3Smt.Z3interface.with_flat_and_or (fun () ->
                          MainSolver.solve ~timeout:None chc)
                    else MainSolver.solve ~timeout:None chc)
              with
              | None ->
                  continue_census
                    (sprintf "copy none %.1fs"
                       (Common.PhaseTime.now () -. started));
                  None
              | Some r ->
                  let elapsed = Common.PhaseTime.now () -. started in
                  (* under [check_in_copy_only] the process asks nothing,
                     so there is no answer of its own to wait for *)
                  let hold =
                    if config.check_in_copy_only then 0
                    else CheckContinuation.hold_ms ~budget ~elapsed
                  in
                  if hold > 0 then
                    Caml_threads.Thread.delay (Float.of_int hold /. 1000.);
                  Some (r, elapsed))
        with
        | `Won (res', elapsed) ->
            (* in the copy, which now is the run *)
            continuation := None;
            ask_started := started;
            let b = chc_budget ~backup:false turn in
            b := CheckContinuation.rung_budget ~initial:budget ~elapsed;
            continue_census
              (sprintf "copy %s %.1fs budget=%d->%d"
                 (match res' with
                 | PCSP.Problem.Sat _, _ -> "win"
                 | _ -> "counter-play")
                 elapsed budget !b);
            Debug.print
            @@ lazy
                 (sprintf
                    "### The continued check decided after %.1f sec.; the \
                     copy continues the run (budget %d sec.)"
                    elapsed !b);
            f false (freed_reask res')
        | `Not_started ->
            continue_census "not-started (fork)";
            ask_here ()
        | `Racing t when config.check_in_copy_only -> (
            (* The process does not ask: it waits for the copy until the
               check's budget has passed, in OCaml and outside any solver
               call, so the watcher that hands the run to a copy that has
               decided runs at once.  Still racing then: this is the check's
               timeout at [budget], handled as when the process's own ask
               runs out.  Ended without an answer: asked here as without the
               field (the solver's [unknown] or error is read from an ask of
               the process's own).  Taken over by the copy: [finish] never
               returns. *)
            LoopPhase.phase "mustrat-check-wait-copy" (fun () ->
                PCSatCommon.ParallelRace.wait_settled t ~ms:(budget * 1000));
            match Atomic.get t.PCSatCommon.ParallelRace.state with
            | PCSatCommon.ParallelRace.Racing ->
                continue_census
                  (sprintf "wait timeout budget=%d; the copy goes on" budget);
                continuation :=
                  Some
                    ( turn,
                      primal_strat_wf,
                      primal_strat_fn,
                      dual_strat_wf,
                      dual_strat_fn,
                      primal,
                      t,
                      started );
                f false (freed_reask (PCSP.Problem.Timeout, -1))
            | Copy_done | Process_won ->
                PCSatCommon.ParallelRace.finish t;
                continue_census "copy ended without an answer; asking here";
                ask_here ()
            | Copy_won ->
                (* never returns: the run is the copy's *)
                PCSatCommon.ParallelRace.finish t;
                ask_here ())
        | `Racing t -> (
            let res =
              match
                LoopPhase.phase "mustrat-check" (fun () ->
                    MainSolver.solve ~timeout:(Some budget) chc)
              with
              | res -> res
              | exception exn ->
                  PCSatCommon.ParallelRace.finish t;
                  raise exn
            in
            match res with
            | Ok (PCSP.Problem.Timeout, _) ->
                continue_census
                  (sprintf "process timeout budget=%d; the copy goes on" budget);
                continuation :=
                  Some
                    ( turn,
                      primal_strat_wf,
                      primal_strat_fn,
                      dual_strat_wf,
                      dual_strat_fn,
                      primal,
                      t,
                      started );
                f false (freed_reask (PCSP.Problem.Timeout, -1))
            | _ ->
                PCSatCommon.ParallelRace.finish t;
                continue_census "process decided";
                res >>= fun res -> f false (freed_reask res))
    in
    (* The copy-blind re-check of a check whose copy is still asking it
       ([continue_check_in_copy]), asked in a second forked copy while the
       process waits.  Why not here: when this was written a fixedpoint
       query held the OCaml runtime for its whole length (the Z3 bindings
       give it up only around an SMT solver's check and the simplifier), so
       no other thread of the process ran meanwhile -- not the watcher that
       hands the run to a copy that has decided -- and the re-check asked
       here held back the continued check's answer until the re-check's own
       budget ran out (12 s in the first measured run).  The SPACER backend
       now asks the query with the lock released, so that cost is gone;
       asking aside is kept because it is the measured schedule, and waiting
       for a copy still keeps the process in OCaml, where both copies'
       answers are taken at once.

       Exact: the re-check's copy asks the same check of the same solver at
       the same budget as the process would, and claims the run only with an
       answer the process would read as one -- a win of an established
       encoding, or a counter-play with its derivation; everything else
       (a timeout, an unknown, an error, a win of an encoding not
       established) is what the process reads, after the wait, as the
       re-check's timeout, the arm that handles all of them alike. *)
    let ask_aside () =
      if
        not
          (Common.ForkGuard.fits
             ~growth:(Common.ForkGuard.peak_excess_bytes ())
             ())
      then ask_here ()
      else
        match
          PCSatCommon.ParallelRace.start ~reads:`None (fun () ->
              match MainSolver.solve ~timeout:(Some budget) chc with
              | Ok ((PCSP.Problem.Sat _, _) as r) when copy_blind_established
                ->
                  Some r
              | Ok ((PCSP.Problem.Unsat (Some (PCSP.Problem.Formula _)), _) as r)
                ->
                  Some r
              | _ -> None
              | exception exn when not (Common.Timer.is_async exn) -> None)
        with
        | `Won res' ->
            (* in the re-check's copy, which now is the run: the continued
               check's copy is a sibling, which the process has refused the
               run; it is forgotten here, never stopped from here *)
            continuation := None;
            continue_census
              (sprintf "aside %s budget=%d"
                 (match res' with
                 | PCSP.Problem.Sat _, _ -> "win"
                 | _ -> "counter-play")
                 budget);
            f false (freed_reask res')
        | `Not_started -> ask_here ()
        | `Racing t ->
            LoopPhase.phase "mustrat-check-copy-blind" (fun () ->
                PCSatCommon.ParallelRace.wait_settled t
                  ~ms:((budget * 1000) + race_timeout_grace_ms));
            (* never returns once either copy took the run *)
            PCSatCommon.ParallelRace.finish t;
            continue_census (sprintf "aside none budget=%d" budget);
            f false (PCSP.Problem.Timeout, -1)
    in
    (* [copy_blind_recheck_continued]: the re-check of a timed-out check
       asked in a forked copy with no budget, the process not waiting.  The
       copy claims the run only with an answer [ask_aside]'s copy claims it
       with; the process reads the re-check as timed out at once (the arm of
       [f] that hands a timeout on to the rest of the timeout path), now
       and at every retry of the same check while the copy runs, and also
       once the copy has ended without an answer (asking the same check of
       the same solver again, with a budget, cannot decide more). *)
    let ask_cb_continued () =
      (* a race inherited at a fork is a sibling's, whose answer can no
         longer reach this process: forgotten, and the re-check asked anew *)
      (match !cb_continuation with
      | Some (_, _, _, _, _, _, t)
        when not
               (Pid.equal t.PCSatCommon.ParallelRace.owner
                  (Core_unix.getpid ())) ->
          cb_continuation := None
      | _ -> ());
      match !cb_continuation with
      | Some c when same_cb_continued c ->
          let (_, _, _, _, _, _, t) = c in
          continue_census
            (match Atomic.get t.PCSatCommon.ParallelRace.state with
            | PCSatCommon.ParallelRace.Racing ->
                sprintf "cb-continued still asking budget=%d" budget
            | _ -> sprintf "cb-continued ended budget=%d" budget);
          f false (PCSP.Problem.Timeout, -1)
      | _ -> (
          let started = Common.PhaseTime.now () in
          match
            PCSatCommon.ParallelRace.start ~reads:`None (fun () ->
                match MainSolver.solve ~timeout:None chc with
                | Ok ((PCSP.Problem.Sat _, _) as r) when copy_blind_established
                  ->
                    Some r
                | Ok
                    ((PCSP.Problem.Unsat (Some (PCSP.Problem.Formula _)), _) as
                     r) ->
                    Some r
                | _ -> None
                | exception exn when not (Common.Timer.is_async exn) -> None)
          with
          | `Won res' ->
              (* in the re-check's copy, which now is the run: the other
                 copies are siblings, forgotten here, never stopped *)
              continuation := None;
              cb_continuation := None;
              let elapsed = Common.PhaseTime.now () -. started in
              let b = chc_budget ~backup:false turn in
              b := CheckContinuation.rung_budget ~initial:budget ~elapsed;
              continue_census
                (sprintf "cb-continued %s %.1fs budget=%d->%d"
                   (match res' with
                   | PCSP.Problem.Sat _, _ -> "win"
                   | _ -> "counter-play")
                   elapsed budget !b);
              f false res'
          | `Not_started ->
              (* no copy (memory, a failed fork): the re-check is asked here,
                 at the rung's budget, as without the field *)
              ask_here ()
          | `Racing t ->
              continue_census
                (sprintf "cb-continued started budget=%d" budget);
              cb_continuation :=
                Some
                  ( turn,
                    primal_strat_wf,
                    primal_strat_fn,
                    dual_strat_wf,
                    dual_strat_fn,
                    primal,
                    t );
              f false (PCSP.Problem.Timeout, -1))
    in
    let ask_continued () =
      if
        config.copy_blind_recheck_continued && use_copy_blind
        && Option.is_some for_refinement
      then ask_cb_continued ()
      else if
        continue_field && Option.is_some for_refinement
        &&
        match !continuation with
        | Some c -> same_continued c
        | None -> false
      then ask_aside ()
      else if not continue_on then ask_here ()
      else
        match !continuation with
        | Some ((_, _, _, _, _, _, t, _) as c)
          when same_continued c && config.continued_check_flat_and_or -> (
            (* [continued_check_flat_and_or]: the copy asks the check in the
               other shape, so the process does not only wait for it: it asks
               the written shape again here at this rung's budget, from
               nothing, while the copy goes on.  Decided here: the copy is
               stopped (or, had it claimed the run, this never returns) and
               the process goes on with its own answer.  Timed out here: the
               rung's timeout, the copy still going on, as when the copy is
               waited for. *)
            LoopPhase.phase "mustrat-check" (fun () ->
                MainSolver.solve ~timeout:(Some budget) chc)
            >>= fun res ->
            match res with
            | PCSP.Problem.Timeout, _ ->
                (match Atomic.get t.PCSatCommon.ParallelRace.state with
                | PCSatCommon.ParallelRace.Copy_won ->
                    (* never returns: the run is the copy's *)
                    PCSatCommon.ParallelRace.finish t
                | _ -> ());
                continue_census
                  (sprintf "rung timeout budget=%d (asked here too)" budget);
                f false (PCSP.Problem.Timeout, -1)
            | _ ->
                drop_continuation ();
                continue_census
                  (sprintf "decided here at budget=%d; copy dropped" budget);
                f false (freed_reask res))
        | Some ((_, _, _, _, _, _, t, started) as c) when same_continued c -> (
            let elapsed = Common.PhaseTime.now () -. started in
            Debug.print
            @@ lazy
                 (sprintf
                    "### The check is still being asked by a copy (%.1f sec. \
                     so far); waiting until it has run %d sec."
                    elapsed budget);
            LoopPhase.phase "mustrat-check-wait-copy" (fun () ->
                PCSatCommon.ParallelRace.wait_settled t
                  ~ms:(CheckContinuation.wait_ms ~budget ~elapsed));
            match Atomic.get t.PCSatCommon.ParallelRace.state with
            | PCSatCommon.ParallelRace.Racing ->
                continue_census
                  (sprintf "rung timeout budget=%d at %.1fs" budget
                     (Common.PhaseTime.now () -. started));
                f false (PCSP.Problem.Timeout, -1)
            | Copy_won | Process_won | Copy_done ->
                (* never returns when the copy took the run *)
                drop_continuation ();
                continue_census "copy ended; asking here";
                start_continued ())
        | _ -> start_continued ()
    in
    match strategy_free_won with
    | Some won -> won
    | None ->
    ask_started := Common.PhaseTime.now ();
    play_check_secs := None;
    match race with
    | `Won res' ->
        (* in the copy, which now is the run *)
        if reask_census then
          eprintf "mustrat-race-plain: copy %s budget=%d\n%!"
            (match res' with
            | PCSP.Problem.Sat _, _ -> "win"
            | _ -> "counter-play")
            budget;
        Debug.print
        @@ lazy "### The plain Spacer decided the check first; it continues the run";
        f ~plain_reasked:true false (freed_reask res')
    | `Not_started ->
        if reask_census && race_fields then
          eprintf "mustrat-race-plain: %s budget=%d\n%!"
            (if race_this_rung then "not-started" else "first-rung")
            budget;
        ask_continued ()
    | `Racing t ->
        let res =
          Exn.protect
            ~finally:(fun () -> PCSatCommon.ParallelRace.finish t)
            ~f:(fun () ->
              LoopPhase.phase "mustrat-check" @@ fun () ->
              let res = MainSolver.solve ~timeout:(Some budget) chc in
              (match res with
              | Ok (PCSP.Problem.Timeout, _) ->
                  (* the copy, started a moment later with the same budget,
                     may be about to answer *)
                  PCSatCommon.ParallelRace.wait_settled t
                    ~ms:race_timeout_grace_ms
              | _ -> ());
              res)
        in
        if reask_census then
          eprintf "mustrat-race-plain: process %s budget=%d\n%!"
            (match res with
            | Ok (PCSP.Problem.Sat _, _) -> "win"
            | Ok (PCSP.Problem.Unsat (Some (Formula _)), _) -> "counter-play"
            | Ok (PCSP.Problem.Timeout, _) -> "timeout"
            | _ -> "other")
            budget;
        res >>= fun res -> f ~plain_reasked:true false (freed_reask res)

  (* [shared_name_arity_mismatches primal dual]: the names of the Skolem keys
     ([FN] predicates) of either problem that the other problem declares with
     a different sort.  The refinement moves a value read off one side's
     application of such a name to the other side's key of that name,
     applying it to the key's own parameters, so the two declarations must
     agree; an empty result is the precondition of every read-back.  The
     fixpoint predicates are not compared: the reduction may extend them
     differently on the two sides, and nothing is moved between them. *)
  let shared_name_arity_mismatches primal dual =
    let mismatches keys other =
      let other_senv = PCSP.Problem.senv_of other in
      Map.Poly.fold (PCSP.Problem.fnpvs_senv_of keys) ~init:[]
        ~f:(fun ~key ~data acc ->
          match Map.Poly.find other_senv key with
          | Some sort'
            when not
                   (try Stdlib.( = ) data sort'
                    with exn when not (Common.Timer.is_async exn) -> false) ->
              Ident.name_of_tvar key :: acc
          | _ -> acc)
    in
    List.dedup_and_sort ~compare:String.compare
      (mismatches primal dual @ mismatches dual primal)

  let init_strat_of pfwcsp =
    let fn_strat =
      Map.Poly.map (PCSP.Problem.fnpvs_senv_of pfwcsp) ~f:(fun sort ->
          let params =
            let sargs, sret = Logic.Sort.args_ret_of sort in
            assert (Logic.BoolTerm.is_bool_sort sret);
            Logic.sort_env_list_of_sorts sargs
          in
          let arg_params, (xret, sret) = List.rest_last params in
          ( params,
            Set.Poly.of_list
            @@ List.map
                 ~f:(Logic.BoolTerm.eq_of sret (Logic.ExtTerm.mk_var xret))
            @@ Logic.ExtTerm.mk_dummy sret
               :: List.filter_map arg_params ~f:(fun (x, s) ->
                   if Stdlib.(s = sret) then Some (Logic.ExtTerm.mk_var x)
                   else None) ))
    in
    (* The candidate sets multiply in a clause mentioning several keys, so a
       side whose product exceeds the configured bound starts from each key's
       default term alone (the first element of the list above); the check of
       that smaller strategy is the same query, so no answer depends on it. *)
    let fn_strat =
      let fn_strat, fired =
        InitStrategy.bound_candidate_sets
          ~bound:config.init_fn_terms_product_bound
          ~default:(fun params ->
            let _, (xret, sret) = List.rest_last params in
            Logic.BoolTerm.eq_of sret (Logic.ExtTerm.mk_var xret)
            @@ Logic.ExtTerm.mk_dummy sret)
          fn_strat
      in
      if fired then
        Debug.print
        @@ lazy
             (sprintf
                "### Initial Skolem term sets multiply past %d; each key \
                 starts from its default term alone\n"
                (Option.value_exn config.init_fn_terms_product_bound));
      fn_strat
    in
    ( Map.Poly.map (PCSP.Problem.dwfpvs_senv_of pfwcsp) ~f:(fun sort ->
          let params =
            let sargs, sret = Logic.Sort.args_ret_of sort in
            assert (Logic.BoolTerm.is_bool_sort sret);
            Logic.sort_env_list_of_sorts sargs
          in
          Logic.ExtTerm.mk_lambda params @@ Logic.BoolTerm.mk_bool false),
      fn_strat )

  let solve ?(print_sol = false) muclp =
    let open Or_error.Monad_infix in
    stalls := 0;
    split_cut_seen := false;
    split_first_gate :=
      (not config.split_ground_goals_first_integer_only)
      || SplitFirstGate.applies muclp;
    last_check := None;
    last_bounded_ask := None;
    last_copy_blind_check := None;
    copy_blind_recheck_spent := None;
    drop_continuation ();
    drop_cb_continuation ();
    drop_strategy_free_races ();
    Hashtbl.clear wf_rank_pairs;
    SteerAudit.reset ();
    Hashtbl.clear skolem_term_order;
    Hashtbl.clear joint_initial;
    Hashtbl.clear joint_refinements;
    joint_refinement_id := 0;
    rc_reset ();
    Hashtbl.clear wf_by_construction;
    Hashtbl.clear wf_rank_regions;
    Hashtbl.clear wf_region_vars;
    upstream_rewrites := [];
    Debug.print @@ lazy "======== MuStrat ========";
    Debug.print @@ lazy "-=-=-=-= proving/disproving -=-=-=-=";
    (if rc_on () && Option.is_some config.skolem_term_window then
       Or_error.error_string
         "relative_completeness is refused with skolem_term_window: the \
          window drops offered terms"
     else Ok ())
    >>= fun () ->
    let input = muclp in
    preprocess ~elim_forall:true ~elim_exists:true ~elim_pvar_args:true muclp
    >>= fun muclp ->
    (* [ground_query_solve]: a ground query decided on its finite reachable
       part answers here, before the reductions.  It is asked on the
       optimizer's output, the problem the reductions would receive (the
       optimizer preserves equivalence); under [validate_verdicts] it is asked
       on the input as received instead, so that no unvalidated rewrite stands
       between the input and an answer.  [None] leaves the run as it was. *)
    match
      MuCLP.GroundSolve.run ~phase:"mustrat-ground-solve"
        ~report:(fun line -> Debug.print @@ lazy line)
        config.ground_query_solve
        (if config.validate_verdicts then input else muclp)
    with
    | Some sol ->
        if print_sol then
          print_endline
            (if config.output_yes_no then lts_str_of_solution sol
             else str_of_solution sol);
        Or_error.return (sol, -1, "")
    | None ->
    (* The two sides are linked only by the names of their Skolem keys: the
       refinement moves a counter-play's decision for the checked side's
       universal to the opponent's existential of the same name.  A key is
       named after its block's bound variable, a repeated name getting a
       suffix in traversal order, and [get_dual] reorders the operands of
       [and]/[or]; so in [(forall n m. g \/ A) /\ (forall n m. not g \/ B)]
       the primal's first [n] key sat in the A-block and the dual's in the
       B-block, every decision was filed under the block whose guard made it
       useless, and both sides stalled.  With every binder named apart first,
       a key's name is its own variable's on both sides and denotes the same
       block.  Meaning is kept (alpha-renaming); names only choose which
       candidate terms are tried, and every verdict still comes from a won
       check. *)
    (* The names link the two sides only if a shared name also has the same
       arity on both.  A key's parameters are the variables bound around its
       binder (a universal's name and an existential's Skolem predicate alike
       take every enclosing bound variable, not the other variables of its
       own block), so the arity follows the nesting of the binders.  The dual
       is built by [Evaluator.simplify_neg], which merges a binder directly
       under one of the same kind into one block; the primal is the
       optimizer's output as it stands, and its last step inlines predicate
       bodies after its last simplification, leaving [forall a. forall b. F]
       nested where the dual has [exists b a. not F].  The primal's key for [b]
       then took [a] as a parameter and the dual's did not: a counter-play's
       value for [b], read back from the primal's 7-ary universal into the
       dual's 6-ary existential, was a lambda still waiting for one argument,
       and the next check put that lambda where a formula belongs (an
       assertion failure converting the check, on term-comp's
       [pgarch.t2_fixed] with the plain inlining).  So the primal is given the
       same simplification the dual gets.  Exact: [Evaluator.simplify]
       preserves meaning.  Postcondition (checked below by
       [shared_name_arity_mismatches]): every name both sides declare has the
       same sort on both. *)
    let muclp =
      let simplified = MuCLP.Problem.simplify muclp in
      if config.validate_verdicts then
        upstream_rewrites :=
          ( "binder normalisation",
            List.zip_exn (formulas_of_muclp muclp)
              (formulas_of_muclp simplified) )
          :: !upstream_rewrites;
      simplified
    in
    let muclp = MuCLP.Problem.rename_binders_apart muclp in
    set_pred_index muclp;
    game_largest_literal := RankingCheck.largest_literal (formulas_of_muclp muclp);
    Debug.print @@ lazy "### Generating Primal Problem\n";
    (* [validate_verdicts]: the reduction's rewrites are recorded for the
       check below; off, nothing is recorded *)
    let recording what f =
      if config.validate_verdicts then (
        let res, pairs = MuCLP.Reducer.with_recorded_rewrites f in
        upstream_rewrites := (what, pairs) :: !upstream_rewrites;
        res)
      else f ()
    in
    (* [clausal_reductions]: both reductions in negation and conjunctive
       normal form, an equivalent shape; off, as built *)
    let clausal =
      if config.clausal_reductions then
        Tuple2.map_fst ~f:(PCSP.Problem.to_nnf >> PCSP.Problem.to_cnf)
      else Fn.id
    in
    let primal, primal_nu_wfs =
      clausal
      @@ recording "primal reduction" (fun () ->
             to_pfwcsp ~layout:copy_layout_primal muclp)
    in
    Debug.print
    @@ lazy (sprintf "\n### Primal Problem:\n%s\n" @@ PCSP.Problem.str_of primal);
    Debug.print @@ lazy "### Generating Dual Problem\n";
    let dual, dual_nu_wfs =
      clausal
      @@
      let dual_muclp, negations = MuCLP.Util.get_dual_with_pairs muclp in
      if config.validate_verdicts then
        upstream_rewrites := ("dual negation", negations) :: !upstream_rewrites;
      recording "dual reduction" (fun () ->
          to_pfwcsp ~layout:copy_layout_dual dual_muclp)
    in
    Debug.print
    @@ lazy (sprintf "\n### Dual Problem:\n%s\n" @@ PCSP.Problem.str_of dual);
    (match shared_name_arity_mismatches primal dual with
    | [] -> ()
    | mismatches ->
        failwith
        @@ sprintf
             "MuStrat: the primal and the dual declare %s with different \
              sorts, so a decision read off one side cannot be moved to the \
              other"
             (String.concat ~sep:", " mismatches));
    let primal_strat_wf, primal_strat_fn = init_strat_of primal in
    let dual_strat_wf, dual_strat_fn = init_strat_of dual in
    Debug.print @@ lazy "\n## Initialized the current primal wf strategy:";
    Map.Poly.iteri primal_strat_wf ~f:(fun ~key ~data ->
        let args, phi' = Logic.Term.let_lam data in
        print_strat key args phi');
    Debug.print @@ lazy "\n## Initialized the current primal fn strategy:";
    Map.Poly.iteri primal_strat_fn ~f:(fun ~key ~data:(args, terms') ->
        Set.iter terms' ~f:(print_strat key args));
    Debug.print @@ lazy "\n## Initialized the current dual wf strategy:";
    Map.Poly.iteri dual_strat_wf ~f:(fun ~key ~data ->
        let args, phi' = Logic.Term.let_lam data in
        print_strat key args phi');
    Debug.print @@ lazy "\n## Initialized the current dual fn strategy:";
    Map.Poly.iteri dual_strat_fn ~f:(fun ~key ~data:(args, terms') ->
        Set.iter terms' ~f:(print_strat key args));
    (* a copy still asking a check ([continue_check_in_copy]) must not
       outlive the run: stopped before any answer leaves, and on a raise *)
    (* [validate_verdicts]: every rewrite of the input recorded above must be
       an equivalence, or no verdict of this run is trusted *)
    let upstream_refusal =
      if not config.validate_verdicts then None
      else
        List.find_map (List.rev !upstream_rewrites) ~f:(fun (what, pairs) ->
            match
              VerdictValidation.equivalent_pairs
                ~timeout_ms:config.validate_verdicts_timeout_ms pairs
            with
            | Ok () ->
                eprintf "mustrat-validate: %s (%d rewrites) validated\n%!" what
                  (List.length pairs);
                None
            | Error r -> Some (what, r))
    in
    (match upstream_refusal with
    | Some (what, reason) ->
        eprintf "mustrat-validate: %s refused\n%!" what;
        Debug.print
        @@ lazy
             (sprintf "### The %s is not validated (answering unknown): %s"
                what reason);
        Ok Unknown
    | None ->
        Exn.protect
          ~finally:(fun () ->
            drop_continuation ();
            drop_cb_continuation ();
            drop_strategy_free_races ())
          ~f:(fun () ->
            solve_primal_dual true
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)))
    >>= function
    | sol ->
        Debug.print @@ lazy "=========================";
        if print_sol then
          print_endline
          @@ sprintf "%s"
               (if config.output_yes_no then lts_str_of_solution sol
                else str_of_solution sol);
        Or_error.return (sol, -1, "" (*ToDo*))

  let solve_pcsp ?(print_sol = false) pcsp =
    (* This backend reduces a predicate constraint problem to fixpoint logic,
       and a fixpoint problem has no place to carry a predicate's KIND: the
       reduction makes every predicate an ordinary least fixpoint.  Every kind
       but the ordinary one states an obligation the clauses do not -- a
       functional predicate must be total and deterministic, a well-founded one
       may not contain a cycle, a non-empty one may not be false everywhere --
       so dropping it answers a weaker question, and the answer comes back
       "satisfiable" on inputs the kind is what refutes.  A three-line file
       whose two clauses force one functional predicate to take two values at
       the same argument is answered satisfiable here and refuted by the
       predicate constraint solver.

       The problem constructor is shared -- the class name on the command line
       documents the input and nothing checks it -- so the compatibility table
       cannot refuse the pairing and the check has to happen here.  Naming the
       one kind that IS supported cannot go stale the way a list of kinds to
       refuse did: the kinds nobody thought of were accepted by such a list. *)
    PCSP.Problem.refuse_non_ord_kinds ~backend:"MuStrat" pcsp;
    let (module Preprocessor : Preprocessor.PreprocessorType) =
      Preprocessor.(make @@ Config.make true config.verbose 4 4 true)
    in
    Debug.print
    @@ lazy "************* converting pfwCSP to muCLP ***************";
    Preprocessor.solve
      (fun ?oracle pcsp ->
        ignore oracle;
        let open Or_error.Monad_infix in
        solve ~print_sol:false (MuCLP.Util.of_chc ~print:Debug.print pcsp)
        >>= fun (sol, _, _) ->
        let sol =
          match sol with
          | Valid -> PCSP.Problem.Sat Map.Poly.empty (* ToDo *)
          | Invalid -> PCSP.Problem.Unsat None (* ToDo *)
          | Unknown -> PCSP.Problem.Unknown
          | Timeout -> PCSP.Problem.Timeout
        in
        if print_sol then
          print_endline @@ sprintf "%s" (PCSP.Problem.str_of_solution sol);
        Or_error.return
          ( sol,
            {
              PCSatCommon.State.num_cegis_iters = -1;
              unsat_witness = None;
              kind_certificates = Map.Poly.empty;
            } ))
      pcsp

  let determinize fml chc det params =
    Debug.print @@ lazy "strategy template:";
    Map.Poly.iteri det ~f:(fun ~key ~data:(senv, t) ->
        Debug.print
        @@ lazy
             (sprintf "%s: %s" (Ident.name_of_tvar key)
                (Logic.ExtTerm.str_of_term Map.Poly.empty
                   (Map.force_merge (Map.Poly.of_alist_exn params) senv)
                   t)));
    Debug.print @@ lazy "";
    let chc =
      ( Map.Poly.empty,
        Logic.Term.mk_apps
          (Logic.BoolTerm.mk_imply ())
          [ fml; Logic.BoolTerm.mk_bool false ] )
      :: chc
    in
    let params = PCSP.Params.make @@ Map.Poly.of_alist_exn params in
    let problem = PCSP.Problem.of_formulas ~params (Set.Poly.of_list chc) in
    Debug.print @@ lazy "recursion-free CHC problem for determinization:";
    Debug.print @@ lazy (PCSP.Problem.str_of problem);
    Debug.print @@ lazy "";
    let open Or_error in
    pcsp_solver_determ () >>= fun (module PCSPSolver) ->
    PCSPSolver.solve problem >>= function
    | PCSP.Problem.Sat subs, _num_iters ->
        Debug.print
        @@ lazy
             ("solution:\n" ^ Logic.str_of_term_subst Logic.ExtTerm.str_of subs);
        Ok (Map.Poly.map det ~f:(Tuple2.map_snd ~f:(Logic.ExtTerm.subst subs)))
    | PCSP.Problem.Unsat _, _num_iters -> assert false
    | PCSP.Problem.Unknown, _num_iters -> assert false
    | PCSP.Problem.OutSpace _, _ -> assert false
    | PCSP.Problem.Timeout, _ -> assert false

  let lia_solve_smt f print_sol to_determinize =
    let open StratSynth in
    let f = Option.value_exn @@ LIA.formula_of_term_with_constants f in
    Debug.print @@ lazy (sprintf "theory is LIA");
    Debug.print
    @@ lazy (sprintf "input: %s\n" (LIAStrategySynthesis.formula_to_string f));
    let p, s = LIAStrategySynthesis.nondet_strategy_synthesis z3_solve f in
    Debug.print
    @@ lazy
         (sprintf "strategy skelton for %s:\n%s"
            (LIAStrategySynthesis.player_to_string p)
            (LIAStrategySynthesis.ssforest_to_string s));
    let f =
      match p with SAT -> f | UNSAT -> PreFormula.neg_formula LIA.neg_atom f
    in
    (if to_determinize then
       let fml, chc, det, params = LIAStrategySynthesis.loseCHC [] s f in
       match determinize fml chc det params with
       | Ok ds ->
           Debug.print
           @@ lazy
                (sprintf "determinized strategy for %s:"
                   (LIAStrategySynthesis.player_to_string p));
           Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
               Debug.print
               @@ lazy
                    (sprintf "%s: %s" (Ident.name_of_tvar key)
                       (Logic.ExtTerm.str_of_term Map.Poly.empty senv t)))
       | Error err -> failwith (Error.to_string_hum err));
    let solution =
      match p with
      | SAT -> SMT.Problem.Sat [] (*ToDo*)
      | UNSAT -> SMT.Problem.Unsat
    in
    Debug.print @@ lazy "=========================";
    if print_sol then
      print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
    Ok solution

  (* [lra_virtual_terms] selects the game: the step rule ([LRAStrategySynthesis],
     the default) or Loos-Weispfenning virtual terms ([LRAVSStrategySynthesis]).
     Both decide the verdict by checking a concrete strategy, so either answer
     is sound; they differ in which strategies they find. *)
  let lra_solve_smt ~virtual_terms f print_sol to_determinize =
    let open StratSynth in
    let f = Option.value_exn @@ LRA.formula_of_term_with_constants f in
    Debug.print @@ lazy (sprintf "theory is LRA");
    Debug.print
    @@ lazy (sprintf "input: %s\n" (LRAStrategySynthesis.formula_to_string f));
    let play ~nondet ~is_sat ~player_to_string ~ssforest_to_string ~lose =
      let p, s = nondet z3_solve f in
      Debug.print
      @@ lazy
           (sprintf "strategy skelton for %s:\n%s" (player_to_string p)
              (ssforest_to_string s));
      let sat = is_sat p in
      let f = if sat then f else PreFormula.neg_formula LRA.neg_atom f in
      (if to_determinize then
         let fml, chc, det, params = lose [] s f in
         match determinize fml chc det params with
         | Ok ds ->
             Debug.print
             @@ lazy
                  (sprintf "determinized strategy for %s:" (player_to_string p));
             Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
                 Debug.print
                 @@ lazy
                      (sprintf "%s: %s" (Ident.name_of_tvar key)
                         (Logic.ExtTerm.str_of_term Map.Poly.empty senv t)))
         | Error err -> failwith (Error.to_string_hum err));
      sat
    in
    let sat =
      if virtual_terms then
        let open LRAVSStrategySynthesis in
        play ~nondet:nondet_strategy_synthesis
          ~is_sat:(function SAT -> true | UNSAT -> false)
          ~player_to_string
          ~ssforest_to_string:(fun s -> ssforest_to_string s)
          ~lose:loseCHC
      else
        let open LRAStrategySynthesis in
        play ~nondet:nondet_strategy_synthesis
          ~is_sat:(function SAT -> true | UNSAT -> false)
          ~player_to_string
          ~ssforest_to_string:(fun s -> ssforest_to_string s)
          ~lose:loseCHC
    in
    let solution = if sat then SMT.Problem.Sat [] (*ToDo*) else SMT.Problem.Unsat in
    Debug.print @@ lazy "=========================";
    if print_sol then
      print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
    Ok solution

  (* [encode_bool_vars g]: [g] with every Boolean variable [b] bound by one
     of its quantifiers replaced by an arithmetic one [x] of the same name,
     bound by the same quantifier, each occurrence of [b] read as [x > 0],
     and every Boolean constant of the script (a nullary predicate variable
     here) replaced likewise by a fresh [x] bound existentially outermost;
     [x] is real when [g] binds a real anywhere and an integer otherwise.
     Precondition: [g] has no free term variable (the script's free
     arithmetic constants were bound existentially at the outermost level),
     is let-free and alpha-converted.  A Boolean constant is outermost
     existential too, which is where its [x] is bound.
     Guarantee: the result is equivalent to [g], since [x > 0] takes both
     truth values as [x] ranges over the reals or the integers, so each
     quantifier over [x] ranges over exactly the truth values [b] ranged
     over, with the same player choosing; no Boolean variable is left.  It
     is linear in [g]: a Boolean variable is read where it is compared with
     [true] or [false] (which is how the reader writes a Boolean used as a
     formula) or with another Boolean variable, and the one equivalence it
     builds duplicates two atoms, never a subformula.  [None] when [g] uses
     a Boolean variable any other way (under an [ite], in an equality
     between Boolean formulas, under a [Random] binder), which the caller
     refuses.  [g] itself when it binds no Boolean and has no Boolean
     constant, so the formulas this
     does not concern reach the strategy synthesis unchanged.  The
     strategy game has no Boolean sort: before this, such an input was
     refused as outside both arithmetic theories. *)
  let encode_bool_vars g =
    let open LogicOld in
    let is_bool = function T_bool.SBool -> true | _ -> false in
    let rec binds f phi =
      match phi with
      | Formula.Bind (_, senv, phi, _) ->
          List.exists senv ~f:(fun (_, s) -> f s) || binds f phi
      | Formula.UnaryOp (_, phi, _) -> binds f phi
      | Formula.BinaryOp (_, phi1, phi2, _) -> binds f phi1 || binds f phi2
      | _ -> false
    in
    (* the reader writes a Boolean constant of the script ([declare-fun b
       () Bool]) as a nullary predicate variable, not as a term variable, so
       it is free here although every free term variable has been bound *)
    let consts =
      Formula.pred_sort_env_of g |> Set.to_list
      |> List.filter_map ~f:(function p, [] -> Some p | _ -> None)
    in
    if List.is_empty consts && not (binds is_bool g) then Some g
    else
      let target =
        if binds (function T_real.SReal -> true | _ -> false) g then
          T_real.SReal
        else T_int.SInt
      in
      let positive x =
        let v = Term.mk_var x target in
        Formula.mk_atom
          (match target with
          | T_real.SReal -> T_real.mk_rgt v (T_real.rzero ())
          | _ -> T_int.mk_gt v (T_int.zero ()))
      in
      let const_vars =
        List.map consts ~f:(fun p -> (p, Ident.mk_fresh_tvar ()))
      in
      let exception Unsupported in
      let rec of_bool_term = function
        | Term.Var (x, T_bool.SBool, _) -> positive x
        | Term.FunApp (T_bool.Formula phi, [], _) -> enc phi
        | _ -> raise Unsupported
      and enc_atom atm =
        match atm with
        | Atom.App
            (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op), [ t1; t2 ], _)
          when is_bool (Term.sort_of t1) -> (
            let iff =
              if T_bool.is_true t2 then of_bool_term t1
              else if T_bool.is_false t2 then Formula.mk_neg (of_bool_term t1)
              else if T_bool.is_true t1 then of_bool_term t2
              else if T_bool.is_false t1 then Formula.mk_neg (of_bool_term t2)
              else
                match (t1, t2) with
                | Term.Var (_, T_bool.SBool, _), Term.Var (_, T_bool.SBool, _)
                  ->
                    let f1 = of_bool_term t1 and f2 = of_bool_term t2 in
                    Formula.mk_or (Formula.mk_and f1 f2)
                      (Formula.mk_and (Formula.mk_neg f1) (Formula.mk_neg f2))
                | _ -> raise Unsupported
            in
            match op with T_bool.Eq -> iff | _ -> Formula.mk_neg iff)
        | Atom.App (Predicate.Var (p, []), [], _) -> (
            match List.Assoc.find const_vars ~equal:Ident.pvar_equal p with
            | Some x -> positive x
            | None -> raise Unsupported)
        | _ ->
            if Set.exists (Atom.term_sort_env_of atm) ~f:(snd >> is_bool) then
              raise Unsupported
            else Formula.mk_atom atm
      and enc = function
        | Formula.Atom (atm, _) -> enc_atom atm
        | Formula.UnaryOp (op, phi, info) -> Formula.mk_unop ~info op (enc phi)
        | Formula.BinaryOp (op, phi1, phi2, info) ->
            Formula.mk_binop ~info op (enc phi1) (enc phi2)
        | Formula.Bind
            (((Formula.Forall | Formula.Exists) as b), senv, phi, info) ->
            Formula.mk_bind ~info b
              (List.map senv ~f:(fun (x, s) ->
                   (x, if is_bool s then target else s)))
              (enc phi)
        | _ -> raise Unsupported
      in
      try
        Some
          (Formula.mk_exists_if_bounded
             (List.map const_vars ~f:(fun (_, x) -> (x, target)))
             (enc g))
      with Unsupported -> None

  let solve_smt ?(print_sol = false) g =
    Debug.print
    @@ lazy (sprintf "original input: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      let senv = Set.to_list @@ LogicOld.Formula.sort_env_of g in
      LogicOld.Formula.mk_exists_if_bounded senv g
    in
    Debug.print @@ lazy (sprintf "closed: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      LogicOld.Formula.elim_let
      @@ Normalizer.normalize_let ~rename:true
      @@ Typeinf.typeinf_formula
           ~print:(*Debug.print*) (fun _ -> ())
           ~default:(Some LogicOld.T_int.SInt (*ToDo*))
      @@ LogicOld.Formula.aconv_tvar g
    in
    (* [None] leaves [g] as it was, to be refused below unless it simplifies
       to a truth value *)
    let encoded = encode_bool_vars g in
    let g =
      Normalizer.normalize @@ Evaluator.simplify @@ LogicOld.Formula.rm_div_mod
      @@ LogicOld.Formula.elim_redundant_quantifiers @@ Normalizer.normalize
      @@ Evaluator.simplify @@ LogicOld.Formula.elim_ite @@ Normalizer.normalize
      @@ Option.value encoded ~default:g
    in
    Debug.print @@ lazy (sprintf "input: %s\n" (LogicOld.Formula.str_of g));
    let f = Logic.ExtTerm.of_old_formula g in
    if false then
      Debug.print
      @@ lazy (sprintf "original input: %s\n" (Logic.ExtTerm.str_of f));
    (* [g] is closed (its free variables were bound existentially above), so
       a [g] the simplification reduced to a truth value is decided by that
       value: [true] is satisfiable and [false] is not, with no strategy to
       synthesise.  A truth value left inside [g] (under a quantifier the
       simplification kept, as [exists x. false]) is read by the arithmetic
       forms below as the empty conjunction or disjunction; their plain
       readers decline it, and before both cases existed every such formula,
       even [(assert true)], was refused as outside both theories. *)
    if LogicOld.Formula.is_true g || LogicOld.Formula.is_false g then (
      let solution =
        if LogicOld.Formula.is_true g then SMT.Problem.Sat [] (*ToDo*)
        else SMT.Problem.Unsat
      in
      Debug.print @@ lazy "the input simplified to a truth value";
      if print_sol then
        print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
      Ok solution)
    else
      (* [Too_many_residues] is the integer strategy synthesis declining a
         case split over the residues of a divisor too large to enumerate
         (raised while reading the formula or while solving it), so it is a
         refusal of the input like the one below, not a crash *)
      try
        if Option.is_some @@ StratSynth.LIA.formula_of_term_with_constants f
        then lia_solve_smt f print_sol config.determinize
        else if
          Option.is_some @@ StratSynth.LRA.formula_of_term_with_constants f
        then
          lra_solve_smt ~virtual_terms:config.lra_virtual_terms f print_sol
            config.determinize
        else if Option.is_none encoded then
          Or_error.error_string
            "MuStrat's SMT solver reads a Boolean variable only as a truth \
             value (compared with true or false) or compared with another \
             Boolean variable, and this formula uses one otherwise"
        else
          (* a refusal of the input, so an error value, not an exception: the
             strategy synthesis has an integer and a real arithmetic form and
             no other *)
          Or_error.error_string
            "MuStrat's SMT solver handles linear integer arithmetic or linear \
             real arithmetic (LIA or LRA) only, and this formula is in neither"
      with StratSynth.LIA.Too_many_residues n ->
        Or_error.error_string
          (sprintf
             "MuStrat's integer strategy synthesis declines this formula: it \
              needs a case split over %s residues of a divisor (at most %s are \
              enumerated)"
             (Z.to_string n)
             (Z.to_string StratSynth.LIA.max_residue_cases))
end

(*
module RandomFormula = struct
  let random_affine vars =
    let vars' = None :: List.map ~f:(fun x -> Some x) vars in
    let max = 20 in
    List.map ~f:(fun x -> (x, Z.of_int (Random.int max - (max / 2)))) vars'
    |> Map.Poly.of_alist_exn

  let random_atom_gt0 vars = LIA.Gt0 (random_affine vars)

  let random_atom_div vars =
    LIA.Div (Z.of_int (Random.int 10 + 1), random_affine vars)

  let random_atom = if Random.bool () then random_atom_gt0 else random_atom_div

  let rec random_formula depth vars var_prefix r =
    let open PreFormula in
    let get_newvar () =
      let n = !r in
      r := n + 1;
      Ident.Tvar (var_prefix ^ string_of_int n)
    in
    if depth <= 0 then Atom (random_atom vars)
    else
      match Random.int 5 with
      | 0 -> Atom (random_atom_gt0 vars)
      | 1 ->
          And
            (List.init (Random.int 5) ~f:(fun _ ->
                 random_formula (depth - 1) vars var_prefix r))
      | 2 ->
          Or
            (List.init (Random.int 5) ~f:(fun _ ->
                 random_formula (depth - 1) vars var_prefix r))
      | 3 ->
          let newvar = get_newvar () in
          Bind
            ( Forall,
              (newvar, IntTerm.SInt),
              random_formula (depth - 1) (newvar :: vars) var_prefix r )
      | 4 ->
          let newvar = get_newvar () in
          Bind
            ( Exists,
              (newvar, IntTerm.SInt),
              random_formula (depth - 1) (newvar :: vars) var_prefix r )
      | _ -> assert false

  let rec winning ds =
    let open LIAStrategySynthesis in
    let open PreFormula in
    function
    | Atom a -> (LIA.term_of_atom a, [])
    | And l ->
        let fs, vars = List.map ~f:(winning ds) l |> List.unzip in
        (BoolTerm.and_of fs, List.concat vars)
    | Or l ->
        let fs, vars = List.map ~f:(winning ds) l |> List.unzip in
        (BoolTerm.or_of fs, List.concat vars)
    | Bind (Forall, v, f) ->
        let f', vars = winning ds f in
        (f', v :: vars)
    | Bind (Exists, (tvar, _), f) ->
        let f', vars = winning ds f in
        let _, t = Map.Poly.find_exn ds tvar in
        (Term.subst (Map.Poly.singleton tvar t) f', vars)

  let test n =
    let open LIAStrategySynthesis in
    for _ = 1 to n do
      let depth = Random.int 10 in
      let f = random_formula depth [] "x" (ref 0) in
      printf "input: %s\n" (formula_to_string f);
      let p, s = nondet_strategy_synthesis f in
      printf "%s\n%s\n" (player_to_string p) (ssforest_to_string s);
      let f =
        match p with SAT -> f | UNSAT -> PreFormula.neg_formula LIA.neg_atom f
      in
      match determinize solve_pcsp s f with
      | Ok ds ->
          print_endline "strategy:";
          Map.Poly.iteri
            ~f:(fun ~key ~data:(senv, t) ->
              printf "%s: %s\n" (Ident.name_of_tvar key)
                (Logic.ExtTerm.str_of_term senv t))
            ds;
          let win, vars = winning ds f in
          let not_win = BoolTerm.neg_of win in
          let module Z3interface =
            Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
          assert (
            Option.is_none
              (Z3interface.check_sat [ not_win ] vars (Z3.mk_context [])))
      | Error _ -> assert false
    done
end

let () =
  let open LIAStrategySynthesis in
  let open PreFormula in
  (match SMT.Smtlib2.from_smt2_file (Sys.get_argv ()).(1) with
  | Ok f -> (
      print_endline @@ LogicOld.Formula.str_of f;
      let f = Logic.ExtTerm.of_old_formula f |> LIA.formula_of_term in
      let f = Option.value_exn f in
      printf "input: %s\n" (formula_to_string f);
      let p, s = nondet_strategy_synthesis f in
      printf "%s\n%s\n" (player_to_string p) (ssforest_to_string s);
      let f =
        match p with SAT -> f | UNSAT -> PreFormula.neg_formula LIA.neg_atom f
      in
      match determinize solve_pcsp s f with
      | Ok ds ->
          Map.Poly.iteri
            ~f:(fun ~key ~data:(senv, t) ->
              printf "%s: %s\n" (Ident.name_of_tvar key)
                (Logic.ExtTerm.str_of_term senv t))
            ds
      | Error _ -> ())
  | Error _ -> assert false);
  print_string "random test\n";
  Random.self_init ();
  RandomFormula.test 100
*)
