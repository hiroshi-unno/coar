open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* Dropping the disjuncts of a formula that repeat an earlier one up to the
   names of their bound variables.

   Contract of [disjuncts phi]: the result is [phi] itself, or the disjunction,
   in their original order, of the disjuncts of [phi] (as
   [Formula.disjuncts_list_of] lists them) without every disjunct that is
   alpha-equivalent to an earlier one -- the same formula once the binders of
   each are renamed, in traversal order, by a counter of its own
   ([Formula.aconv_tvar_norm]); free variables are compared as they are.  So
   the result is equivalent to [phi] in every model and for every
   interpretation of the unknowns ([a \/ a' = a] when [a'] is a renaming of
   [a]'s bound variables).  [phi] is returned unchanged when nothing is
   dropped, when it has fewer than two disjuncts, or when a disjunct has a
   [let] or a variable (free or bound) spelled like the names the comparison
   makes, where the renaming would not be alpha-equivalence.

   Why it is wanted.  A premise the reader inserts into every clause that may
   depend on a universal function -- a [:law] -- is a closed quantified
   formula, and every clause carries it with binders of its own.  Resolution
   unions the two clauses' pure parts, so a resolvent holds one copy per
   clause inlined into it; set-based merging and condensation compare
   disjuncts syntactically and see different binders, so the copies stay.  On
   a Rust-derived input whose laws reach a long straight-line body, 36,158 of
   the 52,710 disjuncts of 251 resolvents were such copies (346 of 439 in one
   resolvent), and the resolvents' total size grew fivefold. *)
(* the number of resolvents [COAR_JOINT_DUMP] has written (instrument only) *)
let joint_dump_count = ref 0

(* whether [COAR_CONDENSE_REPLAY] has replayed its condensation (instrument
   only) *)
let condense_replayed = ref false

(* whether the predicate eliminator's pure-part condensation of each resolvent
   also drops atoms together with the disjuncts over their variables
   ([ClauseOld.condense_pure ~joint]; the preprocessor's
   [elim_joint_condense]); process-wide and only ever turned on *)
let joint_condense = ref false

(* the preprocessor's [elim_joint_prune_doomed]
   ([ClauseOld.condense_pure ~joint_prune_doomed]); process-wide and only
   ever turned on *)
let joint_prune_doomed = ref false

module AlphaDedup = struct
  (* whether the predicate eliminator applies [disjuncts] to each resolvent
     (the preprocessor's [elim_dedup_alpha_disjuncts]); process-wide and only
     ever turned on, like the reader's switches *)
  let enabled = ref false

  let prefix = "#adb"

  let spelled_like_ours x =
    String.is_prefix (Ident.name_of_tvar x) ~prefix

  let canon d =
    let k = ref 0 in
    Formula.aconv_tvar_norm
      (fun () ->
        incr k;
        Ident.Tvar (sprintf "%s%d" prefix !k))
      d

  let disjuncts phi =
    let ds = Formula.disjuncts_list_of phi in
    if List.length ds < 2 then phi
    else if
      List.exists ds ~f:(fun d ->
          (not (Formula.is_let_free d))
          || Set.exists (Formula.tvs_of d) ~f:spelled_like_ours
          || Set.exists (Formula.quantified_sort_env_of d) ~f:(fun (x, _) ->
                 spelled_like_ours x))
    then phi
    else
      let seen = Hashtbl.create (module String) in
      let dropped = ref 0 in
      let kept =
        List.filter ds ~f:(fun d ->
            (* only a quantified disjunct can differ from another by bound
               names alone; a quantifier-free one is compared as it is *)
            let c =
              if Set.is_empty (Formula.quantified_sort_env_of d) then d
              else canon d
            in
            let key = Formula.str_of c in
            let same c' = try Stdlib.(c = c') with Invalid_argument _ -> false in
            match Hashtbl.find seen key with
            | Some cs when List.exists cs ~f:same ->
                incr dropped;
                false
            | Some cs ->
                Hashtbl.set seen ~key ~data:(c :: cs);
                true
            | None ->
                Hashtbl.set seen ~key ~data:[ c ];
                true)
      in
      if !dropped = 0 then phi else Formula.or_of kept
end

(* Keys for recording the answers of validity questions.

   [plain] is the sorted list of a formula's disjuncts with the variables of
   each quantifier block sorted by name.  [alpha] is in addition invariant
   under an injective renaming of the formula's variables, free and bound:
   the question the key stands for is whether the formula is VALID, that is
   whether its universal closure holds, and the closure does not change when
   its variables are renamed injectively (sorts kept) nor when its disjuncts
   or the variables of one quantifier block are reordered.

   Contract of [alpha]: it returns a list of formulas whose disjunction is
   obtained from the argument by reordering disjuncts, permuting the
   variables within a quantifier block, renaming every top-level binder to a
   fresh name, and renaming the free variables injectively to fresh names; so
   two formulas with equal keys are valid together or not at all.  (It is
   meant to be complete up to renaming only where the canonical order it uses
   is: a disjunct order or a block order that ties on the name-blind rendering
   is broken by the names, which can only give two alpha-variants two keys,
   never two different questions one key.)

   The canonical order must not depend on the names being normalised away,
   or two alpha-variants would get their disjuncts, and then their new names,
   in different orders: disjuncts are sorted by a rendering in which every
   free variable is written the same, and a variable's new name is its rank
   of first occurrence in the printed text of the sorted disjuncts, found by
   printing each variable as a distinct marker.  A formula with a [let], a
   [let rec], or a free variable spelled like the names this function makes
   gets [plain]'s key instead, which is sound and merely finer. *)
module ValidKey = struct
  let rec canon_binders = function
    | Formula.Bind (binder, senv, body, info) ->
        Formula.mk_bind ~info binder
          (List.sort senv ~compare:(fun (x, _) (y, _) -> Ident.tvar_compare x y))
          (canon_binders body)
    | Formula.UnaryOp (op, phi, info) ->
        Formula.mk_unop ~info op (canon_binders phi)
    | Formula.BinaryOp (op, phi1, phi2, info) ->
        Formula.mk_binop ~info op (canon_binders phi1) (canon_binders phi2)
    | Formula.LetFormula (x, sort, def, body, info) ->
        Formula.mk_let_formula ~info x sort def (canon_binders body)
    | phi -> phi

  let plain phi =
    List.sort ~compare:Stdlib.compare
      (List.map ~f:canon_binders (Set.to_list (Formula.disjuncts_of phi)))

  let bound_prefix = "#ab"
  let free_prefix = "#af"

  (* the position in [text vars'] at which each of [vars] first occurs, where
     [text] prints its argument renaming with the given map; a variable that
     does not occur ranks last *)
  let first_occurrence text vars =
    let vars = List.dedup_and_sort vars ~compare:Ident.tvar_compare in
    let marks =
      List.mapi vars ~f:(fun i x -> (x, Ident.Tvar (sprintf "@%d@" i)))
    in
    let s = text (Map.Poly.of_alist_exn marks) in
    let rank =
      Map.Poly.of_alist_exn
      @@ List.map marks ~f:(fun (x, Ident.Tvar m) ->
          ( x,
            Option.value ~default:Int.max_value
              (String.substr_index s ~pattern:m) ))
    in
    fun x -> Option.value ~default:Int.max_value (Map.Poly.find rank x)

  (* each top-level quantifier block ordered by sort, then by first occurrence
     in its body: a name-blind order of the block's variables *)
  let rec order_blocks = function
    | Formula.Bind (binder, senv, body, info) ->
        let body = order_blocks body in
        let rank =
          first_occurrence
            (fun ren -> Formula.str_of (Formula.rename ren body))
            (List.map ~f:fst senv)
        in
        Formula.mk_bind ~info binder
          (List.stable_sort senv ~compare:(fun (x, s) (y, t) ->
               match
                 String.compare (Term.str_of_sort s) (Term.str_of_sort t)
               with
               | 0 -> Int.compare (rank x) (rank y)
               | c -> c))
          body
    | Formula.UnaryOp (op, phi, info) ->
        Formula.mk_unop ~info op (order_blocks phi)
    | Formula.BinaryOp (op, phi1, phi2, info) ->
        Formula.mk_binop ~info op (order_blocks phi1) (order_blocks phi2)
    | phi -> phi

  let spelled_like_ours x =
    let n = Ident.name_of_tvar x in
    String.is_prefix n ~prefix:bound_prefix
    || String.is_prefix n ~prefix:free_prefix

  let alpha phi =
    let ds = Set.to_list (Formula.disjuncts_of phi) in
    if
      List.exists ds ~f:(fun d ->
          (not (Formula.is_let_free d))
          || Set.exists (Formula.tvs_of d) ~f:spelled_like_ours)
    then plain phi
    else
      (* binders renamed per disjunct, by a counter in traversal order *)
      let ds =
        List.map ds ~f:(fun d ->
            let n = ref 0 in
            let next () =
              incr n;
              Ident.Tvar (sprintf "%s%d" bound_prefix !n)
            in
            Formula.aconv_tvar_norm next (order_blocks d))
      in
      let blind d =
        let all_one =
          Map.Poly.of_alist_exn
          @@ List.map (Set.to_list (Formula.tvs_of d)) ~f:(fun x ->
              (x, Ident.Tvar free_prefix))
        in
        Formula.str_of (Formula.rename all_one d)
      in
      let ds =
        List.map ds ~f:(fun d -> (blind d, d))
        |> List.sort ~compare:(fun (s1, d1) (s2, d2) ->
            match String.compare s1 s2 with
            | 0 -> Stdlib.compare d1 d2
            | c -> c)
        |> List.map ~f:snd
      in
      let fvs = Set.to_list (Set.Poly.union_list (List.map ds ~f:Formula.tvs_of)) in
      let rank =
        first_occurrence
          (fun ren ->
            String.concat ~sep:" | "
              (List.map ds ~f:(fun d -> Formula.str_of (Formula.rename ren d))))
          fvs
      in
      let ren =
        List.stable_sort fvs ~compare:(fun x y ->
            match Int.compare (rank x) (rank y) with
            | 0 -> Ident.tvar_compare x y
            | c -> c)
        |> List.mapi ~f:(fun i x ->
            (x, Ident.Tvar (sprintf "%s%d" free_prefix (i + 1))))
        |> Map.Poly.of_alist_exn
      in
      List.map ds ~f:(Formula.rename ren)
end

(* Deferring the validity question of a large pure clause.

   A clause with no predicate application in its atom sets is PURE; when its
   pure part mentions no unknown either, [ClauseOld.simplify] asks whether the
   whole clause is valid ([separate] puts every disjunct in the part it asks
   about), dropping the clause on [`Valid], turning it into [false] on a
   theory-fixed [`Invalid], and keeping it whole on [`Unknown].  Such a clause
   is counted by no elimination rule (the accounting reads only the atom
   sets), so whether it is dropped changes no later resolution step.

   [wrap] answers [`Unknown] without asking, for a pure clause whose question
   has at least [min_disjuncts] disjuncts, when [defer] is set; otherwise it is
   [check_valid] itself.  Sound because [`Unknown] only keeps the clause: the
   clause set is then a superset of the one the question could have left, and
   every clause in it is still an obligation of the original problem.  The
   caller sets [defer] off for the last simplification of an elimination round
   whose clause set still has an unknown ([unknowns_remain]), so the clause set
   the search is handed is the one it would get without deferral; with no
   unknown left the deferred clauses reach the zero-unknown verdict, which
   decides the same validity question of the same clause by its own means.
   [None] is the identity, whatever [defer] is. *)
module DeferPure = struct
  let wrap ~min_disjuncts ~defer ~on_defer check_valid (_, ps, ns, _) =
    match min_disjuncts with
    | Some n when defer && Set.is_empty ps && Set.is_empty ns ->
        fun phi ->
          let d = Set.length (Formula.disjuncts_of phi) in
          if d >= n then (
            on_defer d;
            `Unknown)
          else check_valid phi
    | _ -> check_valid

  (* does a clause of [cls] still mention an unknown, as an atom or inside its
     pure part? *)
  let unknowns_remain unknowns cls =
    Set.exists cls ~f:(fun (_, ps, ns, phi) ->
        (not (Set.is_empty ps))
        || (not (Set.is_empty ns))
        || (not (Set.is_empty (Formula.pvs_of phi)))
        || not (Set.are_disjoint (Formula.fvs_of phi) unknowns))
end

(* Postponing the validity questions of pure clauses to the zero-unknown
   verdict.

   A pure clause (as in [DeferPure]) is counted by no elimination rule, and
   resolution never touches it, so the question [ClauseOld.simplify] asks of it
   is the same question at every simplification of a round, and whether it is
   dropped changes no resolution step.  With [on], [wrap] answers
   [`Unknown] without asking at every simplification but a round's last
   ([final]); at the last one it asks [full] (the elimination's own question)
   when an unknown remains ([defer] off), so the clause set the search gets is
   the one it gets without [on], and otherwise asks only [words] when
   [words_only] holds (a question whose [`Valid] is a proof of the same formula
   and whose every other answer reads as [`Unknown]) and [full] when it does
   not, so that each pure clause is asked once per round rather than at every
   simplification.

   Contract: the answer is [`Valid] only when [full] or [words] proved the
   formula, [`Invalid] only when [full] answered so, and [`Unknown] otherwise;
   [`Unknown] keeps the clause whole, so the clause set is a superset of the
   one the question could have left and every clause in it is an obligation of
   the original problem.  With no unknown left, the kept clauses reach the
   zero-unknown verdict, which decides the same validity question by its own
   means (pieces, matched-instance forms, pins).  A non-pure clause gets [full].

   Why: on a bit-set input the elimination's undecided questions were all pure
   clauses that survived to the verdict and were proved there, the verdict
   proving one by its pieces in under a second where the elimination's whole
   question ran out of five seconds and the sequence-axiom fallback; each was
   asked once at about nine seconds and then asked again at the re-ask budget
   at later simplifications of the same round. *)
module PureToVerdict = struct
  let wrap ~on ~words_only ~final ~defer ~full ~words (_, ps, ns, _) =
    if on && Set.is_empty ps && Set.is_empty ns then
      if not final then fun _ -> `Unknown
      else if defer && words_only then fun phi ->
        if words phi then `Valid else `Unknown
      else full
    else full
end

(* The size test a complete elimination (the threshold-lifted resolution of
   every remaining unknown, kept only if no unknown is left and the clause set
   never exceeded a bound [m]) can apply before resolving one unknown away.

   [predicted ~rest ~pc ~nc] is [rest + pc * nc]: [rest] the number of clauses
   that do not mention the unknown, [pc] and [nc] its positive and negative
   occurrence counts as [ClauseSetOld.count_pvar_apps] gives them, so [pc * nc]
   is the growth accounting the resolution threshold itself reads.
   [exceeds ~max_clauses ~rest ~pc ~nc] is [predicted > max_clauses].

   What the prediction is, exactly: when every clause mentioning the unknown
   mentions it once (no disjunctive head, no repeated body atom), [pc * nc] is
   the number of raw resolvents.  The clause set after the step is
   [rest] together with what simplification keeps of their CNF clauses, so it
   EQUALS [predicted] when each resolvent is one CNF clause, simplification
   keeps every one and no two coincide (with each other or with a clause of
   [rest]).  It is SMALLER when simplification drops a resolvent (one proved
   valid) or two coincide, and LARGER when a resolvent splits into several CNF
   clauses or an occurrence is repeated.  So a prebound that abandons on
   [exceeds] gives the outcome of the full build exactly when the prediction is
   exact; where resolvents are dropped it can abandon an attempt the build
   would have kept, and where they split the full build's own test still
   catches what the prediction missed.  Neither direction affects soundness:
   resolution preserves satisfiability, so whether the attempt is kept decides
   cost and never the answer. *)
module CompletePrebound = struct
  let predicted ~rest ~pc ~nc = rest + (pc * nc)
  let exceeds ~max_clauses ~rest ~pc ~nc =
    predicted ~rest ~pc ~nc > max_clauses
end

(* A validity question asked in two phases: a short first ask, and, when that
   is undecided, the same question asked again at once with the rest of the
   budget ([pvar_elim_valid_warm_reask_ms] in the preprocessor).

   [ask ~first_ms ~timeout ~fallback_cap f]: [f ~fallback_cap ~timeout] asks
   the question once with a budget of [timeout] ms and a cap on the
   sequence-axiom fallback ([SeqAxiomCap]), and returns its answer and whether
   the solver was not asked natively (a shape it may not return on).  The
   first ask has [first_ms] and no fallback ([Some 0]); a decided answer is
   returned as it is; a refused shape, where nothing was asked natively, is
   asked once with the whole [timeout] and [fallback_cap], as the one-phase
   path asks it; an undecided answer is asked again with what is left of
   [timeout] (at least 1 ms) and [fallback_cap].  With [first_ms] outside
   [1, timeout) it is the one-phase path, [f ~fallback_cap ~timeout].

   Contract: every answer returned is one [f] gave, so nothing is decided that
   the solver did not decide; the wall time of the native asks stays within
   [timeout] up to the overhead of one extra call; the fallback is asked at
   most once, after the last native ask, as on the one-phase path.

   Why "at once": the second ask goes through the same pooled solver the first
   one used, since nothing else asks this domain's pool in between, and a
   quantifier-free question undecided at 5 s in a solver of its own, under
   every seed, was decided in 0.03 s when asked again in a new scope of the
   solver that had tried it inside a scope for 100 ms or more -- not after a
   first try of 10 ms, not after a reset of that solver, and not in a second
   solver of the same context.  The pooled path asks a quantified question
   after a reset, so for those the second ask is an ordinary repeat. *)
module WarmReask = struct
  let ask ~first_ms ~timeout ~fallback_cap f =
    if first_ms < 1 || first_ms >= timeout then f ~fallback_cap ~timeout
    else
      let started = Common.Clock.now_float () in
      match f ~fallback_cap:(Some 0) ~timeout:first_ms with
      | ((`Valid | `Invalid), _) as r -> r
      | `Unknown, true -> f ~fallback_cap ~timeout
      | `Unknown, false ->
          let spent =
            Float.iround_towards_zero_exn
              (Time_float.Span.to_ms
                 (Time_float.diff (Common.Clock.now_float ()) started))
          in
          f ~fallback_cap ~timeout:(Int.max 1 (timeout - spent))
end

(* Which cap the elimination puts on the sequence-axiom fallback for one
   validity question ([Z3interface.with_seq_axiom_fallback_cap]: [None] leaves
   the process-wide budget, [Some 0] asks no fallback, [Some n] at most [n] ms).

   The fallback runs with the smaller of its own budget and the question's, so
   on a question the record asks again ([reask]) under [reask_timeout] after a
   first ask under [valid_timeout], the fallback's budget is [eff reask_timeout]
   where it was [eff valid_timeout] (and [eff reask_timeout] on every earlier
   repeat).  With [once], a repeated ask whose fallback budget would not be
   larger than the first ask's gets [Some 0]: the same question under no more
   budget than it already had.  Otherwise the configured [cap] is returned.

   Contract: the result is [cap] whenever [once] is false or [reask] is false,
   and is never a cap above [cap]; so it can only remove fallback asks, and the
   fallback only ever turns an undecided answer into [`Valid] -- not asking it
   keeps a clause an ask might have dropped, and changes no answer that was
   decided.  [global] is the process-wide budget ([None]: the fallback is off,
   and nothing is asked whatever the cap). *)
module SeqAxiomCap = struct
  let eff ~global ~cap timeout =
    match global with
    | None -> None
    | Some g -> (
        let b = Int.min g timeout in
        match cap with
        | None -> Some b
        | Some c when c <= 0 -> None
        | Some c -> Some (Int.min b c))

  let for_ask ~cap ~once ~global ~valid_timeout ~reask_timeout ~reask =
    if
      once && reask
      &&
      match
        (eff ~global ~cap reask_timeout, eff ~global ~cap valid_timeout)
      with
      | None, _ -> false
      | Some r, Some f -> r <= f
      | Some _, None -> false
    then Some 0
    else cap

  (* The cap for the question actually put: [cap] is [for_ask]'s, [refused]
     whether the solver is not asked natively ([may_not_return]).  With
     [after_refusal_only], a question the solver IS asked gets [Some 0], so
     the fallback runs after a refusal and never after a native timeout (nor,
     therefore, on a re-ask, which only a timed-out question gets).  Contract:
     the result is [cap] whenever [after_refusal_only] is false or [refused]
     is true, and otherwise [Some 0]; it never raises a cap, so it can only
     remove fallback asks, with the soundness argument of [for_ask]. *)
  let for_branch ~after_refusal_only ~refused cap =
    if after_refusal_only && not refused then Some 0 else cap
end

(* Same-name syntactic clause subsumption ([preprocessor.elim_subsume_clauses]).

   A clause is read as the set of its literals: each atom of [ps] (positive),
   each atom of [ns] (negative) and each disjunct of its pure part other than
   [false].  Clause A subsumes clause B when A's literal set is a subset of B's,
   literals compared syntactically with the variable names as they stand (a
   variable carries its sort, so equal literals are over the same sorts).

   Contract of [reduce]: the result is a subset of the argument, every clause
   dropped has a literal set containing that of some clause kept, and no kept
   clause's literal set contains another kept clause's (of two clauses with
   equal literal sets, which differ only in unused variables of the sort
   environment, the one earlier in the set's order is kept).  So the result is
   logically equivalent to the argument in every model of the background
   theory and under every interpretation of the unknowns: a kept subsumer
   implies the clause it subsumes, since the two are universally closed over the
   same named variables and the subsumed clause is the subsumer with more
   disjuncts.  The order of the clauses does not change which literal sets
   remain.

   What it means for the definitions recorded for predicates eliminated by
   resolution: such a definition is the least solution of the defining clauses
   present when the predicate is resolved, and its soundness argument (the
   resolvents are exactly the use clauses under the definition) is relative to
   that clause set only.  The reduced set has the same models as the original,
   so a solution recovered for the reduced set satisfies the original.  A
   dropped defining clause [body' => P t] was implied by a kept one whose body
   is weaker or which does not mention [P] at all; in the first case the
   disjunction of bodies is unchanged, in the second the definition is smaller
   and still a solution of the dropped clause, because the kept clause is
   (with the other predicates' solutions) already true there.

   Cost: each clause is indexed under its least literal, and a clause is
   tested only against the clauses indexed under one of its own literals. *)
module ClauseSubsume = struct
  type lit = Pos of Atom.t | Neg of Atom.t | Pure of Formula.t

  let lits_of ((_, ps, ns, phi) : ClauseOld.t) =
    Set.Poly.union_list
      [
        Set.Poly.map ps ~f:(fun a -> Pos a);
        Set.Poly.map ns ~f:(fun a -> Neg a);
        Set.Poly.filter_map (Formula.disjuncts_of phi) ~f:(fun d ->
            if Formula.is_false d then None else Some (Pure d));
      ]

  (* [preprocessor.elim_subsume_hash_prefilter]: [reduce] by [reduce_hashed].
     Set (never cleared) when a preprocessor is built from a configuration
     that asks for it; process-global because the eliminator's functor
     argument is a fixed signature the tests instantiate by hand. *)
  let hash_prefilter : bool Atomic.t = Atomic.make false

  (* a hash reading up to 100 meaningful nodes of a literal: equal literals
     have equal hashes, which is all [reduce_hashed] relies on *)
  let lit_hash (l : lit) = Stdlib.Hashtbl.hash_param 100 1000 l

  let reduce_plain (cls : ClauseOld.t Set.Poly.t) : ClauseOld.t Set.Poly.t =
    let sized =
      List.stable_sort
        ~compare:(fun (_, a) (_, b) -> Int.compare (Set.length a) (Set.length b))
      @@ List.map (Set.to_list cls) ~f:(fun cl -> (cl, lits_of cl))
    in
    let index : (lit, lit Set.Poly.t list) Map.Poly.t ref = ref Map.Poly.empty in
    let empty_kept = ref false in
    Set.Poly.of_list
    @@ List.filter_map sized ~f:(fun (cl, ls) ->
        let subsumed =
          !empty_kept
          || Set.exists ls ~f:(fun l ->
              match Map.Poly.find !index l with
              | None -> false
              | Some cands ->
                  List.exists cands ~f:(fun a -> Set.is_subset a ~of_:ls))
        in
        if subsumed then None
        else (
          (match Set.min_elt ls with
          | None -> empty_kept := true
          | Some m -> index := Map.Poly.add_multi !index ~key:m ~data:ls);
          Some cl))

  (* The same decisions as [reduce_plain], with the polymorphic comparisons of
     large literals mostly replaced by integer ones.  [reduce_plain] drops a
     clause when some kept clause's literal set A is a subset of its set L; it
     finds A through the index entry of A's least literal, which is in L.  Here
     every literal carries its hash, a clause carries the set H of its literals'
     hashes, and a kept clause is indexed under the hash of its least literal:
     A included in L puts that hash in H, so A is still found, and every
     candidate is tested by [is_subset] on the hash sets first (necessary for
     inclusion) and on the literal sets only then.  The answer for each clause
     is therefore the same, in the same order, so the result is equal.  On a
     clause set whose pure disjuncts are large formulas, the index lookups and
     the failing inclusion tests of [reduce_plain] compare those formulas
     structurally, and that was most of a preprocessing measured at 113 s with
     0.04 s of solver time. *)
  let reduce_hashed (cls : ClauseOld.t Set.Poly.t) : ClauseOld.t Set.Poly.t =
    let sized =
      List.stable_sort
        ~compare:(fun (_, a, _) (_, b, _) ->
          Int.compare (Set.length a) (Set.length b))
      @@ List.map (Set.to_list cls) ~f:(fun cl ->
          let ls = lits_of cl in
          (cl, ls, Set.fold ls ~init:Int.Set.empty ~f:(fun hs l ->
               Set.add hs (lit_hash l))))
    in
    let index : (int, (lit Set.Poly.t * Int.Set.t) list) Hashtbl.t =
      Hashtbl.create (module Int)
    in
    let empty_kept = ref false in
    Set.Poly.of_list
    @@ List.filter_map sized ~f:(fun (cl, ls, hs) ->
        let subsumed =
          !empty_kept
          || Set.exists hs ~f:(fun h ->
              match Hashtbl.find index h with
              | None -> false
              | Some cands ->
                  List.exists cands ~f:(fun (a, ha) ->
                      Set.is_subset ha ~of_:hs && Set.is_subset a ~of_:ls))
        in
        if subsumed then None
        else (
          (match Set.min_elt ls with
          | None -> empty_kept := true
          | Some m -> Hashtbl.add_multi index ~key:(lit_hash m) ~data:(ls, hs));
          Some cl))

  (* [preprocessor.elim_subsume_interned]: [reduce] by [reduce_interned].
     Process-global for the reason [hash_prefilter] is; takes precedence over
     it when both are set. *)
  let interned : bool Atomic.t = Atomic.make false

  (* the literals of [cl] as distinct interned ids, ascending: [ps] and [ns]
     are sets already, and a repeated pure disjunct gets one id *)
  let lit_ids intern ((_, ps, ns, phi) : ClauseOld.t) =
    let ids =
      Set.fold ps ~init:[] ~f:(fun acc a -> intern (Pos a) :: acc)
      |> fun acc ->
      Set.fold ns ~init:acc ~f:(fun acc a -> intern (Neg a) :: acc)
      |> fun acc ->
      (* the list of disjuncts, not [Formula.disjuncts_of]'s set: building
         that set compares the disjuncts structurally, and the repeats it
         would merge get one id here and are dropped below *)
      List.fold (Formula.disjuncts_list_of phi) ~init:acc ~f:(fun acc d ->
          if Formula.is_false d then acc else intern (Pure d) :: acc)
    in
    let a = Array.of_list ids in
    Array.sort a ~compare:Int.compare;
    (* drop repeats (a disjunct occurring twice): the array's length stands
       for the literal set's size *)
    let n = Array.length a in
    if n <= 1 then a
    else
      let k = ref 1 in
      for i = 1 to n - 1 do
        if a.(i) <> a.(!k - 1) then (
          a.(!k) <- a.(i);
          incr k)
      done;
      Array.sub a ~pos:0 ~len:!k

  (* [a] included in [l], both ascending without repeats *)
  let sorted_subset (a : int array) (l : int array) =
    let na = Array.length a and nl = Array.length l in
    if na > nl then false
    else
      let rec go i j =
        if i = na then true
        else if nl - j < na - i then false
        else
          let x = a.(i) and y = l.(j) in
          if x = y then go (i + 1) (j + 1)
          else if x > y then go i (j + 1)
          else false
      in
      go 0 0

  module LitKey = struct
    type t = lit

    let compare = Stdlib.compare
    let hash = lit_hash
    let sexp_of_t _ = Sexp.Atom "lit"
  end

  (* The same decisions as [reduce_plain], with every literal compared
     structurally at most once per call.  Each literal is interned to an
     integer by a table whose equality is the polymorphic [compare] that
     [Set.Poly] orders by, so two literals get the same id exactly when they
     are the same element of a literal set: a clause's literal set becomes an
     ascending id array of the same size, and inclusion of literal sets is
     inclusion of id arrays.  The clauses are visited in [reduce_plain]'s
     order (stably by literal count) and a clause is dropped exactly when some
     kept clause's array is included in its own; to find those, a kept clause
     is indexed under its literal that occurs in the fewest clauses of this
     call, which an including clause must contain.  The kept clauses go into
     the result in the same order as in [reduce_plain], so the result is the
     same set built by the same insertions.  On a clause set with long runs of
     clauses sharing their least literal, [reduce_hashed] tested every pair of
     them; here each clause looks only at the kept clauses keyed by one of its
     own literals, by its rarest. *)
  let reduce_interned (cls : ClauseOld.t Set.Poly.t) : ClauseOld.t Set.Poly.t =
    let tbl = Hashtbl.create (module LitKey) in
    let intern_struct l =
      match Hashtbl.find tbl l with
      | Some i -> i
      | None ->
          let i = Hashtbl.length tbl in
          Hashtbl.add_exn tbl ~key:l ~data:i;
          i
    in
    (* the atoms and disjuncts are mostly physically shared between clauses
       (the normal form's copies, the clauses a resolution step leaves alone),
       so a physical lookup first saves the deep hash and the comparison *)
    let pos = ClauseOld.PhysAtom.create 256
    and neg = ClauseOld.PhysAtom.create 256
    and pure = ClauseOld.PhysFormula.create 256 in
    let memo find add t key l =
      match find t key with
      | Some i -> i
      | None ->
          let i = intern_struct l in
          add t key i;
          i
    in
    let intern = function
      | Pos a as l -> memo ClauseOld.PhysAtom.find_opt ClauseOld.PhysAtom.add pos a l
      | Neg a as l -> memo ClauseOld.PhysAtom.find_opt ClauseOld.PhysAtom.add neg a l
      | Pure d as l ->
          memo ClauseOld.PhysFormula.find_opt ClauseOld.PhysFormula.add pure d l
    in
    let arrs = List.map (Set.to_list cls) ~f:(fun cl -> (cl, lit_ids intern cl)) in
    let freq = Array.create ~len:(Hashtbl.length tbl) 0 in
    List.iter arrs ~f:(fun (_, a) -> Array.iter a ~f:(fun i -> freq.(i) <- freq.(i) + 1));
    let sized =
      List.stable_sort
        ~compare:(fun (_, a) (_, b) -> Int.compare (Array.length a) (Array.length b))
        arrs
    in
    let index : int array list array = Array.create ~len:(Array.length freq) [] in
    let empty_kept = ref false in
    Set.Poly.of_list
    @@ List.filter_map sized ~f:(fun (cl, l) ->
        let subsumed =
          !empty_kept
          || Array.exists l ~f:(fun i ->
              List.exists index.(i) ~f:(fun a -> sorted_subset a l))
        in
        if subsumed then None
        else (
          (if Array.is_empty l then empty_kept := true
           else
             let key =
               Array.fold l ~init:l.(0) ~f:(fun best i ->
                   if freq.(i) < freq.(best) then i else best)
             in
             index.(key) <- l :: index.(key));
          Some cl))

  (* [preprocessor.elim_subsume_persistent]: [reduce] by [reduce_persistent].
     Process-global for the reason [hash_prefilter] is; takes precedence over
     [interned] and [hash_prefilter]. *)
  let persistent : bool Atomic.t = Atomic.make false

  (* The interning tables of [reduce_interned], kept from one call to the next
     in a domain.  Invariant between calls: [structural] maps each literal it
     holds to an id no other entry has, every entry of the three physical
     tables has the id [structural] gives its literal, and every id is below
     [next_id]; so a literal's id is a function of its [compare] class for as
     long as the tables hold it.  [freq], [index] and [keep] are scratch arrays
     indexed by id, all zero, empty and [false] between calls. *)
  type interner = {
    structural : (lit, int) Hashtbl.t;
    pos_ids : int ClauseOld.PhysAtom.t;
    neg_ids : int ClauseOld.PhysAtom.t;
    pure_ids : int ClauseOld.PhysFormula.t;
    mutable next_id : int;
    mutable freq : int array;
    mutable index : int array list array;
    mutable keep : bool array;
  }

  let interner_key : interner option ref Stdlib.Domain.DLS.key =
    Stdlib.Domain.DLS.new_key (fun () -> ref None)

  (* forget the tables of this domain; [reduce_persistent] answers the same
     after it, only the literals it knew are hashed again *)
  let reset_interner () = Stdlib.Domain.DLS.get interner_key := None

  let get_interner () =
    let cell = Stdlib.Domain.DLS.get interner_key in
    match !cell with
    | Some st -> st
    | None ->
        let st =
          {
            structural = Hashtbl.create (module LitKey);
            pos_ids = ClauseOld.PhysAtom.create 256;
            neg_ids = ClauseOld.PhysAtom.create 256;
            pure_ids = ClauseOld.PhysFormula.create 256;
            next_id = 0;
            freq = [||];
            index = [||];
            keep = [||];
          }
        in
        cell := Some st;
        st

  (* The same decisions and the same result as [reduce_interned] (hence as
     [reduce_plain]): the clauses are visited in the same order (stably by the
     number of distinct literals, which does not depend on the ids), a clause
     is dropped exactly when some kept clause's id array is included in its
     own, and the kept clauses are inserted in the same order.  Only the ids
     differ, and a decision reads ids only through equality, which is literal
     equality under the invariant above; the index key of a kept clause (its
     rarest literal, the first in id order among equals) may differ, but an
     including clause holds every literal of a kept clause, its key among them.

     What is saved: the tables outlive the call, so a literal met in an earlier
     call is found by its physical identity and is not hashed deeply or
     compared again.  Between the steps of an elimination most clauses, and
     many disjuncts of the new resolvents, are the same values as before, while
     [reduce_interned] hashed every literal of every clause at every step (on a
     Thrust input of 600 clauses with resolvents of over a hundred disjuncts,
     the deep hash of the literals alone was 8% of a run's samples).

     Memory: after the call only the ids of the literals of the result are kept
     (with their entries in all four tables), so the tables hold the literals
     of the clause set the caller holds, never those of every clause met; and
     the tables are dropped whole once ids run past four times the live ones,
     which bounds the scratch arrays.  An exception inside the call (a timeout)
     drops them too, since the scratch arrays are then not clean. *)
  let reduce_persistent (cls : ClauseOld.t Set.Poly.t) : ClauseOld.t Set.Poly.t =
    let st = get_interner () in
    let intern_struct l =
      match Hashtbl.find st.structural l with
      | Some i -> i
      | None ->
          let i = st.next_id in
          st.next_id <- i + 1;
          Hashtbl.add_exn st.structural ~key:l ~data:i;
          i
    in
    let memo find add t key l =
      match find t key with
      | Some i -> i
      | None ->
          let i = intern_struct l in
          add t key i;
          i
    in
    let intern = function
      | Pos a as l ->
          memo ClauseOld.PhysAtom.find_opt ClauseOld.PhysAtom.add st.pos_ids a l
      | Neg a as l ->
          memo ClauseOld.PhysAtom.find_opt ClauseOld.PhysAtom.add st.neg_ids a l
      | Pure d as l ->
          memo ClauseOld.PhysFormula.find_opt ClauseOld.PhysFormula.add
            st.pure_ids d l
    in
    match
      let arrs =
        List.map (Set.to_list cls) ~f:(fun cl -> (cl, lit_ids intern cl))
      in
      (* the scratch arrays grown to cover every id, by doubling *)
      let n = st.next_id in
      if Array.length st.freq < n then (
        let len = Int.max n (2 * Array.length st.freq) in
        st.freq <- Array.create ~len 0;
        st.index <- Array.create ~len [];
        st.keep <- Array.create ~len false);
      let freq = st.freq and index = st.index and keep = st.keep in
      List.iter arrs ~f:(fun (_, a) ->
          Array.iter a ~f:(fun i -> freq.(i) <- freq.(i) + 1));
      let sized =
        List.stable_sort
          ~compare:(fun (_, a) (_, b) ->
            Int.compare (Array.length a) (Array.length b))
          arrs
      in
      let empty_kept = ref false in
      let kept =
        List.filter_map sized ~f:(fun (cl, l) ->
            let subsumed =
              !empty_kept
              || Array.exists l ~f:(fun i ->
                  List.exists index.(i) ~f:(fun a -> sorted_subset a l))
            in
            if subsumed then None
            else (
              (if Array.is_empty l then empty_kept := true
               else
                 let key =
                   Array.fold l ~init:l.(0) ~f:(fun best i ->
                       if freq.(i) < freq.(best) then i else best)
                 in
                 index.(key) <- l :: index.(key));
              Array.iter l ~f:(fun i -> keep.(i) <- true);
              Some cl))
      in
      let result = Set.Poly.of_list kept in
      (* drop every id no kept clause has, from all four tables, and put the
         scratch arrays back to zero, empty and [false] *)
      let drop_unkept _ i = if keep.(i) then Some i else None in
      ClauseOld.PhysAtom.filter_map_inplace drop_unkept st.pos_ids;
      ClauseOld.PhysAtom.filter_map_inplace drop_unkept st.neg_ids;
      ClauseOld.PhysFormula.filter_map_inplace drop_unkept st.pure_ids;
      Hashtbl.filter_inplace st.structural ~f:(fun i -> keep.(i));
      List.iter arrs ~f:(fun (_, a) ->
          Array.iter a ~f:(fun i ->
              freq.(i) <- 0;
              index.(i) <- [];
              keep.(i) <- false));
      if st.next_id > 65536 && st.next_id > 4 * Hashtbl.length st.structural
      then reset_interner ();
      result
    with
    | result -> result
    | exception e ->
        reset_interner ();
        raise e

  let reduce cls =
    if Atomic.get persistent then reduce_persistent cls
    else if Atomic.get interned then reduce_interned cls
    else if Atomic.get hash_prefilter then reduce_hashed cls
    else reduce_plain cls
end

(* [preprocessor.pvar_elim_words_first]: each validity question of the
   elimination that reads an integer as a word is first asked through the words
   of its matched-instance forms.  Process-global, as the switches below are,
   since the eliminator's own configuration is a module many tests build. *)
let words_first : bool Atomic.t = Atomic.make false

(* [COAR_WORDS_TRACE] in the environment: the words route traces its pieces and questions on
   stderr (read once, before any domain exists) *)
let words_trace = Lazy.from_val (Option.is_some (Stdlib.Sys.getenv_opt "COAR_WORDS_TRACE"))

(* [preprocessor.pvar_elim_words_keep_proved]: the words route goes through
   every piece and the native question is then the conjunction of the pieces
   it did not prove ([SeqInstantiation.words_by_pieces]); exact, since the
   question is valid exactly when every piece is.  Process-global for the same
   reason as [words_first]. *)
let words_keep_proved : bool Atomic.t = Atomic.make false

(* [preprocessor.pvar_elim_split_int_binders_at_ite]: each validity question of
   the elimination is asked with its integer binders split at the thresholds
   of the [ite]s in their bodies and the upper parts shifted to start at zero
   ([IntBinderSplit.rewrite]), an equivalence in every model.  Process-global
   for the same reason as [words_first]. *)
let split_int_binders_at_ite : bool Atomic.t = Atomic.make false

(* [preprocessor.pvar_elim_defer_pure_to_verdict]: the validity question of a
   pure clause (no predicate application in its atom sets, no unknown in its
   pure part) is not asked while an elimination round resolves; at the round's
   last simplification it is asked in full when an unknown remains, and
   otherwise only through the words of its matched-instance forms, reading
   only a proof ([PureToVerdict]).  Process-global for the same reason as
   [words_first]. *)
let defer_pure_to_verdict : bool Atomic.t = Atomic.make false

(* [preprocessor.pvar_elim_defer_pure_to_round_end]: the same postponement as
   [defer_pure_to_verdict], with the round's last simplification asking the
   elimination's own question whether or not an unknown remains
   ([PureToVerdict], [words_only] off).  [defer_pure_to_verdict] wins when both
   are set. *)
let defer_pure_to_round_end : bool Atomic.t = Atomic.make false

(* [preprocessor.pvar_elim_words_full_major_every]: [Some n] makes the forced
   major collection before a new Z3 context happen before every n-th context
   only, while the elimination asks a question through its words
   ([Z3interface.with_new_context_full_major_every]); each such question is a
   context of its own.  The questions asked are the same; only the collector's
   timing changes, at most n dropped contexts waiting for it at once. *)
let words_full_major_every : int option Atomic.t = Atomic.make None

(* [preprocessor.pvar_elim_implied_factor_equalities]: each validity question
   of the elimination is asked with the equations between factors of products
   that its linear facts imply stated as disjuncts
   ([Z3interface.implied_factor_equalities]), an equivalence in every model.
   Process-global for the same reason as [words_first]. *)
let implied_factor_equalities : bool Atomic.t = Atomic.make false

(* [preprocessor.elim_resolution_index]: the resolution rounds read the
   occurrence counts, the clauses applying a predicate and the subsumption
   decisions from a [ResolutionIndex] kept across the steps of one
   elimination, instead of walking the whole clause set at every step.
   Process-global for the reason [ClauseSubsume.hash_prefilter] is. *)
let resolution_index : bool Atomic.t = Atomic.make false

(* The state one chain of resolution steps keeps about its clause set, so that
   a step costs in proportion to the clauses it touches and not to the set.

   Invariant (between steps): the keys of [live] are, element for element, the
   clause set the caller holds (equal under [Stdlib.compare], which [Set.Poly]
   orders by); [clause_of], [lits], [occ], [counts], [lit_occ], [keyed],
   [key_of] and [empties] describe exactly the clauses of [live] by their ids:
   [lits] the clause's distinct literals as ascending interned ids (the literal
   set [ClauseSubsume.reduce] decides on, so its length is that set's size),
   [occ] for each predicate the clauses one of whose atoms mentions it (by
   [atom_pvs], as the safety test reads them), [counts] the sums
   [ClauseSetOld.count_pvar_apps] computes over the whole set for every
   predicate, [lit_occ] for each literal the clauses holding it, [keyed] each
   clause with at least one literal filed under one of its literals ([key_of]),
   and [empties] the clauses without a literal.  When [reduced] holds, no clause
   of [live] is dominated by another (below), which is what the output of
   [ClauseSubsume.reduce] satisfies.

   Domination: [d] dominates [c] when the literal set of [d] is included in
   that of [c] and [d] comes first in [ClauseSubsume.reduce]'s order (fewer
   literals, or as many -- then the same set -- and [d] before [c] under
   [compare]).  [reduce] keeps exactly the clauses no clause of its argument
   dominates: it visits them in that order and drops a clause when a kept one's
   literals are included in its own, and a dropped dominator is itself
   dominated by a kept clause earlier still, whose literals are then included
   too.  So when [R] is [reduced] and [N] is added, [reduce (R u N)] drops
   exactly the clauses of [R] some clause of [N] dominates and the clauses of
   [N] some clause of [R u N] dominates; [step] computes that and builds the
   result from the kept clauses in [reduce]'s order, so it is the same set
   built by the same insertions.

   The tables are mutable: a chain of steps owns its state, and the complete
   elimination that continues a chain uses it after the chain has stopped
   using it; a step that raises leaves it unusable, and nothing reads it
   afterwards. *)
module ResolutionIndex = struct
  type counts = {
    mutable both : int;
    mutable pos : int;
    mutable neg : int;
    mutable pos_nonlin : int;
    mutable neg_nonlin : int;
  }

  type t = {
    atom_pvs : Atom.t -> Ident.pvar Set.Poly.t;
    intern : ClauseSubsume.lit -> int;
    mutable live : (ClauseOld.t, int) Map.Poly.t;
    clause_of : (int, ClauseOld.t) Hashtbl.t;
    lits : (int, int array) Hashtbl.t;
    occ : (Ident.pvar, Int.Hash_set.t) Hashtbl.t;
    counts : (Ident.pvar, counts) Hashtbl.t;
    lit_occ : (int, Int.Hash_set.t) Hashtbl.t;
    keyed : (int, Int.Hash_set.t) Hashtbl.t;
    key_of : (int, int) Hashtbl.t;
    empties : Int.Hash_set.t;
    mutable next : int;
    mutable reduced : bool;
  }

  (* the interning of [ClauseSubsume.reduce_interned], never pruned: a
     literal gets one id for the life of the state, a function of its
     [compare] class *)
  let make_intern () =
    let tbl = Hashtbl.create (module ClauseSubsume.LitKey) in
    let intern_struct l =
      match Hashtbl.find tbl l with
      | Some i -> i
      | None ->
          let i = Hashtbl.length tbl in
          Hashtbl.add_exn tbl ~key:l ~data:i;
          i
    in
    let pos = ClauseOld.PhysAtom.create 256
    and neg = ClauseOld.PhysAtom.create 256
    and pure = ClauseOld.PhysFormula.create 256 in
    let memo find add t key l =
      match find t key with
      | Some i -> i
      | None ->
          let i = intern_struct l in
          add t key i;
          i
    in
    function
    | ClauseSubsume.Pos a as l ->
        memo ClauseOld.PhysAtom.find_opt ClauseOld.PhysAtom.add pos a l
    | Neg a as l ->
        memo ClauseOld.PhysAtom.find_opt ClauseOld.PhysAtom.add neg a l
    | Pure d as l ->
        memo ClauseOld.PhysFormula.find_opt ClauseOld.PhysFormula.add pure d l

  let set_of tbl key =
    Hashtbl.find_or_add tbl key ~default:(fun () -> Int.Hash_set.create ())

  let remove_from tbl key id =
    match Hashtbl.find tbl key with
    | None -> ()
    | Some s ->
        Hash_set.remove s id;
        if Hash_set.is_empty s then Hashtbl.remove tbl key

  let size_of tbl key =
    match Hashtbl.find tbl key with None -> 0 | Some s -> Hash_set.length s

  (* each predicate's (positive, negative) occurrences in one clause, by the
     predicate of each atom, as [ClauseSetOld.count_pvar_apps] counts them *)
  let local_counts ((_, ps, ns, _) : ClauseOld.t) =
    let local = Hashtbl.Poly.create () in
    Set.iter ps ~f:(fun atm ->
        Hashtbl.update local (Atom.pvar_of atm) ~f:(function
          | None -> (1, 0)
          | Some (pc, nc) -> (pc + 1, nc)));
    Set.iter ns ~f:(fun atm ->
        Hashtbl.update local (Atom.pvar_of atm) ~f:(function
          | None -> (0, 1)
          | Some (pc, nc) -> (pc, nc + 1)));
    local

  let add_counts t cl sign =
    Hashtbl.iteri (local_counts cl) ~f:(fun ~key:pvar ~data:(pc, nc) ->
        let c =
          Hashtbl.find_or_add t.counts pvar ~default:(fun () ->
              { both = 0; pos = 0; neg = 0; pos_nonlin = 0; neg_nonlin = 0 })
        in
        if pc > 0 && nc > 0 then c.both <- c.both + sign
        else (
          c.pos <- c.pos + (sign * pc);
          c.neg <- c.neg + (sign * nc));
        if pc >= 2 then c.pos_nonlin <- c.pos_nonlin + sign;
        if nc >= 2 then c.neg_nonlin <- c.neg_nonlin + sign;
        if
          c.both = 0 && c.pos = 0 && c.neg = 0 && c.pos_nonlin = 0
          && c.neg_nonlin = 0
        then Hashtbl.remove t.counts pvar)

  let pvs_of_clause t ((_, ps, ns, _) : ClauseOld.t) =
    Set.concat_map (Set.union ps ns) ~f:t.atom_pvs

  (* registers [cl], which [live] must not hold *)
  let add t cl =
    let id = t.next in
    t.next <- id + 1;
    t.live <- Map.Poly.add_exn t.live ~key:cl ~data:id;
    Hashtbl.set t.clause_of ~key:id ~data:cl;
    let l = ClauseSubsume.lit_ids t.intern cl in
    Hashtbl.set t.lits ~key:id ~data:l;
    Set.iter (pvs_of_clause t cl) ~f:(fun pvar ->
        Hash_set.add (set_of t.occ pvar) id);
    add_counts t cl 1;
    Array.iter l ~f:(fun i -> Hash_set.add (set_of t.lit_occ i) id);
    if Array.is_empty l then Hash_set.add t.empties id
    else
      (* filed under its rarest literal, so the lists [step] reads are short;
         any literal of the clause would be correct *)
      let key =
        Array.fold l ~init:l.(0) ~f:(fun best i ->
            if size_of t.lit_occ i < size_of t.lit_occ best then i else best)
      in
      Hash_set.add (set_of t.keyed key) id;
      Hashtbl.set t.key_of ~key:id ~data:key

  let remove t id =
    let cl = Hashtbl.find_exn t.clause_of id in
    t.live <- Map.Poly.remove t.live cl;
    Hashtbl.remove t.clause_of id;
    let l = Hashtbl.find_exn t.lits id in
    Hashtbl.remove t.lits id;
    Set.iter (pvs_of_clause t cl) ~f:(fun pvar -> remove_from t.occ pvar id);
    add_counts t cl (-1);
    Array.iter l ~f:(fun i -> remove_from t.lit_occ i id);
    Hash_set.remove t.empties id;
    match Hashtbl.find t.key_of id with
    | None -> ()
    | Some key ->
        Hashtbl.remove t.key_of id;
        remove_from t.keyed key id

  let create ~atom_pvs clauses =
    let t =
      {
        atom_pvs;
        intern = make_intern ();
        live = Map.Poly.empty;
        clause_of = Hashtbl.create (module Int);
        lits = Hashtbl.create (module Int);
        occ = Hashtbl.Poly.create ();
        counts = Hashtbl.Poly.create ();
        lit_occ = Hashtbl.create (module Int);
        keyed = Hashtbl.create (module Int);
        key_of = Hashtbl.create (module Int);
        empties = Int.Hash_set.create ();
        next = 0;
        reduced = false;
      }
    in
    Set.iter clauses ~f:(add t);
    t

  (* [ClauseSetOld.count_pvar_apps pvs] of the clauses of [live] *)
  let count_pvar_apps t pvs =
    Hashtbl.fold t.counts ~init:([], []) ~f:(fun ~key:pvar ~data:c (acc, dc) ->
        if not (Set.mem pvs pvar) then (acc, dc)
        else
          let acc =
            if c.both = 0 && c.pos = 0 && c.neg = 0 then acc
            else (pvar, (c.both, c.pos, c.neg)) :: acc
          in
          let dc =
            if c.pos_nonlin > 0 && c.neg_nonlin > 0 then pvar :: dc else dc
          in
          (acc, dc))
    |> fun (acc, dc) -> (Set.Poly.of_list acc, Set.Poly.of_list dc)

  (* the clauses of [live] one of whose atoms mentions [pvar], with their ids *)
  let clauses_of t pvar =
    match Hashtbl.find t.occ pvar with
    | None -> []
    | Some s ->
        Hash_set.fold s ~init:[] ~f:(fun acc id ->
            (id, Hashtbl.find_exn t.clause_of id) :: acc)

  let length t = Map.length t.live

  (* how many [step]s have dropped a clause; a counter for the property
     tests *)
  let dropping_steps = Atomic.make 0
  let find_id t cl = Map.Poly.find t.live cl

  (* makes [live] the clauses of [cls], keeping the ids of the clauses both
     hold; [reduced] then states whether [cls] is a [reduce] output *)
  let sync t cls ~reduced =
    let gone =
      Map.Poly.fold t.live ~init:[] ~f:(fun ~key:cl ~data:id acc ->
          if Set.mem cls cl then acc else id :: acc)
    in
    List.iter gone ~f:(remove t);
    Set.iter cls ~f:(fun cl -> if not (Map.Poly.mem t.live cl) then add t cl);
    t.reduced <- reduced

  (* whether [d] dominates [c] (ids of [live], distinct) *)
  let dominates t d c =
    let ld = Hashtbl.find_exn t.lits d and lc = Hashtbl.find_exn t.lits c in
    ClauseSubsume.sorted_subset ld lc
    && (Array.length ld < Array.length lc
       || Stdlib.compare
            (Hashtbl.find_exn t.clause_of d)
            (Hashtbl.find_exn t.clause_of c)
          < 0)

  (* One resolution step on a [reduced] state, with [ClauseSubsume.reduce]
     applied to the result: [touched] are the ids of the clauses the step
     resolved away, [resolvents] the new clauses.  Returns
     [reduce ((live - touched) u resolvents)] and how many clauses that
     dropped, and leaves the state describing that set, [reduced]. *)
  let step t ~touched ~resolvents =
    assert t.reduced;
    List.iter touched ~f:(remove t);
    let fresh =
      Set.fold resolvents ~init:[] ~f:(fun acc cl ->
          if Map.Poly.mem t.live cl then acc
          else (
            add t cl;
            Map.Poly.find_exn t.live cl :: acc))
    in
    let before = length t in
    let dominated = Int.Hash_set.create () in
    List.iter fresh ~f:(fun n ->
        let l = Hashtbl.find_exn t.lits n in
        (* a dominator of [n]: its key literal is one of [n]'s, or it has no
           literal *)
        let by d = d <> n && dominates t d n in
        if
          Hash_set.exists t.empties ~f:by
          || Array.exists l ~f:(fun i ->
              match Hashtbl.find t.keyed i with
              | None -> false
              | Some s -> Hash_set.exists s ~f:by)
        then Hash_set.add dominated n;
        (* the clauses [n] dominates hold every literal of [n], its rarest
           among them *)
        let mark c = if c <> n && dominates t n c then Hash_set.add dominated c in
        if Array.is_empty l then
          Map.Poly.iter t.live ~f:mark
        else
          let rarest =
            Array.fold l ~init:l.(0) ~f:(fun best i ->
                if size_of t.lit_occ i < size_of t.lit_occ best then i
                else best)
          in
          Option.iter (Hashtbl.find t.lit_occ rarest) ~f:(Hash_set.iter ~f:mark));
    Hash_set.iter dominated ~f:(remove t);
    let kept =
      Map.Poly.to_alist t.live
      |> List.map ~f:(fun (cl, id) ->
          (cl, Array.length (Hashtbl.find_exn t.lits id)))
      |> List.stable_sort ~compare:(fun (_, a) (_, b) -> Int.compare a b)
      |> List.map ~f:fst
    in
    t.reduced <- true;
    if before > length t then Atomic.incr dropping_steps;
    (Set.Poly.of_list kept, before - length t)
end

(* [preprocessor.elim_cnf_shared_fvs]: the clausal form's sort maps reduced
   by [ClauseOld.reduce_sort_map_shared], which gives the same maps.
   Process-global for the reason [ClauseSubsume.hash_prefilter] is. *)
let cnf_shared_fvs : bool Atomic.t = Atomic.make false

(* [preprocessor.elim_resolution_atom_pvs_memo]: the resolution rounds read
   each atom's predicate variables through a physical memo, which gives the
   same sets.  Process-global for the same reason. *)
let resolution_atom_pvs_memo : bool Atomic.t = Atomic.make false

(* [preprocessor.elim_cnf_clause_tree]: the clausal form of predicate
   elimination reads a formula that is already one clause in one pass
   ([Formula.cnf_of_clause_tree]), which gives the same clauses.
   Process-global for the same reason. *)
let cnf_clause_tree : bool Atomic.t = Atomic.make false

(* [preprocessor.elim_set_aside_cnf_clauses]: [Some n] sets aside, in each
   elimination round, every input formula whose clausal form is predicted to
   have more than [n] clauses ([predicted_cnf_clauses]); the round eliminates
   no unknown such a formula mentions, and returns the formula unchanged beside
   its result.  [None]: every formula is put in clausal form.  Process-global
   for the same reason as the switches above. *)
let set_aside_cnf_clauses : int option Atomic.t = Atomic.make None

(* [preprocessor.elim_set_aside_definitional]: the formulas
   [set_aside_cnf_clauses] kept whole are put in clausal form after the last
   round through [definitional_split], with fresh unknowns naming the
   conjunctions the distribution would multiply, instead of being distributed.
   Process-global for the same reason as the switches above. *)
let set_aside_definitional : bool Atomic.t = Atomic.make false

(* [preprocessor.resolution_max_growth]: [Some b] keeps an unknown out of
   resolution, as a named predicate the clauses go on applying, whenever
   resolving it away is predicted to grow the clause set's node size by more
   than [b] ([GrowthGuard.predicted_growth]).  The decision is taken from the
   sizes of the clauses the unknown occurs in, before any resolvent is built.
   [None]: resolution is limited by occurrence counts only.  Why: with one
   positive occurrence the count test always allows a step, and when every
   later definition re-applies the earlier ones, inlining puts a renamed copy
   of an earlier body into a definition that already holds one, so the
   definitions' sizes double along the chain while no clause is duplicated.
   Leaving an unknown in place never changes the problem's satisfiability:
   the clause set is the same constraint, with one predicate still to solve.
   Process-global for the same reason as the switches above. *)
let resolution_max_growth : int option Atomic.t = Atomic.make None

(* how many candidate steps [resolution_max_growth] has refused, for the
   property tests; read by nothing on the solving path *)
let growth_refusals : int Atomic.t = Atomic.make 0

module GrowthGuard = struct
  (* [predicted_growth ~pc ~nc ~spos ~sneg]: resolving an unknown away pairs
     each of its [pc] positive clauses with each of its [nc] negative ones, and
     a resolvent is at most about the two clauses' sizes together, so the
     resolvents total about [nc * spos + pc * sneg], where [spos] and [sneg]
     are the summed sizes of the positive and the negative clauses; the
     [pc + nc] clauses themselves leave.  The result is that difference.  It
     is an estimate, not a bound: substituting a head's arguments for a
     body's parameters can enlarge a resolvent, and simplification usually
     shrinks it.  It is [0] when [pc = nc = 1] (two clauses become one) and
     [(nc - 1) * spos] when [pc = 1], which is the copying that doubles a
     chain of definitions. *)
  let predicted_growth ~pc ~nc ~spos ~sneg =
    (nc * spos) + (pc * sneg) - (spos + sneg)

  (* the size of a clause as the growth trace counts it, its atoms and its
     pure part; the pure part's size kept by physical identity for as long
     as the returned function is held, since a clause a step leaves alone is
     the same value in the next step *)
  let clause_size () =
    let tbl = ClauseOld.PhysFormula.create 1024 in
    fun (_, pos, neg, phi) ->
      let atoms =
        Set.fold (Set.union pos neg) ~init:0 ~f:(fun acc a ->
            acc + Atom.ast_size a)
      in
      let pure =
        match ClauseOld.PhysFormula.find_opt tbl phi with
        | Some n -> n
        | None ->
            let n = Formula.ast_size phi in
            ClauseOld.PhysFormula.add tbl phi n;
            n
      in
      atoms + pure
end

(* An upper bound on the number of clauses [Formula.cnf_of unknowns] (without
   [process_pure]) gives [phi], read in one pass without building them.

   Contract: for [phi] in negation normal form, as [cnf_of] assumes, the result
   is at least [Set.length (Formula.cnf_of exi_senv phi)] whenever [unknowns]
   is the key set of [exi_senv], saturating at [2^40].  It follows
   [cnf_of_aux] case by case: a subtree mentioning no unknown is one clause (or
   none); a conjunction gives at most the sum of its sides' clauses (fewer when
   pure clauses are merged or duplicates meet); a disjunction the product; an
   implication, an equivalence and an exclusive or the same expansions
   [cnf_of_aux] makes; a [let] its body's.  A leaf that mentions an unknown is
   one clause.  Why: the product of a disjunction of conjunctions over
   unknowns is what the normal form multiplies, and on a Thrust closure input
   one formula of 5,388 nodes gave 1,764 clauses of 7.8 million nodes in all,
   which the round then walked clause by clause. *)
let predicted_cnf_clauses unknowns phi =
  let cap = 1 lsl 40 in
  (* the test [cnf_of_aux] makes at every node *)
  let mentions phi =
    Set.exists (Formula.pvs_of phi) ~f:(fun pvar ->
        Set.mem unknowns (Ident.pvar_to_tvar pvar))
    || not (Set.are_disjoint (Formula.tvs_of phi) unknowns)
  in
  let add a b = Int.min cap (a + b) in
  let mul a b =
    if a = 0 || b = 0 then 0 else if a > cap / b then cap else a * b
  in
  let rec go phi =
    match phi with
    | Formula.BinaryOp (And, a, b, _) ->
        let ma, ca = go a and mb, cb = go b in
        if ma || mb then (true, add ca cb) else (false, 1)
    | Formula.BinaryOp (Or, a, b, _) ->
        let ma, ca = go a and mb, cb = go b in
        if ma || mb then (true, mul ca cb) else (false, 1)
    | Formula.BinaryOp (Imply, a, b, _) ->
        go
          (Formula.mk_or
             (Formula.nnf_of @@ Formula.mk_neg a)
             (Formula.nnf_of b))
    | Formula.BinaryOp (Iff, a, b, _) ->
        go
          (Formula.mk_and
             (Formula.mk_or (Formula.nnf_of @@ Formula.mk_neg a) (Formula.nnf_of b))
             (Formula.mk_or (Formula.nnf_of a) (Formula.nnf_of @@ Formula.mk_neg b)))
    | Formula.BinaryOp (Xor, a, b, _) ->
        go
          (Formula.mk_and
             (Formula.mk_or (Formula.nnf_of a) (Formula.nnf_of b))
             (Formula.mk_or
                (Formula.nnf_of @@ Formula.mk_neg a)
                (Formula.nnf_of @@ Formula.mk_neg b)))
    | Formula.LetFormula (_, _, _, body, _) ->
        let m, c = go body in
        (m || mentions phi, c)
    | _ -> (mentions phi, 1)
  in
  snd (go phi)

(* [definitional_split ~bound ~unknowns ~fresh phi]: the formulas whose
   clausal forms together replace the clausal form of [phi], when that would
   have more than [bound] clauses, with fresh unknowns naming the conjunctions
   it multiplies ([preprocessor.elim_set_aside_definitional]).

   Contract.  [phi] is in negation normal form and mentions the unknowns
   [unknowns]; [fresh ()] returns a predicate variable used nowhere else.  The
   result is [(phis, defs)]: [defs] lists the fresh unknowns with their
   argument sorts, and each formula of [phis] has a predicted clausal form
   ([predicted_cnf_clauses]) of at most [bound] clauses unless it is a leaf the
   split does not enter (an implication, a [let] or a binder at the top, or a
   disjunction of such leaves).  Where [phi] is within the bound the result is
   [([phi], [])].  Otherwise a conjunction is split into its conjuncts, and in
   a disjunction every disjunct whose own clausal form has more than one clause
   -- a conjunction, which the distribution would multiply -- is replaced by
   [D(xs)] for a fresh [D] over the disjunct's free term variables [xs] (the
   unknowns excepted), and the formula [not D(xs) \/ C] is split in turn, one
   formula per conjunct of [C].  The split recurses only into proper
   subformulas, so it terminates.

   Why it is sound.  [C] occurs positively, so the formula with [D(xs)] in its
   place, together with [D(xs) => C], implies the original in every model and
   for every interpretation of [D]; and an interpretation of the original's
   unknowns satisfying it extends to the new ones by reading [D] as [C].  So
   the problem keeps its satisfiability both ways (each model of the theory
   admits an interpretation of the old unknowns iff it admits one of the old
   and the new), and a solution of the new problem restricted to the old
   unknowns solves the old one.  It is not the same problem: the solver has
   unknowns to find that the input did not have, and resolution would
   multiply the clauses back if it eliminated them.  Why: a premise
   universally quantified over an unknown becomes, once skolemised, a
   conjunction under the clause's disjunction, and the clausal form multiplies
   one choice per premise; on a Thrust closure input six such premises gave
   one formula 1,764 clauses (3 * 3 * 2 * 2 * 7 * 7), and three formulas 2,142
   of the problem's 2,376, which every later stage then walked clause by
   clause. *)
let definitional_split ~bound ~unknowns ~fresh phi =
  let count = predicted_cnf_clauses unknowns in
  let rec flat op phi =
    match phi with
    | Formula.BinaryOp (op', a, b, _) when Stdlib.( = ) op op' ->
        flat op a @ flat op b
    | _ -> [ phi ]
  in
  let out = ref [] and defs = ref [] in
  let rec go phi =
    if count phi <= bound then out := phi :: !out
    else
      match phi with
      | Formula.BinaryOp (Formula.And, _, _, _) ->
          List.iter (flat Formula.And phi) ~f:go
      | Formula.BinaryOp (Formula.Or, _, _, _) ->
          let parts =
            List.map (flat Formula.Or phi) ~f:(fun c ->
                if count c > 1 then define c else c)
          in
          out := Formula.or_of parts :: !out
      | _ -> out := phi :: !out
  and define c =
    let args =
      Set.to_list
      @@ Set.filter (Formula.term_sort_env_of c) ~f:(fun (x, _) ->
          not (Set.mem unknowns x))
    in
    let pvar = fresh () in
    let sorts = List.map args ~f:snd in
    let atom =
      Formula.mk_atom
      @@ Atom.mk_pvar_app pvar sorts
           (List.map args ~f:(fun (x, s) -> Term.mk_var x s))
    in
    defs := (pvar, sorts) :: !defs;
    let guard = Formula.mk_neg atom in
    List.iter (flat Formula.And c) ~f:(fun cj ->
        go (Formula.mk_or guard cj));
    atom
  in
  go phi;
  (List.rev !out, List.rev !defs)

(* A diagnostic only: the skeleton of [phi] as [predicted_cnf_clauses] reads
   it, with every subformula that mentions no unknown written [#], an atom of
   an unknown written by the unknown's name, and conjunctions and
   disjunctions flattened, so that the product a clausal form makes can be read
   off it.  Written to stderr under [COAR_SET_ASIDE_SKELETON]; read by nothing
   on the solving path. *)
let cnf_skeleton unknowns phi =
  let mentions phi =
    Set.exists (Formula.pvs_of phi) ~f:(fun pvar ->
        Set.mem unknowns (Ident.pvar_to_tvar pvar))
    || not (Set.are_disjoint (Formula.tvs_of phi) unknowns)
  in
  let rec flat op phi =
    match phi with
    | Formula.BinaryOp (op', a, b, _) when Stdlib.( = ) op op' ->
        flat op a @ flat op b
    | _ -> [ phi ]
  in
  let rec go phi =
    if not (mentions phi) then "#"
    else
      match phi with
      | Formula.Atom (Atom.App (Predicate.Var (pvar, _), _, _), _) ->
          Ident.name_of_pvar pvar
      | Formula.Atom _ ->
          "t{"
          ^ String.concat_map_set ~sep:","
              (Set.inter (Formula.tvs_of phi) unknowns)
              ~f:Ident.name_of_tvar
          ^ "}"
      | Formula.UnaryOp (_, a, _) -> "!" ^ go a
      | Formula.BinaryOp (((And | Or) as op), _, _, _) ->
          let parts = List.map (flat op phi) ~f:go in
          let pure, rest = List.partition_tf parts ~f:(String.equal "#") in
          let parts = (if List.is_empty pure then [] else [ "#" ]) @ rest in
          (match op with Formula.And -> "(& " | _ -> "(| ")
          ^ String.concat ~sep:" " parts ^ ")"
      | Formula.BinaryOp (_, a, b, _) -> "(op " ^ go a ^ " " ^ go b ^ ")"
      | Formula.Bind (_, _, a, _) -> "(Q " ^ go a ^ ")"
      | Formula.LetFormula (_, _, _, a, _) -> "(let " ^ go a ^ ")"
      | Formula.LetRec (_, a, _) -> "(letrec " ^ go a ^ ")"
  in
  go phi

(* evaluated now, not when first forced: the elimination runs in every solver
   domain at once (MuVal asks its primal and dual problems in parallel), and a
   [lazy] that a second domain forces while the first is forcing it raises
   [Lazy.Undefined] in the second, which ended a parallel run with that
   exception and no answer *)
let set_aside_skeleton =
  Lazy.from_val
    (Option.is_some (Stdlib.Sys.getenv_opt "COAR_SET_ASIDE_SKELETON"))

(* A cheap syntactic tautology test ([preprocessor.elim_tautology_test]).

   A clause formula is read as a disjunction of signed literals: [a => b]
   contributes the negated conjuncts of [a] and the disjuncts of [b], [not]
   flips the sign, and anything else is one literal.  A literal's key is the
   formula it stands for (its negation when it is negated), and its co-key that
   of its complement; an atom, or a negated atom, is put through
   [Evaluator.simplify] and [Normalizer.normalize] first, so that [x >= 0] and
   the simplifier's form [0 <= -1 - x] of its negation meet.  Larger literals are
   compared as they stand: the two functions are not cheap on them.

   Contract of [formula_is_tautology]: [true] only when some literal's co-key
   is syntactically another literal's key, or a key is [true].  Both functions
   preserve meaning, so equal keys denote the same truth value in every model
   and under every interpretation of the unknowns, and a disjunction holding a
   literal and its complement (or [true]) is valid.  A [false] answer says
   nothing.  [clause_is_tautology] adds the clause shape's own case: an atom in
   both [ps] and [ns].  A valid clause constrains no unknown, so dropping it
   leaves a set with the same models and the same solutions. *)
module ClauseTautology = struct
  let rec signed pol phi acc =
    match phi with
    | Formula.BinaryOp (Or, a, b, _) when pol -> signed pol a (signed pol b acc)
    | Formula.BinaryOp (And, a, b, _) when not pol ->
        signed pol a (signed pol b acc)
    | Formula.BinaryOp (Imply, a, b, _) when pol ->
        signed false a (signed true b acc)
    | Formula.UnaryOp (Not, a, _) -> signed (not pol) a acc
    | f -> (pol, f) :: acc

  let canon_atomic f =
    match f with
    | Formula.Atom _ | Formula.UnaryOp (Not, Formula.Atom _, _) ->
        Normalizer.normalize @@ Evaluator.simplify f
    | f -> f

  let key pol f =
    if pol then canon_atomic f else canon_atomic (Formula.mk_neg f)

  let formula_is_tautology phi =
    let lits = signed true phi [] in
    let keys = Set.Poly.of_list @@ List.map lits ~f:(fun (p, f) -> key p f) in
    Set.exists keys ~f:Formula.is_true
    || List.exists lits ~f:(fun (p, f) -> Set.mem keys (key (not p) f))

  let clause_is_tautology ((_, ps, ns, phi) : ClauseOld.t) =
    (not (Set.is_empty (Set.inter ps ns))) || formula_is_tautology phi
end

(* Simplifying the propositional constants [true] and [false] out of a formula,
   bottom up, without touching anything else; used after a predicate has been
   replaced by a constant.  Exact: each rule is a propositional identity, and a
   quantifier over a body that is constant is the constant, sorts being
   non-empty. *)
let rec simplify_bool_consts phi =
  let open Formula in
  match phi with
  | UnaryOp (Not, a, info) ->
      let a = simplify_bool_consts a in
      if is_true a then mk_false ()
      else if is_false a then mk_true ()
      else mk_unop ~info Not a
  | BinaryOp (And, a, b, info) ->
      let a = simplify_bool_consts a and b = simplify_bool_consts b in
      if is_false a || is_false b then mk_false ()
      else if is_true a then b
      else if is_true b then a
      else mk_binop ~info And a b
  | BinaryOp (Or, a, b, info) ->
      let a = simplify_bool_consts a and b = simplify_bool_consts b in
      if is_true a || is_true b then mk_true ()
      else if is_false a then b
      else if is_false b then a
      else mk_binop ~info Or a b
  | BinaryOp (Imply, a, b, info) ->
      let a = simplify_bool_consts a and b = simplify_bool_consts b in
      if is_false a || is_true b then mk_true ()
      else if is_true a then b
      else if is_false b then mk_neg a
      else mk_binop ~info Imply a b
  | BinaryOp (op, a, b, info) ->
      mk_binop ~info op (simplify_bool_consts a) (simplify_bool_consts b)
  | Bind (((Forall | Exists) as binder), bounds, body, info) ->
      let body = simplify_bool_consts body in
      if is_true body || is_false body then body
      else mk_bind ~info binder bounds body
  | LetFormula (var, sort, def, body, info) ->
      let body = simplify_bool_consts body in
      if is_true body || is_false body then body
      else mk_let_formula ~info var sort def body
  | phi -> phi

module Make
    (Verbose : Debug.Config.ConfigType)
    (Config : sig
      val resolution_threshold : int
      val resolution_complete_max_clauses : int
      val resolution_complete_prebound : bool
      val resolution_complete_early_exit : bool
      val resolution_complete_budget_ms : int option
      val propagate_lb_ub : bool
      val condense_resolvents : bool
      val condense_pure_resolvents : bool
      val condense_pure_unknown_free_resolvents : bool
      val condense_pure_max_checks : int
      val condense_pure_shape_candidates : bool
      val condense_pure_shape_commutative : bool
      val condense_pure_inclusion_candidates : bool
      val condense_pure_max_search_nodes : int option
      val condense_pure_memo_failures : bool
      val split_seq_reads : bool
      val valid_timeout : int
      val valid_rlimit : int option
      val seq_axiom_rlimit : int option
      val valid_fresh_quantified : bool
      val valid_memo : bool
      val valid_memo_reasks : int
      val valid_memo_reask_timeout : int
      val valid_memo_reask_max_disjuncts : int
      val valid_warm_reask_ms : int option
      val valid_memo_alpha : bool
      val valid_defer_pure_min_disjuncts : int option
      val seq_axiom_fallback_ms : int option
      val seq_axiom_fallback_once : bool
      val seq_axiom_fallback_after_refusal_only : bool
      val seq_axiom_fallback_charge_build : bool
      val split_seq_prefix_over_concat : bool
      val fork_refused_ms : int option
      val cvc5_retry_ms : int option
      val subsume_clauses : bool
      val tautology_test : bool
      val assign_before_cnf : bool
    end) =
struct
  module Debug = Debug.Make (Verbose)

  let id : int option ref = ref None
  let eliminated_pvars = ref Map.Poly.empty

  (* why each entry of [eliminated_pvars] was given its definition; a checker
     needs it to know whether the definition is implied by the original clauses
     or only preserves satisfiability *)
  let eliminated_reasons = ref Map.Poly.empty
  let elimination_count = ref 0

  let record_reason pvar reason =
    incr elimination_count;
    eliminated_reasons :=
      Map.Poly.set !eliminated_reasons ~key:(Ident.pvar_to_tvar pvar)
        ~data:(reason, !elimination_count)

  let resolved_pvars = ref Map.Poly.empty

  (* predicates resolved away without a recorded definition (a disjunctive
     head): constrained by the resolvents, so they must not be taken for
     unconstrained afterwards *)
  let resolved_without_def : Ident.tvar Set.Poly.t ref = ref Set.Poly.empty

  (* whether [resolve] records definitions (WitnessConfig.sat) *)
  let record_resolved = ref true

  (* Raised inside a complete elimination that gives up, saying why: [`Built]
     when a clause set it built has more clauses than the bound (the test the
     elimination always applies), [`Prebound] when the predicted size of the
     next step does ([CompletePrebound], before anything of the step is built
     or asked), [`Early_exit] when the step being built passed the bound before
     it was finished, [`Budget] when the attempt's wall-clock budget ran out.
     Caught only by the complete elimination, which then puts the clause set
     and the recorded definitions back. *)
  exception
    Complete_resolution_abandoned of
      [ `Built | `Prebound | `Early_exit | `Budget ]

  (* what the last complete elimination of this module did; read by the
     property tests and by nothing on the solving path *)
  let complete_outcome :
      [ `Kept
      | `Left_unknown
      | `Abandoned of [ `Built | `Prebound | `Early_exit | `Budget ] ]
      option
      ref =
    ref None

  (* how many clauses [resolve] has handed to [simplify_clause], each of which
     may be a validity question; a counter for the property tests *)
  let resolvents_simplified = ref 0

  (* the resolvents [resolve] has normalised since it was last reset; a counter
     for the property tests, as the one above *)
  let resolvents_normalised = ref 0

  (* [Some d] once the wall-clock instant [d] has passed: the attempt's budget
     is spent *)
  let check_complete_deadline = function
    | Some d when Time_float.(now () > d) ->
        raise (Complete_resolution_abandoned `Budget)
    | _ -> ()

  (* *)
  (* The solution of a predicate eliminated by resolution: the disjunction of
     the bodies of its defining clauses (existentially closed over the clause
     variables), which is a valid interpretation once the remaining predicates
     get theirs — the resolvents are exactly the use clauses under that
     substitution.  Quantifier elimination is optional because this runs on
     every resolution; the final solution is quantifier-eliminated once. *)
  let resolve_solution_of ?(simplify_solution = true) pv exi_senv clauses_pos =
    let is_resolved atm = Stdlib.(pv = Atom.pvar_of atm) in
    let args =
      (* deterministic names: drawing them from the global fresh-variable
         counter here changed the names — and with them the search order — of
         everything generated afterwards, and turned a 10 s CEGIS run into a
         timeout (13.c.small) *)
      Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pv)
      |> Logic.Sort.args_of
      |> List.mapi ~f:(fun i s ->
          Term.mk_var
            (Ident.Tvar (sprintf "#sol_%s_%d" (Ident.name_of_pvar pv) i))
            (Logic.ExtTerm.to_old_sort s))
    in
    let eqs, param_senvs, phis =
      List.unzip3
      @@ List.map clauses_pos ~f:(fun (param_senv, ps, ns, phi) ->
          let _, _, args0, _ =
            Atom.let_pvar_app @@ Set.find_exn ~f:is_resolved ps
          in
          let eq = Formula.and_of @@ List.map2_exn args args0 ~f:Formula.eq in
          let ps' =
            Set.filter ps ~f:(Atom.pvar_of >> Stdlib.( <> ) pv)
            |> Set.to_list
            |> List.map ~f:Formula.mk_atom
          in
          let ns' =
            Set.to_list ns |> List.map ~f:(Formula.mk_atom >> Formula.mk_neg)
          in
          let param_senv' =
            Map.Poly.to_alist param_senv |> Logic.to_old_sort_env_list
          in
          ( eq,
            param_senv',
            Formula.mk_neg @@ Formula.or_of @@ ps' @ ns' @ [ phi ] ))
    in
    let params =
      List.map args
        ~f:(Term.let_var >> fst >> Tuple2.map_snd ~f:Logic.ExtTerm.of_old_sort)
    in
    Logic.ExtTerm.mk_lambda params
    @@ Logic.ExtTerm.of_old_formula
    @@ (fun ret ->
      Debug.print
      @@ lazy
           (sprintf "[resolve_solution_of] \n%s (%s) := %s"
              (Ident.name_of_pvar pv)
              (String.concat_map_list ~sep:"," args ~f:Term.str_of)
              (Formula.str_of ret));
      ret)
    @@ (fun phi ->
      if simplify_solution then
        Z3Smt.Z3interface.qelim ~id:!id ~fenv:(LogicOld.get_fenv ()) phi
      else phi)
    @@ Formula.exists (List.concat param_senvs)
    @@ (fun phi -> if simplify_solution then Evaluator.simplify phi else phi)
    @@ Formula.or_of
    @@ List.map2_exn eqs phis ~f:(fun eq phi -> Formula.mk_and eq phi)
  (* *)

  (* three-valued validity for ClauseOld.simplify: an undecided Z3 answer must
     not be taken as "invalid" *)
  (* [phi1 = phi2] between two Bool terms is an iff, and [Formula.cnf_of]
     expands an iff into the two clauses it stands for.  Left as an equality
     *atom* it sits in the clause's pure part instead, where the accounting all
     the rules below decide from is blind to it: [ClauseOld.pvs_of] ignores
     [phi] and [ClauseSetOld.count_pvar_apps] counts only the atom sets, so an
     unknown applied only there looks one-sided and is eliminated while the
     pure part still constrains it.  Only equalities
     that mention an *unknown* are rewritten -- a universal is an array-sorted
     term variable, not a predicate variable, and equalities between those are
     left alone -- and the rewrite lives here rather than in [Formula.cnf_of],
     which fourteen call sites across every backend share. *)
  let expand_bool_eq_of_unknowns exi_senv =
    let unknowns = Map.key_set exi_senv in
    Formula.map_atom ~f:(function
      | Atom.App
          (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as psym), [ t1; t2 ], _) as
        atom
        when (T_bool.is_formula t1 || T_bool.is_formula t2)
             && Fn.non Set.is_empty
                @@ Set.inter
                     (Set.union (Term.fvs_of t1) (Term.fvs_of t2))
                     unknowns -> (
          let fml t =
            if T_bool.is_formula t then T_bool.let_formula t
            else Formula.eq t (T_bool.mk_true ())
          in
          match psym with
          | T_bool.Eq -> Formula.mk_iff (fml t1) (fml t2)
          | _ -> Formula.mk_xor (fml t1) (fml t2)
          | exception exn_ when not (Common.Timer.is_async exn_) -> Formula.mk_atom atom)
      | atom -> Formula.mk_atom atom)

  (* Bounded, and a shape the solver may not return from is not asked.  The
     consumer is the clause simplification, which treats an undecided check as
     "keep every disjunct", so either measure can only cost a simplification,
     never the soundness of a verdict.  Without them a validity query with a
     free sequence and an integer quantifier reading it ([forall i. 0 <= i <
     seq.len s => seq.nth s i = ...], the shape a Rust frontend writes for a
     visited sequence) did not return, and the process never left
     preprocessing.  The shape test catches a quantifier BINDING a sequence or
     any regular expression, where no budget holds; the budget catches the rest,
     and its default of five seconds ([Config.valid_timeout], in milliseconds
     of wall-clock time) is a choice, not a measured bound.  [Config.valid_rlimit]
     adds a deterministic Z3 resource limit per query beside it. *)
  (* The answers of [check_valid] within one [elim_pvs] call, when
     [Config.valid_memo] is set: every clause is simplified again after each
     elimination step, so an untouched clause is asked the same question
     repeatedly, and an undecided one pays the whole budget each time.  An
     entry is a [`Valid] answer, a shape the solver is not asked about, or the
     number of asks that ran out of their budget, which is not a property of
     the query (see [check_valid]).  An [`Invalid] answer is not recorded: it
     comes back in hundredths of a second, and asking it again is not free of
     effect, since the pooled context the later queries share is then not the
     one they would have met without the record -- skipping those asks made
     five clause checks run out of five seconds that were each proved within
     two when they were asked.  Keyed
     by the formula's disjuncts before any rewriting; cleared at the start of each
     [elim_pvs] call, since the answer also depends on the function and
     datatype environments, which may change between problems.  A process-
     global table shared by solver domains, so every access takes the mutex
     (the convention of [Evaluator]'s validity records). *)
  (* For tracing only: " (at T s)", the wall-clock seconds since this module
     was initialised, which is the start of the process to within the
     initialisation of the modules linked before it.  Called only inside the
     [lazy] of a [Debug.print], so it costs nothing when tracing is off, and it
     changes no answer.  It puts the elimination's own steps -- each resolved
     predicate, the normal form, the bounds -- on one clock with the rest of a
     trace, where they had no time at all. *)
  let trace_clock_origin = Common.Clock.now_float ()

  let at () =
    sprintf " (at %.2f s)"
      (Time_float.Span.to_sec
         (Time_float.diff (Common.Clock.now_float ()) trace_clock_origin))

  let valid_memo :
      ( Formula.t list,
        [ `Valid | `Refused | `Undecided of int ] )
      Hashtbl.Poly.t =
    Hashtbl.PolyDeep.create ()
  let valid_memo_mutex = Caml_threads.Mutex.create ()

  let with_valid_memo f =
    Caml_threads.Mutex.lock valid_memo_mutex;
    match f valid_memo with
    | ret ->
        Caml_threads.Mutex.unlock valid_memo_mutex;
        ret
    | exception exn_ ->
        Caml_threads.Mutex.unlock valid_memo_mutex;
        raise exn_

  let valid_dump_count = Atomic.make 0

  let rec check_valid phi =
    if Config.valid_memo then (
      (* a clause comes back from a later round with the same disjuncts in
         another order, and with the variables of a quantifier block listed in
         another order, so the key is the sorted list of its disjuncts with
         each block's variables sorted, which is valid exactly when the
         formula is *)
      let key =
        Common.PhaseTime.with_phase "memo-key" @@ fun () ->
        (* [Config.valid_memo_alpha]: also up to a renaming of the variables,
           so that two clauses equal but for their variables' names share
           one answer *)
        if Config.valid_memo_alpha then ValidKey.alpha phi
        else ValidKey.plain phi
      in
      match with_valid_memo (fun tbl -> Hashtbl.Poly.find tbl key) with
      | Some ((`Valid | `Refused) as r) ->
          Debug.print
          @@ lazy
               (sprintf
                  "[check_valid] repeated query answered from the record: %s"
                  (match r with
                  | `Valid -> "valid"
                  | `Refused -> "undecided (not asked)"));
          (match r with `Valid -> `Valid | _ -> `Unknown)
      | Some (`Undecided n) when Option.is_some Config.valid_warm_reask_ms ->
          (* the two-phase ask has had its second phase already *)
          Debug.print
          @@ lazy
               (sprintf
                  "[check_valid] repeated query answered from the record: \
                   undecided after a warm re-ask (%d asks)"
                  n);
          `Unknown
      | Some (`Undecided n)
        when n > Config.valid_memo_reasks
             || List.length key > Config.valid_memo_reask_max_disjuncts ->
          Debug.print
          @@ lazy
               (sprintf
                  "[check_valid] repeated query answered from the record: \
                   undecided after %d asks (%d disjuncts)"
                  n (List.length key));
          `Unknown
      | prev ->
          (* a query that ran out of its budget is asked again, up to
             [Config.valid_memo_reasks] times and with the short budget
             [Config.valid_memo_reask_timeout]: the same text of one query
             was seen to run out of five seconds twice and then be proved in
             0.05 s, so a timeout is a draw rather than a property of the
             query; a query that never decides pays the short budget only.
             A query of more than [Config.valid_memo_reask_max_disjuncts]
             disjuncts is not asked again: a repeated ask of a clause of
             hundreds of disjuncts costs seconds beyond its budget and was
             never seen to decide *)
          let asked, timeout =
            match prev with
            | Some (`Undecided n) -> (n, Config.valid_memo_reask_timeout)
            | _ -> (0, Config.valid_timeout)
          in
          let fallback_cap =
            SeqAxiomCap.for_ask ~cap:Config.seq_axiom_fallback_ms
              ~once:Config.seq_axiom_fallback_once
              ~global:(Z3Smt.Z3interface.seq_axiom_fallback_base_budget ())
              ~valid_timeout:Config.valid_timeout
              ~reask_timeout:Config.valid_memo_reask_timeout
              ~reask:(asked > 0)
          in
          let r, refused =
            match Config.valid_warm_reask_ms with
            | Some first_ms ->
                WarmReask.ask ~first_ms ~timeout ~fallback_cap
                  (fun ~fallback_cap ~timeout ->
                    check_valid_uncached ~fallback_cap ~timeout phi)
            | None -> check_valid_uncached ~fallback_cap ~timeout phi
          in
          (match r with
          | `Invalid -> ()
          | `Valid | `Unknown ->
              let entry =
                match r with
                | `Valid -> `Valid
                | `Unknown when refused -> `Refused
                | _ -> `Undecided (asked + 1)
              in
              with_valid_memo (fun tbl -> Hashtbl.Poly.set tbl ~key ~data:entry));
          r)
    else
      fst
        (match Config.valid_warm_reask_ms with
        | Some first_ms ->
            WarmReask.ask ~first_ms ~timeout:Config.valid_timeout
              ~fallback_cap:Config.seq_axiom_fallback_ms
              (fun ~fallback_cap ~timeout ->
                check_valid_uncached ~fallback_cap ~timeout phi)
        | None ->
            check_valid_uncached ~fallback_cap:Config.seq_axiom_fallback_ms
              ~timeout:Config.valid_timeout phi)

  (* [fallback_cap]: the cap on the sequence-axiom fallback for this question
     ([SeqAxiomCap]) *)
  and check_valid_uncached ~fallback_cap ~timeout phi =
    Common.PhaseTime.with_phase "valid" @@ fun () ->
    (* With [COAR_ELIM_VALID_DUMP=dir] in the environment, each question's
       solver checks are kept as [dir/qN-PID_k.smt2], an undecided one's
       question also as [dir/qN-PID_native.smt2] (the solver interface's
       [with_validity_dump]), and one line per question -- its name, outcome,
       wall-clock seconds and budget -- is appended to [dir/index.tsv], so
       that a question undecided here can be replayed in a process of its
       own.  A diagnostic; nothing is written without the variable. *)
    Z3Smt.Z3interface.with_validity_dump ~native:false
      ~var:"COAR_ELIM_VALID_DUMP" ~counter:valid_dump_count ~id:!id ~timeout
      ~outcome:(function
        | `Valid, _ -> "valid"
        | `Invalid, _ -> "invalid"
        | `Unknown, _ -> "undecided")
      (LogicOld.get_fenv ()) phi
    @@ fun () -> check_valid_asked ~fallback_cap ~timeout phi

  (* whether [phi], read as an integer as a word ([int_to_bv] of a
     non-numeral), is proved through the words of its pieces'
     matched-instance forms ([SeqInstantiation.valid_by_word_forms]), each
     asked under [timeout] ms: [`Proved], or [`Rest psi] with [psi] valid
     exactly when [phi] is (only with [words_keep_proved]: the pieces not
     proved, [SeqInstantiation.words_by_pieces]), or [`Not_proved], which
     means only "not proved" *)
  and valid_by_words ~timeout phi =
    if not (Z3Smt.Z3interface.reads_int_as_word phi) then `Not_proved
    else Common.PhaseTime.with_phase "words" (fun () ->
        (* [COAR_WORDS_TRACE] set: one stderr line per piece and per question, with its
           outcome and seconds; a diagnostic, nothing else changes *)
        let trace = Lazy.force words_trace in
        let t0 = Common.Clock.now_s () in
        let asks = ref 0 in
        let note m =
          if trace then
            Stdlib.Printf.eprintf "[words-trace] %s at %.2f s\n%!" m
              (Common.Clock.now_s () -. t0);
          Debug.print @@ lazy ("[check_valid] words: " ^ m)
        in
        let ask_word c =
              incr asks;
              let t = Common.Clock.now_s () in
              let r =
                Z3Smt.Z3interface.check_valid_by_words ~timeout:(Some timeout)
                  ~id:!id (LogicOld.get_fenv ()) c
              in
              if trace then
                Stdlib.Printf.eprintf "[words-trace] ask size %d: %s in %.2f s\n%!"
                  (Formula.ast_size c)
                  (match r with `Valid -> "valid" | _ -> "not proved")
                  (Common.Clock.now_s () -. t);
              r
        in
        let ask () =
          if Atomic.get words_keep_proved then
            match
              PCSatCommon.SeqInstantiation.words_by_pieces
                ~two_rounds_first:true ~note ~ask:ask_word phi
            with
            | `Proved -> `Proved
            | `Rest psi -> `Rest psi
            | `Ask_whole -> `Not_proved
          else if
          PCSatCommon.SeqInstantiation.valid_by_word_forms
            ~two_rounds_first:true
            ~note
            ~ask:ask_word phi
          then `Proved
          else `Not_proved
        in
        let r =
          match Atomic.get words_full_major_every with
          | None -> ask ()
          | Some n -> Z3Smt.Z3interface.with_new_context_full_major_every n ask
        in
        if trace then
          Stdlib.Printf.eprintf
            "[words-trace] question size %d: %s, %d asks, %.2f s\n%!"
            (Formula.ast_size phi)
            (match r with
            | `Proved -> "PROVED"
            | `Rest psi -> sprintf "rest of size %d" (Formula.ast_size psi)
            | `Not_proved -> "not proved")
            !asks
            (Common.Clock.now_s () -. t0);
        r)

  and check_valid_asked ~fallback_cap ~timeout phi =
    (* the same question in the form z3 decides (see [Config.split_seq_reads]
       in the preprocessor); only the query is rewritten, never the clause *)
    let phi =
      Common.PhaseTime.with_phase "split" (fun () ->
      if Config.split_seq_reads then Evaluator.split_seq_reads_for_validity phi
      else phi)
    in
    (* [Config.split_seq_prefix_over_concat]: every [extract (a ++ b) 0 k]
       replaced by [ite (k <= len a) (extract a 0 k) (a ++ extract b 0
       (k - len a))], an identity in every model, so the question keeps its
       meaning.  Done here, before the shape test and before the sequence-axiom
       fallback translates [phi], so that both the native ask and the
       fallback's form see the rewritten question.  z3 can fail to find this
       case split by itself: a two-disjunct quantifier-free question of this
       shape ran out of 10 s under every seed tried and was answered within
       half a second once rewritten.  The record ([valid_memo]) is keyed on
       the question before this rewrite, which is a function of it that
       commutes with the renamings and reorderings the key forgets, so one key
       still stands for one asked question; and a record hit then costs no
       rewrite. *)
    let phi =
      if Config.split_seq_prefix_over_concat then
        Common.PhaseTime.with_phase "prefix-concat" (fun () ->
            Evaluator.rewrite_seq_prefix_over_concat phi)
      else phi
    in
    (* [split_int_binders_at_ite]: a read at [x - c] under a binder [x] that
       an [ite] splits at [c] is not matched by a ground read, so the solver
       finds the instance it needs only by model-based instantiation, and on
       one recorded question whether it did depended on the spelling of a
       generated sort's name.  The split makes the read one at [x].  Exact, so
       both the native ask and the fallback's form see the rewritten
       question; the record is keyed on the question before it, as for the
       prefix rewrite above *)
    let phi =
      if Atomic.get split_int_binders_at_ite then
        Common.PhaseTime.with_phase "int-binder-split" (fun () ->
            IntBinderSplit.rewrite_at IntBinderSplit.elim_tally phi)
      else phi
    in
    (* [implied_factor_equalities]: exact, so the native ask and the
       fallback's form both see the rewritten question; keyed in the record
       before it, as the rewrites above *)
    let phi =
      if Atomic.get implied_factor_equalities then
        Common.PhaseTime.with_phase "factor-eqs" (fun () ->
            Z3Smt.Z3interface.implied_factor_equalities ~timeout ~id:!id
              (LogicOld.get_fenv ()) phi)
      else phi
    in
    let not_asked = "not asked: the solver may not return on this shape" in
    let started = Common.Clock.now_float () in
    let fallback_before = Z3Smt.Z3interface.seq_axiom_fallback_secs_here () in
    let build_before =
      Z3Smt.Z3interface.seq_axiom_fallback_build_secs_here ()
    in
    (* [words_first]: a question that reads an integer as a word is first
       asked through the words of its pieces' matched-instance forms
       ([SeqInstantiation.valid_by_word_forms]), each under the question's
       budget; only a proof is read, so anything else leaves the question to
       be asked as before *)
    let words =
      if Atomic.get words_first then valid_by_words ~timeout phi else `Not_proved
    in
    let by_words = match words with `Proved -> true | _ -> false in
    let words_traced =
      Lazy.force words_trace && Atomic.get words_first
      && Z3Smt.Z3interface.reads_int_as_word phi
    in
    (* [words_keep_proved]: what is asked from here on is the conjunction of
       the pieces the words route did not prove, valid exactly when [phi] is
       (see [SeqInstantiation.words_by_pieces]); a proof or a countermodel of
       it is one of [phi] *)
    let phi = match words with `Rest psi -> psi | _ -> phi in
    let r =
      if by_words then (
        Debug.print
        @@ lazy
             "[check_valid] proved through the words of its matched-instance \
              forms";
        `Valid)
      else
      Z3Smt.Z3interface.with_rlimit ~label:"elim" Config.valid_rlimit @@ fun () ->
      (* the fallback's own resource limit: its checks are asked in a
         context of their own, so they get a count of their own *)
      Z3Smt.Z3interface.with_seq_axiom_rlimit Config.seq_axiom_rlimit
      @@ fun () ->
      Z3Smt.Z3interface.with_seq_axiom_charge_build
        Config.seq_axiom_fallback_charge_build
      @@ fun () ->
      let refused =
        Common.PhaseTime.with_phase "shape" (fun () ->
            Z3Smt.Z3interface.may_not_return phi)
      in
      Z3Smt.Z3interface.with_seq_axiom_fallback_cap
        (SeqAxiomCap.for_branch
           ~after_refusal_only:Config.seq_axiom_fallback_after_refusal_only
           ~refused fallback_cap)
      @@ fun () ->
      if refused then
        (* a shape refused natively may still be proved with the sequences
           axiomatised, which binds no sequence (and is off unless asked);
           when that proves nothing, [Config.fork_refused_ms] asks the refused
           question itself in a forked copy killed at the smaller of the two
           budgets, in a fresh context with no Z3 budget (the kill is the
           bound), and reads only its proof.  After the fallback, so that a
           question the fallback proves costs no copy *)
        (match
          Z3Smt.Z3interface.with_seq_axiom_fallback
            ~caller_timeout:(Some timeout)
            ~id:!id (LogicOld.get_fenv ()) phi
            (`Unknown not_asked)
        with
        | (`Valid | `Invalid _) as r -> r
        | r -> (
            match Config.fork_refused_ms with
            | None -> r
            | Some ms -> (
                let fenv = LogicOld.get_fenv () in
                match
                  Common.PhaseTime.with_phase "fork-refused" @@ fun () ->
                  PCSatCommon.ForkedQuery.valid_within
                    ~ms:(Int.min ms timeout) (fun () ->
                      match
                        Z3Smt.Z3interface.check_sat ~timeout:None
                          ~fresh_solver:true ~id:None fenv
                          [ LogicOld.Formula.negate phi ]
                      with
                      | `Unsat -> `Valid
                      | `Sat model -> `Invalid model
                      | res -> res)
                with
                | `Valid -> `Valid
                | `Timeout | `Unknown _ -> r)))
      else
        Z3Smt.Z3interface.check_valid ~timeout:(Some timeout)
          ~fresh_solver:
            (Config.valid_fresh_quantified
            && LogicOld.Formula.number_of_quantifiers phi > 0)
          ~id:!id
          (LogicOld.get_fenv ()) phi
    in
    (* [Config.cvc5_retry_ms]: a question Z3 left undecided (refused shapes
       included) is given to cvc5 as a process of its own with that budget,
       and only its [unsat] of the negation is read, as a proof
       ([PCSatCommon.Cvc5Proof.valid_within]); anything else leaves the answer
       as it was *)
    let r =
      match (r, Config.cvc5_retry_ms) with
      | (`Valid | `Invalid _), _ | _, None -> r
      | _, Some ms ->
          if
            Common.PhaseTime.with_phase "cvc5-retry" (fun () ->
                PCSatCommon.Cvc5Proof.valid_within ~site:"elim" ~ms ~id:!id
                  (LogicOld.get_fenv ()) phi)
          then `Valid
          else r
    in
    let secs () =
      Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) started)
    in
    (* how much of this question's time was the sequence-axiom fallback, and
       the clock; for the trace only *)
    let fallback () =
      let f =
        Z3Smt.Z3interface.seq_axiom_fallback_secs_here () -. fallback_before
      in
      let b =
        Z3Smt.Z3interface.seq_axiom_fallback_build_secs_here () -. build_before
      in
      (if Float.(f > 0.) then sprintf " (fallback %.2f s, build %.2f s)" f b
       else "")
      ^ at ()
    in
    (* which exact query, for telling apart two asks the record would take
       for one: the text's length and a hash of it *)
    let text () =
      let s = LogicOld.Formula.str_of phi in
      sprintf "%d chars, text hash %08x" (String.length s)
        (Stdlib.Hashtbl.hash s)
    in
    if words_traced && not by_words then
      Stdlib.Printf.eprintf "[words-trace] then natively%s: %s in %.2f s\n%!"
        (match words with `Rest _ -> " (the rest)" | _ -> "")
        (match r with
        | `Valid -> "valid"
        | `Invalid _ -> "invalid"
        | `Timeout -> "timeout"
        | _ -> "undecided")
        (secs ());
    match r with
    | `Valid ->
        Debug.print
        @@ lazy
             (sprintf "[check_valid] valid in %.2f s (%s)%s" (secs ()) (text ())
                (fallback ()));
        (`Valid, false)
    | `Invalid _ ->
        Debug.print
        @@ lazy
             (sprintf "[check_valid] invalid in %.2f s (%s)%s" (secs ())
                (text ()) (fallback ()));
        (`Invalid, false)
    | r ->
        let secs = secs () in
        (* under [COAR_ELIM_VALID_DUMP], an undecided question as rewritten
           above, whether or not it was asked natively; only undecided ones,
           since printing a question builds a context of its own *)
        Z3Smt.Z3interface.dump_native_question ~id:!id (LogicOld.get_fenv ())
          phi;
        Debug.print
        @@ lazy
             (sprintf "[check_valid] undecided after %.2f s [%s]%s (%s): %s" secs
                (text ()) (fallback ())
                (* say WHICH undecided: the solver's own reason separates "I
                   gave up on these quantifiers" from "I was interrupted" and
                   from "I answered but produced no model", and those want
                   different repairs.  Printing them all as "unknown" sent one
                   investigation looking for an incompleteness that was not
                   there. *)
                (match r with
                | `Timeout -> "timeout"
                | `Unknown reason -> reason
                | _ -> "unknown")
                (LogicOld.Formula.str_of phi));
        ( `Unknown,
          match r with
          | `Unknown reason -> String.equal reason not_asked
          | _ -> false )

  (* Is it satisfiable, with a budget?  Used where the question is whether any
     choice of the functional predicates works at all: the predicates appear as
     uninterpreted function symbols, which are implicitly existential, so an
     [Unsat] means no choice of them satisfies the clause in any model -- and
     that refutes the system, since a solution would have to satisfy it in every
     model.  [Sat] is [exists P. exists M] and says nothing, so it is not acted
     on. *)
  let check_sat_bounded ~timeout phi =
    match
      Z3Smt.Z3interface.check_sat ~timeout:(Some timeout) ~id:!id
        (LogicOld.get_fenv ()) [ phi ]
    with
    | `Unsat -> `Unsat
    | `Sat _ -> `Sat
    | `Timeout -> `Timeout
    | _ -> `Unknown

  (* The same question with a caller-chosen budget, for the places that need
     to know *whether* a formula is decidable before committing to it: a Z3 call
     is not interruptible by the alarm-based timer, so an undecidable one hangs
     the process rather than costing an answer. *)
  let check_valid_bounded ~timeout phi =
    match
      Z3Smt.Z3interface.check_valid ~timeout:(Some timeout) ~id:!id
        (LogicOld.get_fenv ()) phi
    with
    | `Valid -> `Valid
    | `Invalid _ -> `Invalid
    | `Timeout -> `Timeout
    | _ -> `Unknown

  (* for ClauseOld.simplify on interpretation-dependent disjuncts: is the
     universal closure satisfiable in some model? *)
  let check_sat_forall phi =
    Common.PhaseTime.with_phase "sat-forall" @@ fun () ->
    match
      (* [phi] is universally quantified and Z3 need not terminate on it (a
         datatype over arrays is enough); this runs once per such disjunct of
         every clause in every elimination round, so the budget matches the
         neighbouring simplification queries.  An undecided answer keeps the
         disjunct, which is the safe direction. *)
      Z3Smt.Z3interface.check_sat ~timeout:(Some 1000) ~id:!id
        (LogicOld.get_fenv ()) [ phi ]
    with
    | `Sat _ ->
        Debug.print
        @@ lazy
             (sprintf "[check_sat_forall] sat: %s" (LogicOld.Formula.str_of phi));
        `Sat
    | `Unsat ->
        Debug.print
        @@ lazy
             (sprintf "[check_sat_forall] unsat: %s"
                (LogicOld.Formula.str_of phi));
        `Unsat
    | r ->
        (* the solver's own reason, for the same purpose as the one above *)
        Debug.print
        @@ lazy
             (sprintf "[check_sat_forall] undecided (%s): %s"
                (match r with
                | `Timeout -> "timeout"
                | `Unknown reason -> reason
                | _ -> "unknown")
                (LogicOld.Formula.str_of phi));
        `Unknown

  (* [ClauseOld.simplify] with the large pure clauses' questions deferred
     ([DeferPure]; [Config.valid_defer_pure_min_disjuncts]); [defer] is off
     only for the last simplification of a round that leaves an unknown *)
  (* [final] marks a round's last simplification ([PureToVerdict]) *)
  let simplify_clause ?(defer = true) ?(final = false) unknowns cl =
    let check_valid =
      DeferPure.wrap ~min_disjuncts:Config.valid_defer_pure_min_disjuncts
        ~defer
        ~on_defer:(fun d ->
          Debug.print
          @@ lazy
               (sprintf
                  "[check_valid] deferred: a pure clause of %d disjuncts" d))
        check_valid cl
    in
    let check_valid =
      PureToVerdict.wrap
        ~on:
          (Atomic.get defer_pure_to_verdict
          || Atomic.get defer_pure_to_round_end)
        ~words_only:(Atomic.get defer_pure_to_verdict) ~final ~defer
        ~full:check_valid
        ~words:(fun phi ->
          (* only a proof of the whole question is read here: [`Rest] (the
             pieces left by [words_keep_proved]) is "not proved" *)
          let r =
            match valid_by_words ~timeout:Config.valid_timeout phi with
            | `Proved -> true
            | `Rest _ | `Not_proved -> false
          in
          Debug.print
          @@ lazy
               (sprintf
                  "[check_valid] pure clause left to the verdict: %s through \
                   its words"
                  (if r then "proved" else "not proved"));
          r)
        cl
    in
    ClauseOld.simplify ~check_sat_forall unknowns check_valid cl

  (* [~elim_free_univ_vars] is labelled because it is the expensive argument and
     the call site otherwise shows nothing of it: it runs once per resolvent and
     is 50-96% of this function's time.  It eliminates the variables a clause
     quantifies IMPLICITLY and is not quantifier elimination, which is why it no
     longer shares a name with the real one. *)
  (* [?guard], when given, is called with the size of the clause set built so
     far (the clauses not mentioning [pv] plus the resolvents simplification
     has kept) before each simplification of a resolvent and after each one
     it keeps, and may raise to stop the step; the clauses are simplified in
     the same order as without it, so a step it does not stop returns the
     same set, and since that set only grows while it is built, the last size
     the guard is told is the size of the result. *)
  (* [ClauseSubsume.reduce], logged *)
  let subsume ~where cls =
    let cls' =
      Common.PhaseTime.with_phase "subsume" (fun () -> ClauseSubsume.reduce cls)
    in
    let d = Set.length cls - Set.length cls' in
    if d > 0 then
      Debug.print
      @@ lazy
           (sprintf "[elim_pvs] subsumption (%s): %d of %d clauses dropped" where
              d (Set.length cls));
    cls'

  (* [ClauseTautology.clause_is_tautology], logged *)
  let drop_tautologies ~where cls =
    let cls' = Set.filter cls ~f:(Fn.non ClauseTautology.clause_is_tautology) in
    let d = Set.length cls - Set.length cls' in
    if d > 0 then
      Debug.print
      @@ lazy
           (sprintf "[elim_pvs] tautology test (%s): %d of %d clauses dropped"
              where d (Set.length cls));
    cls'

  (* [?tick], when given, is called before each resolvent is normalised and
     may raise to stop the step.  The normalisation (quantifier elimination
     included) runs over every resolvent before [?guard] sees the first, and
     on a large step it is most of the step's time, so a wall-clock budget
     read only through [?guard] was read after the time had been spent. *)
  (* [?index], when given, describes [clauses] ([ResolutionIndex]'s invariant)
     and is [reduced], and [Config.subsume_clauses] holds: the clauses applying
     [pv] are read from it, and the step's subsumption is
     [ResolutionIndex.step]; the result is the same set, built by the same
     insertions, and the index then describes it.  Without it the whole
     clause set is partitioned and subsumed. *)
  let resolve ?guard ?tick ?index ~elim_free_univ_vars exi_senv pv clauses =
    Common.PhaseTime.with_phase "resolve" @@ fun () ->
    Debug.print @@ lazy (sprintf "eliminating %s" @@ Ident.name_of_pvar pv);
    (* Both of these rebuild a structure the size of the predicate signature --
       one converts every sort to the other term representation -- and both are
       constants of this call, so they are computed here rather than once per
       resolvent. *)
    let exi_senv_old = Logic.to_old_sort_env_map exi_senv in
    let unknowns = Map.key_set exi_senv in
    let is_resolved atm = Stdlib.(pv = Atom.pvar_of atm) in
    (* With the index the rest is not built (only its size and membership are
       read, from the index less the touched clauses), and the two sides are
       built as [Set.partition3_map] builds them, by adding their elements in
       increasing order, so they are the same trees. *)
    let clauses_pos, clauses_neg, clauses_rest, touched =
      match index with
      | None ->
          let pos, neg, rest =
            Set.partition3_map clauses ~f:(fun ((_, ps, ns, _) as cl) ->
                if Set.exists ps ~f:is_resolved then `Fst cl
                else if Set.exists ns ~f:is_resolved then `Snd cl
                else `Trd cl)
          in
          (pos, neg, Some rest, [])
      | Some index ->
          let pos, neg =
            List.fold (ResolutionIndex.clauses_of index pv) ~init:([], [])
              ~f:(fun (pos, neg) ((_, (_, ps, ns, _)) as e) ->
                if Set.exists ps ~f:is_resolved then (e :: pos, neg)
                else if Set.exists ns ~f:is_resolved then (pos, e :: neg)
                else (pos, neg))
          in
          let in_order l =
            List.map l ~f:snd
            |> List.sort ~compare:Stdlib.compare
            |> List.fold ~init:Set.Poly.empty ~f:Set.add
          in
          (in_order pos, in_order neg, None, List.map (pos @ neg) ~f:fst)
    in
    let clauses_pos_lin, clauses_pos_nonlin =
      Set.partition_tf clauses_pos ~f:(fun (_, ps, _, _) ->
          Set.count ps ~f:is_resolved = 1)
    in
    (* recorded lazily: building the definition here (fresh names, formula
       construction) measurably changed later CEGIS runs; it is forced only
       when the final answer is assembled.  Only
       when every defining clause has a single occurrence of [pv] in its head:
       the recorded definition is the least solution of the defining clauses,
       which a disjunctive head [P t1 \/ P t2 \/ ...] does not have (the
       resolvents replace both occurrences at once, and a definition built
       from one of them violated a use clause: x > 0 => P x \/ P (-x),
       P x /\ x > 0 => false is satisfiable but got P := x >= 1). *)
    if not !record_resolved then ()
    else if Set.is_empty clauses_pos_nonlin then
      resolved_pvars :=
        Map.Poly.set !resolved_pvars ~key:(Ident.pvar_to_tvar pv)
          ~data:
            (lazy
              (resolve_solution_of ~simplify_solution:false pv exi_senv
                 (Set.to_list clauses_pos)))
    else (
      resolved_without_def :=
        Set.add !resolved_without_def (Ident.pvar_to_tvar pv);
      Debug.print
      @@ lazy
           (sprintf
              "[resolve] no solution recorded for %s: a defining clause has a \
               disjunctive head"
              (Ident.name_of_pvar pv)));
    let clauses_neg_lin, clauses_neg_nonlin =
      Set.partition_tf clauses_neg ~f:(fun (_, _, ns, _) ->
          Set.count ns ~f:is_resolved = 1)
    in
    Debug.print
    @@ lazy
         (sprintf
            "#rest %d, #poslin: %d, #posnonlin: %d, #neglin: %d, \
             #negnonlin: %d%s"
            (match clauses_rest with
            | Some rest -> Set.length rest
            | None ->
                Option.value_map index ~default:0 ~f:ResolutionIndex.length
                - List.length touched)
            (Set.length clauses_pos_lin)
            (Set.length clauses_pos_nonlin)
            (Set.length clauses_neg_lin)
            (Set.length clauses_neg_nonlin)
            (at ()));
    let cnf_resolvents =
      Set.concat_map ~f:(fun cl ->
          Option.iter tick ~f:(fun tick -> tick ());
          incr resolvents_normalised;
          Common.PhaseTime.with_phase "normalise" @@ fun () ->
          let senv, phi =
            let senv, phi = ClauseOld.to_formula cl in
            (* ToDo: the following can be a bottle neck *)
            let phi =
              Common.PhaseTime.with_phase "simp1" (fun () ->
                  Normalizer.normalize @@ Evaluator.simplify phi)
            in
            let phi =
              if !AlphaDedup.enabled then
                Common.PhaseTime.with_phase "alpha-dedup" (fun () ->
                    AlphaDedup.disjuncts phi)
              else phi
            in
            Common.PhaseTime.with_phase "free-univ" (fun () ->
                elim_free_univ_vars (senv, phi))
          in
          Set.Poly.map ~f:(fun (ps, ns, phi) ->
              (* the elimination of free universals can make two quantified
                 disjuncts renamings of each other again *)
              let phi =
                if !AlphaDedup.enabled then
                  Common.PhaseTime.with_phase "alpha-dedup" (fun () ->
                      AlphaDedup.disjuncts phi)
                else phi
              in
              (* Condensation (see [ClauseOld.condense] for why it is exact):
                 resolution unions the two clauses' premises, so a premise the
                 positive side carried with some arguments projected away --
                 a callee precondition derived from the caller's invariant,
                 say, with the caller's own variables private to it -- lands
                 beside the full premise it is an instance-generalisation of,
                 and only syntactically identical atoms merge in a set.  The
                 copy makes a one-premise clause a two-premise one, which
                 costs the learner its negative examples, and makes a
                 predicate look non-linear to the occurrence counts every
                 elimination rule decides from.  It runs after
                 [elim_free_univ_vars] because before it the linking
                 equalities are still in the pure part and the copy's
                 variables are not yet private; it runs on every resolvent,
                 so a copy on a predicate eliminated later is removed before
                 it is resolved and multiplied. *)
              let ps, ns, phi =
                if Config.condense_resolvents then (
                  let ps', ns', phi' =
                    ClauseOld.condense ~unknowns (ps, ns, phi)
                  in
                  let dropped =
                    Set.length ps + Set.length ns - Set.length ps'
                    - Set.length ns'
                  in
                  if dropped > 0 then
                    Debug.print
                    @@ lazy
                         (sprintf "[condense] %d literal(s) dropped while eliminating %s"
                            dropped (Ident.name_of_pvar pv));
                  (ps', ns', phi'))
                else (ps, ns, phi)
              in
              let ps, ns, phi =
                if Config.condense_pure_resolvents then
                  Common.PhaseTime.with_phase "condense-pure" (fun () ->
                      (* [COAR_CONDENSE_LOG] (instrument only): one stderr line
                         before and one after each condensation, with the
                         resolvent's disjunct and atom counts and pure-part
                         size, and afterwards the seconds, normalisations and
                         search calls spent; the line before is what names a
                         call that does not return.  The result is the same
                         either way. *)
                      let log =
                        Option.is_some (Stdlib.Sys.getenv_opt "COAR_CONDENSE_LOG")
                      in
                      let checks = ref 0 and nodes = ref 0 in
                      let joint_dropped = ref 0 in
                      let t0 = Common.Clock.now_s () in
                      let nd = List.length (Formula.disjuncts_list_of phi) in
                      if log then (
                        (* disjuncts equal to an earlier one once each one's
                           binders are renamed by a counter of its own, and the
                           quantified disjuncts among all *)
                        let ds = Formula.disjuncts_list_of phi in
                        let canon d =
                          let k = ref 0 in
                          Formula.str_of
                            (Formula.aconv_tvar_norm
                               (fun () ->
                                 incr k;
                                 Ident.Tvar (sprintf "#cl%d" !k))
                               d)
                        in
                        let seen = Hash_set.Poly.create () in
                        let dups =
                          List.count ds ~f:(fun d ->
                              let c = canon d in
                              if Hash_set.mem seen c then true
                              else (
                                Hash_set.add seen c;
                                false))
                        in
                        let quant =
                          List.count ds ~f:(fun d ->
                              not (Set.is_empty (Formula.quantified_sort_env_of d)))
                        in
                        (* atoms beyond the first of each predicate, per
                           polarity: copies the atom condensation left *)
                        let extra atoms =
                          Set.length atoms
                          - Set.length
                              (Set.Poly.map atoms ~f:(fun a ->
                                   match a with
                                   | Atom.App (Predicate.Var (p, _), _, _) ->
                                       Some (Ident.name_of_pvar p)
                                   | _ -> None))
                        in
                        eprintf
                          "[condense-pure] start %s disj=%d atoms=%d pure=%d \
                           quantified=%d alpha-dups=%d same-pred-atoms=%d\n%!"
                          (Ident.name_of_pvar pv) nd
                          (Set.length ps + Set.length ns)
                          (Formula.ast_size phi) quant dups
                          (extra ps + extra ns));
                      ClauseOld.condense_profile_reset ();
                      (* [COAR_CONDENSE_REPLAY=P] (instrument only): the first
                         condensation of a resolvent of predicate [P] is
                         first run with [~joint:false] on the same clause and
                         its time, normalisations, search calls and profile
                         printed; the call below then runs as configured.
                         With [COAR_CONDENSE_REPLAY_EXIT] the process exits
                         after that call.  The result is the same either
                         way. *)
                      let replay =
                        match Stdlib.Sys.getenv_opt "COAR_CONDENSE_REPLAY" with
                        | Some p
                          when String.equal p (Ident.name_of_pvar pv)
                               && not !condense_replayed ->
                            condense_replayed := true;
                            true
                        | _ -> false
                      in
                      if replay then (
                        let c0 = ref 0 and n0 = ref 0 in
                        let t = Common.Clock.now_s () in
                        let _, _, phi0 =
                          ClauseOld.condense_pure ~unknowns ~checks_used:c0
                            ~nodes_used:n0
                            ~max_checks:Config.condense_pure_max_checks
                            ~shape_candidates:Config.condense_pure_shape_candidates
                            ~shape_commutative:
                              Config.condense_pure_shape_commutative
                            ~inclusion_candidates:
                              Config.condense_pure_inclusion_candidates
                            ?max_search_nodes:Config.condense_pure_max_search_nodes
                            ~memo_failures:Config.condense_pure_memo_failures
                            ~atom_free:Config.condense_pure_unknown_free_resolvents
                            ~joint:false (ps, ns, phi)
                        in
                        eprintf
                          "[condense-replay] joint=off %s disj=%d->%d secs=%.3f                            checks=%d nodes=%d | %s\n%!"
                          (Ident.name_of_pvar pv) nd
                          (List.length (Formula.disjuncts_list_of phi0))
                          (Common.Clock.now_s () -. t) !c0 !n0
                          (ClauseOld.condense_profile_str ());
                        ClauseOld.condense_profile_reset ());
                      let t0 = if replay then Common.Clock.now_s () else t0 in
                      let ((_, _, phi') as res) =
                      ClauseOld.condense_pure ~unknowns
                        ~checks_used:checks ~nodes_used:nodes
                        ~max_checks:Config.condense_pure_max_checks
                        ~shape_candidates:Config.condense_pure_shape_candidates
                        ~shape_commutative:Config.condense_pure_shape_commutative
                        ~inclusion_candidates:
                          Config.condense_pure_inclusion_candidates
                        ?max_search_nodes:Config.condense_pure_max_search_nodes
                        ~memo_failures:Config.condense_pure_memo_failures
                        ~atom_free:Config.condense_pure_unknown_free_resolvents
                        ~joint:!joint_condense ~joint_dropped
                        ~joint_prune_doomed:!joint_prune_doomed
                        (ps, ns, phi)
                      in
                      if log then
                        eprintf
                          "[condense-pure] done %s disj=%d->%d secs=%.3f checks=%d nodes=%d joint-atoms=%d\n%!"
                          (Ident.name_of_pvar pv) nd
                          (List.length (Formula.disjuncts_list_of phi'))
                          (Common.Clock.now_s () -. t0) !checks !nodes !joint_dropped;
                      if log || replay then
                        eprintf "[condense-profile] %s %s\n%!"
                          (Ident.name_of_pvar pv) (ClauseOld.condense_profile_str ());
                      if replay then (
                        eprintf
                          "[condense-replay] joint=%b %s disj=%d->%d secs=%.3f                            checks=%d nodes=%d joint-atoms=%d\n%!"
                          !joint_condense (Ident.name_of_pvar pv) nd
                          (List.length (Formula.disjuncts_list_of phi'))
                          (Common.Clock.now_s () -. t0) !checks !nodes
                          !joint_dropped;
                        if Option.is_some
                             (Stdlib.Sys.getenv_opt "COAR_CONDENSE_REPLAY_EXIT")
                        then Stdlib.exit 0);
                      res)
                else (ps, ns, phi)
              in
              (* [COAR_JOINT_DUMP=DIR] (instrument only): each resolvent left
                 with two atoms of one predicate and polarity is written to
                 DIR, one literal per line ([+]/[-] atoms, [|] disjuncts), at
                 most [COAR_JOINT_DUMP_MAX] files (default 40).  The result is
                 the same either way. *)
              (match Stdlib.Sys.getenv_opt "COAR_JOINT_DUMP" with
              | None -> ()
              | Some dir ->
                  let maxn =
                    Option.value_map ~default:40 ~f:Int.of_string
                      (Stdlib.Sys.getenv_opt "COAR_JOINT_DUMP_MAX")
                  in
                  let name = function
                    | Atom.App (Predicate.Var (p, _), _, _) ->
                        Some (Ident.name_of_pvar p)
                    | _ -> None
                  in
                  let extra atoms =
                    Set.length atoms - Set.length (Set.Poly.map atoms ~f:name)
                  in
                  if extra ps + extra ns > 0 && !joint_dump_count < maxn then (
                    incr joint_dump_count;
                    let oc =
                      Out_channel.create
                        (sprintf "%s/r%03d_%s.txt" dir !joint_dump_count
                           (Ident.name_of_pvar pv))
                    in
                    Set.iter ps ~f:(fun a ->
                        Out_channel.output_string oc ("+ " ^ Atom.str_of a ^ "\n"));
                    Set.iter ns ~f:(fun a ->
                        Out_channel.output_string oc ("- " ^ Atom.str_of a ^ "\n"));
                    List.iter (Formula.disjuncts_list_of phi) ~f:(fun d ->
                        Out_channel.output_string oc
                          ("| " ^ Formula.str_of d ^ "\n"));
                    Out_channel.close oc));
              (senv, ps, ns, phi))
          @@ (fun phi ->
          Common.PhaseTime.with_phase "cnf" (fun () ->
              Formula.cnf_of exi_senv_old phi))
          @@ expand_bool_eq_of_unknowns exi_senv
          @@ Common.PhaseTime.with_phase "simp2" (fun () ->
              Normalizer.normalize @@ Evaluator.simplify phi))
      @@ Common.PhaseTime.with_phase "build" @@ fun () ->
      Set.Poly.map ~f:(fun (senv, ps, ns, phis) ->
          (senv, ps, ns, Formula.or_of phis))
      @@ Set.Poly.union_list
           [
             Set.cartesian_map clauses_pos_lin clauses_neg_lin
               ~f:(fun (senv1, ps1, ns1, phi1) ncl ->
                 (*print_string "ll:"; Out_channel.flush stdout;*)
                 let ps11, ps12 = Set.partition_tf ps1 ~f:is_resolved in
                 Set.fold ps11 ~init:(senv1, ps12, ns1, [ phi1 ])
                   ~f:(fun (senv, ps, ns, phis) -> function
                   | Atom.App (_, ts1, _) -> (
                       let senv2, ps2, ns2, phi2 = ClauseOld.refresh_tvar ncl in
                       let ns21, ns22 = Set.partition_tf ns2 ~f:is_resolved in
                       match Set.choose ns21 with
                       | Some (Atom.App (_, ts2, _)) ->
                           ( Map.force_merge senv senv2,
                             Set.union ps ps2,
                             Set.union ns ns22,
                             phis
                             @ (phi2 :: List.map2_exn ts1 ts2 ~f:Formula.neq) )
                       | _ -> assert false)
                   | _ -> assert false));
             Set.concat_map clauses_pos_nonlin
               ~f:(fun (senv1, ps1, ns1, phi1) ->
                 let ps11, ps12 = Set.partition_tf ps1 ~f:is_resolved in
                 Set.fold ps11
                   ~init:(Set.Poly.singleton (senv1, ps12, ns1, [ phi1 ]))
                   ~f:(fun acc -> function
                     | Atom.App (_, ts1, _) ->
                         Set.concat_map acc ~f:(fun (senv, ps, ns, phis) ->
                             Set.Poly.map clauses_neg_lin ~f:(fun ncl ->
                                 (*print_string "nl:"; Out_channel.flush stdout;*)
                                 let senv2, ps2, ns2, phi2 =
                                   ClauseOld.refresh_tvar ncl
                                 in
                                 let ns21, ns22 =
                                   Set.partition_tf ns2 ~f:is_resolved
                                 in
                                 match Set.choose ns21 with
                                 | Some (Atom.App (_, ts2, _)) ->
                                     ( Map.force_merge senv senv2,
                                       Set.union ps ps2,
                                       Set.union ns ns22,
                                       phis
                                       @ phi2
                                         :: List.map2_exn ts1 ts2 ~f:Formula.neq
                                     )
                                 | _ -> assert false))
                     | _ -> assert false));
             Set.concat_map clauses_neg_nonlin
               ~f:(fun (senv1, ps1, ns1, phi1) ->
                 let ns11, ns12 = Set.partition_tf ns1 ~f:is_resolved in
                 Set.fold ns11
                   ~init:(Set.Poly.singleton (senv1, ps1, ns12, [ phi1 ]))
                   ~f:(fun acc -> function
                     | Atom.App (_, ts1, _) ->
                         Set.concat_map acc ~f:(fun (senv, ps, ns, phis) ->
                             Set.Poly.map clauses_pos_lin ~f:(fun pcl ->
                                 (*print_string "ln:"; Out_channel.flush stdout;*)
                                 let senv2, ps2, ns2, phi2 =
                                   ClauseOld.refresh_tvar pcl
                                 in
                                 let ps21, ps22 =
                                   Set.partition_tf ps2 ~f:is_resolved
                                 in
                                 match Set.choose ps21 with
                                 | Some (Atom.App (_, ts2, _)) ->
                                     ( Map.force_merge senv senv2,
                                       Set.union ps ps22,
                                       Set.union ns ns2,
                                       phis
                                       @ phi2
                                         :: List.map2_exn ts1 ts2 ~f:Formula.neq
                                     )
                                 | _ -> assert false))
                     | _ -> assert false));
           ]
    in
    let simplify cl =
      incr resolvents_simplified;
      Common.PhaseTime.with_phase "simplify" (fun () ->
          simplify_clause unknowns cl)
    in
    match (clauses_rest, index) with
    | Some clauses_rest, _ ->
        let cls =
          match guard with
          | None ->
              Set.union clauses_rest
              @@ Set.Poly.filter_map ~f:simplify cnf_resolvents
          | Some guard ->
              Set.fold cnf_resolvents ~init:clauses_rest ~f:(fun acc cl ->
                  guard (Set.length acc);
                  match simplify cl with
                  | None -> acc
                  | Some cl ->
                      let acc = Set.add acc cl in
                      guard (Set.length acc);
                      acc)
        in
        if Config.subsume_clauses then subsume ~where:"resolvents" cls else cls
    | None, None -> assert false
    | None, Some index ->
        (* the same resolvents, simplified in the same order, and [?guard]
           told the sizes the set built above would have: the rest (the
           index less the touched clauses) and every resolvent it does not
           already hold *)
        let touched_set = Int.Hash_set.of_list touched in
        let in_rest cl =
          match ResolutionIndex.find_id index cl with
          | Some id -> not (Hash_set.mem touched_set id)
          | None -> false
        in
        let rest_size = ResolutionIndex.length index - List.length touched in
        let resolvents =
          match guard with
          | None -> Set.Poly.filter_map ~f:simplify cnf_resolvents
          | Some guard ->
              Set.fold cnf_resolvents ~init:(Set.Poly.empty, 0)
                ~f:(fun (acc, added) cl ->
                  guard (rest_size + added);
                  match simplify cl with
                  | None -> (acc, added)
                  | Some cl ->
                      let added =
                        if Set.mem acc cl || in_rest cl then added
                        else added + 1
                      in
                      let acc = Set.add acc cl in
                      guard (rest_size + added);
                      (acc, added))
              |> fst
        in
        let cls, dropped =
          Common.PhaseTime.with_phase "subsume" (fun () ->
              ResolutionIndex.step index ~touched ~resolvents)
        in
        if dropped > 0 then
          Debug.print
          @@ lazy
               (sprintf
                  "[elim_pvs] subsumption (resolvents): %d of %d clauses \
                   dropped"
                  dropped (Set.length cls + dropped));
        cls

  let rec elim_one_side_unbounded_pvars exi_senv eliminable_pvs clauses =
    let pvs =
      Set.Poly.filter_map
        (fst @@ ClauseSetOld.count_pvar_apps eliminable_pvs clauses)
        ~f:(fun (pvar, (_dc, pc, nc)) ->
          if (*dc = 0 &&*) pc = 0 (* pvar can be false *) then (
            Debug.print
            @@ lazy
                 (sprintf "%s is assigned false because there is no LB"
                 @@ Ident.name_of_pvar pvar);
            record_reason pvar PCSP.Params.OneSidedNoLB;
            let params =
              mk_fresh_sort_env_list @@ Logic.Sort.args_of
              @@ Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pvar)
            in
            let phi =
              Logic.Term.mk_lambda params @@ Logic.ExtTerm.mk_bool false
            in
            eliminated_pvars :=
              Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pvar)
                ~data:phi;
            Some pvar)
          else if (*dc = 0 &&*) nc = 0 (* pvar can be true *) then (
            Debug.print
            @@ lazy
                 (sprintf "%s is assigned true because there is no UB"
                 @@ Ident.name_of_pvar pvar);
            record_reason pvar PCSP.Params.OneSidedNoUB;
            let params =
              mk_fresh_sort_env_list @@ Logic.Sort.args_of
              @@ Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pvar)
            in
            let phi =
              Logic.Term.mk_lambda params @@ Logic.ExtTerm.mk_bool true
            in
            eliminated_pvars :=
              Map.Poly.add_exn !eliminated_pvars ~key:(Ident.pvar_to_tvar pvar)
                ~data:phi;
            Some pvar)
          else None)
    in
    let clauses' =
      Set.filter clauses ~f:(fun (_, ps, ns, _) ->
          Set.is_empty
          @@ Set.inter pvs (Set.Poly.map (Set.union ps ns) ~f:Atom.pvar_of))
    in
    if Set.eqlen clauses clauses' then clauses'
    else elim_one_side_unbounded_pvars exi_senv eliminable_pvs clauses'

  (* The budget for the two decisions below.  It is not a performance knob: a
     formula Z3 can decide at all it decides quickly here, and the one input the
     rule was derived from was refused at 20 s and again at 30 s, so a larger
     budget bought nothing there.  Small enough to be paid once per candidate
     per elimination round.

     Instrumented under a 5000 ms budget, over 40 calls across four corpora
     the outcome is bimodal with nothing in between: every query that DECIDES
     returns within 31 ms (Valid 19, max 8 ms; Unsat 2, max 8 ms; Sat 13, max
     31 ms) and every query that does not spends the whole budget (Timeout 6,
     5482 ms).  So a budget of seconds buys no answer above 31 ms and costs
     its whole length each time it is not going to:
     `benchmarks/ECHC/bar.smt2` spends ten of twelve seconds on two such calls
     under 5000 ms, and answers sat,0 with no CEGIS round at all.

     500 is the measured maximum times sixteen.  It is not a shape test and
     cannot be: the queries that time out are indistinguishable from the ones
     that decide -- same theory, same sorts, same binder and free-variable
     counts, sizes overlapping (a decided one at 48 characters against a timed
     out one at 85, a decided one at 69 against a timed out one at 94).  That is
     the opposite of the regex case, where a whole theory does not return and
     refusing by sort is right; here a budget is the only instrument, and what
     was wrong with it was its size. *)
  let fn_elim_timeout = 500

  (* An [FN] predicate that no clause puts in a head is replaced by an
     existential in the pure part.

     A solution [P] of kind [FN] and arity n+1 must satisfy
     [forall x_bar. exists! y. P(x_bar, y)]: for every argument tuple exactly
     one result.  Suppose every clause mentioning [P] has the shape

       forall x_bar y z_bar_i.  P(x_bar, y) => psi_i(x_bar, y, z_bar_i)

     for i = 1..k -- [P] only as a premise, exactly once per clause, applied to
     distinct variables, with no unknown anywhere else in the clause.  Then
     those k clauses together are equisatisfiable with the single constraint

       forall x_bar. exists y. AND_i forall z_bar_i. psi_i(x_bar, y, z_bar_i)

     and [P] leaves the signature.  Forward: by *totality* there is a y0 with
     P(x_bar, y0); each clause instantiated there has its premise true, so its
     conclusion holds, and y0 witnesses the new constraint.  Backward: choose a
     witness y at each x_bar and let [P] be the graph of that choice -- total
     and *single-valued* by construction, hence a solution of the kind -- and
     each clause holds because its only instance with the premise true is at the
     chosen y.

     Each side condition pays for one step of that argument:

     - ONE conjunction, not one existential per clause.  The witness is shared
       across the k clauses because [P] has one value at x_bar.  Replacing each
       clause separately by [forall x_bar. exists y. psi_i] would permit a
       different y per clause, which no single [P] need realise: unsound.
     - NO UNKNOWN in psi_i.  Otherwise the introduced [exists y] stands over a
       formula containing unknowns, and a head existential is Skolemised back
       into an FN unknown further down the pipeline -- the rule would delete
       [P] and immediately create its replacement.
     - THE ARGUMENTS ARE DISTINCT VARIABLES, the result included.  With a term
       in an argument, say P(f(z), y), two z with f(z1) = f(z2) may be given
       different witnesses, and the graph of that choice is then not
       single-valued, so it is not a solution of the kind.  Only the backward
       direction fails, so the rule would stay sound for [unsat] and stop being
       an equivalence -- which is why it is a condition and not a caveat.

     THE TRADE THE RULE MAKES, AND WHEN IT IS REFUSED.  What the k clauses cost
     while [P] is in the signature is a CEGIS loop; what the single constraint
     costs is one SMT query, and that query has an existential under a universal
     over arrays, which Z3 frequently does not decide.  An undecided query here
     is worse than a slow loop: a Z3 call is not interruptible by the
     alarm-based timer, so it hangs the process instead of costing an answer.
     The rule therefore asks the question with a budget first and applies itself
     only when the answer comes back -- valid or invalid, either settles the
     constraint -- and otherwise leaves the clauses exactly as they were.

     EVERY OUTCOME OF THIS RULE IS TAGGED [elim_one_sided_fn], deliberately:
     it has three (eliminated, kept because a condition fails, kept because the
     residual query was not decided) and for a while only the middle one carried
     the tag, so grepping for it showed the rule REFUSING and showed nothing at
     all when it fired.  A reader then cannot tell a rule that worked from a
     rule that was never called, which is the failure an acceptance test for it
     is most likely to make.

     No definition is recorded for the eliminated predicate: the backward
     direction *chooses* a witness per argument tuple and that choice need not
     be expressible in any template language.  The predicate is marked as
     accounted for without a definition, exactly as a resolution with a
     disjunctive head is, so that nothing downstream takes it for
     unconstrained. *)
  let elim_one_sided_fn_pvars exi_senv fn_pvs clauses =
    let unknowns = Map.key_set exi_senv in
    Set.fold fn_pvs ~init:clauses ~f:(fun clauses pvar ->
        let mentions (_, ps, ns, phi) =
          Set.exists (Set.union ps ns) ~f:(fun atm ->
              Stdlib.(pvar = Atom.pvar_of atm))
          || Set.mem (Formula.pvs_of phi) pvar
        in
        let cls_with, cls_rest = Set.partition_tf clauses ~f:mentions in
        let sorts =
          match Map.Poly.find exi_senv (Ident.pvar_to_tvar pvar) with
          | None -> []
          | Some s ->
              List.map ~f:Logic.ExtTerm.to_old_sort @@ Logic.Sort.args_of s
        in
        (* the clause, read against the shape above, or [None] with the
           condition it fails named for the trace *)
        let analyze (senv, ps, ns, phi) =
          let reject reason =
            Debug.print
            @@ lazy
                 (sprintf "[elim_one_sided_fn] %s kept: %s"
                    (Ident.name_of_pvar pvar) reason);
            None
          in
          if Fn.non Set.is_empty ps then reject "it occurs in a head"
          else if Set.length ns <> 1 then
            reject "the clause has another unknown in its premises"
          else if
            Fn.non Set.is_empty @@ Set.inter unknowns
            @@ Set.Poly.map ~f:Ident.pvar_to_tvar
            @@ Formula.pvs_of phi
          then reject "an unknown occurs in the clause's pure part"
          else
            let pv, _, ts, _ = Atom.let_pvar_app @@ Set.choose_exn ns in
            if Stdlib.(pv <> pvar) then
              reject "the clause's one premise is a different unknown"
            else
              let xs =
                List.map ts ~f:(function
                  | Term.Var (x, _, _) -> Some x
                  | _ -> None)
              in
              if List.exists xs ~f:Option.is_none then
                reject "an argument is a term rather than a variable"
              else
                let xs = List.filter_opt xs in
                if List.contains_dup xs ~compare:Stdlib.compare then
                  reject "two arguments are the same variable"
                else if List.length xs <> List.length sorts then
                  reject "the application's arity differs from the signature's"
                else
                  let others =
                    Set.diff (Formula.fvs_of phi) (Set.Poly.of_list xs)
                  in
                  if Fn.non (Set.is_subset ~of_:(Map.key_set senv)) others then
                    reject
                      "a variable of the pure part has no sort in the clause"
                  else Some (senv, xs, phi, others)
        in
        if Set.is_empty cls_with || List.is_empty sorts then clauses
        else
          match Option.all @@ List.map ~f:analyze @@ Set.to_list cls_with with
          | None -> clauses
          | Some analyzed -> (
              (* one set of parameters for all k clauses: the witness is shared *)
              let params =
                List.map sorts ~f:(fun s -> (Ident.mk_fresh_tvar (), s))
              in
              let conjuncts =
                List.map analyzed ~f:(fun (senv, xs, phi, others) ->
                    let phi =
                      Formula.subst
                        (Map.Poly.of_alist_exn
                        @@ List.map2_exn xs params ~f:(fun x (v, s) ->
                            (x, Term.mk_var v s)))
                        phi
                    in
                    Formula.mk_forall_if_bounded
                      (List.map (Set.to_list others) ~f:(fun x ->
                           ( x,
                             Logic.ExtTerm.to_old_sort
                             @@ Map.Poly.find_exn senv x )))
                      phi)
              in
              let args, ret =
                (List.drop_last_exn params, List.last_exn params)
              in
              let cl =
                ClauseOld.reduce_sort_map
                  ( Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list args,
                    Set.Poly.empty,
                    Set.Poly.empty,
                    Formula.mk_exists_if_bounded [ ret ]
                    @@ Formula.and_of conjuncts )
              in
              let _, _, _, phi = cl in
              match check_valid_bounded ~timeout:fn_elim_timeout phi with
              | (`Timeout | `Unknown) as res ->
                  Debug.print
                  @@ lazy
                       (sprintf
                          "[elim_one_sided_fn] %s kept: the constraint it \
                           would leave is %s, and a query nothing answers \
                           hangs the process where the loop at least runs: %s"
                          (Ident.name_of_pvar pvar)
                          (match res with
                          | `Timeout -> "not decided within the budget"
                          | _ -> "undecidable for the solver")
                          (ClauseOld.str_of cl));
                  clauses
              | `Valid | `Invalid ->
                  Debug.print
                  @@ lazy
                       (sprintf
                          "[elim_one_sided_fn] %s eliminated: replaced by an \
                           existential over its result (%d clause(s)): %s"
                          (Ident.name_of_pvar pvar) (List.length analyzed)
                          (ClauseOld.str_of cl));
                  record_reason pvar PCSP.Params.FnOneSided;
                  resolved_without_def :=
                    Set.add !resolved_without_def (Ident.pvar_to_tvar pvar);
                  Set.add cls_rest cl))

  (* The same reading of the [FN] kind used as a refutation, for the clause the
     rule above cannot take: one whose premises are SEVERAL functional
     predicates rather than one.

     For a clause  P_1(x_bar_1, y_1) /\ ... /\ P_m(x_bar_m, y_m) => psi  each
     P_j is total, so whatever the universally quantified variables are, there
     are results y_1..y_m making every premise true, and the clause then gives
     psi at those results.  So

       N = forall args. exists y_1..y_m. forall z_bar. psi

     is a CONSEQUENCE of the system, and adding a consequence changes no answer:
     it is satisfied wherever the system is, and cannot rescue a system that is
     not.  A solution must satisfy the clauses in *every* model of the theory,
     so N in turn must hold in every model -- and therefore a model falsifying N
     refutes the system.  That is what makes this worth adding: N mentions no
     unknown, so one query decides it, and an invalid N is [unsat] for the whole
     problem.

     IT IS A CONSEQUENCE AND NOT AN EQUIVALENCE, which is the whole difference
     from the single-premise rule, and why the clauses stay.  The witnesses
     [exists y_1..y_m] may be chosen knowing *all* the universals, where each
     P_j's result may depend only on that P_j's own arguments -- the
     dependency-quantified existential the encoding started from.  So N holding
     says nothing about the system being satisfiable, and replacing the clause
     by it would license a wrong [sat].

     What the forward direction needs is only that the results can be COMPUTED,
     which is much less than the elimination rule asks for.  Each result must be
     a variable of its own, the arguments may be arbitrary terms, and:

     - THE RESULTS MUST BE PAIRWISE DISTINCT.  Two premises sharing one result,
       [P_1(x_bar, y) /\ P_2(z_bar, y) => psi], make the clause an *agreement*
       condition -- it fires only where the two functions happen to agree -- and
       totality says nothing about agreement.  Choosing the two results
       separately gives [exists y_1 y_2. y_1 = y_2 => psi], true by picking
       y_1 <> y_2 and therefore empty.  No consequence is available from such a
       clause by this argument at all.
     - THE USES MUST BE ACYCLIC.  A premise whose argument mentions another
       premise's result is fine -- evaluate that one first -- so what has to be
       excluded is a cycle through such uses: [P_1(y_2, y_1) /\ P_2(y_1, y_2) =>
       false] asks for a fixed point of f_1 . f_2, which need not exist, and N
       would then be false for a system that is satisfiable. *)
  (* Can the results be computed at all?  A premise whose argument is another
     premise's result is not a problem by itself -- evaluate that other one
     first -- so what has to be excluded is a *cycle* through such uses.  With
     one, [P1(y2, y1) /\ P2(y1, y2) => false] asks for a fixed point of
     [f1 . f2], which need not exist, and the consequence built below would be
     false for a system that is satisfiable.  The test is the obvious one:
     repeatedly take the premises all of whose arguments are already available,
     and report whether any are left over. *)
  let cyclic_premises premises =
    let owner =
      Map.Poly.of_alist_exn @@ List.mapi premises ~f:(fun i (_, y) -> (y, i))
    in
    let rec settle known = function
      | [] -> false
      | remaining ->
          let ready, rest =
            List.partition_tf remaining ~f:(fun (_, deps) ->
                List.for_all deps ~f:(Set.mem known))
          in
          if List.is_empty ready then true
          else
            settle
              (Set.union known @@ Set.Poly.of_list @@ List.map ready ~f:fst)
              rest
    in
    settle Set.Poly.empty
    @@ List.mapi premises ~f:(fun i (ts, _) ->
        ( i,
          Set.to_list
          @@ Set.Poly.filter_map ~f:(Map.Poly.find owner)
          @@ Set.Poly.union_list @@ List.map ts ~f:Term.fvs_of ))

  let fn_refutation_consequences exi_senv fn_pvs clauses =
    if Set.is_empty fn_pvs then clauses
    else
      let unknowns = Map.key_set exi_senv in
      Set.fold clauses ~init:clauses ~f:(fun acc ((senv, ps, ns, phi) as cl) ->
          let sort_of x =
            Option.map ~f:Logic.ExtTerm.to_old_sort @@ Map.Poly.find senv x
          in
          (* A premise as (its argument terms, its result variable), or the
             condition it fails -- named, because "some premise does not fit" is
             what one otherwise has to re-derive by hand.

             Only the RESULT has to be a variable, and that is the whole
             difference from the elimination rule above.  This direction uses
             totality alone, so a witness exists for whatever the arguments
             evaluate to and they may be arbitrary terms, repeated ones
             included.  The elimination rule needs distinct variables because
             its backward direction reads the clause's instances back as a
             single-valued graph, which a repeated or compound argument
             destroys; refuting needs nothing of the sort. *)
          let split atm =
            let pv, _, ts, _ = Atom.let_pvar_app atm in
            let name = Ident.name_of_pvar pv in
            if not (Set.mem fn_pvs pv) then
              Error (sprintf "%s is not a functional predicate" name)
            else
              match List.last ts with
              | None ->
                  Error
                    (sprintf "%s takes no arguments, so it has no result" name)
              | Some (Term.Var (y, _, _)) when Option.is_some (sort_of y) ->
                  Ok (List.drop_last_exn ts, y)
              | Some (Term.Var _) ->
                  Error
                    (sprintf "the result of %s has no sort in the clause" name)
              | Some _ ->
                  Error
                    (sprintf "the result of %s is a term rather than a variable"
                       name)
          in
          let reject reason =
            Debug.print
            @@ lazy
                 (sprintf "[fn_consequence] no consequence from %s: %s"
                    (ClauseOld.str_of cl) reason);
            acc
          in
          if Set.is_empty ns then acc
          else if Fn.non Set.is_empty ps then
            reject "an unknown occurs in the head"
          else if
            Fn.non Set.is_empty @@ Set.inter unknowns
            @@ Set.Poly.map ~f:Ident.pvar_to_tvar
            @@ Formula.pvs_of phi
          then reject "an unknown occurs in the pure part"
          else
            match Result.all @@ List.map ~f:split @@ Set.to_list ns with
            | Error reason -> reject reason
            | Ok premises -> (
                let args =
                  Set.to_list @@ Set.Poly.union_list
                  @@ List.concat_map premises ~f:(fst >> List.map ~f:Term.fvs_of)
                in
                let rets = List.map premises ~f:snd in
                let mem xs x = List.mem xs x ~equal:Stdlib.( = ) in
                if List.contains_dup rets ~compare:Stdlib.compare then
                  (* [P1(x_bar, y) /\ P2(z_bar, y) => psi] fires only where the
                     two functions agree, and totality says nothing about
                     agreement.  Choosing the two results separately gives
                     [exists y1 y2. y1 = y2 => psi], which is satisfied by
                     picking y1 <> y2 and so says nothing at all: there is no
                     consequence to be had from such a clause by this argument,
                     and that is a property of the clause rather than a gap
                     here. *)
                  reject
                    "two premises share a result variable, so the clause is an \
                     agreement condition and totality does not reach it"
                else if cyclic_premises premises then
                  reject
                    "the results are mutually recursive, so the witnesses \
                     would need a fixed point that may not exist"
                else
                  let env =
                    List.filter_map ~f:(fun x ->
                        Option.map (sort_of x) ~f:(fun s -> (x, s)))
                  in
                  let zs =
                    Set.to_list
                    @@ Set.diff (Formula.fvs_of phi)
                    @@ Set.Poly.of_list (args @ rets)
                  in
                  let n =
                    Formula.mk_exists_if_bounded (env rets)
                    @@ Formula.mk_forall_if_bounded (env zs) phi
                  in
                  (* a result used as another premise's argument is bound by the
                     existential, not by the universal block around it *)
                  let args =
                    List.dedup_and_sort ~compare:Stdlib.compare
                    @@ List.filter args ~f:(Fn.non (mem rets))
                  in
                  let add what n =
                    Debug.print
                    @@ lazy
                         (sprintf
                            "a model falsifies what the totality of %s forces \
                             on %s -- adding %s as a consequence: %s"
                            (String.concat ~sep:", "
                            @@ List.map ~f:(Atom.pvar_of >> Ident.name_of_pvar)
                            @@ Set.to_list ns)
                            (ClauseOld.str_of cl) what (Formula.str_of n));
                    Set.add acc
                    @@ ClauseOld.reduce_sort_map
                         ( Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list
                           @@ env args,
                           Set.Poly.empty,
                           Set.Poly.empty,
                           n )
                  in
                  let decide ~timeout n =
                    check_valid_bounded ~timeout
                    @@ Formula.mk_forall_if_bounded (env args) n
                  in
                  (* The consequence keeps the clause's own universals inside
                     the existential, and one of them is often a universal
                     FUNCTION -- an array-sorted term variable, which is what a
                     declared universal function is here.  Refuting the
                     consequence then asks the solver to *invent* an array, and
                     it does not: the one this was written for reads
                     [exists i. forall a. a[i] \/ ... \/ exists k. not a[k+1] /\
                     not a[k]], where the witness is any array that is false at
                     [i] and nowhere twice in a row, and Z3 answers neither at
                     20 s nor at 30 s.

                     But a universal may be instantiated at any value, and the
                     instance is implied by it, so an instance of the
                     consequence is a consequence too -- invalidating THAT
                     refutes the system just as well, and it is a formula with
                     one quantified array fewer.  The candidate offered is the
                     point hole [lambda n. n <> v] for each index [v] the clause
                     has in scope: the array that is false exactly where the
                     clause reads it.  On the input above it is the witness, and
                     Z3 decides the instance in well under a second where it
                     does not decide the original at all.  Only Bool-valued
                     arrays get a candidate, because that is the shape the hole
                     has. *)
                  let point_holes =
                    let zenv = env zs in
                    List.concat_map zenv ~f:(fun (z, zsort) ->
                        match zsort with
                        | T_array.SArray (si, se)
                          when Stdlib.(se = T_bool.SBool) ->
                            List.filter_map (rets @ args) ~f:(fun v ->
                                if Stdlib.(sort_of v <> Some si) then None
                                else
                                  let x = Ident.mk_fresh_tvar () in
                                  let hole =
                                    T_array.mk_lambda (x, si) se
                                    @@ T_bool.of_formula
                                    @@ Formula.neq (Term.mk_var x si)
                                         (Term.mk_var v si)
                                  in
                                  Some
                                    ( sprintf "%s := (lambda x. x <> %s)"
                                        (Ident.name_of_tvar z)
                                        (Ident.name_of_tvar v),
                                      Formula.mk_exists_if_bounded (env rets)
                                      @@ Formula.mk_forall_if_bounded
                                           (List.filter zenv
                                              ~f:(fst >> Stdlib.( <> ) z))
                                      @@ Formula.subst
                                           (Map.Poly.singleton z hole)
                                           phi ))
                        | _ -> [])
                  in
                  (* The order of the three attempts below is worth a paragraph,
                     because measuring it moved the two inputs this answers from
                     20.1 s and 10.7 s to 10.1 s and 0.2 s, and a naive order
                     put 122 s into a clause that answers nothing.

                     Only an INVALID answer is acted on, so the question is
                     purely which formulation reaches one soonest.  The
                     un-instantiated query is undecidable here for a reason
                     visible in the formula -- it quantifies over an array --
                     and on the inputs at hand every second of the runtime was
                     its timeout, so the holes go first and it becomes the
                     fallback.  On a clause with no universal array there are no
                     holes and this is exactly the plain query it always was.

                     A short look at the general statement before the holes was
                     tried and removed: an instance of a valid consequence is
                     valid, so a quick VALID would prune the whole hole list --
                     but it costs a second on every clause and on the corpus at
                     hand it never arrived inside one, leaving only the cost. *)
                  (* The consequence above replaces each premise's result by an
                     EXISTENTIAL, and that quietly undoes what the dependency
                     sets are for: one [exists y_1 ... y_m] block lets every
                     witness see every universal, where each P_j's result may
                     see only P_j's own arguments.  Read through the kind's
                     semantics instead there is no need for an existential at
                     all -- a total, single-valued P_j *is* a function, so the
                     clause

                       AND_j P_j(x_bar_j, y_j)  =>  psi

                     says exactly  forall vars. psi[y_j := f_j(x_bar_j)]  with
                     f_j a function of that premise's own arguments and nothing
                     else.  Asking whether that is SATISFIABLE with the f_j as
                     uninterpreted symbols asks whether any choice of the
                     functional predicates works: [Unsat] means none does in any
                     model, which refutes the system, and it is the only answer
                     acted on.  Other clauses constraining the same predicates
                     only make it harder, so ignoring them keeps the direction
                     safe.

                     This is strictly sharper than the existential form -- it is
                     the difference between a problem and its linearisation, and
                     on the inputs at hand the linearisation is satisfiable while
                     the problem is not -- so it is tried first. *)
                  (* each premise read as the function its kind says it is *)
                  let witness_of =
                    List.map premises ~f:(fun (ts, y) ->
                        ( y,
                          Term.mk_fvar_app
                            (Ident.mk_fresh_tvar ~prefix:(Some "#fn_") ())
                            (List.map ts ~f:Term.sort_of)
                            (Option.value_exn (sort_of y))
                            ts ))
                  in
                  let psi_fun =
                    Formula.subst (Map.Poly.of_alist_exn witness_of) phi
                  in
                  let uni = env (args @ zs) in
                  let as_functions = Formula.mk_forall_if_bounded uni psi_fun in
                  (* THE EXPANSION.  The formula above is the right question and
                     no solver answers it, because it quantifies over arrays --
                     the universal functions.  A universal may be instantiated at
                     anything and the instance is implied, so a CONJUNCTION of
                     instances is implied too, and refuting that refutes the
                     system with no array quantifier left to decide.

                     Which instances.  The refutation of the input this was
                     derived from needs exactly two arrays: the constant one,
                     which pins the value both witnesses must agree on, and the
                     hole that is false at precisely that value, which then
                     falsifies the specification there.  The second is the
                     interesting one, because the value is
                     [f_j(x_bar_j)] -- an application of one of the WITNESS
                     functions -- so a family built from the variables in scope
                     cannot express it and one built from the witnesses can.
                     That is the Ackermann-style step: name the witness at a
                     canonical point, then make a hole at that name.

                     So, per Bool-valued array universal: the two constant
                     arrays, and a hole [lambda n. n <> t] for each index term
                     [t] of the right sort -- the universals in scope, and each
                     witness applied to its own arguments with the array ones
                     pinned to the constant array.  Everything else stays
                     universally quantified, which is stronger than guessing a
                     value for it and costs nothing. *)
                  let expansion =
                    let is_bool_array = function
                      | T_array.SArray (_, se) -> Stdlib.(se = T_bool.SBool)
                      | _ -> false
                    in
                    let arrays = List.filter uni ~f:(snd >> is_bool_array) in
                    let const_true si =
                      T_array.mk_const_array si T_bool.SBool
                      @@ T_bool.of_formula @@ Formula.mk_true ()
                    in
                    let index_terms si =
                      List.filter_map uni ~f:(fun (x, s) ->
                          if Stdlib.(s = si) then Some (Term.mk_var x s)
                          else None)
                      @ List.filter_map witness_of ~f:(fun (y, t) ->
                          if Stdlib.(sort_of y <> Some si) then None
                          else
                            match t with
                            | Term.FunApp (FVar (f, sargs, sret), ts, _) ->
                                Some
                                  (Term.mk_fvar_app f sargs sret
                                  @@ List.map ts ~f:(fun a ->
                                      match Term.sort_of a with
                                      | T_array.SArray (s1, se)
                                        when Stdlib.(se = T_bool.SBool) ->
                                          const_true s1
                                      | _ -> a))
                            | _ -> None)
                      |> List.dedup_and_sort ~compare:Stdlib.compare
                    in
                    let candidates (_, s) =
                      match s with
                      | T_array.SArray (si, _) ->
                          const_true si
                          :: T_array.mk_const_array si T_bool.SBool
                               (T_bool.of_formula @@ Formula.mk_false ())
                          :: List.map (index_terms si) ~f:(fun t ->
                              let x = Ident.mk_fresh_tvar () in
                              T_array.mk_lambda (x, si) T_bool.SBool
                              @@ T_bool.of_formula
                              @@ Formula.neq (Term.mk_var x si) t)
                          |> fun cs -> List.take cs 5
                      | _ -> []
                    in
                    (* NOT the cartesian product.  On the input this was derived
                       from that is five candidates over four array universals,
                       625 instances, where the hand refutation uses TWO.  What
                       it uses is a pattern: every array at the constant, then
                       one candidate pushed into all of them, or into one of them
                       with the rest at the constant.  Generating that is linear
                       in candidates times universals instead of exponential, and
                       it contains the two the hand proof needs. *)
                    let assignments arrays =
                      let base =
                        Map.Poly.of_alist_exn
                        @@ List.filter_map arrays ~f:(fun (x, s) ->
                            match s with
                            | T_array.SArray (si, _) -> Some (x, const_true si)
                            | _ -> None)
                      in
                      let cands =
                        (* once per SORT, not once per variable: every call mints
                           a fresh binder for the hole, so the same candidate
                           built for two same-sorted universals is two terms that
                           no comparison identifies, and the count multiplies for
                           nothing *)
                        List.concat_map
                          (List.dedup_and_sort ~compare:Stdlib.compare
                          @@ List.map arrays ~f:snd)
                          ~f:(fun s -> candidates (Ident.Tvar "", s))
                      in
                      (* which universals take the candidate: none, any one,
                         any TWO, or all.  Pairs are not decoration -- the
                         three-party agreement input needs exactly one instance
                         with two of its three predicates at the hole and the
                         third at the constant, and with singletons and the full
                         set alone its query is undecided where with that one
                         instance added it is refuted.  Subsets beyond pairs are
                         not generated: the proofs at hand use one, two or all,
                         and 2^n grows faster than anything checks. *)
                      let at c xs =
                        List.fold xs ~init:base ~f:(fun m x ->
                            Map.Poly.set m ~key:x ~data:c)
                      in
                      base
                      :: List.concat_map cands ~f:(fun c ->
                          let fits (_, s) = Stdlib.(Term.sort_of c = s) in
                          let xs =
                            List.map ~f:fst @@ List.filter arrays ~f:fits
                          in
                          (at c xs :: List.map xs ~f:(fun x -> at c [ x ]))
                          @ List.concat_mapi xs ~f:(fun k x ->
                              List.map
                                (List.drop xs (k + 1))
                                ~f:(fun y -> at c [ x; y ])))
                    in
                    (* The two bounds below were eight and 160, which were the
                       shape at hand rather than a measurement: a four-party
                       agreement problem has nine universally quantified arrays
                       in its one clause and needs 185 instances, so it missed
                       both by a little, the expansion was refused outright, and
                       the plain query it fell back to is undecided.  Raised and
                       measured over 132 dependency-quantified files: no verdict
                       disagreement, one file differing at the budget's edge
                       whose two runs differ under a FIXED binary as well, and
                       the aggregate wall clock 0.88 of what it was, because a
                       problem refuted in preprocessing stops costing a whole
                       budget in the loop.  They are still bounds and not a
                       licence: the assignments grow with the square of the
                       arrays, so something has to refuse, and what a bigger
                       shape needs is a better pattern rather than a bigger
                       cap. *)
                    if List.is_empty arrays || List.length arrays > 16 then None
                    else
                      let asgs =
                        List.dedup_and_sort ~compare:Stdlib.compare
                        @@ assignments arrays
                      in
                      if List.length asgs > 512 then None
                      else
                        (* A sort the problem QUANTIFIES OVER -- a
                           declare-forall-sort -- ranges over every non-empty
                           type, so assuming it has at most n elements is an
                           instance of that quantifier and therefore a
                           weakening: a refutation under the assumption refutes
                           the system.  It is worth assuming because a proof by
                           pigeonhole over the interpretations of a predicate on
                           such a sort is infinite until the sort is finite, and
                           finite it is a formula.  Four is the bound because
                           that is what the input this was measured on needs --
                           two and three elements leave too little room to pick
                           the two points a pigeonhole differs at.  Conjoined
                           rather than substituted, so nothing else changes. *)
                        let card_bound =
                          List.map
                            (List.dedup_and_sort ~compare:Stdlib.compare
                            @@ List.concat_map uni
                                 ~f:(snd >> Term.svs_of_sort >> Set.to_list))
                            ~f:(fun sv ->
                              let so = Sort.SVar sv in
                              let x = Ident.mk_fresh_tvar () in
                              Formula.mk_forall [ (x, so) ]
                              @@ Formula.or_of
                              @@ List.init 4 ~f:(fun _ ->
                                  Formula.eq (Term.mk_var x so)
                                  @@ Term.mk_var (Ident.mk_fresh_tvar ()) so))
                        in
                        Some
                          ( List.length asgs,
                            Formula.and_of @@ card_bound
                            @ [
                                Formula.mk_forall_if_bounded
                                  (List.filter uni
                                     ~f:(Fn.non (snd >> is_bool_array)))
                                @@ Formula.and_of
                                @@ List.map asgs ~f:(fun m ->
                                    Formula.subst m psi_fun);
                              ] )
                  in
                  let rec try_holes = function
                    | (what, n) :: rest -> (
                        match decide ~timeout:fn_elim_timeout n with
                        | `Invalid -> add what n
                        | _ -> try_holes rest)
                    | [] -> (
                        match decide ~timeout:fn_elim_timeout n with
                        | `Valid ->
                            reject
                              "it holds in every model -- totality alone does \
                               not refute this clause"
                        | `Invalid -> add "it" n
                        | `Timeout ->
                            reject
                              "undecided within the budget, and no point hole \
                               for a universal array decided it either"
                        | `Unknown ->
                            reject
                              "undecidable for the solver, and no point hole \
                               for a universal array decided it either")
                  in
                  match
                    match expansion with
                    | Some (k, e) -> (
                        let r = check_sat_bounded ~timeout:fn_elim_timeout e in
                        Debug.print
                        @@ lazy
                             (sprintf
                                "%d instantiations of the functional reading: \
                                 %s"
                                k
                                (match r with
                                | `Unsat -> "REFUTED"
                                | `Sat -> "sat, which says nothing"
                                | `Timeout -> "nothing within the budget"
                                | _ -> "unknown"));
                        match r with
                        | `Unsat -> `Unsat
                        | _ ->
                            check_sat_bounded ~timeout:fn_elim_timeout
                              as_functions)
                    | None ->
                        check_sat_bounded ~timeout:fn_elim_timeout as_functions
                  with
                  | `Unsat ->
                      Debug.print
                      @@ lazy
                           (sprintf
                              "no choice of %s satisfies %s, reading each as \
                               the function its kind says it is -- the system \
                               is refuted: %s"
                              (String.concat ~sep:", "
                              @@ List.map ~f:(Atom.pvar_of >> Ident.name_of_pvar)
                              @@ Set.to_list ns)
                              (ClauseOld.str_of cl)
                              (Formula.str_of as_functions));
                      Set.add acc
                      @@ ClauseOld.reduce_sort_map
                           ( Map.Poly.empty,
                             Set.Poly.empty,
                             Set.Poly.empty,
                             Formula.mk_false () )
                  | res ->
                      Debug.print
                      @@ lazy
                           (sprintf
                              "reading %s as the functions their kind says \
                               they are leaves a formula the solver answers %s \
                               on, so it refutes nothing here: %s"
                              (String.concat ~sep:", "
                              @@ List.map ~f:(Atom.pvar_of >> Ident.name_of_pvar)
                              @@ Set.to_list ns)
                              (match res with
                              | `Sat -> "sat, which says nothing"
                              | `Timeout -> "nothing within the budget"
                              | _ -> "unknown")
                              (Formula.str_of as_functions));
                      try_holes point_holes))

  (* [?normalise], when given, is applied to each clause the substitution
     changed before it is simplified; it must return clauses whose conjunction
     is equivalent to its argument (the assign-before-normal-form lever passes
     the normalisation a resolvent gets). *)
  let subst_preds ?normalise unknowns psub cls =
    let cls1, cls2 =
      Set.partition_map cls ~f:(fun cl ->
          let cl, changed = ClauseOld.subst_preds psub cl in
          if changed then Second cl else First cl)
    in
    let cls2 =
      match normalise with None -> cls2 | Some f -> Set.concat_map cls2 ~f
    in
    (cls1, Set.Poly.filter_map cls2 ~f:(simplify_clause unknowns))

  let lbs_ubs_of exi_senv clauses =
    (* the predicate names, as a set: a constant of this call, where it used to
       be rebuilt for each clause reaching one of the two filters below *)
    let unknowns = Map.key_set exi_senv in
    Tuple2.map_both
      ~f1:(Set.Poly.filter_map ~f:Fn.id)
      ~f2:(Set.Poly.filter_map ~f:Fn.id)
    @@ Set.unzip
    @@ Set.Poly.map clauses ~f:(fun (_, ps, ns, phi) ->
        if false then
          Debug.print @@ lazy (sprintf "[lbs_ubs_of] %s" @@ Formula.str_of phi);
        (* assume that [phi] is alpha-renamed *)
        let lenv = Set.of_map @@ Formula.let_sort_env_of phi in
        (* let lenv = Set.Poly.empty in *)
        if Set.is_singleton ps && Set.is_empty ns then
          match Set.choose ps with
          | Some (Atom.App (Predicate.Var (pvar, sorts), ts, _)) ->
              let xs = mk_fresh_sort_env_list sorts in
              let phi' =
                Formula.or_of
                @@ (phi :: List.map2_exn ~f:Formula.neq ts (Term.of_sort_env xs))
              in
              let ys =
                Set.diff
                  (Set.diff (Formula.sort_env_of phi') (Set.Poly.of_list xs))
                  lenv
                |> Set.filter ~f:(fst >> Set.mem unknowns >> not)
              in
              let senv =
                Map.of_set_exn @@ Logic.of_old_sort_env_set
                @@ Set.union (Set.Poly.of_list xs) ys
              in
              if false then
                Debug.print
                @@ lazy
                     (sprintf "[lbs_ubs_of] senv: %s"
                     @@ Logic.(
                          str_of_sort_env_list ExtTerm.str_of_sort
                          @@ Map.Poly.to_alist senv));
              (* (exists ys. not phi /\ xs = ts) => pvar(xs) *)
              let lb =
                Formula.exists (Set.to_list ys)
                @@ Formula.elim_let_equi false
                @@ Normalizer.normalize_let ~rename:true
                @@ Formula.mk_neg @@ snd
                @@ Qelim.elim_free_univ_vars_old
                     (Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list xs)
                     exi_senv (senv, phi')
              in
              Debug.print
              @@ lazy
                   (sprintf "LB of %s(%s): %s" (Ident.name_of_pvar pvar)
                      (str_of_sort_env_list LogicOld.Term.str_of_sort xs)
                      (Formula.str_of lb));
              (Some (pvar, (xs, lb)), None)
          | _ -> assert false
        else if Set.is_empty ps && Set.is_singleton ns then
          match Set.choose ns with
          | Some (Atom.App (Predicate.Var (pvar, sorts), ts, _)) ->
              let xs = mk_fresh_sort_env_list sorts in
              let phi' =
                Formula.or_of
                @@ (phi :: List.map2_exn ~f:Formula.neq ts (Term.of_sort_env xs))
              in
              let ys =
                Set.diff
                  (Set.diff (Formula.sort_env_of phi') (Set.Poly.of_list xs))
                  lenv
                |> Set.filter ~f:(fst >> Set.mem unknowns >> not)
              in
              let senv =
                Map.of_set_exn @@ Logic.of_old_sort_env_set
                @@ Set.union (Set.Poly.of_list xs) ys
              in
              if false then
                Debug.print
                @@ lazy
                     (sprintf "[lbs_ubs_of] senv: %s"
                     @@ Logic.(
                          str_of_sort_env_list ExtTerm.str_of_sort
                          @@ Map.Poly.to_alist senv));
              (* pvar(xs) => (forall ys. xs = ts => phi) *)
              let ub =
                Formula.forall (Set.to_list ys)
                @@ Formula.elim_let_equi true
                @@ Normalizer.normalize_let ~rename:true
                @@ snd
                @@ Qelim.elim_free_univ_vars_old
                     (Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list xs)
                     exi_senv (senv, phi')
              in
              Debug.print
              @@ lazy
                   (sprintf "UB of %s(%s): %s" (Ident.name_of_pvar pvar)
                      (str_of_sort_env_list LogicOld.Term.str_of_sort xs)
                      (Formula.str_of ub));
              (None, Some (pvar, (xs, ub)))
          | _ -> assert false
        else (None, None))

  let clause_of_lb pvar (senv, phi) =
    ( Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list senv,
      Set.Poly.singleton @@ Atom.pvar_app_of_senv pvar senv,
      Set.Poly.empty,
      Formula.mk_neg phi )

  let clause_of_ub pvar (senv, phi) =
    ( Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list senv,
      Set.Poly.empty,
      Set.Poly.singleton @@ Atom.pvar_app_of_senv pvar senv,
      phi )

  let or_preds params preds =
    Formula.or_of @@ Set.to_list
    @@ Set.Poly.map preds ~f:(fun (params', phi) ->
        Formula.rename (ren_of_sort_env_list params' params) phi)

  let and_preds params preds =
    Formula.and_of @@ Set.to_list
    @@ Set.Poly.map preds ~f:(fun (params', phi) ->
        Formula.rename (ren_of_sort_env_list params' params) phi)

  let elim_pvars_with_lb_ub ?normalise exi_senv eliminable_pvs clauses =
    let cls = ref Set.Poly.empty in
    (* the predicate names, as a set: a constant of this call, where it used to
       be rebuilt twice for every candidate predicate *)
    let unknowns = Map.key_set exi_senv in
    (* Group the bounds by the predicate they bound, in one pass.  Asking
       instead, for each candidate, which of *all* the bounds are its own costs
       a factor of the number of candidates. *)
    let group_by_pvar bounds =
      let tbl = Hashtbl.Poly.create () in
      Set.iter bounds ~f:(fun (pvar, bound) ->
          Hashtbl.update tbl pvar ~f:(function
            | None -> Set.Poly.singleton bound
            | Some s -> Set.add s bound));
      fun pvar -> Option.value ~default:Set.Poly.empty @@ Hashtbl.find tbl pvar
    in
    let psub =
      let lbs, ubs = lbs_ubs_of exi_senv clauses in
      let lbs_of = group_by_pvar lbs and ubs_of = group_by_pvar ubs in
      Map.of_set_exn
      @@ Set.Poly.filter_map eliminable_pvs ~f:(fun pvar ->
          let pvar_lbs = lbs_of pvar in
          let pvar_ubs = ubs_of pvar in
          let pvar_lbs_ubs = Set.union pvar_lbs pvar_ubs in
          if Set.is_empty pvar_lbs_ubs then None
          else
            let params, _ = Set.choose_exn pvar_lbs_ubs in
            let lb = or_preds params pvar_lbs in
            let ok_lb =
              LogicOld.Formula.is_quantifier_free lb
              && Set.(is_empty @@ inter (Formula.fvs_of lb) unknowns)
            in
            let ub = and_preds params pvar_ubs in
            let ok_ub =
              LogicOld.Formula.is_quantifier_free ub
              && Set.(is_empty @@ inter (Formula.fvs_of ub) unknowns)
            in
            if
              ok_lb
              && Z3Smt.Z3interface.is_valid ~id:!id (LogicOld.get_fenv ()) lb
            then (
              Debug.print
              @@ lazy
                   (sprintf "%s is assigned true because LB is true"
                   @@ Ident.name_of_pvar pvar);
              record_reason pvar PCSP.Params.LbValid;
              let phi =
                Logic.(
                  Term.mk_lambda (of_old_sort_env_list params)
                  @@ ExtTerm.mk_bool true)
              in
              eliminated_pvars :=
                Map.Poly.add_exn !eliminated_pvars
                  ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
              Some
                (pvar, (params, Formula.mk_true (), Formula.mk_false (), false)))
            else if
              ok_ub
              && Z3Smt.Z3interface.is_valid ~id:!id (LogicOld.get_fenv ())
                 @@ Formula.mk_neg ub
            then (
              Debug.print
              @@ lazy
                   (sprintf "%s is assigned false because UB is false"
                   @@ Ident.name_of_pvar pvar);
              record_reason pvar PCSP.Params.UbUnsat;
              let phi =
                Logic.(
                  Term.mk_lambda (of_old_sort_env_list params)
                  @@ ExtTerm.mk_bool false)
              in
              eliminated_pvars :=
                Map.Poly.add_exn !eliminated_pvars
                  ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
              Some
                (pvar, (params, Formula.mk_false (), Formula.mk_true (), false)))
            else if
              Set.exists pvar_lbs ~f:(snd >> Formula.is_exists)
              || Set.exists pvar_ubs ~f:(snd >> Formula.is_forall)
            then None
            else if
              ok_lb && ok_ub
              && Z3Smt.Z3interface.is_valid ~id:!id (LogicOld.get_fenv ())
                 @@ Formula.mk_iff lb ub
            then (
              Debug.print
              @@ lazy
                   (sprintf "%s is assigned %s because LB and UB are equivalent"
                      (Ident.name_of_pvar pvar)
                   @@ Formula.str_of lb);
              record_reason pvar PCSP.Params.Forced;
              let phi =
                Logic.(
                  Term.mk_lambda (of_old_sort_env_list params)
                  @@ ExtTerm.of_old_formula lb (*ToDo: ub is ignored*))
              in
              eliminated_pvars :=
                Map.Poly.add_exn !eliminated_pvars
                  ~key:(Ident.pvar_to_tvar pvar) ~data:phi;
              Some (pvar, (params, lb, Formula.mk_neg ub, false)))
            else if Config.propagate_lb_ub then (
              Debug.print
              @@ lazy
                   (sprintf "LB and UB of %s are propagated"
                   @@ Ident.name_of_pvar pvar);
              (*ToDo: this may widen the solution space?*)
              cls :=
                Set.Poly.union_list
                  [
                    Set.Poly.map ~f:(clause_of_lb pvar) pvar_lbs;
                    Set.Poly.map ~f:(clause_of_ub pvar) pvar_ubs;
                    !cls;
                  ];
              Some (pvar, (params, lb, Formula.mk_neg ub, true)))
            else None)
    in
    let cls1, cls2 =
      subst_preds ?normalise (Map.key_set exi_senv) psub clauses
    in
    Set.Poly.union_list [ !cls; cls1; cls2 ]

  (* whether any unknown is still applied in a clause, its pure part
     included *)
  let mentions_unknown clauses =
    Set.exists clauses ~f:(fun (_, ps, ns, phi) ->
        (not (Set.is_empty ps))
        || (not (Set.is_empty ns))
        || not (Set.is_empty (Formula.pvs_of phi)))

  (* whether every unknown the clauses apply is one resolution may remove, so
     that a complete elimination can succeed at all: an unknown of another
     kind, or one applied inside a pure part, would survive it *)
  let only_eliminable_unknowns eliminable_pvs clauses =
    Set.for_all clauses ~f:(fun (_, ps, ns, phi) ->
        Set.is_empty (Formula.pvs_of phi)
        && Set.for_all (Set.union ps ns) ~f:(fun atm ->
            Set.for_all (Atom.pvs_of atm) ~f:(Set.mem eliminable_pvs)))

  (* A trace of the term size each resolution step leaves behind, off unless
     the environment variable COAR_ELIM_GROWTH is set.  The growth test
     below reads occurrence counts only, so with [pc = 1] or [nc = 1] no
     clause is duplicated and yet every resolvent receives a copy of the
     eliminated clauses' pure parts; this prints, per step, the predicate,
     its counts, the clause count, the total and largest clause size and the
     total pure-part size before and after, the summed size of the clauses
     the predicate occurs in on each side, and a structural prediction of the
     resolvents' size made without substituting: every positive clause is
     paired with every negative one, so the prediction is
     [nc * size(pos side) + pc * size(neg side)].  One line per step on
     stderr, prefixed [elim-growth]; sizes are [Formula.ast_size] and
     [Atom.ast_size], one linear walk per clause. *)
  (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
  let elim_growth_trace =
    Lazy.from_val (Option.is_some (Stdlib.Sys.getenv_opt "COAR_ELIM_GROWTH"))

  let clause_sizes (_, pos, neg, phi) =
    let atoms =
      Set.fold (Set.union pos neg) ~init:0 ~f:(fun acc a -> acc + Atom.ast_size a)
    in
    let pure = Formula.ast_size phi in
    (atoms + pure, pure)

  let clause_set_stats clauses =
    Set.fold clauses ~init:(0, 0, 0, 0) ~f:(fun (n, tot, mx, pure) cl ->
        let sz, p = clause_sizes cl in
        (n + 1, tot + sz, Int.max mx sz, pure + p))

  let print_elim_growth ~complete ~atom_pvs pv pc nc before after secs =
    let n0, t0, m0, p0 = clause_set_stats before in
    let n1, t1, m1, p1 = clause_set_stats after in
    let side f =
      Set.fold before ~init:0 ~f:(fun acc ((_, pos, neg, _) as cl) ->
          if Set.exists (f pos neg) ~f:(fun a -> Set.mem (atom_pvs a) pv) then
            acc + fst (clause_sizes cl)
          else acc)
    in
    let spos = side (fun pos _ -> pos) and sneg = side (fun _ neg -> neg) in
    Stdlib.Printf.eprintf
      "[elim-growth] %s pvar=%s pc=%d nc=%d clauses=%d->%d size=%d->%d        max=%d->%d pure=%d->%d spos=%d sneg=%d predicted=%d secs=%.3f\n%!"
      (if complete then "complete" else "threshold")
      (Ident.name_of_pvar pv) pc nc n0 n1 t0 t1 m0 m1 p0 p1 spos sneg
      ((nc * spos) + (pc * sneg))
      secs

  (* [threshold] bounds the growth one elimination may cause, and
     [max_clauses] the size of the clause set after each one; both are
     changed only by the complete elimination below, which calls this
     function again with the threshold lifted. *)
  let rec elim_pvars_by_resolution ?(threshold = Config.resolution_threshold)
      ?max_clauses ?deadline ?atom_pvs ?index ?clause_size elim_free_univ_vars
      exi_senv eliminable_pvs clauses =
    (* [resolution_max_growth]'s clause sizes, kept along the chain *)
    let clause_size =
      match (clause_size, Atomic.get resolution_max_growth) with
      | Some _, _ -> clause_size
      | None, Some _ -> Some (GrowthGuard.clause_size ())
      | None, None -> None
    in
    (* [Atom.pvs_of], remembered by physical identity across the rounds of
       one elimination when [resolution_atom_pvs_memo] is set: the clauses a
       step leaves alone are the same values in the next round, and the
       predicate variables of an atom walk all its argument terms *)
    let atom_pvs =
      match atom_pvs with
      | Some f -> f
      | None ->
          if Atomic.get resolution_atom_pvs_memo then (
            let tbl = ClauseOld.PhysAtom.create 1024 in
            fun atm ->
              match ClauseOld.PhysAtom.find_opt tbl atm with
              | Some s -> s
              | None ->
                  let s = Atom.pvs_of atm in
                  ClauseOld.PhysAtom.add tbl atm s;
                  s)
          else Atom.pvs_of
    in
    (* [preprocessor.elim_resolution_index]: built once from the clauses a
       chain starts with, then passed along the chain and kept describing its
       clause set; only with subsumption on, which is what makes a step's
       result computable from the clauses it touches *)
    let index =
      match index with
      | Some _ -> index
      | None ->
          if Atomic.get resolution_index && Config.subsume_clauses then
            Some
              (Common.PhaseTime.with_phase "index" (fun () ->
                   ResolutionIndex.create ~atom_pvs clauses))
          else None
    in
    (match max_clauses with
    | Some m when Set.length clauses > m ->
        raise (Complete_resolution_abandoned `Built)
    | _ -> ());
    check_complete_deadline deadline;
    let count_tok = Common.PhaseTime.start "choose" in
    let pvs, dc_pvs =
      match index with
      | Some index -> ResolutionIndex.count_pvar_apps index eliminable_pvs
      | None -> ClauseSetOld.count_pvar_apps eliminable_pvs clauses
    in
    (* Which clauses mention which predicate, built once for this round.  The
       safety test below reads only the clauses the candidate occurs in -- a
       clause without it leaves the accumulator untouched, and the [p || n]
       guard there is a short-circuit that cannot change the conjunctions'
       value -- so folding the whole clause set once per candidate costs a
       factor of the number of candidates for nothing, and the caller asks the
       question again after every single elimination. *)
    let clauses_of_pvar =
      match index with
      | Some index ->
          fun pvar -> List.map (ResolutionIndex.clauses_of index pvar) ~f:snd
      | None ->
          let tbl = Hashtbl.Poly.create () in
          Set.iter clauses ~f:(fun ((_, pos, neg, _) as cl) ->
              Set.iter
                (Set.concat_map (Set.union pos neg) ~f:atom_pvs)
                ~f:(fun pvar ->
                  Hashtbl.update tbl pvar ~f:(function
                    | None -> [ cl ]
                    | Some cls -> cl :: cls)));
          fun pvar -> Option.value ~default:[] @@ Hashtbl.find tbl pvar
    in
    let candidates =
      Set.Poly.filter_map pvs ~f:(fun (pvar, (dc, pc, nc)) ->
          if dc = 0 && not (Set.mem dc_pvs pvar) then
            let pn = pc * nc in
            (* bounded variable elimination: resolving away [pvar] replaces
               [pc + nc] clauses by [pc * nc]; allow it when the net growth is
               within the threshold (in particular always when [pc = 1] or
               [nc = 1], where no clause is duplicated) *)
            if pn - (pc + nc) <= threshold then
              Some
                ( pvar,
                  List.length @@ Logic.Sort.args_of
                  @@ Map.Poly.find_exn exi_senv (Ident.pvar_to_tvar pvar),
                  (pc, nc, pn) )
            else None
          else None)
    in
    (* [resolution_max_growth]: a candidate whose resolution is predicted to
       grow the clause set by more than the bound is not one; it stays a
       predicate of the problem.  Decided from the sizes of the clauses it
       occurs in, before anything is resolved. *)
    let candidates =
      match (Atomic.get resolution_max_growth, clause_size) with
      | Some bound, Some size ->
          Set.filter candidates ~f:(fun (pvar, _, (pc, nc, _)) ->
              let spos, sneg =
                List.fold (clauses_of_pvar pvar) ~init:(0, 0)
                  ~f:(fun (sp, sn) ((_, pos, neg, _) as cl) ->
                    let mem side =
                      Set.exists side ~f:(fun a -> Set.mem (atom_pvs a) pvar)
                    in
                    let p = mem pos and n = mem neg in
                    if p || n then
                      let sz = size cl in
                      ((if p then sp + sz else sp), if n then sn + sz else sn)
                    else (sp, sn))
              in
              let growth = GrowthGuard.predicted_growth ~pc ~nc ~spos ~sneg in
              if growth <= bound then true
              else (
                Atomic.incr growth_refusals;
                if Lazy.force elim_growth_trace then
                  Stdlib.Printf.eprintf
                    "[elim-growth] kept pvar=%s pc=%d nc=%d spos=%d sneg=%d \
                     growth=%d bound=%d\n\
                     %!"
                    (Ident.name_of_pvar pvar) pc nc spos sneg growth bound;
                Debug.print
                @@ lazy
                     (sprintf
                        "[elim_pvs] %s kept: resolving it is predicted to \
                         grow the clauses by %d nodes (pc %d, nc %d, %d and \
                         %d nodes on each side), past %d"
                        (Ident.name_of_pvar pvar) growth pc nc spos sneg bound);
                false))
      | _ -> candidates
    in
    (* Whether resolving a candidate away is safe.  Only the clauses it occurs
       in can say: a clause without it leaves the accumulator untouched, and
       the [p || n] guard is a short-circuit that decides how much work is done
       rather than what comes out. *)
    let is_safe (pvar, _, (_, _, _)) =
      List.fold (clauses_of_pvar pvar) ~init:(true, true)
        ~f:(fun (p, n) (senv, pos, neg, _phi) ->
          if p || n then
            match Set.find pos ~f:(atom_pvs >> Fn.flip Set.mem pvar) with
            | Some atm ->
                ( p
                  && Set.is_subset ~of_:(Atom.tvs_of atm)
                       (ClauseOld.tvs_of
                          ( senv,
                            Set.remove pos atm,
                            neg,
                            Formula.mk_true () (*phi*) )),
                  n )
            | None -> (
                match Set.find neg ~f:(atom_pvs >> Fn.flip Set.mem pvar) with
                | Some atm ->
                    ( p,
                      n
                      && Set.is_subset ~of_:(Atom.tvs_of atm)
                           (ClauseOld.tvs_of
                              ( senv,
                                pos,
                                Set.remove neg atm,
                                Formula.mk_true () (*phi*) )) )
                | None -> (p, n))
          else (p, n))
      |> Tuple2.uncurry ( || )
    in
    (* Sort every candidate first and look for a safe one in that order, rather
       than testing all of them to split the list in two.  The sort is stable,
       so filtering the sorted list is the same as sorting the filtered one:
       the first safe candidate is exactly the one the safe group would have
       yielded, and when none is safe the head of the whole list is the one the
       unsafe group would have yielded.  The difference is that safety -- which
       walks each of the candidate's clauses -- is asked about the candidates
       up to the first safe one instead of about all of them. *)
    let sorted =
      candidates |> Set.to_list
      |> List.sort
           ~compare:(fun
               (_, arity1, (pc1, nc1, pn1)) (_, arity2, (pc2, nc2, pn2)) ->
             if pc1 = 1 || nc1 = 1 then
               if pc2 = 1 || nc2 = 1 then
                 if pn1 = pn2 then arity2 - arity1 else pn1 - pn2
               else -1
             else if pc2 = 1 || nc2 = 1 then 1
             else if pn1 = pn2 then arity2 - arity1
             else pn1 - pn2)
    in
    let safe, chosen =
      match List.find sorted ~f:is_safe with
      | Some cand -> (true, [ cand ])
      | None -> (false, sorted)
    in
    Common.PhaseTime.stop count_tok;
    chosen |> function
    | []
      when Option.is_none max_clauses
           && Config.resolution_complete_max_clauses > 0
           && mentions_unknown clauses
           && only_eliminable_unknowns eliminable_pvs clauses -> (
        (* THE THRESHOLD STOPPED IT; TRY FINISHING THE JOB.  The threshold
           exists to keep the clause set from multiplying, and it is blind to
           the case where a few more eliminations remove every unknown: the
           rest of the run then asks one validity question per clause instead
           of searching a hypothesis space for a solution, and a solution
           the space cannot state -- one needing an existential over a
           clause-local witness -- is then never needed at all.  So every
           remaining unknown is resolved away with the growth bound lifted,
           under a bound on the clause set instead, and the result is kept
           only if no unknown is left.  Resolution preserves satisfiability
           either way, so the choice decides cost and never the answer.  The
           definitions [resolve] records for model recovery are put back
           with the clauses when the attempt is abandoned. *)
        let deadline =
          Option.map Config.resolution_complete_budget_ms ~f:(fun ms ->
              Time_float.add (Common.Clock.now_float ())
                (Time_float.Span.of_ms (Float.of_int ms)))
        in
        let saved_resolved = !resolved_pvars in
        let saved_without_def = !resolved_without_def in
        let restore () =
          resolved_pvars := saved_resolved;
          resolved_without_def := saved_without_def
        in
        match
          Common.PhaseTime.with_phase "complete" (fun () ->
          elim_pvars_by_resolution ~threshold:Int.max_value
            ~max_clauses:Config.resolution_complete_max_clauses ?deadline
            ~atom_pvs ?index ?clause_size elim_free_univ_vars exi_senv
            eliminable_pvs clauses)
        with
        | clauses' when not (mentions_unknown clauses') ->
            complete_outcome := Some `Kept;
            Debug.print
            @@ lazy
                 (sprintf
                    "[elim_pvs] complete elimination: every unknown resolved \
                     away, %d clauses"
                    (Set.length clauses'));
            clauses'
        | _ ->
            complete_outcome := Some `Left_unknown;
            Debug.print
            @@ lazy
                 "[elim_pvs] complete elimination left an unknown; abandoned";
            restore ();
            clauses
        | exception Complete_resolution_abandoned how ->
            complete_outcome := Some (`Abandoned how);
            (match how with
            | `Budget ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[elim_pvs] complete elimination ran out of its %d ms \
                         budget; abandoned"
                        (Option.value ~default:0
                           Config.resolution_complete_budget_ms))
            | `Built | `Prebound | `Early_exit ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[elim_pvs] complete elimination exceeded %d clauses; \
                         abandoned"
                        Config.resolution_complete_max_clauses);
                if not (Stdlib.( = ) how `Built) then
                  Debug.print
                  @@ lazy
                       (if Stdlib.( = ) how `Prebound then
                          "[elim_pvs]   (by the predicted size, before \
                           resolving)"
                        else "[elim_pvs]   (while the step was being built)"));
            restore ();
            clauses)
    | [] -> clauses
    | (pv, arity, (pc, nc, _pn)) :: _rs ->
        Debug.print
        @@ lazy
             (sprintf
                "%s %s (arity %d) occurs %s times positively and %s times \
                 negatively%s"
                (if safe then "[safe]" else "[unsafe]")
                (Ident.name_of_pvar pv) arity (string_of_int pc)
                (string_of_int nc) (at ()));
        (*List.iter rs ~f:(fun (pv, arity, (pc, nc, _pn)) ->
            Debug.print @@ lazy
              (sprintf "%s %s (arity %d) occurs %s times positively and %s times negatively"
                 (if safe then "[safe]" else "[unsafe]")
                 (Ident.name_of_pvar pv) arity (string_of_int pc) (string_of_int nc)));*)
        (* inside a complete elimination: the size tests that can stop a step
           before or while it is built ([Config.resolution_complete_prebound],
           [Config.resolution_complete_early_exit]) and the attempt's budget;
           each raises [Complete_resolution_abandoned], which the complete
           elimination catches, and nothing else *)
        (match max_clauses with
        | Some m when Config.resolution_complete_prebound ->
            let rest = Set.length clauses - List.length (clauses_of_pvar pv) in
            if CompletePrebound.exceeds ~max_clauses:m ~rest ~pc ~nc then (
              Debug.print
              @@ lazy
                   (sprintf
                      "[elim_pvs] complete elimination: resolving %s would \
                       give %d + %d * %d clauses, past %d"
                      (Ident.name_of_pvar pv) rest pc nc m);
              raise (Complete_resolution_abandoned `Prebound))
        | _ -> ());
        let guard =
          match max_clauses with
          | Some m
            when Config.resolution_complete_early_exit
                 || Option.is_some deadline ->
              Some
                (fun n ->
                  check_complete_deadline deadline;
                  if Config.resolution_complete_early_exit && n > m then
                    raise (Complete_resolution_abandoned `Early_exit))
          | _ -> None
        in
        let tick =
          Option.map deadline ~f:(fun d () -> check_complete_deadline (Some d))
        in
        (* a probe's strict deadline, when the preprocessing is asked to read
           it: before this predicate is resolved away and before each
           resolvent is normalised *)
        PCSatCommon.SolveDeadline.check_in_preprocessing ();
        let tick =
          if Atomic.get PCSatCommon.SolveDeadline.in_preprocessing then
            Some
              (fun () ->
                PCSatCommon.SolveDeadline.check_in_preprocessing ();
                Option.iter tick ~f:(fun t -> t ()))
          else tick
        in
        let t0 = Common.Clock.now_float () in
        let clauses' =
          match index with
          | Some index when index.ResolutionIndex.reduced ->
              resolve ?guard ?tick ~index ~elim_free_univ_vars exi_senv pv
                clauses
          | _ ->
              let clauses' =
                resolve ?guard ?tick ~elim_free_univ_vars exi_senv pv clauses
              in
              (* the chain's first step, on clauses no subsumption has
                 reduced: the whole set was subsumed above, and the index is
                 brought to its result *)
              Option.iter index ~f:(fun index ->
                  Common.PhaseTime.with_phase "index" (fun () ->
                      ResolutionIndex.sync index clauses' ~reduced:true));
              clauses'
        in
        if Lazy.force elim_growth_trace then
          print_elim_growth ~complete:(Option.is_some max_clauses) ~atom_pvs pv
            pc nc clauses clauses'
            (Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) t0));
        elim_pvars_by_resolution ~threshold ?max_clauses ?deadline ~atom_pvs
          ?index ?clause_size elim_free_univ_vars exi_senv
          (Set.remove eliminable_pvs pv)
          clauses'

  let elim_pvs ?(record_resolved_defs = true) ?(elim_one_sided_fn = false)
      ?(fn_consequences = false) ?(bpvs = Set.Poly.empty) pcsp =
    eliminated_pvars := Map.Poly.empty;
    eliminated_reasons := Map.Poly.empty;
    (* the persistent subsumption's tables live for one elimination: they
       start from none, and they are dropped at its end (below), since they
       hold literals the clause set no longer needs once it is rewritten *)
    ClauseSubsume.reset_interner ();
    elimination_count := 0;
    if Config.valid_memo then with_valid_memo Hashtbl.Poly.clear;
    resolved_pvars := Map.Poly.empty;
    resolved_without_def := Set.Poly.empty;
    record_resolved := record_resolved_defs;
    let rec inner iter pcsp0 =
      Debug.print @@ lazy (sprintf "[elim_pvs] iter: %d%s" iter (at ()));
      let exi_senv = PCSP.Problem.senv_of pcsp0 in
      let eliminable_pvs =
        Set.filter (PCSP.Problem.pvs_of pcsp0) ~f:(fun t ->
            PCSP.Problem.is_bool_valued_ord_pred pcsp0 t && not (Set.mem bpvs t))
        |> Set.Poly.map ~f:Ident.tvar_to_pvar
      in
      let fn_pvs =
        if (not elim_one_sided_fn) && not fn_consequences then Set.Poly.empty
        else
          Set.filter (PCSP.Problem.pvs_of pcsp0) ~f:(fun t ->
              PCSP.Problem.is_fn_pred pcsp0 t && not (Set.mem bpvs t))
          |> Set.Poly.map ~f:Ident.tvar_to_pvar
      in
      let elim_free_univ_vars =
        Qelim.elim_free_univ_vars_old Map.Poly.empty exi_senv
      in
      (* constants of this iteration: converting the predicate signature to the
         other term representation, and its names as a set.  Both used to be
         rebuilt inside the per-formula and per-clause maps below. *)
      let exi_senv_old = Logic.(to_old_sort_env_map exi_senv) in
      let unknowns = Map.key_set exi_senv in
      let pcsp1 =
        (fun p ->
          Common.PhaseTime.with_phase "unused" (fun () ->
              PCSP.Problem.remove_unused_params p))
        @@ PCSP.Problem.elim_unsat_wf_predicates (*ToDo*) ~print:Debug.print
        @@
        if PCSP.Problem.is_cnf pcsp0 then pcsp0
        else
          PCSP.Problem.map_raw_old_exn pcsp0 ~f:(fun inp ->
              (* note that phis may contain variables with the same name but different types *)
              let pairs =
                Common.PhaseTime.with_phase "refresh" @@ fun () ->
                if iter = 0 then Set.Poly.map ~f:Formula.refresh_tvar inp
                else inp
              in
              (* [set_aside_cnf_clauses]: the formulas whose clausal form
                 would exceed the bound skip this round and come back
                 unchanged with its result, and no unknown they mention is
                 eliminated.  Sound whatever is set aside: eliminating fewer
                 unknowns keeps satisfiability as eliminating them does, and a
                 formula left as it was keeps its meaning.  The round can
                 eliminate fewer unknowns (those of a set-aside formula) and
                 also more: the resolution stops at the first candidate its
                 growth test refuses, and an unknown set aside no longer
                 stands there. *)
              let aside, pairs =
                match Atomic.get set_aside_cnf_clauses with
                | None -> (Set.Poly.empty, pairs)
                | Some bound ->
                    Set.partition_tf pairs ~f:(fun (_, phi) ->
                        predicted_cnf_clauses unknowns
                          (expand_bool_eq_of_unknowns exi_senv
                          @@ snd (Formula.rm_quant ~forall:true phi))
                        > bound)
              in
              if Lazy.force set_aside_skeleton then
                Set.iter aside ~f:(fun (_, phi) ->
                    let body =
                      expand_bool_eq_of_unknowns exi_senv
                      @@ snd (Formula.rm_quant ~forall:true phi)
                    in
                    Stdlib.Printf.eprintf
                      "[set-aside-round] iter=%d predicted=%d size=%d skeleton=%s\n%!"
                      iter
                      (predicted_cnf_clauses unknowns body)
                      (Formula.ast_size body)
                      (cnf_skeleton unknowns body));
              let aside_pvs =
                Set.concat_map aside ~f:(fun (_, phi) -> Formula.pvs_of phi)
              in
              if Lazy.force elim_growth_trace && not (Set.is_empty aside) then
                Stdlib.Printf.eprintf
                  "[cnf-set-aside] iter=%d formulas=%d unknowns=%s\n%!" iter
                  (Set.length aside)
                  (String.concat_map_set ~sep:"," aside_pvs
                     ~f:Ident.name_of_pvar);
              let fn_pvs = Set.diff fn_pvs aside_pvs in
              let senvs, phis = Set.unzip pairs in
              let senvs', phis =
                Common.PhaseTime.with_phase "rm-quant" @@ fun () ->
                Set.unzip
                @@ Set.Poly.map ~f:(Formula.rm_quant ~forall:true) phis
              in
              let senv =
                Map.of_set_exn @@ Logic.of_old_sort_env_set @@ Set.concat
                @@ Set.union (Set.Poly.map ~f:Set.of_map senvs) senvs'
              in
              Debug.print
              @@ lazy
                   (sprintf "[elim_pvs] senv: %s"
                   @@ Logic.str_of_sort_env_list Logic.ExtTerm.str_of_sort
                   @@ Map.Poly.to_alist senv);
              Debug.print
              @@ lazy
                   (sprintf "[elim_pvs] bpvs: %s"
                      (String.concat_map_set ~sep:"," bpvs ~f:Ident.name_of_tvar));
              Debug.print
              @@ lazy (sprintf "[elim_pvs] cnf transformation in progress");
              (* [Config.tautology_test]: drop a valid input clause before its
                 conjunctive normal form is built *)
              let phis =
                if not Config.tautology_test then phis
                else
                  Common.PhaseTime.with_phase "taut-input" @@ fun () ->
                  let phis' =
                    Set.filter phis
                      ~f:(Fn.non ClauseTautology.formula_is_tautology)
                  in
                  let d = Set.length phis - Set.length phis' in
                  if d > 0 then
                    Debug.print
                    @@ lazy
                         (sprintf
                            "[elim_pvs] tautology test (input): %d of %d \
                             clauses dropped"
                            d (Set.length phis));
                  phis'
              in
              (* the clause set of [phis]: the conjunctive normal form, and the
                 clause-level tautology test and subsumption when they are on *)
              let clauses_of phis =
                let cnt = ref 0 in
                Common.PhaseTime.with_phase "cnf" (fun () ->
                Set.concat_map phis ~f:(fun phi ->
                    cnt := !cnt + 1;
                    Debug.print
                    @@ lazy
                         (sprintf
                            "[elim_pvs] transforming %s clause (out of %d): %s"
                            (Ordinal.string_of (Ordinal.make !cnt))
                            (Set.length phis) (Formula.str_of phi));
                    let cls =
                      (if Atomic.get cnf_clause_tree then
                         Formula.cnf_of_clause_tree
                       else Formula.cnf_of ~process_pure:false)
                        exi_senv_old
                      @@ expand_bool_eq_of_unknowns exi_senv phi
                    in
                    (* the normal form multiplies the alternatives of a
                       disjunction of conjunctions that mention unknowns, so
                       one input formula can give hundreds of clauses; this
                       says which *)
                    if Set.length cls > 1 then
                      Debug.print
                      @@ lazy
                           (sprintf
                              "[elim_pvs] the %s clause gives %d clauses"
                              (Ordinal.string_of (Ordinal.make !cnt))
                              (Set.length cls));
                    (* with COAR_ELIM_GROWTH set, one line per input formula:
                       its size and the number and summed size of the clauses
                       its normal form gives *)
                    if Lazy.force elim_growth_trace then
                      Stdlib.Printf.eprintf
                        "[cnf-growth] iter=%d formula=%d size=%d clauses=%d \
                         clause_size=%d\n\
                         %!"
                        iter !cnt (Formula.ast_size phi) (Set.length cls)
                        (Set.fold cls ~init:0 ~f:(fun acc (ps, ns, pure) ->
                             acc + Formula.ast_size pure
                             + Set.fold (Set.union ps ns) ~init:0
                                 ~f:(fun a atm -> a + Atom.ast_size atm)));
                    (* with COAR_CNF_DUMP naming a directory, every input
                       formula whose normal form has more than one clause is
                       written there, one file per formula *)
                    (match Stdlib.Sys.getenv_opt "COAR_CNF_DUMP" with
                    | Some dir when Set.length cls > 1 ->
                        Out_channel.write_all
                          (sprintf "%s/iter%d_f%d_pid%d_c%d.txt" dir iter !cnt
                             (Core_unix.getpid () |> Pid.to_int)
                             (Set.length cls))
                          ~data:(Formula.str_of phi)
                    | _ -> ());
                    cls))
                |> (fun cls ->
                Common.PhaseTime.with_phase "reduce" @@ fun () ->
                let reduce =
                  if Atomic.get cnf_shared_fvs then
                    ClauseOld.reduce_sort_map_shared ()
                  else ClauseOld.reduce_sort_map
                in
                Set.Poly.map cls ~f:(fun (ps, ns, phi) ->
                    reduce (senv, ps, ns, phi)))
                |> (if Config.tautology_test then fun cls ->
                      Common.PhaseTime.with_phase "taut" (fun () ->
                          drop_tautologies ~where:"cnf" cls)
                    else Fn.id)
                |> if Config.subsume_clauses then subsume ~where:"cnf"
                   else Fn.id
              in
              (* A predicate application inside a clause's *pure* part is
                 invisible to the accounting every rule below decides from:
                 [ClauseOld.pvs_of] ignores [phi] outright and
                 [ClauseSetOld.count_pvar_apps] counts only the atom sets.  The
                 DQCHC encoding of a premise like [forall a. X a = K a] puts
                 one there, inside a Bool-valued equality, and [K] then looks
                 one-sided and is eliminated although [phi] still constrains it
                 -- the clauses mentioning it are dropped and the pure part is
                 left referring to a predicate that no longer exists
                 Such predicates are excluded from
                 every rule here; a missed elimination costs time, a wrong one
                 costs the answer. *)
              let without_pure_part_unknowns eliminable_pvs cls =
                let in_phi =
                  Set.concat_map cls ~f:(fun (_, _, _, phi) ->
                      LogicOld.Formula.pvs_of phi)
                in
                if Fn.non Set.is_empty (Set.inter eliminable_pvs in_phi) then
                  Debug.print
                  @@ lazy
                       (sprintf "[elim_pvs] applied inside a pure part: %s"
                          (String.concat_map_set ~sep:", " ~f:Ident.name_of_pvar
                             (Set.inter eliminable_pvs in_phi)));
                Set.diff eliminable_pvs in_phi
              in
              (* the one-sided assignments and the bounds, then subsumption *)
              let bounds ?normalise eliminable_pvs cls =
                Debug.print
                @@ lazy
                     (sprintf
                        "[elim_pvs] begin elim_one_side_unbounded_pvars [%d]:\n%s"
                        (Set.length cls) (ClauseSetOld.str_of cls));
                cls
                |> elim_one_side_unbounded_pvars exi_senv eliminable_pvs
                |> (fun cls ->
                Debug.print
                @@ lazy ("[elim_pvs] end elim_one_side_unbounded_pvars" ^ at ());
                Debug.print
                @@ lazy
                     (sprintf "[elim_pvs] begin elim_pvars_with_lb_ub [%d]:\n%s"
                        (Set.length cls) (ClauseSetOld.str_of cls));
                cls)
                |> elim_pvars_with_lb_ub ?normalise exi_senv eliminable_pvs
                |> fun cls ->
                Debug.print @@ lazy ("[elim_pvs] end elim_pvars_with_lb_ub" ^ at ());
                if Config.subsume_clauses then subsume ~where:"bounds" cls
                else cls
              in
              Common.DagCensus.report ~items:(Set.length inp)
                (sprintf "elim iter %d: input" iter) inp;
              let cls =
                Common.PhaseTime.with_phase "to-cnf" (fun () -> clauses_of phis)
              in
              Common.DagCensus.report ~items:(Set.length cls)
                (sprintf "elim iter %d: clausal form" iter) cls;
              (* with COAR_CNF_SHARING set, the heap words the input formulas
                 and the clause set occupy, the latter as one value and as the
                 sum over its clauses (their ratio is the physical sharing
                 between clauses) *)
              if Option.is_some (Stdlib.Sys.getenv_opt "COAR_CNF_SHARING") then
                Stdlib.Printf.eprintf
                  "[cnf-sharing] iter=%d formulas=%d formula_words=%d \
                   clauses=%d clause_set_words=%d clause_words_sum=%d\n\
                   %!"
                  iter (Set.length phis)
                  (Obj.reachable_words (Obj.repr phis))
                  (Set.length cls)
                  (Obj.reachable_words (Obj.repr cls))
                  (Set.fold cls ~init:0 ~f:(fun acc cl ->
                       acc + Obj.reachable_words (Obj.repr cl)));
              (* the normalisation [resolve] gives each resolvent (before its
                 condensation, which concerns premises a resolution unions):
                 simplification, the elimination of the variables the clause
                 quantifies implicitly, and the normal form; the conjunction
                 of the result is equivalent to [cl] *)
              let normalise_like_resolvent cl =
                let senv, phi = ClauseOld.to_formula cl in
                let senv, phi =
                  elim_free_univ_vars
                    (senv, Normalizer.normalize @@ Evaluator.simplify phi)
                in
                Set.Poly.map ~f:(fun (ps, ns, phi) -> (senv, ps, ns, phi))
                @@ Formula.cnf_of exi_senv_old
                @@ expand_bool_eq_of_unknowns exi_senv
                @@ Normalizer.normalize @@ Evaluator.simplify phi
              in
              Debug.print
              @@ lazy ("[elim_pvs] cnf transformation completed" ^ at ());
              (* begin: predicate variable elimination *)
              let eliminable_pvs =
                Set.diff
                  (without_pure_part_unknowns eliminable_pvs cls)
                  aside_pvs
              in
              Common.PhaseTime.with_phase "bounds" (fun () ->
              if not Config.assign_before_cnf then bounds eliminable_pvs cls
               else
                 (* [Config.assign_before_cnf]: the bounds are found on the
                    clause set as usual, and the predicates they assign a
                    constant (no positive or no negative occurrence, a valid
                    lower bound, an unsatisfiable upper bound) are then
                    substituted into the input formulas instead, before the
                    conjunctive normal form is built again; the bounds step
                    then runs on that clause set for the rest.  A constant
                    under a disjunction makes the conjunctive normal form
                    multiply copies that the substitution would only make
                    redundant afterwards.  Exact for the same reason the
                    assignment is: the normal form of the substituted formulas
                    is the substitution applied to the normal form, up to
                    propositional simplification of the constants.  Every
                    other definition the first run recorded is discarded and
                    found again by the second. *)
                 let snapshot =
                   (!eliminated_pvars, !eliminated_reasons, !elimination_count)
                 in
                 let first = bounds eliminable_pvs cls in
                 let consts =
                   Map.Poly.to_alist !eliminated_reasons
                   |> List.filter_map ~f:(fun (tvar, (reason, count)) ->
                       if Map.Poly.mem (Tuple3.get2 snapshot) tvar then None
                       else
                         match (reason : PCSP.Params.elim_reason) with
                         | OneSidedNoLB | UbUnsat -> Some (count, tvar, reason, false)
                         | OneSidedNoUB | LbValid -> Some (count, tvar, reason, true)
                         | _ -> None)
                   |> List.sort ~compare:(fun (c1, _, _, _) (c2, _, _, _) ->
                       Int.compare c1 c2)
                 in
                 if List.is_empty consts then first
                 else (
                   let defs =
                     List.map consts ~f:(fun (_, tvar, _, _) ->
                         (tvar, Map.Poly.find_exn !eliminated_pvars tvar))
                   in
                   let e, r, c = snapshot in
                   eliminated_pvars := e;
                   eliminated_reasons := r;
                   elimination_count := c;
                   List.iter2_exn consts defs
                     ~f:(fun (_, tvar, reason, _) (_, def) ->
                       eliminated_pvars :=
                         Map.Poly.add_exn !eliminated_pvars ~key:tvar ~data:def;
                       record_reason (Ident.tvar_to_pvar tvar) reason);
                   let psub =
                     Map.Poly.of_alist_exn
                     @@ List.map consts ~f:(fun (_, tvar, _, value) ->
                         let params =
                           mk_fresh_sort_env_list
                           @@ List.map ~f:Logic.ExtTerm.to_old_sort
                           @@ Logic.Sort.args_of
                           @@ Map.Poly.find_exn exi_senv tvar
                         in
                         ( Ident.tvar_to_pvar tvar,
                           ( params,
                             if value then Formula.mk_true ()
                             else Formula.mk_false () ) ))
                   in
                   Debug.print
                   @@ lazy
                        (sprintf
                           "[elim_pvs] assigned before the normal form: %s"
                           (String.concat_map_list ~sep:", " consts
                              ~f:(fun (_, tvar, _, value) ->
                                sprintf "%s := %b" (Ident.name_of_tvar tvar)
                                  value)));
                   let phis =
                     Set.Poly.filter_map phis ~f:(fun phi ->
                         let phi =
                           simplify_bool_consts @@ Formula.subst_preds psub phi
                         in
                         if Formula.is_true phi then None else Some phi)
                   in
                   let cls' = clauses_of phis in
                   let eliminable_pvs =
                     without_pure_part_unknowns
                       (Set.diff eliminable_pvs
                          (Set.Poly.of_list (Map.Poly.keys psub)))
                       cls'
                   in
                   Debug.print
                   @@ lazy
                        (sprintf
                           "[elim_pvs] clauses after assigning before the \
                            normal form: %d (were %d)"
                           (Set.length cls') (Set.length cls));
                   (* A constant this second run finds that the first did
                      not (a nullary [p14] whose only defining clause was
                      [not p4 \/ p14], with [p4 := true] assigned above)
                      reaches the ordinary pipeline only one step later, as
                      a resolution with the unit clause it has become, and
                      every clause it occurs in then gets a resolvent's
                      normalisation: its implicitly universal variables fixed
                      by an equation are eliminated ([x != 10 \/ C x] becomes
                      [C 10]).  Substituting the constant here instead left
                      those clauses unnormalised -- an equivalent clause set
                      with more variables and larger formulas, on which the
                      learner did measurably worse -- so the clauses this run
                      changes are normalised the same way. *)
                   bounds ~normalise:normalise_like_resolvent eliminable_pvs
                     cls'))
              |> (fun cls ->
              Debug.print
              @@ lazy
                   (sprintf
                      "[elim_pvs] begin elim_pvars_by_resolution [%d]:\n%s"
                      (Set.length cls) (ClauseSetOld.str_of cls));
              cls)
              |> (fun cls ->
              Common.DagCensus.report ~items:(Set.length cls)
                (sprintf "elim iter %d: before resolution" iter) cls;
              Common.PhaseTime.with_phase "resolution" (fun () ->
                  elim_pvars_by_resolution elim_free_univ_vars exi_senv
                    eliminable_pvs cls))
              |> (fun cls ->
              Common.DagCensus.report ~items:(Set.length cls)
                (sprintf "elim iter %d: after resolution" iter) cls;
              cls)
              |> (if elim_one_sided_fn then
                    elim_one_sided_fn_pvars exi_senv fn_pvs
                  else Fn.id)
              |> (if fn_consequences then
                    fn_refutation_consequences exi_senv fn_pvs
                  else Fn.id)
              |> (fun cls ->
              Debug.print
              @@ lazy ("[elim_pvs] end elim_pvars_by_resolution" ^ at ());
              Debug.print
              @@ lazy
                   (sprintf "[elim_pvs] begin result [%d]:\n%s" (Set.length cls)
                      (ClauseSetOld.str_of cls));
              cls)
              (* end: predicate variable elimination *)
              |> (fun cls ->
              (* the round's last simplification: a deferred question is
                 asked here when an unknown remains, so the search gets the
                 clause set it would get without deferral *)
              (fun out ->
                Common.DagCensus.report ~items:(Set.length out)
                  (sprintf "elim iter %d: after final simplify" iter) out;
                out)
              @@ Common.PhaseTime.with_phase "final-simplify" @@ fun () ->
              let defer =
                Set.is_empty aside_pvs
                && not (DeferPure.unknowns_remain unknowns cls)
              in
              (* one scope of the simplifier's memo for the clauses (when
                 switched on): they share large pure parts physically, and
                 simplified one by one each got its own copy *)
              Evaluator.with_shared_simplify @@ fun () ->
              Set.union aside
              @@ Set.Poly.filter_map cls ~f:(fun cl ->
                  let open Option in
                  simplify_clause ~defer ~final:true unknowns cl
                  >>= fun cl ->
                  let senv, phi =
                    ClauseOld.to_formula @@ ClauseOld.reduce_sort_map cl
                  in
                  Some (Logic.to_old_sort_env_map senv, phi))))
      in
      Common.DagCensus.report
        (sprintf "elim iter %d: output" iter)
        (PCSP.Problem.formulas_of ~full_clauses:false pcsp1);
      if
        Map.Poly.equal Stdlib.( = )
          (PCSP.Problem.senv_of pcsp0)
          (PCSP.Problem.senv_of pcsp1)
      then pcsp1
      else (
        Debug.print
        @@ lazy ("*** pcsp senv has been changed, repeat elim_pvs" ^ at ());
        inner (iter + 1) pcsp1)
    in
    let res =
      Exn.protect
        ~f:(fun () -> inner 0 pcsp)
        ~finally:ClauseSubsume.reset_interner
    in
    (* the formulas [set_aside_cnf_clauses] kept whole through the rounds are
       put in clausal form once, after the last round, so that what follows
       receives clauses as it does without the switch; inside one
       datatype-conversion scope, so the clauses share the datatypes of the
       formulas they come from *)
    let res =
      match Atomic.get set_aside_cnf_clauses with
      | Some bound when not (PCSP.Problem.is_cnf res) ->
          let exi_senv = PCSP.Problem.senv_of res in
          let unknowns = Map.key_set exi_senv in
          let exi_senv_old = Logic.to_old_sort_env_map exi_senv in
          (* the unknowns [definitional_split] adds, with their sorts *)
          let added = ref Map.Poly.empty in
          let fresh () =
            let v =
              Ident.mk_fresh_tvar_avoiding ~prefix:"Dcnf"
                ~taken:(fun v -> Map.Poly.mem exi_senv v || Map.Poly.mem !added v)
                ()
            in
            Ident.tvar_to_pvar v
          in
          let to_clause senv (ps, ns, pure) =
            ( senv,
              Formula.or_of
                (pure
                 :: Set.to_list (Set.Poly.map ps ~f:Formula.mk_atom)
                @ Set.to_list
                    (Set.Poly.map ns ~f:(Formula.mk_atom >> Formula.mk_neg))) )
          in
          let res =
          Logic.ExtTerm.with_shared_datatype_conversion @@ fun () ->
          PCSP.Problem.map_raw_old_exn res ~f:(fun inp ->
              Common.DagCensus.report ~items:(Set.length inp)
                "elim: set-aside expansion input (old)" inp;
              (fun out ->
                Common.DagCensus.report ~items:(Set.length out)
                  "elim: set-aside expansion output (old)" out;
                out)
              @@ Set.concat_map inp ~f:(fun (senv, phi) ->
                  let senv', body = Formula.rm_quant ~forall:true phi in
                  let body = expand_bool_eq_of_unknowns exi_senv body in
                  if Lazy.force set_aside_skeleton then
                    Stdlib.Printf.eprintf
                      "[set-aside-skeleton] predicted=%d size=%d skeleton=%s\n%!"
                      (predicted_cnf_clauses unknowns body)
                      (Formula.ast_size body)
                      (cnf_skeleton unknowns body);
                  if predicted_cnf_clauses unknowns body <= bound then
                    Set.Poly.singleton (senv, phi)
                  else
                    let senv = Map.force_merge senv (Map.of_set_exn senv') in
                    if Atomic.get set_aside_definitional then (
                      let phis, defs =
                        definitional_split ~bound ~unknowns ~fresh body
                      in
                      List.iter defs ~f:(fun (pvar, sorts) ->
                          added :=
                            Map.Poly.set !added ~key:(Ident.pvar_to_tvar pvar)
                              ~data:
                                (Logic.Sort.mk_fun
                                   (List.map sorts ~f:Logic.ExtTerm.of_old_sort
                                   @ [ Logic.BoolTerm.SBool ])));
                      let exi_senv_old =
                        Map.force_merge exi_senv_old
                          (Logic.to_old_sort_env_map !added)
                      in
                      if Lazy.force set_aside_skeleton then
                        Stdlib.Printf.eprintf
                          "[set-aside-definitional] formulas=%d unknowns=%d arities=%s\n%!"
                          (List.length phis) (List.length defs)
                          (String.concat_map_list ~sep:","
                             ~f:(snd >> List.length >> string_of_int) defs);
                      Set.Poly.of_list
                      @@ List.concat_map phis ~f:(fun phi ->
                          Set.to_list
                          @@ Set.Poly.map ~f:(to_clause senv)
                          @@ Formula.cnf_of ~process_pure:false exi_senv_old phi))
                    else
                    let cls = Formula.cnf_of ~process_pure:false exi_senv_old body in
                    if Lazy.force set_aside_skeleton then (
                      let taut =
                        Set.count cls ~f:(fun (ps, ns, _) ->
                            not (Set.are_disjoint ps ns))
                      in
                      let atoms =
                        Set.concat_map cls ~f:(fun (ps, ns, _) ->
                            Set.union
                              (Set.Poly.map ps ~f:(fun a -> "+" ^ Atom.str_of a))
                              (Set.Poly.map ns ~f:(fun a -> "-" ^ Atom.str_of a)))
                      in
                      Stdlib.Printf.eprintf
                        "[set-aside-expanded] clauses=%d syntactic-tautologies=%d distinct-literals=%d\n%!"
                        (Set.length cls) taut (Set.length atoms);
                      Set.iter atoms ~f:(fun a ->
                          if not (String.is_prefix ~prefix:"-FN_" a) then
                            Stdlib.Printf.eprintf "[set-aside-literal] %s\n%!" a));
                    Set.Poly.map cls ~f:(to_clause senv)))
          in
          if Map.Poly.is_empty !added then res
          else
            PCSP.Problem.map_params res ~f:(fun params ->
                {
                  params with
                  PCSP.Params.senv = Map.force_merge params.PCSP.Params.senv !added;
                  kind_map =
                    Kind.add_kinds (Map.Poly.key_set !added) Kind.Ord
                      params.PCSP.Params.kind_map;
                })
      | _ -> res
    in
    Common.DagCensus.report "elim: after the set-aside expansion"
      (PCSP.Problem.formulas_of ~full_clauses:false res);
    Debug.print @@ lazy ("[elim_pvs] finished" ^ at ());
    ( ( !eliminated_pvars,
        !eliminated_reasons,
        !resolved_pvars,
        !resolved_without_def ),
      res )
  (*ToDo: reconstruct solution for pvars eliminated by elim_pvars_by_resolution using solve_non_rec*)

  let solution_of_unit_clause clause =
    let _senv, ps, ns, phi = clause in
    let ftv = Formula.term_sort_env_of phi |> Set.elements in
    let quantifiers = fst @@ refresh_sort_env_list ~prefix:None ftv in
    let subst_map =
      List.zip_exn ftv quantifiers
      |> List.map ~f:(fun ((tvar, sort), (bvar, sort')) ->
          assert (Stdlib.(sort = sort'));
          (tvar, Term.mk_var bvar sort))
      |> Map.Poly.of_alist_exn
    in
    let phi = Formula.subst subst_map phi in
    if Set.is_singleton ps then
      match Set.choose ps with
      | Some (Atom.App (Predicate.Var (pvar, sorts), terms, _)) ->
          let params = sort_env_list_of_sorts sorts in
          let phi =
            try
              Formula.exists quantifiers
              @@ List.fold
                   ~init:(Evaluator.simplify @@ Formula.mk_neg phi)
                   ~f:(fun phi ((tvar, sort), term) ->
                     let term = Term.subst subst_map term in
                     Formula.mk_and
                       (Formula.eq term (Term.mk_var tvar sort))
                       phi)
              @@ List.zip_exn params terms
            with exn_ when not (Common.Timer.is_async exn_) ->
              failwith "params must be exactly same length to terms"
          in
          (pvar, (params, phi))
      | _ -> assert false
    else if Set.is_singleton ns then
      match Set.choose ns with
      | Some (Atom.App (Predicate.Var (pvar, sorts), terms, _)) ->
          let params = sort_env_list_of_sorts sorts in
          let phi =
            let condition =
              try
                List.fold ~init:None ~f:(fun c ((tvar, sort), term) ->
                    let eq =
                      Formula.eq
                        (Term.subst subst_map term)
                        (Term.mk_var tvar sort)
                    in
                    match c with
                    | None -> Some eq
                    | Some phi -> Some (Formula.mk_and eq phi))
                @@ List.zip_exn params terms
              with exn_ when not (Common.Timer.is_async exn_) ->
                failwith "params must be exactly same length to terms"
            in
            match condition with
            | Some condition ->
                Formula.forall quantifiers @@ Formula.mk_imply condition phi
            | None -> failwith "there must be at least one params"
          in
          (pvar, (params, phi))
      | _ -> assert false
    else failwith "one of ps or ns has one element, the other does zero"

  let rec solve_non_rec unknowns cnf =
    let pvar, (senv, phi) =
      match
        Set.find cnf ~f:(fun (_, ps, ns, _) ->
            Set.length ps + Set.length ns = 1)
      with
      | Some clause -> solution_of_unit_clause clause
      | None ->
          failwith
            "At least one clause must have exactly one predicate variable."
    in
    let psub = Map.Poly.singleton pvar (senv, phi, Formula.mk_neg phi, false) in
    let cnf1, cnf2 = subst_preds unknowns psub cnf in
    let cnf = Set.union cnf1 cnf2 in
    (pvar, (senv, phi))
    :: (if Set.is_empty cnf then [] else solve_non_rec unknowns cnf)
end
