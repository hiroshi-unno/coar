(* The resolution phase of PCSat's CEGIS loop: derive new decided examples
   from the decided ones and the clauses, recording each derivation in the
   clause graph so a refutation can be re-checked.

   One round, [resolve], runs these rules on the version space it is given:
   deciding atoms from the problem's fact and goal clauses (and from witness
   groups) when those switches are on; proving an undecided or decided
   atom positive, or refuting it, when the clause resolved against the
   decided units leaves only that atom and its matching condition is
   satisfiable ([prove], [refute], via [contradicts]); and resolving the
   undecided examples, and optionally the problem's own clauses, one step
   against the decided units and collecting the unit examples left
   ([acquire]).  The new examples are returned in the state with their
   sources.

   Contract.  Every example added follows from the clauses and the decided
   examples it cites, in every model of the background theory: what a Z3
   model fixes about a term the theory leaves open (a selector off its
   constructor, an uninterpreted function, a division by zero) is attached to
   the derived example as its guard rather than assumed, a ground guard is
   dropped only when it is valid, and a derivation whose model disagrees with
   the unifier that matched it is discarded.  Questions whose shape Z3 may not
   return on are refused, which can lose a derivation but never adds one. *)
open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSatCommon

module Make
    (Config : SMTResolver.Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : sig
  val run_phase : int -> State.u -> State.u Or_error.t
end = struct
  let config = Config.config
  let id = PCSP.Problem.id_of APCSP.problem

  (* the magnitudes the problem states, computed once.  Used to tell a value the
     program gave from one the solver merely picked, which nothing in a model
     distinguishes. *)
  let stated_literals =
    lazy
      (Set.concat_map
         (PCSP.Problem.old_formulas_of APCSP.problem)
         ~f:LogicOld.abs_num_literals_of_formula)

  (* the selective counterpart of [generalise_matching]: open only what the
     problem does not state.  Applied to the substitution the model produced,
     whose values then reach the derived example both in its atoms and, through
     [Formula.subst sub phi] below, in its guard -- which is what keeps a fresh
     parameter constrained and the model's own value its witness. *)
  let generalise_invented sub =
    if not config.generalise_invented_values then sub
    else
      let f = LogicOld.make_generaliser ~stated:(Lazy.force stated_literals) in
      Map.Poly.map sub ~f

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id
  let old_dpos = ref Set.Poly.empty
  let old_dneg = ref Set.Poly.empty
  let old_und = ref Set.Poly.empty

  (* With [problem_clause_self_loop_depth_arrays_program_only]: the positions
     of a predicate's arguments that hold a universal relation, read once per
     predicate and arity off the problem's constraints, which do not change
     during a solve. *)
  let universal_positions_memo : (Ident.pvar * int, int list) Hashtbl.Poly.t =
    Hashtbl.Poly.create ()

  let universal_positions_of pvar (sorts : Sort.t list) =
    Hashtbl.find_or_add universal_positions_memo (pvar, List.length sorts)
      ~default:(fun () ->
        CellQual.universal_array_positions ~pvar
          ~params:
            (List.mapi sorts ~f:(fun i s -> (Ident.Tvar (sprintf "u%d" i), s)))
          (Set.to_list (PCSP.Problem.old_formulas_of APCSP.problem)))

  (* per decided example, how many self-loop steps of the problem-clause site
     derived it (absent = 0); read and written only when
     [problem_clause_self_loop_depth_bound] is on.  Keyed on the example clause
     in [ExClause.normalize] form (see the site); an example that comes back in
     a spelling the key does not identify counts as depth 0, which weakens the
     bound and does not change what is sound. *)
  let loop_depths : ExClause.t LoopDepth.t ref = ref LoopDepth.empty

  (* [COAR_LOOP_DEPTH_COUNT=1] prints, per round, what the depth bound withheld
     and recorded, so that a run shows the bound was read and fired *)
  (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
  let loop_depth_count =
    Lazy.from_val
      (match Sys.getenv "COAR_LOOP_DEPTH_COUNT" with
      | Some ("1" | "2" | "true" | "yes") -> true
      | _ -> false)

  (* [COAR_LOOP_DEPTH_COUNT=2] also prints every source with its depth *)
  (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
  let loop_depth_detail =
    Lazy.from_val
      (match Sys.getenv "COAR_LOOP_DEPTH_COUNT" with
      | Some "2" -> true
      | _ -> false)

  let loop_depth_round = ref 0

  (* set by [resolve] for the run; records how a derived example was obtained *)
  let record :
      (ExClause.t ->
      via:Clause.t option ->
      premises:ExClause.t list ->
      LogicOld.TermSubst.t ->
      unit)
      ref =
    ref (fun _ ~via:_ ~premises:_ _ -> ())

  (* the substitution of the resolved clause's variables: the one-step unifier
     [theta] with the values [sub] found for what it left open (params and
     the clause's remaining variables); variables neither binds stay as they
     are and become parameters of the re-derived instance *)
  let clause_subst exi_senv (origin : Clause.t) theta sub =
    Map.Poly.filter_keys ~f:(fun x -> not (Map.Poly.mem exi_senv x))
    @@ Map.Poly.mapi (Clause.sort_env_of origin) ~f:(fun ~key:x ~data:s ->
        let t =
          match Map.Poly.find theta x with
          | Some t -> t
          | None -> Term.mk_var x (Logic.ExtTerm.to_old_sort s)
        in
        Term.subst sub t)

  let insert_source src = Option.map ~f:(fun a -> (a, src))

  (* A decided example used as a premise is cited as itself, so the clause
     graph records direct parents (a checker needs the unit derived earlier in
     the same run, not its sources).  This requires [ClauseGraph.add_ex_from]
     to test example-set membership rather than vertex membership: testing the
     vertex would find the unit's vertex already created through the edge, the
     unit would be skipped when added and the solver would lose it (one input
     goes from 12 iterations to hundreds). *)
  let cite ex = Set.Poly.singleton (ClauseGraph.mk_example ex, false)

  (* [inherit_goal_reads]: file under the derived negative atom the records of
     the decided negative examples of its own predicate among the derivation's
     sources, each joined with the resolved clause's reads at the instance
     [via].  Returns how many records were filed; any failure costs the
     records, never the example. *)
  let inherit_goal_reads exi_senv ~source ~origin ~via (cl : ExClause.t) =
    if not config.inherit_goal_reads then 0
    else
      match Set.to_list cl.ExClause.negative with
      | [ derived ] when Set.is_empty cl.ExClause.positive -> (
          match (GoalReads.key_of_atom derived, ExAtom.pvar_of derived) with
          | Some target, Some pvar -> (
              let from =
                Set.to_list source
                |> List.filter_map ~f:(function
                     | ClauseGraph.Example ex, _
                       when Set.is_empty ex.ExClause.positive -> (
                         match Set.to_list ex.ExClause.negative with
                         | [ a ] -> (
                             match ExAtom.pvar_of a with
                             | Some p when Ident.pvar_equal p pvar -> Some a
                             | _ -> None)
                         | _ -> None)
                     | _ -> None)
              in
              if List.is_empty from then 0
              else
                let own =
                  match Clause.to_old_formula exi_senv origin with
                  | phi -> GoalReads.instance_reads ~target phi via
                  | exception exn_ when not (Common.Timer.is_async exn_) -> []
                in
                match GoalReads.inherit_records ~target ~from ~own with
                | n ->
                    if n > 0 then
                      Debug.print
                      @@ lazy
                           (sprintf "  [goal reads] %d record(s) inherited for %s" n
                              target);
                    n
                | exception exn_ when not (Common.Timer.is_async exn_) -> 0)
          | _ -> 0)
      | _ -> 0

  let src_exs_of (hide_und : bool) =
    Set.Poly.map ~f:(fun ex ->
        (ex, Set.Poly.singleton (ClauseGraph.mk_example ex, hide_und)))

  let src_cls_of (hide_und : bool) =
    Set.Poly.map ~f:(fun cl ->
        (cl, Set.Poly.singleton (ClauseGraph.mk_clause cl, hide_und)))

  exception E

  let unifiable = function
    | Atom.True _, Atom.True _ | False _, False _ -> Some (Formula.mk_true ())
    | App (pred, terms, _), App (pred', terms', _)
      when Stdlib.( = ) pred pred' && List.length terms = List.length terms'
      -> (
        try
          Some
            (Formula.and_of
            @@ List.filter_map (List.zip_exn terms terms') ~f:(function
              | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                  if Z.Compare.( = ) n1 n2 then None else raise E
              | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                ->
                  if Q.( = ) r1 r2 then None else raise E
              | ( FunApp (T_bool.Formula (Formula.Atom (atm1, _)), [], _),
                  FunApp (T_bool.Formula (Formula.Atom (atm2, _)), [], _) )
                when (Atom.is_true atm1 || Atom.is_false atm1)
                     && (Atom.is_true atm2 || Atom.is_false atm2) ->
                  if
                    (Atom.is_true atm1 && Atom.is_true atm2)
                    || (Atom.is_false atm1 && Atom.is_false atm2)
                  then None
                  else raise E
              | t1, t2 -> Some (Formula.eq t1 t2)))
        with E -> None)
    | _ -> None

  (* [unifiable] returns the equations under which two atoms agree, and every
     one of them is then handed to a solver, which answers with one arbitrary
     solution.  An equation with a PARAMETER on one side does not need a
     solver: it is a binding, and realising it is what lets one example's
     parameter meet another's -- which is what a refutation needs, since two
     distinct parameters no more meet than two distinct constants do.  Only the
     equations between two non-parameters are a question for anyone else.

     [params] is the set the caller treats as open.  The result is the bindings
     that were realised and the equations that remain; a variable already bound
     is not rebound, and an equation whose sides are both parameters binds the
     later to the earlier so that the choice does not depend on argument order. *)
  let split_bindings params phi =
    let is_param x = Set.mem params x in
    let rec collect sub rest = function
      | [] -> (sub, rest)
      | eq :: eqs -> (
          match eq with
          | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
            -> (
              let bind x t =
                if Map.Poly.mem sub x || Set.mem (Term.tvs_of t) x then None
                else Some (Map.Poly.set sub ~key:x ~data:t)
              in
              match (t1, t2) with
              | Term.Var (x, _, _), _ when is_param x -> (
                  match bind x t2 with
                  | Some sub' -> collect sub' rest eqs
                  | None -> collect sub (eq :: rest) eqs)
              | _, Term.Var (y, _, _) when is_param y -> (
                  match bind y t1 with
                  | Some sub' -> collect sub' rest eqs
                  | None -> collect sub (eq :: rest) eqs)
              | _ -> collect sub (eq :: rest) eqs)
          | _ -> collect sub (eq :: rest) eqs)
    in
    let sub, rest = collect Map.Poly.empty [] (Formula.conjuncts_list_of phi) in
    (sub, Formula.and_of rest)

  let verbose = false

  (* THE RESOLUTION PHASE'S OWN SOLVER QUESTIONS.
     Both rules below decide from a model of a formula built out of a clause and
     decided examples, and such a formula can quantify over a sequence (a clause
     binding one, or an example whose parameter is one).  A call inside Z3 is not
     interruptible by the alarm-based timer, and over a quantified sequence Z3's
     own budget is not known to hold either: on a Rust-derived input (the
     constraint problem of an iterator's [Skip] loop with its loop invariant
     removed) the contradiction test's first such question never returned, grew
     past 8 GB
     and ignored SIGINT.  So [contradicts] tests the shape first
     ([may_not_return]) and does not ask when it fails.  [acquire_papp] asks
     under the budget only, because on that same input its 144 sequence-
     quantified questions were all decided, within 15 ms.

     WHAT A REFUSAL MEANS.  Each caller reads anything but [`Sat] (resp. a
     proved validity) as "no step": [contradicts] then reports no
     contradiction and [acquire_papp] derives no example.  A resolution step
     not taken derives nothing, so a refusal or an exhausted budget
     ([resolution_query_timeout]) can lose an answer -- the step was needed
     for a refutation -- and can never make one wrong. *)
  let resolution_queries_refused = Atomic.make 0

  let resolution_query_refused ~site phis =
    if List.exists phis ~f:Z3Smt.Z3interface.may_not_return then (
      Atomic.incr resolution_queries_refused;
      Debug.print
      @@ lazy
           (sprintf
              "[resolution] %s: not asked, the query may not return (%d refused \
               so far): %s"
              site
              (Atomic.get resolution_queries_refused)
              (Formula.str_of (Formula.and_of phis)));
      true)
    else false

  (* AN ACCOUNT OF THE PHASE'S SOLVER QUESTIONS BY CALL SITE.  With the
     phase-time report on, every question below is counted under
     [resolution-q/<site>/<outcome>] with its wall time, and once more under
     [.../slow] when it took a second or more, so that a run spending its
     resolution time in exhausted budgets says which question did so.  It only
     reads a clock and adds to a table; with the report off it is one test of
     a flag.

     Two diagnostics are read from the environment, off unless set.
     [COAR_RESOL_REASK] = [pooled], [fresh] or [both]: a question at a
     [check_sat] site that came back undecided is asked again, in a pooled
     context ([pooled]) or in a context of its own ([fresh]) or both, pooled
     first, under the same budget, and the second answer is counted under
     [resolution-q/<site>/reask-<mode>/<outcome>].  Nothing reads the second
     answer, so the step taken is the one the first answer decides.
     [COAR_RESOL_REASK_DUMP] = a path prefix: each re-ask's question is written
     as SMT-LIB2 to [<prefix><site>_<k>_<mode>_<j>.smt2]
     ([Z3interface.with_query_dump]).  Both allocate and force collections (a
     new context is preceded by a full major collection), so they change the
     run they observe. *)
  let resolution_reask =
    match Sys.getenv "COAR_RESOL_REASK" with
    | Some "pooled" -> [ false ]
    | Some "fresh" -> [ true ]
    | Some "both" -> [ false; true ]
    | _ -> []

  let resolution_reask_dump = Sys.getenv "COAR_RESOL_REASK_DUMP"
  let resolution_reask_count = Atomic.make 0

  (* an undecided answer is told apart by Z3's reason, reduced to letters,
     digits and dashes and cut at 40 characters, so that it stays one row
     name *)
  let reason_tag reason =
    String.map reason ~f:(fun c -> if Char.is_alphanum c then c else '-')
    |> fun s -> String.prefix s 40

  let sat_outcome = function
    | `Sat _ -> "sat"
    | `Unsat -> "unsat"
    | `Unknown reason -> "unknown:" ^ reason_tag reason
    | `Timeout -> "timeout"

  let valid_outcome = function
    | `Valid -> "valid"
    | `Invalid _ -> "invalid"
    | `Unknown _ -> "unknown"
    | `Timeout -> "timeout"
    | _ -> "other"

  let account_query ~site ~outcome f =
    if not !Common.PhaseTime.on then f ()
    else
      let t0 = Common.PhaseTime.now () in
      let record o =
        let dt = Common.PhaseTime.now () -. t0 in
        let row = sprintf "resolution-q/%s/%s" site o in
        Common.PhaseTime.add row dt;
        if Float.(dt >= 1.) then Common.PhaseTime.add (row ^ "/slow") dt
      in
      match f () with
      | r ->
          record (outcome r);
          r
      | exception e ->
          record "raised";
          raise e

  (* [check_sat] at a resolution site, accounted, and re-asked when
     [COAR_RESOL_REASK] says so (see above) *)
  let resolution_sat ~site ~timeout fenv phis =
    let ask ~fresh_solver () =
      Z3Smt.Z3interface.check_sat ~id ~timeout ~fresh_solver fenv phis
    in
    let r = account_query ~site ~outcome:sat_outcome (ask ~fresh_solver:false) in
    (match r with
    | `Unknown _ | `Timeout when not (List.is_empty resolution_reask) ->
        let k = Atomic.fetch_and_add resolution_reask_count 1 in
        List.iter resolution_reask ~f:(fun fresh_solver ->
            let mode = if fresh_solver then "fresh" else "pooled" in
            let go () =
              ignore
                (account_query
                   ~site:(sprintf "%s/reask-%s" site mode)
                   ~outcome:sat_outcome (ask ~fresh_solver))
            in
            match resolution_reask_dump with
            | Some prefix ->
                Z3Smt.Z3interface.with_query_dump
                  (sprintf "%s%s_%d_%s"
                     prefix
                     (String.map site ~f:(function
                       | ' ' | '(' | ')' | '/' -> '_'
                       | c -> c))
                     k mode)
                  go
            | None -> go ())
    | _ -> ());
    r

  (* With [solve_store_chain_eqs], a question is asked with each write chain
     equated to an array term solved for its variable ([Ast.StoreChainEq]): an
     equisatisfiable question whose models are the original's once the fresh
     variables it adds are dropped, which is done here, so a caller reads the
     answer as an answer about [phis]. *)
  let resolution_check_sat ?(refuse = true) ~site fenv phis =
    if refuse && resolution_query_refused ~site phis then `Unknown "refused"
    else if not config.solve_store_chain_eqs then
      resolution_sat ~site ~timeout:config.resolution_query_timeout fenv phis
    else
      let solve =
        if config.solve_store_chain_eqs_contextual then
          StoreChainEq.solve_contextual
        else StoreChainEq.solve
      in
      match solve phis with
      | _, [] ->
          resolution_sat ~site ~timeout:config.resolution_query_timeout fenv
            phis
      | phis', fresh -> (
          if !Common.PhaseTime.on then
            Common.PhaseTime.add
              (sprintf "resolution-q/%s/store-chain-solved" site)
              0.;
          let fresh = Set.Poly.of_list (List.map fresh ~f:fst) in
          match
            resolution_sat ~site ~timeout:config.resolution_query_timeout fenv
              phis'
          with
          | `Sat model ->
              `Sat
                (List.filter model ~f:(fun ((x, _), _) ->
                     not (Set.mem fresh x)))
          | r -> r)

  (* side condition of the example [contradicts] is about to derive; [true]
     unless the model fixed interpretation-dependent terms *)
  let residual = ref (Formula.mk_true ())


  (* the decided examples as atoms with their sources, built once per atom
     to prove or refute: [contradicts] is tried on every resolvent of that
     atom, and rebuilding these two sets inside it -- once per resolvent, so
     23,641 times over 5,025 atoms on seven resolution-heavy files -- was
     half of [contradicts]' time and all of it waste, the sets being the same
     for every resolvent of one atom *)
  let decided_atoms exs =
    Set.Poly.filter_map exs ~f:(fun (e, _src) ->
        insert_source (cite e, e) @@ ExClause.old_atom_of_uclause e)

  (* Does the model agree with what the resolution step already committed?

     A refutation has two substitutions.  [theta] is the resolution's own
     matcher: it says which term of the clause each parameter of the atom stands
     for, and which value each clause variable was matched to.  [sub] is the
     model a solver returned for the resolvent's remaining constraint.  The
     example is built from [sub] alone, and the derivation is recorded through
     [theta] -- so if the two disagree about a parameter, the example says
     something the clause it is recorded as coming from does not.

     The consistency check inside [contradicts] covers the parameters it is
     handed, and not the clause variables [theta] has already fixed.  On a
     contributed benchmark a clause whose argument was
     [mut(t(t(x1,x2), x3), t(t(x6,x7), x3))] -- [x3] in both the current and the
     final, so the two must agree -- produced an example giving them 0 and 3,
     because [theta] said [x3 = 0] and nothing carried that into the model.  The
     answer was a wrong [unsat] on a program that verifies.

     So here: close [theta] under itself, push the model through it, and ask
     whether the result can still be the parameter's value.  Clause variables the
     model does not mention stay free, which is why this asks for UNIFIABILITY
     and not equality -- the disagreement to catch is between two concrete
     terms.  A step that fails this is not recorded; declining loses examples
     and cannot invent one. *)
  let model_agrees_with_matcher theta sub atm =
    let theta_closed = Map.Poly.map theta ~f:(Term.subst theta) in
    let rec compatible t1 t2 =
      match (t1, t2) with
      | Term.Var _, _ | _, Term.Var _ -> true (* the model left it open *)
      | Term.FunApp (f1, ts1, _), Term.FunApp (f2, ts2, _) ->
          if List.length ts1 <> List.length ts2 then false
          else if Stdlib.(f1 <> f2) then
            (* two different constructors or two different literals cannot be
               the same value; anything else may differ only in notation *)
            match (f1, f2) with
            | T_dt.DTCons _, T_dt.DTCons _
            | T_int.Int _, T_int.Int _
            | T_bool.Formula _, _
            | _, T_bool.Formula _ ->
                false
            | _ -> true
          else List.for_all2_exn ts1 ts2 ~f:compatible
      | _ -> true
    in
    Set.for_all (Atom.fvs_of atm) ~f:(fun x ->
        match (Map.Poly.find theta_closed x, Map.Poly.find sub x) with
        | Some t_theta, Some t_sub -> compatible (Term.subst sub t_theta) t_sub
        | _ -> true)

  let contradicts ~positive ~negative ~graph fenv exi_senv
      (((uni_senv, c_pos, c_neg, c_phi), source), params, theta) =
    ignore graph;
    residual := Formula.mk_true ();
    try
      if verbose then
        Debug.print
        @@ lazy
             ("  checking contradiction: "
             ^ Clause.str_of exi_senv (uni_senv, c_pos, c_neg, c_phi));
      let eqs, srcs, premises =
        let f atms atm =
          let xs, srcs, exs =
            List.unzip3 @@ Set.to_list
            @@ Set.Poly.filter_map atms ~f:(fun (atm', (src, e)) ->
                let _param_senv (*ToDo*), atm' = Atom.refresh_tvar atm' in
                Option.map ~f:(fun x -> (x, src, e))
                @@ unifiable
                     (Logic.ExtTerm.to_old_atm exi_senv uni_senv atm, atm'))
          in
          if List.is_empty xs then raise E
          else (Formula.or_of xs, Set.Poly.union_list srcs, exs)
        in
        List.unzip3 @@ Set.to_list
        @@ Set.union
             (Set.Poly.map c_pos ~f:(f negative))
             (Set.Poly.map c_neg ~f:(f positive))
      in
      let srcs = Set.Poly.union_list srcs in
      (* the decided units that could falsify the other literals: the
         premises of the derived example, for its derivation record *)
      let premises = List.concat premises in
      let phi =
        Formula.and_of
        @@ Formula.mk_neg (Logic.ExtTerm.to_old_fml exi_senv uni_senv c_phi)
           :: eqs
      in
      (* what the derived example must satisfy for [KeepOpenParams] to open a
         value: the matching condition AND the equations tying each resolved
         atom parameter to the clause term it was unified with.  The condition
         alone is over the resolvent's variables, so a parameter whose clause
         term is not a lone variable of its class looks unconstrained without
         them and would be opened although the clause fixes it. *)
      let premise =
        Formula.and_of [ phi; KeepOpenParams.link_of ~params theta ]
      in
      let fvs = Formula.term_sort_env_of phi in
      let bvs = Set.filter fvs ~f:(fst >> Map.Poly.mem exi_senv >> not) in
      let cond =
        Formula.exists (Set.to_list bvs)
          phi (* unbound variables are non-predicate function variables *)
      in
      if verbose then
        Debug.print
        @@ lazy
             ("    sufficient condition: " ^ Formula.str_of cond ^ " is valid?");
      Option.map ~f:(fun (r, srcs) -> (r, srcs, premises, !residual, premise))
      @@ insert_source (Set.union source srcs)
      @@
      let dms =
        Set.Poly.of_list @@ List.map ~f:fst @@ LogicOld.get_dummy_term_senv ()
      in
      if Set.exists (Set.Poly.map ~f:fst bvs) ~f:(Set.mem dms) then (
        (* a derivation thrown away for containing a position nothing bound.
           Counted rather than described because a plan was once built on the
           belief that this is where generality goes, and a counter here
           returned zero on the input it was built for. *)
        PCSatCommon.GeneralityMonitor.lose Resolution
          "derivation-discarded-for-a-dummy" 1;
        (*ToDo*) None)
      else if Set.eqlen fvs bvs then (
        (* without non-predicate function variables*)
        match resolution_check_sat ~site:"contradicts" fenv [ phi ] with
        | `Sat model ->
            if verbose then Debug.print @@ lazy "    yes";
            let sub =
              (* A Z3 model describes every symbol its solver knows, and the
                 solvers are pooled and reused, so the model can carry
                 declarations left by an earlier query -- on one run of
                 [benchmarks/CHC/ADTs/list_x_append_11.smt2] a query over
                 [$1:X ; $2:X] came back with a model over [$1:X List ;
                 $2:X List ; $2:X ; $1:X ; x0:X List ; x1:X List ; x2:X List].
                 The substitution below is keyed by *name*, because that is what
                 a term substitution is keyed by, so a stale entry at another
                 sort collides with the one this query asked about: the process
                 used to die here with "Map.of_alist_exn: duplicate key", and
                 picking either of the two would silently put a list where an
                 element belongs.  So drop an entry that shadows a name of this
                 query at a sort this query does not use.  Entries for names the
                 query never mentions are kept: they cost nothing here and the
                 parameter map substituted below may still use them. *)
              (* THE SUBSTITUTION MAY ONLY SPEAK ABOUT WHAT THE QUERY ASKED,
                 for the reason spelled out at the other site that does this: a
                 pooled solver's model describes every symbol its context knows,
                 the substitution is keyed by NAME, and it is applied to terms
                 whose variables the query need not mention, so a left-over
                 entry replaces one of them by a value of the wrong sort.  The
                 filter used to run only when the map would otherwise collide,
                 which covers the case with a duplicate to notice and misses the
                 one that matters -- the stale entry present and the right one
                 absent.  It is unconditional.

                 An unconditional filter was tried once before and cost 14% more
                 CEGIS iterations over 123 files, but that version decided which
                 entry a query "uses" by comparing sorts with polymorphic
                 compare, which does not order a datatype reliably and so
                 dropped entries it should have kept.  This one compares the
                 PRINTED sort. *)
              (* the environment the substitution will be APPLIED to: the
                 query's variables and the CLAUSE's, since the caller
                 substitutes into the clause's atom *)
              LogicOld.model_subst ~freshvar:true model
                ~target:
                  (Set.union fvs
                     (Set.Poly.map ~f:(fun (x, so) ->
                          (x, Logic.ExtTerm.to_old_sort so))
                     @@ Map.to_set uni_senv))
            in
            (* what [phi] still says once the model's values are in: over
               interpreted symbols it is [true]; a residue can only be about
               interpretation-dependent terms ([tl nil = nil]), and the derived
               example must carry it as its side condition rather than assert
               the literal in every model *)
            let sub =
              (* The model is one solution of the matching condition, and a
                 solver picks a value for everything the query constrains
                 whether or not the constraint forces it -- so the example comes
                 out carrying numbers that are no part of what was derived, and
                 two examples that mean the same thing become different atoms
                 and never collide.  On one input the chain of a refutation is
                 [10,20] to [0,20] to [0,0] and the loop does unroll it, with a
                 different arbitrary tail each round, and the example set stays
                 satisfiable for that reason alone.

                 With this on, every variable the condition leaves open becomes
                 a parameter instead, and the condition itself travels as the
                 example's side condition below.  That is what the resolution
                 actually concluded -- these conflict *if* the condition holds --
                 rather than one instance of it. *)
              (* two independent halves.  [unify_parameters] realises the
                 matching equations that a binding can realise, which is what
                 lets one example's parameter meet another's;
                 [generalise_matching] then turns what is left open into
                 parameters rather than taking the model's values for them, and
                 is the half measured to cost answers. *)
              let bound =
                if not config.unify_parameters then Map.Poly.empty
                else
                  (* [params], not [fvs].  [fvs] is the free variables of the
                     matching condition, which are the CLAUSE's and are
                     universally quantified -- binding one restricts the clause.
                     [params] is what the caller computed as open: the example
                     atom's variables that are neither unknowns nor dummies,
                     which is what an example is universally quantified over and
                     what may be bound to another example's.  Written against
                     [fvs] first, this made zero bindings and the derived
                     examples were identical with the flag on and off. *)
                  fst @@ split_bindings params phi
              in
              let sub =
            (* [force_merge] fails when the two disagree, and they do: at the
               other site [sub] is still empty when this runs, but here it
               already holds the model's values, and a variable the model fixed
               is also one a binding wants.  The model's value is kept, because
               it is the one the rest of this derivation was built against;
               dropping it for a binding is what raised [Failure force_merge]
               and ended the run. *)
            Map.Poly.merge sub bound ~f:(fun ~key:_ -> function
              | `Left v | `Right v -> Some v
              | `Both (v, _) -> Some v)
          in
              if not config.generalise_matching then sub
              else
                Set.fold fvs ~init:sub ~f:(fun acc (x, srt) ->
                    if Map.Poly.mem bound x then acc
                    else
                    if Sort.is_arrow srt then acc
                    else
                      Map.Poly.set acc ~key:x
                        ~data:
                          (Term.mk_var
                             (Ident.mk_fresh_dontcare (Ident.name_of_tvar x))
                             srt))
            in
            (* the same selective opening as at the other site, and it is sound
               here for a reason worth spelling out, because the check just
               below looks as though it forbids it.

               Opening a value puts a parameter into [residual], which is the
               derived example's guard.  A guard is DISCHARGED only when
               [ExAtom.of_old_atom_known_sat] allows it, which requires the
               guard to be GROUND and to mention no term the theory leaves open
               -- so a guard mentioning a fresh parameter is kept rather than
               discharged, and so is a ground guard over an open term, which the
               model shows satisfiable and not valid.  The check below is
               conditioned on the same two properties, because what it protects
               is that discharge: it establishes that the model really witnesses
               the condition, on which the discharge rests.  The two tests
               therefore complement each other exactly.  Ground and fixed by the
               theory: the check runs and the guard may be dropped.  Otherwise:
               no discharge, and
               nothing for the check to protect -- the example still says
               [cond => +-P(t)], which holds whether or not the model was a
               genuine witness, since a condition no model satisfies makes it
               vacuous. *)
            let sub = generalise_invented sub in
            residual := Evaluator.simplify (Formula.subst sub phi);
            (* THE MODEL IS THE WITNESS, SO CHECK THAT IT IS ONE.  Everything
               below treats the model returned above as a witness that the
               matching condition holds -- a derived example's guard over
               symbols the theory fixes is discharged on exactly that ground,
               with no further query (a residue over a term the theory leaves
               open passes this check and is kept as the guard, since the model
               shows it satisfiable and not valid).  The
               note above says what the residue may be: over interpreted symbols
               it is [true], and anything left can only be about a term the
               theory leaves open, such as a selector on the wrong constructor.
               A residue that is ground, mentions no such term, and is still not
               [true] therefore means the "model" does not satisfy the formula
               it was returned for, and every conclusion drawn from it is void.

               That is not hypothetical.  Z3 4.15.2 answers [sat] to an equality
               between two constant-array literals over a datatype index -- a
               finite index domain, the fragment its array procedure does not
               cover -- and answers [sat] to the negation as well; asked for the
               model it offers, it reports the two arrays differing at the very
               index the equality constrains.  A resolution step licensed by
               that [sat] derived a negative example that does not follow, and a
               satisfiable constrained Horn problem answered [unsat].  Declining
               here loses an answer where the residue is true but not provably
               so, which is the safe direction; asserting one is not.  Z3 5.1.0
               answers that equality correctly, and this check stays whatever
               the version: it costs one evaluation and holds of any model any
               solver returns. *)
            if
              (not (Formula.is_true !residual))
              && Set.is_empty (Formula.term_sort_env_of !residual)
              && not (ClauseOld.interpretation_dependent !residual)
            then (
              if verbose then
                Debug.print
                @@ lazy
                     ("    no: the model does not satisfy the condition --                        residue " ^ Formula.str_of !residual);
              raise E);
            let theta = Map.Poly.map theta ~f:(Term.subst sub) in
            Some
              (Map.Poly.merge sub theta ~f:(fun ~key:_x -> function
                | `Left v | `Right v -> Some v
                | `Both (v1, v2) ->
                    if Stdlib.(v1 = v2) then Some v1
                    else if config.keep_model_over_matcher then
                      (* The sibling site that turns a model into an example
                         keeps the model's value here, with the reason that the
                         rest of the derivation was built against it. This one
                         demanded the two be SYNTACTICALLY equal and threw the
                         whole step away otherwise -- which is strictly stronger
                         than the compatibility test that runs afterwards and
                         that exists for exactly this disagreement, and it fires
                         first, so a step the later test would have accepted is
                         never offered to it. Measured on one input: the
                         satisfiability check said yes and the step was
                         discarded on the next line, twenty times. Keeping the
                         model's value hands the step on; a genuine
                         incompatibility is still caught, because the later test
                         asks whether the model can be the parameter's value at
                         all rather than whether it is written the same way. *)
                      Some v1
                    else
                      (*failwith (Ident.name_of_tvar x ^ ":" ^ LogicOld.Term.str_of v1 ^ ":" ^ LogicOld.Term.str_of v2)*)
                      raise E))
        | _ ->
            if verbose then Debug.print @@ lazy "    no";
            None)
      else if Set.are_disjoint (Set.Poly.map ~f:fst bvs) params then
        (* with function variables and without parameters *)
        if
          Evaluator.is_valid
            (fun phi ->
              (not (resolution_query_refused ~site:"contradicts (valid)" [ phi ]))
              && account_query ~site:"contradicts-valid"
                   ~outcome:(fun b -> if b then "valid" else "not-valid")
                   (fun () ->
                     Z3Smt.Z3interface.is_valid ~id
                       ~timeout:config.resolution_query_timeout fenv phi))
            cond
        then
          let _ = if verbose then Debug.print @@ lazy "    yes!" in
          Some theta
        else
          let _ = if verbose then Debug.print @@ lazy "    no!" in
          None
      else None
    with E ->
      if verbose then Debug.print @@ lazy "    unification failed";
      None

  let contradicts_assuming_pos ~dpos ~dneg ~graph fenv exi_senv cs
      ((param_senv, atm), source) =
    let dms =
      Set.Poly.of_list @@ List.map ~f:fst @@ LogicOld.get_dummy_term_senv ()
    in
    let params =
      Set.filter (Atom.fvs_of atm) ~f:(fun x ->
          (not (Map.Poly.mem exi_senv x)) && not (Set.mem dms x))
    in
    ClauseGraph.resolve_one_step_all
      ~print:(if verbose then Debug.print ~id:None else fun _ -> ())
      (Set.Poly.singleton
         ( (Logic.of_old_sort_env_map param_senv, Logic.ExtTerm.of_old_atom atm),
           source ))
      Set.Poly.empty exi_senv cs
    |> fun resolvents ->
    let positive = decided_atoms dpos and negative = decided_atoms dneg in
    resolvents
    |> Set.find_map ~f:(fun (c, sub, origin) ->
        Option.map ~f:(fun (r, srcs, premises, cond, premise) ->
            (r, srcs, origin, sub, premises, cond, premise))
        @@ contradicts ~positive ~negative ~graph fenv exi_senv
             ( c,
               params,
               (* all parameters need to be substituted *)
               Map.of_set_exn
               @@ Set.Poly.map params ~f:(fun x ->
                   ( x,
                     match Map.Poly.find sub x with
                     | Some r -> r
                     | None -> (
                         Term.mk_dummy
                         @@
                         match Map.Poly.find param_senv x with
                         | Some s -> s
                         | None -> T_int.SInt (*ToDo*)) )) ))

  let contradicts_assuming_neg ~dpos ~dneg ~graph fenv exi_senv cs
      ((param_senv, atm), source) =
    let dms =
      Set.Poly.of_list @@ List.map ~f:fst @@ LogicOld.get_dummy_term_senv ()
    in
    let params =
      Set.filter (Atom.fvs_of atm) ~f:(fun x ->
          (not (Map.Poly.mem exi_senv x)) && not (Set.mem dms x))
    in
    ClauseGraph.resolve_one_step_all
      ~print:(if verbose then Debug.print ~id:None else fun _ -> ())
      Set.Poly.empty
      (Set.Poly.singleton
         ( (Logic.of_old_sort_env_map param_senv, Logic.ExtTerm.of_old_atom atm),
           source ))
      exi_senv cs
    |> fun resolvents ->
    let positive = decided_atoms dpos and negative = decided_atoms dneg in
    resolvents
    |> Set.find_map ~f:(fun (c, sub, origin) ->
        Option.map ~f:(fun (r, srcs, premises, cond, premise) ->
            (r, srcs, origin, sub, premises, cond, premise))
        @@ contradicts ~positive ~negative ~graph fenv exi_senv
             ( c,
               params,
               (* all parameters need to be substituted *)
               Map.of_set_exn
               @@ Set.Poly.map params ~f:(fun x ->
                   ( x,
                     match Map.Poly.find sub x with
                     | Some r -> r
                     | None -> (
                         Term.mk_dummy
                         @@
                         match Map.Poly.find param_senv x with
                         | Some s -> s
                         | None -> T_int.SInt (*ToDo*)) )) ))

  (* A parameter the incoming example already had is a position the VALIDATOR
     left open, because the model that produced that example did not assign it.
     The resolution's substitution is built total, so it has a value for such a
     position whether or not the derivation needed one, and substituting closes
     it: an example arrives as [p(..., $1)] and is stored as [p(..., empty)].
     Measured on one input, every parameter that arrived open was closed this
     way -- two of two.

     What the derivation actually concluded is [p(..., $1)] TOGETHER WITH
     [$1 = empty], and those are not the same thing to a consumer.  The atom is
     what labeling and resolution key on, so keeping it [p(..., $1)] lets two
     examples derived at different values be the SAME atom, with the difference
     in their guards; substituting makes them two atoms that can never meet.
     So the equation is moved to the condition instead of applied to the atom. *)
  let keep_open_params ~sub ~cond ~phi atm =
    (* [phi] is the derivation's premise before the model's substitution [sub]
       (for a resolution step: the matching condition and the equations tying
       the resolved atom's parameters to the clause); [cond] is [phi] under
       [sub], simplified.  A class of equal-valued variables is opened as one
       parameter only when the premise holds for every value of it, which is
       the contract of [KeepOpenParams.open_classes].

       The first version of this dropped every atom variable the SUBSTITUTED
       condition does not mention, and a substituted condition mentions none of
       the substitution's variables, so every parameter was opened whether the
       derivation constrained it or not.  The second tested the matching
       condition alone, which is over the resolvent's variables and does not
       mention the resolved atom's parameters: a parameter whose clause term was
       a compound term, or a variable of another class, passed vacuously, and a
       negative example claimed its atom false at every value of a position the
       clause and the parents had fixed. *)
    let open_vars = Set.Poly.map ~f:fst @@ Atom.term_sort_env_of atm in
    let on_class cls value ok =
      Debug.print
      @@ lazy
           (sprintf "  [keep_open_params] {%s} = %s: %s"
              (String.concat ~sep:"," (List.map cls ~f:Ident.name_of_tvar))
              (Term.str_of value)
              (if ok then "opened" else "kept"))
    in
    let sub' = KeepOpenParams.open_classes ~on_class ~open_vars ~premise:phi sub in
    if phys_equal sub' sub then (sub, cond)
    else (sub', Evaluator.simplify (Formula.subst sub' phi))

  (* A derived example is normalised before its parameters get their canonical
     names, so the sign [normalize] gives an equation depends on the fresh names
     of that derivation, and the same example reached twice can be spelled
     [x - e = 0] once and [e - x = 0] the other time and kept as two.  Resolving
     against the problem's own clauses makes that multiplicative: a recursive
     clause whose head carries an equation per step, such as a list membership
     test [(= x e) \/ z], turns each positive example into one per sign choice,
     so the set doubled every round (1, 5, 4, 7, 12, 20, 38, 72, 144, 279
     examples added per round on a list-membership input; eight of round five's
     twelve were one fact under eight spellings).  Fixing the signs after the
     renaming merges them.  It is applied only where that site is on, so a run
     without it keeps the spelling -- and hence the trajectory -- it had. *)
  let canon_derived_signs cl =
    if config.resolve_against_problem_clauses then ExClause.canon_eq_signs cl
    else cl

  let prove ~dpos ~dneg ~graph fenv exi_senv cs ((param_senv, atm), source) =
    match
      contradicts_assuming_neg ~dpos ~dneg ~graph fenv exi_senv cs
        ((param_senv, atm), source)
    with
    | Some (sub, source', origin, theta, premises, cond, premise) ->
        let sub =
          (*ToDo: is this enough?*) Map.Poly.map sub ~f:(Term.subst sub)
        in
        let sub_ex, cond =
          if config.keep_example_params then
            keep_open_params ~sub ~cond ~phi:premise atm
          else (sub, cond)
        in
        let via = clause_subst exi_senv origin theta sub_ex in
        Debug.print
        @@ lazy
             ("  added as a positive example with: "
             ^ LogicOld.TermSubst.str_of sub);
        let dms =
          Set.Poly.of_list @@ List.map ~f:fst @@ LogicOld.get_dummy_term_senv ()
        in
        if false then
          print_endline
          @@ LogicOld.str_of_sort_env_list LogicOld.Term.str_of_sort
               (LogicOld.get_dummy_term_senv ());
        let unknowns = Set.union dms @@ Map.key_set exi_senv in
        if not (model_agrees_with_matcher theta sub atm) then (
          Debug.print
          @@ lazy
               "  NOT added as a positive example: the model disagrees with \
                the resolution's own matcher";
          dpos)
        else
          let cl =
            canon_derived_signs @@ ExClause.normalize_params unknowns
            @@ ExClause.mk_unit_pos
            @@ (let sub = sub_ex in
                ExAtom.of_old_atom_known_sat ~bvs:dms exi_senv
                  (Formula.subst sub cond)
                @@ Atom.subst sub atm)
          in
          PCSatCommon.GeneralityMonitor.(
            if on () then
              use Resolution "derived-examples-still-parametric"
                (Set.count (ExClause.exatoms_of cl) ~f:ExAtom.is_ppapp));
          Debug.print @@ lazy ("  add positive example " ^ ExClause.str_of cl);
          !record cl ~via:(Some origin) ~premises via;
          Set.add dpos (cl, source')
    | None -> dpos

  let refute ~dpos ~dneg ~graph fenv exi_senv cs ((param_senv, atm), source) =
    match
      contradicts_assuming_pos ~dpos ~dneg ~graph fenv exi_senv cs
        ((param_senv, atm), source)
    with
    | Some (sub, source', origin, theta, premises, cond, premise) ->
        let sub =
          (*ToDo: is this enough?*) Map.Poly.map sub ~f:(Term.subst sub)
        in
        let sub_ex, cond =
          if config.keep_example_params then
            keep_open_params ~sub ~cond ~phi:premise atm
          else (sub, cond)
        in
        let via = clause_subst exi_senv origin theta sub_ex in
        Debug.print
        @@ lazy
             ("  added as a negative example with: "
             ^ LogicOld.TermSubst.str_of sub);
        let dms =
          Set.Poly.of_list @@ List.map ~f:fst @@ LogicOld.get_dummy_term_senv ()
        in
        if false then
          print_endline
          @@ LogicOld.str_of_sort_env_list LogicOld.Term.str_of_sort
               (LogicOld.get_dummy_term_senv ());
        let unknowns = Set.union dms @@ Map.key_set exi_senv in
        if not (model_agrees_with_matcher theta sub atm) then (
          Debug.print
          @@ lazy
               "  NOT added as a negative example: the model disagrees with \
                the resolution's own matcher";
          dneg)
        else
          let cl =
            canon_derived_signs @@ ExClause.normalize_params unknowns
            @@ ExClause.mk_unit_neg
            @@ (let sub = sub_ex in
                ExAtom.of_old_atom_known_sat ~bvs:dms exi_senv
                  (Formula.subst sub cond)
                @@ Atom.subst sub atm)
          in
          PCSatCommon.GeneralityMonitor.(
            if on () then
              use Resolution "derived-examples-still-parametric"
                (Set.count (ExClause.exatoms_of cl) ~f:ExAtom.is_ppapp));
          Debug.print @@ lazy ("  add negative example " ^ ExClause.str_of cl);
          (* the refuting clause's read indices, beside the derived example
             and filed under its atom only; a failure to convert the clause
             costs the record, never the example *)
          let inherited =
            inherit_goal_reads exi_senv ~source:source' ~origin ~via cl
          in
          (if config.record_goal_reads && inherited = 0 then
             match Set.to_list cl.ExClause.negative with
             | [ derived ] -> (
                 match GoalReads.key_of_atom derived with
                 | None -> ()
                 | Some target -> (
                     match Clause.to_old_formula exi_senv origin with
                     | phi_origin ->
                         let n =
                           GoalReads.record_instance ~target ~allow_step:true
                             phi_origin via
                         in
                         if n > 0 then
                           Debug.print
                           @@ lazy
                                (sprintf "  [goal reads] recorded for %s" target)
                     | exception exn_ when not (Common.Timer.is_async exn_) -> ()))
             | _ -> ());
          !record cl ~via:(Some origin) ~premises via;
          Set.add dneg (cl, source')
    | None -> dneg

  let acquire_papp ?(vary_arrays = false) ~graph fenv parametric ucs pure atm =
    ignore graph;
    let phi = Evaluator.simplify_neg pure in
    Debug.print
    @@ lazy
         (sprintf "checking (%s | %s)" (Formula.str_of phi)
            (Atom.str_of ~priority:0 atm));
    let dms =
      Set.Poly.of_list @@ List.map ~f:fst @@ LogicOld.get_dummy_term_senv ()
    in
    if Set.exists (Formula.tvs_of phi) ~f:(Set.mem dms) then (*ToDo*) None
    else
      let enforce_new, srcs =
        if config.enforce_new then
          let phis, srcs =
            let x, _, ts, _ = Atom.let_pvar_app atm in
            List.unzip @@ Set.to_list
            @@ Set.Poly.filter_map ~f:(fun (((y, _), ts'), src) ->
                if Stdlib.(x = y) then
                  Some
                    ( Formula.or_of
                      @@ List.map2_exn ts ts' ~f:(fun t t' ->
                          (*ToDo: here t' is assumed to have no variable*)
                          assert (Set.is_empty @@ Term.tvs_of t');
                          Formula.neq t t'),
                      src )
                else None)
            @@ Set.Poly.filter_map ucs ~f:(fun (ex, _src) ->
                insert_source (cite ex) @@ ExClause.papp_of_uclause ex)
          in
          (Formula.and_of phis, Set.Poly.union_list srcs)
        else (Formula.mk_true (), Set.Poly.empty)
      in
      match
        (* budgeted, not refused by shape: see [resolution_check_sat] *)
        resolution_check_sat ~refuse:false ~site:"acquire_papp" fenv
          [ phi; enforce_new ]
      with
      | `Sat model ->
          let sub =
            (* THE SUBSTITUTION MAY ONLY SPEAK ABOUT WHAT THE QUERY ASKED.
               A pooled Z3 solver's model describes every symbol its context
               knows, which includes declarations left by earlier queries on the
               same instance; the substitution below is keyed by NAME, and it is
               applied to the atom, whose variables the query need not mention
               at all.  A left-over entry for one of those then replaces a
               variable by a value of the WRONG SORT and nothing notices: on a
               contributed ADT benchmark an [$1] of the element sort was
               replaced by [nil], giving [cons nil nil], and the solver rejected
               the next query it appeared in -- an uncaught exception rather
               than a verdict.

               So an entry is kept only when the query mentions that name AT
               THAT SORT.  A variable of the atom the query says nothing about
               is not a don't-care to be filled in: it stays a variable, which
               is what makes it a parameter of the derived example.  The sorts
               are compared as PRINTED, because a sort can be a datatype and
               polymorphic compare does not order those reliably. *)
            (* the environment the substitution will be APPLIED to, which is
               the query's variables together with the atom's: the atom is what
               the entries are substituted into, and its variables need not
               occur in the query at all *)
            LogicOld.model_subst ~freshvar:parametric model
              ~target:
                (Set.union
                   (Formula.term_sort_env_of
                   @@ Formula.and_of [ phi; enforce_new ])
                   (Atom.term_sort_env_of atm))
          in
          (* as in [contradicts]: the part of the constraint the model leaves
             undecided is interpretation-dependent and becomes the example's
             side condition *)
          (* both halves here too, and for the reason the comment below gives:
             changing one of the two sites leaves the negative examples
             parametric and the positive ones concrete, so they still cannot
             meet and a measurement of it tests nothing *)
          let bound =
            if not config.unify_parameters then Map.Poly.empty
            else
              fst
              @@ split_bindings
                   (Set.Poly.map ~f:fst @@ Formula.term_sort_env_of phi)
                   phi
          in
          let sub =
            (* [force_merge] fails when the two disagree, and they do: at the
               other site [sub] is still empty when this runs, but here it
               already holds the model's values, and a variable the model fixed
               is also one a binding wants.  The model's value is kept, because
               it is the one the rest of this derivation was built against;
               dropping it for a binding is what raised [Failure force_merge]
               and ended the run. *)
            Map.Poly.merge sub bound ~f:(fun ~key:_ -> function
              | `Left v | `Right v -> Some v
              | `Both (v, _) -> Some v)
          in
          let sub =
            (* and, as in [contradicts], the model is one solution of a
               condition rather than the condition itself.  Without this the two
               sites disagree: the negative examples come out parametric and the
               positive ones keep the solver's arbitrary values, so the two
               still cannot meet -- which is what a refutation needs them to
               do. *)
            if not config.generalise_matching then sub
            else
              Set.fold (Formula.term_sort_env_of phi) ~init:sub
                ~f:(fun acc (x, srt) ->
                  if Sort.is_arrow srt || Map.Poly.mem bound x then acc
                  else
                    Map.Poly.set acc ~key:x
                      ~data:
                        (Term.mk_var
                           (Ident.mk_fresh_dontcare (Ident.name_of_tvar x))
                           srt))
          in
          let sub = generalise_invented sub in
          let sub =
            (* only for a positive example: the arrays the condition reads only
               through [select] get a default of their own, the model's values
               kept at the read positions; the condition is re-evaluated on the
               result and the old model kept unless it is still [true].  The
               novelty filter [enforce_new] is not part of the licence and is
               not re-checked. *)
            let sub', outcome =
              PCSatCommon.VaryArrays.apply ~on:vary_arrays ~cond:phi ~atm sub
            in
            if vary_arrays then
              Debug.print
              @@ lazy
                   ("  [vary derived arrays] "
                   ^ PCSatCommon.VaryArrays.str_of_outcome outcome);
            sub'
          in
          Some (sub, srcs, Evaluator.simplify (Formula.subst sub phi))
      | _ -> None

  (* A resolvent with several applications of ONE predicate on one side is
     dropped by the fold below, which only turns a UNIT clause into an example.
     That is where most of the negative information goes on a goal whose body
     is not a single application: a counterexample to [p2 /\\ p5 /\\ p6 => false]
     enters as three literals, resolution removes [p5] and [p6], and what is
     left is [not p2(t1) \\/ not p2(t2)] -- two applications of one predicate at
     arguments a solver chose, which never collapse and so never become the
     negative example the refutation needs.

     They collapse under a CONDITION, and [unifiable] already computes it: if
     [c] makes the arguments agree then the two literals are one literal, and
     the clause [not a1 \\/ not a2 \\/ pure] is [not a1 \\/ pure] wherever [c]
     holds -- which as a clause is [not a1 \\/ pure \\/ not c].  So the collapse
     is exactly a rewrite of the pure part to [pure \\/ not c], and the result is
     a unit clause the existing path turns into a parametric example, guarded by
     what the collapse assumed.  Nothing here needs a new kind of example: the
     representation carried a guard already.

     It is not restricted to two.  Every application is unified against the
     first and the conditions are conjoined, so [n] of them collapse at once,
     and the guard is the one formula under which all [n] agree. *)
  let collapse_same_pred fenv exi_senv (((uni_senv, pos, neg, pure), source), rest) =
    let cond_of atms =
      match Set.to_list atms with
      | (_ :: _ :: _ as l) ->
          let a = List.hd_exn l in
          let old = Logic.ExtTerm.to_old_atm exi_senv uni_senv in
          let a0 = old a in
          let conds =
            List.map (List.tl_exn l) ~f:(fun b -> unifiable (a0, old b))
          in
          if List.exists conds ~f:Option.is_none then (
            None)
          else
            let c = Formula.and_of @@ List.filter_map conds ~f:Fn.id in
            (* [unifiable] returns the equations under which the arguments
               agree and does NOT ask whether they can: it compares two
               constants only when they ARE the argument, so
               [seq.unit 6 = seq.unit 8] comes back as an equation to satisfy
               rather than as a failure.  Collapsing on an unsatisfiable
               condition produces a clause whose new pure part is valid, which
               is a clause that says nothing -- so the condition is checked
               here, once, before anything is rewritten. *)
            (match
               resolution_sat ~site:"collapse" ~timeout:(Some 1000) fenv [ c ]
             with
            | `Sat _ ->
                Some (a, c)
            | _ ->
                None)
      | _ -> None
    in
    let rebuild keep_pos (a, c) =
      let pure' =
        Logic.ExtTerm.of_old_formula @@ Formula.mk_or
             (Logic.ExtTerm.to_old_fml exi_senv uni_senv pure)
             (Formula.mk_neg c)
      in
      let pos', neg' =
        if keep_pos then (Set.Poly.singleton a, Set.Poly.empty)
        else (Set.Poly.empty, Set.Poly.singleton a)
      in
      (((uni_senv, pos', neg', pure'), source), rest)
    in
    if Set.length pos > 1 && Set.is_empty neg then
      match cond_of pos with Some r -> rebuild true r | None -> (((uni_senv, pos, neg, pure), source), rest)
    else if Set.length neg > 1 && Set.is_empty pos then
      match cond_of neg with Some r -> rebuild false r | None -> (((uni_senv, pos, neg, pure), source), rest)
    else (((uni_senv, pos, neg, pure), source), rest)

  let acquire fenv exi_senv ~dpos ~dneg ~und ~graph cs =
    let cs =
      if config.collapse_same_pred then
        Set.Poly.map cs ~f:(collapse_same_pred fenv exi_senv)
      else cs
    in
    if Set.is_empty cs then (dpos, dneg, und)
    else (
      Debug.print @@ lazy "********** one-step resolved constraints ***********";
      Debug.print
      @@ lazy
           (PCSP.Problem.str_of
              (PCSP.Problem.of_clauses ~params:(PCSP.Params.make exi_senv)
              @@ Set.Poly.map ~f:(fst >> fst) cs));
      Debug.print @@ lazy "";
      Set.fold cs ~init:(dpos, dneg, und)
        ~f:(fun
            (dpos, dneg, und)
            (((uni_senv, pos, neg, pure), source), (theta, origin))
          ->
          match (Set.to_list pos, Set.to_list neg) with
          | [ atm ], [] | [], [ atm ] ->
              let atm = Logic.ExtTerm.to_old_atm exi_senv uni_senv atm in
              let pure = Logic.ExtTerm.to_old_fml exi_senv uni_senv pure in
              let tvs = Set.union (Atom.tvs_of atm) (Formula.tvs_of pure) in
              let fnvs = Set.inter tvs (Map.key_set exi_senv) in
              (*if
                Set.exists
                  (Set.Poly.union_list [ Formula.pvs_of pure; Atom.pvs_of atm ]
                  |> Set.Poly.map ~f:Ident.pvar_to_tvar)
                  ~f:(PCSP.Problem.is_tot_pred APCSP.problem)
                || true
              then (dpos, dneg, und)
              else*)
              if Set.is_empty fnvs then (
                (* without function variables *)
                let parametric =
                  config.parametric_examples && Fn.non Set.is_empty tvs
                in
                if Set.is_empty neg then (
                  if
                    (* positive unit clause *)
                    parametric && config.add_unit_clause_as_is
                  then assert false
                  else
                    match
                      acquire_papp
                        ~vary_arrays:config.vary_derived_array_defaults ~graph
                        fenv parametric dpos pure atm
                    with
                    | None -> (dpos, dneg, und)
                    | Some (sub, src, cond) ->
                        let dms =
                          Set.Poly.of_list @@ List.map ~f:fst
                          @@ LogicOld.get_dummy_term_senv ()
                        in
                        if false then
                          print_endline
                          @@ LogicOld.str_of_sort_env_list
                               LogicOld.Term.str_of_sort
                               (LogicOld.get_dummy_term_senv ());
                        let sub, cond =
                          if config.keep_example_params then
                            keep_open_params ~sub ~cond
                            ~phi:(Evaluator.simplify_neg pure) atm
                          else (sub, cond)
                        in
                        let phi = Atom.subst sub atm in
                        let cl =
                          canon_derived_signs @@ ExClause.normalize_params
                            (Set.union dms @@ Map.key_set exi_senv)
                          @@ ExClause.mk_unit_pos
                          @@ ExAtom.of_old_atom_known_sat ~bvs:dms exi_senv cond
                               phi
                        in
                        if Set.exists (Atom.tvs_of phi) ~f:(Set.mem dms) then
                          (*ToDo*) (dpos, dneg, und)
                        else (
                          Debug.print
                          @@ lazy
                               ("  added as a positive example with: "
                               ^ LogicOld.TermSubst.str_of sub);
                          Debug.print
                          @@ lazy
                               ("  add positive example " ^ ExClause.str_of cl);
                          !record cl ~via:(Some origin) ~premises:[]
                            (clause_subst exi_senv origin theta sub);
                          (Set.add dpos (cl, Set.union src source), dneg, und)))
                else if
                  (* negative unit clause *)
                  parametric && config.add_unit_clause_as_is
                then assert false
                else
                  match acquire_papp ~graph fenv parametric dneg pure atm with
                  | None -> (dpos, dneg, und)
                  | Some (sub, src, cond) ->
                      let dms =
                        Set.Poly.of_list @@ List.map ~f:fst
                        @@ LogicOld.get_dummy_term_senv ()
                      in
                      if false then
                        print_endline
                        @@ LogicOld.str_of_sort_env_list
                             LogicOld.Term.str_of_sort
                             (LogicOld.get_dummy_term_senv ());
                      let sub, cond =
                        if config.keep_example_params then
                          keep_open_params ~sub ~cond
                            ~phi:(Evaluator.simplify_neg pure) atm
                        else (sub, cond)
                      in
                      let phi = Atom.subst sub atm in
                      let cl =
                        canon_derived_signs @@ ExClause.normalize_params
                          (Set.union dms @@ Map.key_set exi_senv)
                        @@ ExClause.mk_unit_neg
                        @@ ExAtom.of_old_atom_known_sat ~bvs:dms exi_senv cond
                             phi
                      in
                      if Set.exists (Atom.tvs_of phi) ~f:(Set.mem dms) then
                        (*ToDo*)
                        (dpos, dneg, und)
                      else (
                        Debug.print
                        @@ lazy
                             ("  added as a negative example with: "
                             ^ LogicOld.TermSubst.str_of sub);
                        Debug.print
                        @@ lazy ("  add negative example " ^ ExClause.str_of cl);
                        let via = clause_subst exi_senv origin theta sub in
                        ignore
                          (inherit_goal_reads exi_senv
                             ~source:(Set.union src source) ~origin ~via cl
                            : int);
                        !record cl ~via:(Some origin) ~premises:[] via;
                        (dpos, Set.add dneg (cl, Set.union src source), und)))
              else (* with function variables *) (dpos, dneg, und)
          | [], [] -> (
              let pure = Logic.ExtTerm.to_old_fml exi_senv uni_senv pure in
              let tvs = Formula.tvs_of pure in
              let fnvs = Set.inter tvs (Map.key_set exi_senv) in
              if Set.is_empty fnvs then
                (* without function variables *)
                (dpos, dneg, und)
              else
                (* with function variables *)
                match
                  ExClause.make exi_senv Set.Poly.empty Set.Poly.empty pure
                with
                | None -> (dpos, dneg, und)
                | Some cl ->
                    let dms =
                      Set.Poly.of_list @@ List.map ~f:fst
                      @@ LogicOld.get_dummy_term_senv ()
                    in
                    if false then
                      print_endline
                      @@ LogicOld.str_of_sort_env_list LogicOld.Term.str_of_sort
                           (LogicOld.get_dummy_term_senv ());
                    let unknowns = Set.union dms @@ Map.key_set exi_senv in
                    ( dpos,
                      dneg,
                      (*ToDo*)
                      Set.add und
                        ( canon_derived_signs
                          @@ ExClause.normalize_params unknowns cl,
                          source )
                    ))
          | _, _ -> (dpos, dneg, und)))

  (* Does a decided example settle this clause literal at EVERY value of the
     clause's parameters?  The literal is removed unconditionally, so an overlap
     is not enough -- two atoms that can be made equal are equal only there, and
     dropping the literal on that would assert what the example does not say and
     is a wrong refutation.  The question is therefore
     [forall (the literal's variables). exists (the example's parameters). args
     equal], which a renaming satisfies.  Quantified, so the query that cannot
     return is declined rather than asked, and an undecided answer is a no. *)
  let settled_by ~id fenv exi_senv senv lit examples =
    let lit_atm = Logic.ExtTerm.to_old_atm exi_senv senv lit in
    match Atom.let_pvar_app lit_atm with
    | exception exn_ when not (Common.Timer.is_async exn_) -> false
    | pvar, _, largs, _ ->
        Set.exists examples ~f:(fun ((param_senv, ex), _src) ->
            let ex_atm = Logic.ExtTerm.to_old_atm exi_senv param_senv ex in
            match Atom.let_pvar_app ex_atm with
            | exception exn_ when not (Common.Timer.is_async exn_) -> false
            | pvar', _, eargs, _ ->
                Ident.pvar_equal pvar pvar'
                && List.length largs = List.length eargs
                &&
                let eqs =
                  Formula.and_of @@ List.map2_exn largs eargs ~f:Formula.eq
                in
                let ex_params =
                  Set.to_list
                  @@ Set.filter (Formula.term_sort_env_of eqs) ~f:(fun (x, _) ->
                      Map.Poly.mem param_senv x)
                in
                let body = Formula.exists ex_params eqs in
                let rest =
                  Set.to_list
                  @@ Set.filter (Formula.term_sort_env_of body) ~f:(fun (x, _) ->
                      not (Map.Poly.mem exi_senv x))
                in
                let query = Formula.forall rest body in
                (not (Z3Smt.Z3interface.may_not_return query))
                &&
                match
                  account_query ~site:"settled-by" ~outcome:valid_outcome
                    (fun () ->
                      Z3Smt.Z3interface.check_valid ~id ~timeout:(Some 5000)
                        fenv query)
                with
                | `Valid ->
                    Debug.print
                    @@ lazy
                         (sprintf "  a decided example settles %s everywhere"
                            (Atom.str_of ~priority:0 lit_atm));
                    true
                | _ -> false)

  (* ------------------------------------------------------------------
     Aggressive positive-example generation.  It derives
     *positive* examples rather than waiting for the validator's
     counterexamples: [parametric_positive_examples] turns a clause that is a
     single positive literal with a false body into a parametric positive
     example; [forward_chain_one_query] and [forward_chain_enumerating] derive positives by
     resolving one step, the second by trying all argument pairs; and
     [reduction1] is the reduction the branch experimented with beside them.

     It is switched by [eager_positive_examples], off by default, so
     nothing changes until an input is measured to want it.  On the branch it
     ran behind [let adding_examples = true in if adding_examples then ...],
     an always-taken branch; a configuration field is what that was standing
     in for.
     ------------------------------------------------------------------ *)

  let parametric_positive_examples clauses =
    Debug.print @@ lazy "<Parametric Positive Examples>";

    let exi_senv = PCSP.Problem.senv_of APCSP.problem in

    let examples = ref [] in

    Set.iter clauses ~f:(fun cl ->
      Debug.print @@ lazy (sprintf "\n@ clause: %s" (Clause.str_of exi_senv cl));

      let uni_senv = Clause.sort_env_of cl in
      let (_, pos, neg, phi) = cl in

      Debug.print @@ lazy ("phi: " ^ (Logic.ExtTerm.str_of phi));

      if (Set.is_empty neg) && Logic.ExtTerm.is_false phi then
        if (Set.is_singleton pos) then
          let term = Set.nth pos 0 |> Option.value_exn in
          let term = Logic.ExtTerm.to_old_atom exi_senv uni_senv term [] in
          let atom = ExAtom.of_old_atom exi_senv (LogicOld.Formula.mk_true ()) term in
          let ex = ExClause.mk_unit_pos (ExAtom.normalize_params atom) in
          Debug.print @@ lazy ("add parametric example" ^ ExClause.str_of ex);
          (* let _ = Stdlib.read_line () in *)
          examples := (ex, [(ClauseGraph.Clause cl, true)]) :: !examples
    );

    Debug.print @@ lazy "</Parametric Positive Examples>\n";
    Set.Poly.of_list !examples

  (* The matching step: an atom's
     arguments paired with those of each known positive example of the same
     predicate, which the callers below turn into the equalities a derivation
     has to satisfy. *)
  let mk_eqs atom pred_pos pos_examples =
    let pred_name, vs = Logic.Term.let_var_app atom in
    List.iter vs ~f:(fun x ->
      Debug.print @@ lazy (Logic.ExtTerm.str_of x);
    );

    let ex_num = ref 0 in

    (* gather candidate arguments from positive examples for each predicate application position *)
    let pred_args = Set.fold pos_examples ~init:[] ~f:(fun acc ex ->
      ex_num := !ex_num + 1;

      Debug.print @@ lazy ("focusing: " ^ ExClause.str_of ex);
      assert (Set.is_empty ex.negative);
      assert (Set.is_singleton ex.positive);
      let ex = Option.value_exn @@ Set.nth ex.positive 0 in

      match ExAtom.pvar_of ex with
      | None -> acc
      | Some pred'_name ->
        let pred_name = Ident.str_of_tvar pred_name in
        let pred'_name = Ident.str_of_pvar pred'_name in
        Debug.print @@ lazy (sprintf "pred_name = %s, pred'_name = %s" pred_name pred'_name);
        if Stdlib.(pred_name <> pred'_name) then
          acc
        else begin
          Debug.print @@ lazy "here?";
          let args = Option.value_exn @@ ExAtom.args_of ex in
          let renamed = List.map args ~f:(fun arg ->
            Debug.print @@ lazy (sprintf "arg: %s" (LogicOld.Term.str_of arg));
            (match arg with
             | Var (Tvar tv, sym, info) ->
                (* [Term.t] is private now, so the node is rebuilt through the
                   smart constructor rather than by applying [Var] *)
                let tv = sprintf "%s###%d###%d" tv pred_pos !ex_num in
                LogicOld.Term.mk_var ~info (Ident.Tvar tv) sym
             | x -> x)) in
          acc @ [(renamed)]
        end
    )
    in
    (vs, pred_args)

  (* ONE RULE, TWO SEARCH STRATEGIES, and the pair below is the whole of the
     difference.  The rule is: apply a Horn clause forwards, with every body
     atom matched against an example already decided positive, and take its
     head.  What differs is how the matching is searched --
     [forward_chain_one_query] hands the solver a conjunction over body atoms
     of a disjunction over candidate matches and lets it choose, while
     [forward_chain_enumerating] enumerates the pairings and asks once per
     pairing through [forward_chain_by_pairing].  Both then add the same
     novelty condition, that the head derived is not one already known, which
     is the same idea as this module's own [enforce_new]. *)

  (* One forward-chaining step over
     *every* pairing of the clause's body atoms with known positives, rather
     than one pairing. *)
  let forward_chain_by_pairing clause vs pairs goal_constraint =
    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let uni_senv = Clause.sort_env_of clause in
    let (_, pos, _neg, body) = clause in
    let head_term = Set.nth pos 0 |> Option.value_exn in
    let orig = Logic.ExtTerm.neg_of body in
    let phi =
      Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv orig []
    in
    let phi = Evaluator.simplify phi in

    let fenv = vs.VersionSpace.fenv in

    let examples = ref [] in

    let rec iter assigns pairs =
      match pairs with
      | [] -> begin
        let result = resolution_sat ~site:"forward-pairing" ~timeout:config.eager_smt_timeout fenv [ phi; assigns; goal_constraint ] in
        match result with
        | `Sat model -> begin
          Debug.print @@ lazy "Sat";
          List.iter model ~f:(fun ((tv, _sort), t) ->
            let t_str = Option.value_map t ~default:"None" ~f:LogicOld.Term.str_of in
            Debug.print @@ lazy (sprintf "%s => %s" (Ident.str_of_tvar tv) t_str);
          );
          let sub = LogicOld.remove_dontcare ~freshvar:true model |> Map.Poly.of_alist_exn in
          let head_term = Logic.ExtTerm.to_old_term exi_senv uni_senv head_term [] in
          Debug.print @@ lazy (sprintf "head_term1: %s" (LogicOld.Term.str_of head_term));
          let head_term = LogicOld.Term.subst sub head_term in
          Debug.print @@ lazy (sprintf "head_term2: %s" (LogicOld.Term.str_of head_term));
          let head_term = Logic.ExtTerm.of_old_term head_term in
          Debug.print @@ lazy (sprintf "head_term3: %s" (Logic.ExtTerm.str_of head_term));
          let head_atom = Logic.ExtTerm.to_old_atom exi_senv uni_senv head_term [] in
          Debug.print @@ lazy (sprintf "head_atom: %s" (LogicOld.Atom.str_of head_atom));
          let head = ExAtom.of_old_atom exi_senv (LogicOld.Formula.mk_true ()) head_atom in
          let head = ExAtom.normalize head in
          let ex = ExClause.mk_unit_pos head in
          Debug.print @@ lazy ("obtained example:" ^ ExClause.str_of ex);
          examples := (ex, [(ClauseGraph.Clause clause, true)]) :: !examples;
          end
        | `Unsat -> Debug.print @@ lazy "Unsat"
        | _ -> Debug.print @@ lazy "Otherwise"
        end
      | ((pos_args, ex_args_list) :: xs) ->
        List.iter ex_args_list ~f:(fun ex_args ->
          let eqs = List.zip_exn pos_args ex_args in
          let assign =
            LogicOld.Formula.and_of @@
            List.map eqs ~f:(fun (a, b) ->
              let a = Logic.ExtTerm.to_old_term Map.Poly.empty uni_senv a [] in
              LogicOld.Formula.eq a b
            )
          in
          iter (LogicOld.Formula.mk_and assigns assign) xs
        )
    in
    iter (LogicOld.Formula.mk_true ()) pairs;
    !examples

  (* Forward chaining one step: a
     clause whose body atoms all match decided positives yields its head as a
     new positive example. *)
  let forward_chain_enumerating clauses vs =
    Debug.print @@ lazy "<Positive One Step 2>";

    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let (d_dpos, _, _) = VersionSpace.pos_neg_und_examples_of vs in

    Debug.print @@ lazy "<d_dpos>";
    Set.iter d_dpos ~f:(fun x ->
      Debug.print @@ lazy (ExClause.str_of x)
    );
    Debug.print @@ lazy "</d_dpos>";

    let clauses = Set.filter clauses ~f:(fun (cl:Clause.t) ->
      let (_, pos, _, _) = cl in
      not (Set.is_empty pos)
    ) in

    let examples = ref [] in
    Set.iter clauses ~f:(fun cl ->
      Debug.print @@ lazy (sprintf "\n@ clause: %s" (Clause.str_of exi_senv cl));
      let (_, pos, neg, _) = cl in

      let pred_pos = ref 0 in
      let pairs = Set.fold neg ~init:[] ~f:(fun acc n -> (* visiting each predicate application positions *)
        pred_pos := !pred_pos + 1;
        acc @ [mk_eqs n !pred_pos d_dpos]
      ) in

      let uni_senv = Clause.sort_env_of cl in
      let head_term = Set.nth pos 0 |> Option.value_exn in
      let (pos_args, ex_args_list) = mk_eqs head_term (-1) d_dpos in
      let goal_constraint =
        LogicOld.Formula.and_of @@
          List.map ex_args_list ~f:(fun ex_args ->
            let vars = List.filter ex_args ~f:LogicOld.Term.is_var in
            let to_be_bound = List.map vars ~f:(LogicOld.Term.let_var >> fst) in
            let eqs = List.zip_exn pos_args ex_args in
            let eq_f =
            LogicOld.Formula.and_of @@
            List.map eqs ~f:(fun (a, b) ->
              let a = Logic.ExtTerm.to_old_term Map.Poly.empty uni_senv a [] in
              LogicOld.Formula.eq a b
            ) in
            let bound_f = LogicOld.Formula.mk_exists to_be_bound eq_f in
            LogicOld.Formula.negate bound_f
          )
      in
      Debug.print @@ lazy (sprintf "goal constraint: %s" (LogicOld.Formula.str_of goal_constraint));

      let obtained = forward_chain_by_pairing cl vs pairs goal_constraint in
      examples := !examples @ obtained
    );

    Debug.print @@ lazy "</Positive One Step 2>";
    (* let _ = Stdlib.read_line () in *)
    List.iter !examples ~f:(fun (ex, src) ->
      let (g, _) = List.hd_exn src in
      let s = ClauseGraph.str_of_vertex exi_senv g in
      Debug.print @@ lazy (sprintf "ex: %s   from   %s" (ExClause.str_of ex) s);
    );
    Set.Poly.of_list !examples

  (* The same step in the branch's
     earlier form, kept beside its successor rather than replaced by it. *)
  let forward_chain_one_query clauses vs =
    Debug.print @@ lazy "<Positive One Step>";
    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let (d_dpos, d_dneg, d_und) = VersionSpace.pos_neg_und_examples_of vs in
    let fenv = vs.VersionSpace.fenv in

    Debug.print @@ lazy "<d_dpos>";
    Set.iter d_dpos ~f:(fun x ->
      Debug.print @@ lazy (ExClause.str_of x)
    );
    Debug.print @@ lazy "</d_dpos>";

    Debug.print @@ lazy "<d_dneg>";
    Set.iter d_dneg ~f:(fun x ->
      Debug.print @@ lazy (ExClause.str_of x)
    );
    Debug.print @@ lazy "</d_dneg>";

    Debug.print @@ lazy "<d_und>";
    Set.iter d_und ~f:(fun x ->
      Debug.print @@ lazy (ExClause.str_of x)
    );
    Debug.print @@ lazy "</d_und>\n";

    let clauses = Set.filter clauses ~f:(fun (cl:Clause.t) ->
      let (_, pos, _, _) = cl in
      not (Set.is_empty pos)
    ) in

    let examples = ref [] in
    Set.iter clauses ~f:(fun cl ->
      Debug.print @@ lazy (sprintf "\n@ clause: %s" (Clause.str_of exi_senv cl));
      let (_, pos, neg, body) = cl in
      let pred_pos = ref 0 in
      let pairs = Set.fold neg ~init:[] ~f:(fun acc n ->
        pred_pos := !pred_pos + 1;
        acc @ [mk_eqs n !pred_pos d_dpos]
      ) in

      let uni_senv = Clause.sort_env_of cl in
      let orig = Logic.ExtTerm.neg_of body in
      let phi =
        Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv orig []
      in
      let phi = Evaluator.simplify phi in
      Debug.print @@ lazy (sprintf "phi: %s" @@ LogicOld.Formula.str_of phi);
      let assign =
        LogicOld.Formula.and_of @@
        List.map pairs ~f:(fun (pos_args, ex_args_list) ->
          LogicOld.Formula.or_of @@
          List.map ex_args_list ~f:(fun ex_args ->
            let eqs = List.zip_exn pos_args ex_args in
            LogicOld.Formula.and_of @@
            List.map eqs ~f:(fun (a, b) ->
              let a = Logic.ExtTerm.to_old_term Map.Poly.empty uni_senv a [] in
              LogicOld.Formula.eq a b
            )
          )
        ) in
      Debug.print @@ lazy (sprintf "assign for clause: %s" (LogicOld.Formula.str_of assign));

      let head_term = Set.nth pos 0 |> Option.value_exn in
      let (pos_args, ex_args_list) = mk_eqs head_term (-1) d_dpos in
      let goal_constraint =
        LogicOld.Formula.and_of @@
          List.map ex_args_list ~f:(fun ex_args ->
            let vars = List.filter ex_args ~f:LogicOld.Term.is_var in
            let to_be_bound = List.map vars ~f:(LogicOld.Term.let_var >> fst) in
            let eqs = List.zip_exn pos_args ex_args in
            let eq_f =
            LogicOld.Formula.and_of @@
            List.map eqs ~f:(fun (a, b) ->
              let a = Logic.ExtTerm.to_old_term Map.Poly.empty uni_senv a [] in
              LogicOld.Formula.eq a b
            ) in
            let bound_f = LogicOld.Formula.mk_exists to_be_bound eq_f in
            LogicOld.Formula.negate bound_f
          )
      in
      Debug.print @@ lazy (sprintf "goal constraint: %s" (LogicOld.Formula.str_of goal_constraint));

      let result = resolution_sat ~site:"forward-one-query" ~timeout:config.eager_smt_timeout fenv [ phi; assign; goal_constraint ] in
      match result with
      | `Sat model -> begin
        Debug.print @@ lazy "Sat";
        List.iter model ~f:(fun ((tv, _sort), t) ->
          let t_str =
            (match t with
             | Some t -> LogicOld.Term.str_of t
             | None -> "NONE")
          in
          Debug.print @@ lazy (sprintf "%s => %s" (Ident.str_of_tvar tv) t_str);
        );
        let sub = LogicOld.remove_dontcare ~freshvar:true model |> Map.Poly.of_alist_exn in
        let head_term = Logic.ExtTerm.to_old_term exi_senv uni_senv head_term [] in
        let head_term = LogicOld.Term.subst sub head_term in
        Debug.print @@ lazy (sprintf "head_term1: %s" (LogicOld.Term.str_of head_term));
        let head_term = Logic.ExtTerm.of_old_term head_term in
        Debug.print @@ lazy (sprintf "head_term2: %s" (Logic.ExtTerm.str_of head_term));
        let head_atom = Logic.ExtTerm.to_old_atom exi_senv uni_senv head_term [] in
        let head = ExAtom.of_old_atom exi_senv (LogicOld.Formula.mk_true ()) head_atom in
        let head = ExAtom.normalize head in
        let ex = ExClause.mk_unit_pos head in
        Debug.print @@ lazy ("obtained example:" ^ ExClause.str_of ex);
        (* let _ = Stdlib.read_line () in *)
        examples := (ex, [(ClauseGraph.Clause cl, true)]) :: !examples
      end
      | `Unsat -> Debug.print @@ lazy "Unsat"
      | _ -> Debug.print @@ lazy "Otherwise"
    );
    Debug.print @@ lazy "</Positive One Step>";
    (* let _ = Stdlib.read_line () in *)
    Set.Poly.of_list !examples

  let _reduction1 clauses vs ((params_senv, cand) : CandSol.t) =
    Debug.print @@ lazy "<Reduction1>";

    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let (d_dpos, d_dneg, d_und) = VersionSpace.pos_neg_und_examples_of vs in
    let fenv = vs.VersionSpace.fenv in
    let cand_map = CandSol.to_subst (params_senv, cand) in

    Debug.print @@ lazy "<d_dpos>";
    Set.iter d_dpos ~f:(fun x ->
      Debug.print @@ lazy (ExClause.str_of x)
    );
    Debug.print @@ lazy "</d_dpos>";

    Debug.print @@ lazy "<d_dneg>";
    Set.iter d_dneg ~f:(fun x ->
      Debug.print @@ lazy (ExClause.str_of x)
    );
    Debug.print @@ lazy "</d_dneg>";

    Debug.print @@ lazy "<d_und>";
    Set.iter d_und ~f:(fun x ->
      Debug.print @@ lazy (ExClause.str_of x)
    );
    Debug.print @@ lazy "</d_und>\n";

    Set.iter clauses ~f:(fun cl ->
        Debug.print @@ lazy (sprintf "\n@ clause: %s" (Clause.str_of exi_senv cl));

        let (_, pos, neg, phi) = cl in
        (*
         phi \/ not neg \/ pos == not phi, neg => pos
         if pos is empty, "... -> false"
         *)
        Debug.print @@ lazy "<pos>";
        Set.iter pos ~f:(fun p ->
          Debug.print @@ lazy (Logic.ExtTerm.str_of p);
        );
        Debug.print @@ lazy "</pos>";

        Debug.print @@ lazy "<neg>";
        (*
          If I($1, 0, 1):example & I(x, y, z), I(x', y, z) => ... : clause,
           we avoid the case x = $1 = x' so x = x'.
          Thus, we rename I($1, 0, 1) w.r.t. the application position.
          For example, I($1, 0, 1) ~ I(x, y, z) and I($2 <- renamed, 0, 1) ~ I(x', y, z).

          On the basis of the above observation, we rename using positions
          Furthermore, 
          If { I(array, $1), I($1, 2) } : examples & I(x, y) => ... : clause,
          (array = x /\ $1 = y) \/ ($1 = x /\ 2 = y) fails due to type-mismatch for array = x and $1 = x.
          Therefore, we need to rename such as
            { I(array, $1), I($1, 2) }  => { I(array, $1_1), I($1_2, 2)}.
          
          Namely, we need to use both of the application position and index of examples.
        *)
        let pred_pos = ref 0 in
        let pairs = Set.fold neg ~init:[] ~f:(fun acc n ->
          pred_pos := !pred_pos + 1;

          Debug.print @@ lazy (Logic.ExtTerm.str_of n);

          let _i, vs = Logic.Term.let_var_app n in
          List.iter vs ~f:(fun x ->
            Debug.print @@ lazy (Logic.ExtTerm.str_of x);
          );

          let ex_num = ref 0 in
          let pred_args = Set.fold d_dpos ~init:[] ~f:(fun acc ex ->
            ex_num := !ex_num + 1;

            Debug.print @@ lazy ("focusing: " ^ ExClause.str_of ex);
            assert (Set.is_empty ex.negative);
            assert (Set.is_singleton ex.positive);
            let ex = Option.value_exn @@ Set.nth ex.positive 0 in

            if ExAtom.equal ex (ExAtom.mk_true ()) then
              acc
            else
              let args = Option.value_exn @@ ExAtom.args_of ex in
              let renamed = List.map args ~f:(fun arg ->
                (match arg with
                 | Var (Tvar tv, sym, info) ->
                    let tv = sprintf "%s###%d###%d" tv !pred_pos !ex_num in
                    LogicOld.Term.mk_var ~info (Ident.Tvar tv) sym
                 | x -> x)) in
              acc @ [(renamed)]
          )
          in
          acc @ [(vs, pred_args)]
        ) in
        Debug.print @@ lazy "</neg>";
        Debug.print @@ lazy (sprintf "phi: %s" (Logic.ExtTerm.str_of phi));

        List.iter pairs ~f:(fun (args, targets) ->
          List.iter targets ~f:(fun (terms) ->
            assert(List.length args = List.length terms);
            let eqs = List.zip_exn args terms in
            List.iter eqs ~f:(fun (a, b) ->
               Debug.print @@ lazy (sprintf "%s ~~~ %s" (Logic.ExtTerm.str_of a) (LogicOld.Term.str_of b));
            );
          );
        );

        let uni_senv = Clause.sort_env_of cl in
        let clause = Clause.to_formula cl in
        let phi = Logic.Term.subst cand_map clause in
        let phi =
          Logic.ExtTerm.to_old_formula Map.Poly.empty (Map.force_merge params_senv uni_senv) phi []
        in
        let phi = Evaluator.simplify phi in
        Debug.print @@ lazy (sprintf "phi: %s" @@ LogicOld.Formula.str_of phi);

        let neg_phi = LogicOld.Formula.negate phi in
        Debug.print @@ lazy (sprintf "neg phi: %s" @@ LogicOld.Formula.str_of neg_phi);

        let assign =
        LogicOld.Formula.and_of @@
        List.map pairs ~f:(fun (pos_args, ex_args_list) ->
          LogicOld.Formula.or_of @@
          List.map ex_args_list ~f:(fun ex_args ->
            let eqs = List.zip_exn pos_args ex_args in
            LogicOld.Formula.and_of @@
            List.map eqs ~f:(fun (a, b) ->
              let a = Logic.ExtTerm.to_old_term Map.Poly.empty (Map.force_merge params_senv uni_senv) a [] in
              LogicOld.Formula.eq a b
            )
          )
        ) in
        Debug.print @@ lazy (sprintf "assign for clause: %s" (LogicOld.Formula.str_of assign));
        (* The commented-out route below went through
           [check_clause_nonparam_smt], which negates what it is given: the
           formula here is already the negation, so that call would ask about
           its negation instead. Hence the direct [check_sat]. *)
        let result = resolution_sat ~site:"reduction1" ~timeout:config.eager_smt_timeout fenv [ neg_phi; assign ] in
        match result with
        | `Sat _model -> Debug.print @@ lazy "Sat"
        | `Unsat -> Debug.print @@ lazy "Unsat"
        | _ -> Debug.print @@ lazy "Otherwise"
    );
    Debug.print @@ lazy "</Reduction1>";
    let _ = Stdlib.read_line () in
    ()


  (* ---- deciding held atoms from the problem's fact and goal clauses ----

     [FactGoal] holds the rule and the argument that each answer is sound;
     this is the driver.  Which atoms are asked:
     - an atom of an undecided example that no decided example already states,
       against the fact clauses and the goal clauses of its predicate;
     - an atom decided positive, against the goal clauses only, and one decided
       negative, against the fact clauses only -- an answer there is a
       conflict, which the labeling that follows turns into a refutation, and
       both halves of it are sound derivations.
     The clauses are the PREPROCESSED problem's, the one whose predicates the
     examples mention; learned clauses are not asked.

     Cost.  One question per (atom, clause), each with [factgoal_timeout]; the
     answer depends on the atom and the clause alone, so it is cached for the
     whole solve, undecided answers included, and no question is asked twice.  At most
     [factgoal_queries_per_round] questions are asked per round; an atom left
     unasked by the cap is asked in a later round.  Both numbers are a choice
     with room, not a measured bound: the one corpus count of the rule (120
     CHC files) had no question undecided within a 2 s budget. *)
  let factgoal_timeout = Some 1000
  let factgoal_queries_per_round = 32

  let factgoal_entries =
    lazy
      (FactGoal.entries_of_problem
         (PCSP.Problem.senv_of APCSP.problem)
         (PCSP.Problem.clauses_of APCSP.problem))

  (* (role, clause index, atom) -> answer summary, over the solve *)
  let factgoal_cache : (string, bool) Hashtbl.t = Hashtbl.create (module String)

  (* the validator's guard decision: a ground guard is dropped only when it is
     VALID, satisfiability licensing nothing *)
  let factgoal_discharge fenv cond =
    match resolution_sat ~site:"factgoal" ~timeout:(Some 1000) fenv [ cond ] with
    | `Unsat -> `Unsat
    | `Sat _ -> (
        match
          resolution_sat ~site:"factgoal-neg" ~timeout:(Some 1000) fenv
            [ Formula.mk_neg cond ]
        with
        | `Unsat -> `Sat
        | _ -> `Unknown)
    | _ -> `Unknown

  (* the firing condition of [fact_goal_structured_only], decided once from the
     problem's sort environments *)
  let factgoal_fires =
    lazy
      (FactGoal.fires ~enabled:config.decide_by_fact_goal_clauses
         ~structured_only:config.fact_goal_structured_only
         (PCSP.Problem.senv_of APCSP.problem)
         (PCSP.Problem.clauses_of APCSP.problem))

  let decide_by_fact_goal vs dpos0 dneg0 und0 =
    if not (Lazy.force factgoal_fires) then Set.Poly.empty
    else
      let exi_senv = PCSP.Problem.senv_of APCSP.problem in
      let entries = List.mapi (Lazy.force factgoal_entries) ~f:(fun i e -> (i, e)) in
      let atoms_of exs =
        Set.filter (ExClauseSet.exatoms_of exs) ~f:(fun a ->
            ExAtom.is_papp a || ExAtom.is_ppapp a)
      in
      let pos = atoms_of dpos0 and neg = atoms_of dneg0 in
      let und = Set.diff (atoms_of und0) (Set.union pos neg) in
      let asked = ref 0 and capped = ref 0 and derived = ref [] in
      (* wall-clock seconds spent in the questions this round, so that the
         pass's cost can be read off a trace rather than inferred *)
      let spent = ref 0.0 in
      let n_pos = ref 0 and n_neg = ref 0 and n_valid = ref 0 in
      let ask roles atm =
        match FactGoal.parts_of_atom atm with
        | None -> ()
        | Some (pv, _, _, _) ->
            List.iter roles ~f:(fun role ->
                let decided = ref false in
                List.iter entries ~f:(fun (i, (e : FactGoal.entry)) ->
                    if
                      (not !decided) && Stdlib.(e.role = role)
                      && Ident.pvar_equal e.pvar pv
                    then
                      let key =
                        sprintf "%s#%d#%s" (FactGoal.str_of_role role) i
                          (ExAtom.str_of atm)
                      in
                      match Hashtbl.find factgoal_cache key with
                      | Some _ -> ()
                      | None when !asked >= factgoal_queries_per_round ->
                          incr capped
                      | None ->
                          incr asked;
                          let t0 = Common.Clock.now_s () in
                          let answer =
                            FactGoal.decide ~id ~timeout:factgoal_timeout
                              ~discharge:(factgoal_discharge vs.VersionSpace.fenv)
                              vs.VersionSpace.fenv exi_senv e atm
                          in
                          spent := !spent +. (Common.Clock.now_s () -. t0);
                          Debug.print
                          @@ lazy
                               (sprintf "[fact-goal] %s clause %d at %s: %s"
                                  (FactGoal.str_of_role role) i
                                  (ExAtom.str_of atm)
                                  (FactGoal.str_of_answer answer));
                          let record ex ~rule ~subst =
                            decided := true;
                            (match role with
                            | FactGoal.Fact -> incr n_pos
                            | FactGoal.Goal -> incr n_neg);
                            (* the dry-run control stops at the same point
                               and records nothing; the counts then say what
                               would have been derived *)
                            if not config.fact_goal_dry_run then begin
                            let ex' =
                              ExClause.normalize_params (Map.key_set exi_senv)
                              @@ ExClause.normalize ex
                            in
                            VersionSpace.record_derivation ~via:(Some e.clause)
                              vs ex ~rule ~subst;
                            VersionSpace.copy_derivation vs ~from:ex ~to_:ex';
                            derived :=
                              ( ex',
                                Set.Poly.singleton
                                  (ClauseGraph.Clause e.clause, false) )
                              :: !derived
                            end
                          in
                          (match answer with
                          | FactGoal.Instance (sub, ex) ->
                              record ex ~rule:"instance" ~subst:(Some sub)
                          | FactGoal.Valid ->
                              incr n_valid;
                              record (FactGoal.unit_of role atm)
                                ~rule:FactGoal.validity_rule ~subst:None
                          | FactGoal.No | FactGoal.Undecided -> ());
                          (* every answer is final, an undecided one included:
                             the question and its budget are the same next round,
                             and re-asking the undecided ones spent the per-round
                             cap -- on one run 484 of the questions asked were
                             repeats of 88 undecided ones, while the queue of
                             unasked atoms grew to 266 *)
                          Hashtbl.set factgoal_cache ~key ~data:true))
      in
      Set.iter und ~f:(ask [ FactGoal.Fact; FactGoal.Goal ]);
      Set.iter pos ~f:(ask [ FactGoal.Goal ]);
      Set.iter neg ~f:(ask [ FactGoal.Fact ]);
      Debug.print
      @@ lazy
           (sprintf
              "[fact-goal] %d question(s) asked in %.3f s, %d left for a later \
               round; derived %d positive(s) and %d negative(s), %d by validity"
              !asked !spent !capped !n_pos !n_neg !n_valid);
      Set.Poly.of_list !derived

  let witness_groups =
    lazy
      (FactGoal.wgroups_of_problem
         ~fnpvs:(PCSP.Problem.fnpvs_of APCSP.problem)
         (PCSP.Problem.senv_of APCSP.problem)
         (PCSP.Problem.clauses_of APCSP.problem))

  (* Rule W of [FactGoal] over the witness groups: a head atom of an undecided
     example, or of a decided negative one (a conflict), is asked of each group
     of its predicate; a group without a head is asked once per count of
     decided positives.  The decided positives are the unit positive examples,
     which are consequences of the problem.  A question is cached with the
     number of decided positives it saw, since more positives can only make it
     valid; budget and cap as for the fact-goal pass. *)
  let decide_by_witness_groups vs dpos0 dneg0 und0 =
    if not config.decide_by_witness_groups then Set.Poly.empty
    else
      let groups = List.mapi (Lazy.force witness_groups) ~f:(fun i g -> (i, g)) in
      if List.is_empty groups then Set.Poly.empty
      else
        let exi_senv = PCSP.Problem.senv_of APCSP.problem in
        let atoms_of exs =
          Set.filter (ExClauseSet.exatoms_of exs) ~f:(fun a ->
              ExAtom.is_papp a || ExAtom.is_ppapp a)
        in
        let pos_atoms = atoms_of dpos0 in
        let pos =
          Set.to_list pos_atoms |> List.filter_map ~f:FactGoal.parts_of_atom
        in
        let npos = List.length pos in
        let neg = atoms_of dneg0 in
        let und = Set.diff (atoms_of und0) (Set.union pos_atoms neg) in
        let asked = ref 0 and derived = ref [] and n_dec = ref 0 in
        let t0 = Common.Clock.now_s () in
        let ask i (g : FactGoal.wgroup) atm =
          let key =
            sprintf "wg#%d#%d#%s" i npos
              (Option.value_map atm ~default:"-" ~f:ExAtom.str_of)
          in
          if Hashtbl.mem factgoal_cache key || !asked >= factgoal_queries_per_round
          then ()
          else (
            incr asked;
            let answer =
              FactGoal.decide_witness ~id ~timeout:factgoal_timeout
                vs.VersionSpace.fenv g pos atm
            in
            Hashtbl.set factgoal_cache ~key ~data:true;
            Debug.print
            @@ lazy
                 (sprintf "[witness-group] %s at %s: %s"
                    (FactGoal.str_of_wgroup g)
                    (Option.value_map atm ~default:"-" ~f:ExAtom.str_of)
                    (FactGoal.str_of_answer answer));
            match answer with
            | FactGoal.Valid ->
                incr n_dec;
                let ex =
                  match atm with
                  | Some atm -> ExClause.mk_unit_pos atm
                  | None -> ExClause.mk_false ()
                in
                let ex' =
                  ExClause.normalize_params (Map.key_set exi_senv)
                  @@ ExClause.normalize ex
                in
                let via = (List.hd_exn g.gmembers).mclause in
                VersionSpace.record_derivation ~via:(Some via) vs ex
                  ~rule:FactGoal.witness_rule ~subst:None;
                VersionSpace.copy_derivation vs ~from:ex ~to_:ex';
                derived :=
                  ( ex',
                    Set.Poly.of_list
                    @@ List.map g.gmembers ~f:(fun m ->
                        (ClauseGraph.Clause m.FactGoal.mclause, false)) )
                  :: !derived
            | _ -> ())
        in
        List.iter groups ~f:(fun (i, (g : FactGoal.wgroup)) ->
            match g.ghead with
            | None -> ask i g None
            | Some (hpv, _) ->
                Set.iter (Set.union und neg) ~f:(fun atm ->
                    match FactGoal.parts_of_atom atm with
                    | Some (pv, _, _, _) when Ident.pvar_equal pv hpv ->
                        ask i g (Some atm)
                    | _ -> ()));
        Debug.print
        @@ lazy
             (sprintf
                "[witness-group] %d group(s), %d question(s) in %.3f s, %d \
                 decided, over %d decided positive(s)"
                (List.length groups) !asked
                (Common.Clock.now_s () -. t0)
                !n_dec npos);
        Set.Poly.of_list !derived

  let resolve e =
    (* the counters this phase owns, registered before it does anything, so the
       report distinguishes "nothing was discarded" from "the phase did not
       run" *)
    PCSatCommon.GeneralityMonitor.(
      expect Resolution "lose" [ "derivation-discarded-for-a-dummy" ];
      expect Resolution "use" [ "derived-examples-still-parametric" ]);
    let open State.Monad_infix in
    Ok e >>=? fun vs _a ->
    let dpos0, dneg0, und0 = VersionSpace.pos_neg_und_examples_of vs in
    (* asked first, on what this phase received, so that its questions do not
       depend on what the resolution rules below derive this round *)
    let fact_goal =
      Set.union
        (decide_by_fact_goal vs dpos0 dneg0 und0)
        (decide_by_witness_groups vs dpos0 dneg0 und0)
    in
    let d_dpos = Set.diff dpos0 !old_dpos in
    let d_dneg = Set.diff dneg0 !old_dneg in
    let d_und = Set.diff und0 !old_und in
    let fenv = vs.fenv in
    old_dpos := dpos0;
    old_dneg := dneg0;
    old_und := und0;
    let clauses =
      Set.union
        (PCSP.Problem.clauses_of APCSP.problem)
        (vs.learned_clauses |> Hash_set.to_list |> Set.Poly.of_list)
    in
    let cs = clauses |> src_cls_of false in
    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let graph = vs.examples.graph in
    (record :=
       fun ex ~via ~premises sub ->
         VersionSpace.record_derivation ~via ~premises vs ex ~rule:"resolution"
           ~subst:(Some sub));
    let dpos, dneg =
      let to_be_refuted, to_be_proved =
        let to_be_refuted, to_be_proved =
          if config.refute then
            ( Set.Poly.filter_map
                (if config.only_diff then d_dpos else dpos0)
                ~f:(fun c ->
                  Option.map
                    (ExAtom.to_old_atom @@ ExClause.exatom_of_uclause c)
                    ~f:(fun a ->
                      (a, Set.Poly.singleton (ClauseGraph.mk_example c, false)))),
              Set.Poly.filter_map
                (if config.only_diff then d_dneg else dneg0)
                ~f:(fun c ->
                  Option.map
                    (ExAtom.to_old_atom @@ ExClause.exatom_of_uclause c)
                    ~f:(fun a ->
                      (a, Set.Poly.singleton (ClauseGraph.mk_example c, false))))
            )
          else (Set.Poly.empty, Set.Poly.empty)
        in
        if config.decide then
          let atms =
            Set.Poly.filter_map ~f:(fun (a, c) ->
                Option.map ~f:(fun a -> (a, c)) @@ ExAtom.to_old_atom a)
            @@ Set.concat_map ~f:(fun c ->
                Set.Poly.map (ExClause.exatoms_of c) ~f:(fun a ->
                    (a, Set.Poly.singleton (ClauseGraph.mk_example c, false))))
            @@
            (* Set.filter ~f:(fun ex ->
                Debug.print @@ lazy ("decide:" ^ ExClause.str_of ex);
                let pvs = ExClause.pvs_of ex |> Set.Poly.map ~f:Ident.pvar_to_tvar in
                not @@ Set.exists pvs ~f:(PCSP.Problem.is_tot_pred APCSP.problem)) @@ *)
            if config.only_diff then d_und else und0
          in
          (Set.union to_be_refuted atms, Set.union to_be_proved atms)
        else (to_be_refuted, to_be_proved)
      in
      let bvs = Map.key_set exi_senv in
      Set.union
        (Set.Poly.map ~f:(fun a -> (false, a))
        @@ ExAtomSet.reduce_with_source bvs to_be_refuted)
        (Set.Poly.map ~f:(fun a -> (true, a))
        @@ ExAtomSet.reduce_with_source bvs to_be_proved)
      |> Set.Poly.map ~f:(fun (b, ((param_senv, atm), source)) ->
          (Map.Poly.length param_senv, b, ((param_senv, atm), source)))
      |> Set.to_list
      |> List.sort ~compare:(fun (n1, _, _) (n2, _, _) -> n2 - n1)
      |> List.fold
           ~init:(src_exs_of false dpos0, src_exs_of false dneg0)
           ~f:(fun (dpos, dneg) (_, b, ((param_senv, atm), source)) ->
             if b then (
               Debug.print
               @@ lazy
                    ("proving "
                    ^ Formula.str_of
                        ((*Formula.exists (Set.to_list @@ Atom.term_sort_env_of atm) @@*)
                         Formula.mk_atom atm));
               ( prove ~dpos ~dneg ~graph fenv exi_senv cs
                   ((param_senv, atm), source),
                 dneg ))
             else (
               Debug.print
               @@ lazy
                    ("refuting "
                    ^ Formula.str_of
                        ((*Formula.forall (Set.to_list @@ Atom.term_sort_env_of atm) @@*)
                         Formula.mk_atom atm));
               ( dpos,
                 refute ~dpos ~dneg ~graph fenv exi_senv cs
                   ((param_senv, atm), source) )))
    in
    let dpos, dneg, und =
      (* if not config.acquire_und then dpos, dneg, und0 else *)
      (if config.only_diff then d_und else und0)
      |> src_exs_of true
      |> ExClauseSet.refresh_params_with_src exi_senv
      |> ClauseGraph.to_clause_set_with_src exi_senv
      |> ClauseGraph.resolve_one_step_all
           ~print:(fun _ -> () (*Debug.print*))
           (Set.Poly.filter_map dpos ~f:(fun (ex, _src) ->
                insert_source (cite ex) @@ ExClause.atom_of_uclause ex))
           (Set.Poly.filter_map dneg ~f:(fun (ex, _src) ->
                insert_source (cite ex) @@ ExClause.atom_of_uclause ex))
           exi_senv
      |> Set.Poly.map ~f:(fun (c, theta, origin) -> (c, (theta, origin)))
      |> (fun cls ->
           let p =
             Set.Poly.filter_map dpos ~f:(fun (ex, _src) ->
                 insert_source (cite ex) @@ ExClause.atom_of_uclause ex)
           and n =
             Set.Poly.filter_map dneg ~f:(fun (ex, _src) ->
                 insert_source (cite ex) @@ ExClause.atom_of_uclause ex)
           in
           let tested = ref 0 in
           let test examples senv lit =
             incr tested;
             config.simplify_with_matching
             && settled_by ~id fenv exi_senv senv lit examples
           in
           let r =
             ClauseGraph.simplify_with ~falsified:(test n) ~verified:(test p) p
               n cls
           in
           Debug.print
           @@ lazy
                (sprintf
                   "[simplify_with] %d literal(s) offered to the settling test, \
                    over %d clause(s), %d positive and %d negative example(s)"
                   !tested (Set.length cls) (Set.length p) (Set.length n));
           r)
      |> acquire fenv exi_senv ~dpos ~dneg ~und:(src_exs_of true und0) ~graph
    in
    let dpos_in, dneg_in, und_in = (dpos, dneg, und) in
    let dpos, dneg, und =
      (if config.resolve_against_problem_clauses then cs else Set.Poly.empty)
      |> (let parametric (ex, _src) =
            not (Map.Poly.is_empty (ExClause.params_of ex))
          in
          let atoms ~only_parametric =
            Set.Poly.filter_map ~f:(fun ((ex, _src) as e) ->
                if only_parametric && not (parametric e) then None
                else insert_source (cite ex) @@ ExClause.atom_of_uclause ex)
          in
          let resolve ~only_parametric cs =
            ClauseGraph.resolve_one_step_all
              ~print:(fun _ -> () (*Debug.print*))
              (atoms ~only_parametric dpos) (atoms ~only_parametric dneg)
              exi_senv cs
          in
          fun cs ->
            let loops, others =
              if config.problem_clause_self_loop_depth_bound then
                (* the self-loops are resolved below, depth by depth *)
                ( Set.Poly.empty,
                  Set.filter cs ~f:(fun (cl, _) -> not (Clause.is_self_loop cl))
                )
              else if config.problem_clause_self_loops_parametric_only then
                Set.partition_tf cs ~f:(fun (cl, _) -> Clause.is_self_loop cl)
              else (Set.Poly.empty, cs)
            in
            let all_parametric = config.problem_clause_sources_parametric_only in
            Set.union
              (resolve ~only_parametric:all_parametric others)
              (resolve ~only_parametric:true loops))
      |> Set.Poly.map ~f:(fun (c, theta, origin) -> (c, (theta, origin)))
      |> Set.union
           ((* The unit clauses of the original problem are resolution partners,
               so putting them in derives more examples per round -- and costs,
               because a larger graph yields more examples and more examples make
               the synthesis heavier.  The two are wanted in opposite
               directions: a refutation is reached by having more examples and an
               invariant is found sooner with fewer.  Measured over one corpus,
               switching this on unconditionally gains exactly one answer and
               loses exactly one, and they are the two sides of one program.

               So it is switched on for the rounds where the loop has told us it
               cannot synthesise its way out, and left off otherwise.  A run
               whose synthesis keeps succeeding never sets that flag and pays
               nothing. *)
            if config.unit_prop || (config.unit_prop_when_stalled && !(vs.VersionSpace.synthesis_stalled))
            then
              Set.Poly.map ~f:(fun ((cl, _) as c) -> (c, (Map.Poly.empty, cl)))
              @@ Set.filter cs ~f:(fun (cl, _c) -> Clause.is_unit cl)
            else Set.Poly.empty)
      |> ClauseGraph.simplify_with
           (Set.Poly.filter_map dpos ~f:(fun (ex, _src) ->
                insert_source (cite ex) @@ ExClause.atom_of_uclause ex))
           (Set.Poly.filter_map dneg ~f:(fun (ex, _src) ->
                insert_source (cite ex) @@ ExClause.atom_of_uclause ex))
      |> acquire fenv exi_senv ~dpos ~dneg ~und ~graph
    in
    (* The self-loop steps of the problem-clause site under the depth bound:
       sources are the decided examples as this phase received them, each
       resolved through the self-loop clauses only while its depth is below the
       bound, and whatever a step adds is one deeper than its sources. *)
    let dpos, dneg, und =
      if
        not
          (config.resolve_against_problem_clauses
          && config.problem_clause_self_loop_depth_bound)
      then (dpos, dneg, und)
      else
        let loops = Set.filter cs ~f:(fun (cl, _) -> Clause.is_self_loop cl) in
        let bound = config.problem_clause_self_loop_depth in
        (* the per-source bound, only when the arrays bound is set: a source
           whose predicate reaches an array gets it, every other one [bound].
           Left [None] otherwise, so [LoopDepth] runs exactly as without it. *)
        let reaches (pvar, sorts) =
          if config.problem_clause_self_loop_depth_arrays_program_only then
            CellQual.reaches_program_array
              ~universal:(universal_positions_of pvar sorts)
              sorts
          else List.exists sorts ~f:CellQual.reaches_array
        in
        let bound_of =
          Option.map config.problem_clause_self_loop_depth_arrays
            ~f:(fun n (_, (ex, _)) ->
              if Set.exists (ExClause.pvar_sorts_of ex) ~f:reaches then n
              else bound)
        in
        let keep (ex, _src) =
          (not config.problem_clause_self_loops_parametric_only)
          || not (Map.Poly.is_empty (ExClause.params_of ex))
        in
        let sources =
          Set.union
            (Set.Poly.map ~f:(fun e -> (true, e)) (Set.filter dpos_in ~f:keep))
            (Set.Poly.map ~f:(fun e -> (false, e)) (Set.filter dneg_in ~f:keep))
        in
        (* keyed on the normal form: the labeler's unit propagation returns
           every decided example through [ExClause.normalize], and where that
           changes it -- a derived guard such as [0 = 0] becomes [true] -- the
           normalised copy is added as a second example, which under a key on
           the raw clause arrived at depth 0 and continued the chain the bound
           had stopped.  Measured on a counter loop: every guarded example the
           site added came back the next round in both spellings. *)
        let key (_, (ex, _)) = ExClause.normalize ex in
        let atoms_of polarity srcs =
          Set.Poly.filter_map srcs ~f:(fun (b, (ex, _src)) ->
              if Bool.equal b polarity then
                insert_source (cite ex) @@ ExClause.atom_of_uclause ex
              else None)
        in
        let step (dpos, dneg, und) srcs =
          let dpos', dneg', und' =
            ClauseGraph.resolve_one_step_all
              ~print:(fun _ -> ())
              (atoms_of true srcs) (atoms_of false srcs) exi_senv loops
            |> Set.Poly.map ~f:(fun (c, theta, origin) -> (c, (theta, origin)))
            |> ClauseGraph.simplify_with
                 (Set.Poly.filter_map dpos ~f:(fun (ex, _src) ->
                      insert_source (cite ex) @@ ExClause.atom_of_uclause ex))
                 (Set.Poly.filter_map dneg ~f:(fun (ex, _src) ->
                      insert_source (cite ex) @@ ExClause.atom_of_uclause ex))
            |> acquire fenv exi_senv ~dpos ~dneg ~und ~graph
          in
          ( (dpos', dneg', und'),
            Set.union
              (Set.Poly.map ~f:(fun e -> (true, e)) (Set.diff dpos' dpos))
              (Set.Poly.map ~f:(fun e -> (false, e)) (Set.diff dneg' dneg)) )
        in
        let before = !loop_depths in
        let state, after =
          LoopDepth.unroll ?bound_of ~bound ~key ~step before sources
            (dpos, dneg, und)
        in
        loop_depths := after;
        incr loop_depth_round;
        let report =
          lazy
            (sprintf
               "[loop-depth] round %d: %d source(s), %d withheld at depth >= %d%s, \
                %d example(s) newly recorded, %d recorded in all"
               !loop_depth_round (Set.length sources)
               (LoopDepth.withheld ?bound_of ~bound ~key before sources)
               bound
               (match config.problem_clause_self_loop_depth_arrays with
               | None -> ""
               | Some n -> sprintf " (%d where an array is reachable)" n)
               (Map.Poly.length after - Map.Poly.length before)
               (Map.Poly.length after))
        in
        Debug.print report;
        if Lazy.force loop_depth_count then (
          eprintf "%s\n%!" (Lazy.force report);
          if Lazy.force loop_depth_detail then
            Set.iter sources ~f:(fun ((b, (ex, _)) as e) ->
                eprintf "[loop-depth]   %s depth %d: %s\n%!"
                  (if b then "pos" else "neg")
                  (LoopDepth.depth before (key e))
                  (ExClause.str_of ex)));
        state
    in
    (* Of what that site added, the ground points are dropped when asked: an
       example present before it ran is kept whatever it is. *)
    let dpos, dneg, und =
      if not config.problem_clause_resolvents_parametric_only then (dpos, dneg, und)
      else
        let keep before =
          Set.filter ~f:(fun ((ex, _) as e) ->
              Set.mem before e || not (Map.Poly.is_empty (ExClause.params_of ex)))
        in
        (keep dpos_in dpos, keep dneg_in dneg, keep und_in und)
    in
    let added =
      Set.diff
        (Set.Poly.map ~f:fst @@ Set.Poly.union_list [ dpos; dneg; und ])
        (Set.Poly.union_list [ dpos0; dneg0; und0 ])
    in
    Debug.print @@ lazy "*** Example Instances obtained by Resolution:";
    Debug.print
    @@ lazy
         (String.concat_map_list ~sep:";\n" ~f:ExClause.str_of
         @@ Set.to_list added);
    Debug.print @@ lazy "";
    (* The forward rule contributes to the same set as the resolution rules
       above, so that both kinds of derivation leave this phase together. *)
    let eager =
      if not config.eager_positive_examples then Set.Poly.empty
      else
        (* one strategy, not both: they are the same rule and running the two
           derives each example twice, at two solver calls apiece.  Which one
           is better is unmeasured, so the enumerating form is the default
           here because its novelty condition is the sharper of the two. *)
        Set.Poly.map ~f:(fun (ex, d) -> (ex, Set.Poly.of_list d))
        @@ Set.Poly.union_list
             [
               parametric_positive_examples clauses;
               (if config.eager_one_query then forward_chain_one_query clauses vs
                else forward_chain_enumerating clauses vs);
             ]
    in
    Ok
      (State.of_examples vs
      @@ Set.Poly.union_list [ dpos; dneg; und; eager; fact_goal ])

  let run_phase _iters = resolve
end
