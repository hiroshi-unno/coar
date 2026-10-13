open Core
open Common.Util
open PCSatCommon
open Coordination
open Preprocessing

module type SolverType = sig
  val solve :
    ?bpvs:Ast.Ident.tvar_set ->
    ?filename:string option ->
    ?print_sol:bool ->
    ?solution_read:bool ->
    PCSP.Problem.t ->
    State.output Or_error.t
  (** [solution_read] ([true] by default): whether the caller reads the
      solution returned with a [sat] verdict.  When it does not, the solution is
      not completed with the definitions of the predicates preprocessing
      eliminated, unless this solver prints it or checks it itself; the verdict
      and the printed answer are the same. *)

  val preprocess :
    ?bpvs:Ast.Ident.tvar_set -> PCSP.Problem.t -> PCSP.Problem.t Or_error.t

  val reset : unit -> unit
  val push : unit -> unit
  val pop : unit -> unit
end

(* The definitions recorded for predicates eliminated by resolution are
   existentially quantified over the clause variables.  Eliminating the
   quantifiers is
   done here, once, for the solution that is printed: inside the solving
   pipeline it would run on every PCSat call MuVal makes (Z3 queries and time
   between rounds), and unbounded it took longer than the solving itself
   (13.c.small), so each definition gets a 1 s budget and keeps the
   quantified form otherwise. *)
(* Which binders Z3's [qe] tactic must not be asked to eliminate.

   A sequence-sorted binder makes the call not return AT ALL -- not slowly,
   and not bounded by the [timeout] below, which is handed to the tactic as
   [try_for] and does not hold: 40 s and counting on one four-line definition.
   The process then never prints the answer it has already computed, because
   this step runs after the verdict is decided and only tidies the model about
   to be printed.

   Two repairs were rejected before this one.  Bounding the call with this
   process's own wall clock cannot work: the timer raises from a SIGALRM
   handler and OCaml runs handlers at safe points, so a Z3 call that does not
   return is not interruptible.  And declining inside the quantifier
   eliminator itself -- where three such declines already live, for bit
   vectors, [Power] and a cancelled tactic -- would hand a still-quantified
   formula back to every caller, including ones that assume it is
   quantifier-free; that shape has already produced a "safe" answer for an
   unsafe input once.  So the decline is here, at the one caller that provably
   tolerates it: what this function returns is cosmetic, and its existing
   handler already keeps the untidied definition when the call raises. *)
(* Whether a binder makes the call unable to return is one question with one
   answer, and it lives beside the solver entry points it is about: the sorts
   and the evidence for each are there, and so is the reason it must read the
   BOUND variables rather than the free ones. *)

(* Tidy the model that is about to be printed, and nothing more.

   Everything a caller needs to know is in its one call site and was not in
   the name this had before, which read as a step the answer depends on.  It
   runs ONLY when the answer is about to be printed; it CANNOT change a
   verdict, the solution being already assembled and the verdict already
   decided; and it is BEST EFFORT -- a definition whose elimination raises is
   kept as it was.

   The gap between that name and that contract is where a defect lived: because
   the function read as load bearing, nobody asked what happens when the
   elimination does not come back, and the answer was that the process never
   printed an answer it had already computed.  The guard below is the repair. *)
(* The wall clock the tidying of one solution may take, and the size, as a
   tree, past which a definition is kept as it is.  The definitions recorded
   for eliminated predicates are built by substituting one into the next,
   which shares the substituted term physically wherever its predicate
   occurred, so a chain of them is small in memory while its tree -- which
   the conversion below walks -- doubles with each link.  On a Rust-derived
   problem with 220 such definitions one took minutes to convert and the
   following ones twice as long each, so a run with the answer decided in
   half a minute printed nothing within ten.  Each budget of a second given to
   the quantifier elimination does not bound that conversion, which comes
   before it.  Both numbers are choices; past either the definitions are kept
   as they are, which is what the elimination's own failure already gives. *)
(* The reader's three process-wide switches -- whether a [:law] premise reaches the assertions
   applying an unknown that depends on the law's function, whether repeated premise conjuncts are
   dropped, whether constructor-fixed existentials are removed before skolemisation -- as the
   problem [config] solves wants them, starting from their present values.  A switch is only ever
   moved away from the reader's default here: a later reading in the same process (another solver
   whose configuration leaves it alone) must keep what an earlier one asked for. *)
let law_reader_switches (config : Config.t) =
  ( config.law_reach_dependents || !SMT.Smtlib2.law_reaches_dependents,
    config.law_dedup_premises && !SMT.Smtlib2.law_dedup_premises,
    config.onepoint_constructor_binders
    && !PCSP.Problem.onepoint_constructor_binders )

(* [law_reader_switches config] applied to the reader, for a caller about to read the input that
   [config] will solve, so that the reading is the one the solver would otherwise make again *)
let set_law_reader_switches (config : Config.t) =
  let reach, dedup, onepoint = law_reader_switches config in
  SMT.Smtlib2.law_reaches_dependents := reach;
  SMT.Smtlib2.law_dedup_premises := dedup;
  PCSP.Problem.onepoint_constructor_binders := onepoint;
  if config.name_quantified_premises then
    PCSP.Parser.name_quantified_premises := true

let tidy_budget_s = 60.
let tidy_max_nodes = 2_000_000

let tidy_solution ?(budget_s = tidy_budget_s) ?(max_nodes = tidy_max_nodes) =
  function
  | PCSP.Problem.Sat sol ->
      let deadline = Common.Clock.now_s () +. budget_s in
      PCSP.Problem.Sat
        (Map.Poly.map sol ~f:(fun term ->
             if Float.(Common.Clock.now_s () >= deadline) then term
             else if Ast.Logic.Term.ast_size_up_to max_nodes term > max_nodes
             then term
             else
             try
               let params, body = Ast.Logic.ExtTerm.let_lam term in
               if
                 not
                   (Set.is_subset
                      (Ast.Logic.ExtTerm.fvs_of body)
                      ~of_:(Set.Poly.of_list @@ List.map ~f:fst params))
               then term
               else
                 let phi =
                   Ast.Logic.ExtTerm.to_old_fml Map.Poly.empty
                     (Map.Poly.of_alist_exn params)
                     body
                 in
                 if Ast.LogicOld.Formula.is_quantifier_free phi then term
                 else if Z3Smt.Z3interface.may_not_return phi then term
                 else
                   Ast.Logic.ExtTerm.mk_lambda params
                   @@ Ast.Logic.ExtTerm.of_old_formula
                   @@ Ast.Evaluator.simplify
                   @@ Z3Smt.Z3interface.qelim ~timeout:(Some 1000) ~id:None
                        ~fenv:(Ast.LogicOld.get_fenv ()) phi
             with exn_ when not (Common.Timer.is_async exn_) -> term))
  | sol -> sol

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  (* Constructed before any solving domain exists, so setting the process-wide
     switch here is race-free; it is only ever turned on. *)
  let () =
    if config.seq_read_range_guard then
      Ast.ClauseOld.enable_seq_read_range_guard ()

  (* The simplifier's process-wide switches, written here for the same
     reason as the guard above and only ever turned on: a nested solver whose
     configuration leaves them off must not switch them off under one running
     with them on. *)
  let () =
    if config.simplify_normal_forms then
      Atomic.set Ast.Evaluator.simplify_normal_forms true;
    if config.abstract_oor_reads_under_binders then
      Atomic.set Ast.Evaluator.abstract_out_of_range_reads_under_binders true;
    if config.simplify_skip_simplified then
      Atomic.set Ast.Evaluator.simplify_skip_simplified true;
    if config.let_inline_by_expanded_size then
      Atomic.set Ast.Evaluator.inline_by_expanded_size true

  let () =
    if config.hspace_normalize_memo then
      Atomic.set Ast.HypSpace.normalize_memo true

  let context = Context.create ()

  (* The Z3 fresh-context policy is process-global, so it is written here, when
     the configuration is loaded and before any solving domain exists.  Only a
     configuration that asks for a policy writes it: a nested solver configured
     with the default must not switch off what the top-level one asked for. *)
  let () =
    match config.z3_fresh_retry with
    | Z3Smt.Z3interface.Off -> ()
    | policy -> Z3Smt.Z3interface.set_fresh_retry_policy policy

  (* The sequence-axiom fallback is process-global like the policy above and
     is written here for the same reason; a configuration that leaves it off
     does not switch off what another one asked for. *)
  let () =
    Option.iter config.seq_axiom_fallback
      ~f:Z3Smt.Z3interface.set_seq_axiom_fallback

  (* process-wide like the two above; only a value other than the default is
     written *)
  let () =
    if config.z3_new_context_full_major_every <> 1 then
      Z3Smt.Z3interface.set_new_context_full_major_every
        config.z3_new_context_full_major_every

  let () =
    if Option.is_some config.z3_new_context_full_major_bytes then
      Z3Smt.Z3interface.set_new_context_full_major_bytes
        config.z3_new_context_full_major_bytes

  let () =
    if config.z3_clean_reset_pool then (
      Z3Smt.Z3interface.set_clean_pool_max_uses
        config.z3_clean_reset_pool_max_uses;
      Z3Smt.Z3interface.set_clean_reset_pool true)

  let () =
    if config.z3_seq_axiom_full_major_every <> 1 then
      Z3Smt.Z3interface.set_seq_axiom_full_major_every
        config.z3_seq_axiom_full_major_every

  (* process-wide; the last configuration loaded decides *)
  let () =
    Z3Smt.Z3interface.set_seq_axiom_fork_runner
      (if config.z3_seq_axiom_fork then
         Some (fun ~ms ask -> PCSatCommon.ForkedQuery.run_forked ~ms ask)
       else None)

  let () = if config.z3_flat_and_or then Z3Smt.Z3interface.set_flat_and_or true

  let () =
    if config.z3_int_to_bv_range then Z3Smt.Z3interface.set_int_to_bv_range true

  let () =
    if config.bv_unsigned_linear_templates then
      Ast.LogicOld.set_bv_unsigned_linear_templates true

  let () =
    if config.z3_int_to_bv_mod_pow2 then
      Z3Smt.Z3interface.set_int_to_bv_mod_pow2 true

  let () =
    if config.z3_int_to_bv_twins then Z3Smt.Z3interface.set_int_to_bv_twins true

  let () =
    if config.z3_int_to_bv_pow2_shifts then
      Z3Smt.Z3interface.set_int_to_bv_pow2_shifts true

  let () =
    if config.z3_words_seq_as_arrays then
      Z3Smt.Z3interface.set_words_seq_as_arrays true

  let () =
    if config.eval_recursive_qualifiers_ground then
      Atomic.set PCSatCommon.TruthTable.eval_recursive_qualifiers_ground true;
    if config.skip_induction_cells then
      Atomic.set PCSatCommon.TruthTable.skip_induction_cells true;
    if config.truth_table_seq_length_form then
      Atomic.set PCSatCommon.SeqLengthForm.enabled true;
    if config.declare_reached_functions_only then
      Atomic.set Z3Smt.Z3interface.declare_reached_functions_only true

  (* the clock of durations and deadlines: the first configuration applied in
     a process decides it, before this solver takes any reading *)
  let () = Common.Clock.configure config.monotonic_deadlines

  (* the phase-time account, process-wide once on like the two above *)
  let () = if config.phase_time_report then Common.PhaseTime.enable ()

  (* [COAR_READ_STAGES] set: the reader's per-stage lines ([PCSP.Parser.stage_trace]) and each
     probe reading's outcome go to stderr, so that a run whose time goes to its readings names
     the stage and whether the reading was used; an instrument, it changes nothing else *)
  let read_stages = Option.is_some (Sys.getenv "COAR_READ_STAGES")
  let () =
    if read_stages then PCSP.Parser.stage_trace := fun l -> eprintf "%s\n%!" l

  (* one line on stderr saying the input was re-read for its [:law] premises,
     whenever a switch asked for that re-read, so that a run shows it happened *)
  module LawDebug =
    Common.Debug.Make
      ((val Common.Debug.Config.(
              if config.law_reach_dependents || not config.law_dedup_premises
              then
                enable
              else disable)))

  (* its counters, on stderr at the end of a top-level run that set it *)
  module SeqAxDebug =
    Common.Debug.Make
      ((val Common.Debug.Config.(
              match config.seq_axiom_fallback with
              | None -> disable
              | Some _ -> enable)))

  (* The fresh-context counters are reported on stderr at the end of a
     top-level run whenever this configuration set a policy, so that a run can
     show whether the retry still decides anything the pooled path did not. *)
  module Debug =
    Common.Debug.Make
      ((val Common.Debug.Config.(
              match config.z3_fresh_retry with
              | Z3Smt.Z3interface.Off -> disable
              | _ -> enable)))

  let preprocessor =
    let open Or_error in
    ExtFile.unwrap config.preprocessor >>= fun cfg -> Ok (Preprocessor.make cfg)

  let coordinator =
    let open Or_error in
    ExtFile.unwrap config.coordinator >>= fun cfg ->
    Ok (Coordinator.make cfg context)

  (* the checker's matched-instance forms ([Config.matched_forms_check_solution]):
     following the coordinator's switches unless overridden *)
  let checker_matched_forms =
    match ExtFile.unwrap config.coordinator with
    | Error _ -> None
    | Ok (c : Coordinator.Config.t) ->
        if
          Option.value config.matched_forms_check_solution
            ~default:c.matched_instance_forms_no_unknown_query
        then
          Some
            ( c.matched_instance_aligned_hyps_no_unknown_query,
              c.matched_instance_hyp_budget_no_unknown_query )
        else None

  let sol_printer =
    let open Or_error in
    ExtFile.unwrap config.sol_printer >>= fun cfg -> Ok (SolPrinter.make cfg)

  let tidy_solution_for_printing solution = tidy_solution solution

  (* [rec_fun_graph_unknowns]: the problem with its counted recursive
     applications encoded by graph unknowns ([PCSP.RecFunGraph.encode], which
     states why the result is equisatisfiable); the problem itself when the
     switch is off.  [rec_fun_graph_candidates] also records each graph as the
     first candidate of its unknown. *)
  (* whether the encoding is applied to the problem the preprocessor hands
     the CEGIS loop ([post_preprocessing_solve]) rather than to the problem
     as read; then the read-time encoding below is off on every path, so no
     constraint is encoded by both *)
  let rec_fun_graph_post =
    config.rec_fun_graph_unknowns
    && (config.rec_fun_graph_after_preprocessing
       || config.rec_fun_graph_dynamic)

  let encode_rec_fun_graph pcsp =
    if config.rec_fun_graph_unknowns && not rec_fun_graph_post then (
      let pcsp', added =
        PCSP.RecFunGraph.encode
          ~unknown_free_only:config.rec_fun_graph_unknown_free_only
          ~graph_candidates:config.rec_fun_graph_candidates pcsp
      in
      Debug.print
      @@ lazy
           (sprintf "rec_fun_graph_unknowns: %d unknown(s) introduced%s"
              (List.length added)
              (String.concat
                 (List.map added ~f:(fun v -> " " ^ Ast.Ident.name_of_tvar v))));
      pcsp')
    else pcsp

  (* [rec_fun_graph_after_preprocessing], [rec_fun_graph_dynamic]: [solve]
     (the coordinator's entry point) given the problem the preprocessor
     leaves, encoded as those switches say.  Contract: with neither switch,
     [solve p]; otherwise [solve] of a problem equisatisfiable with [p] --
     [p] with its clauses that mention no unknown encoded
     ([PCSP.RecFunGraph.encode_clauses], under the first switch), and, under
     the second, re-solved with each clause of that problem that validation
     left undecided and that applies a counted function encoded in turn
     ([PCSatCommon.RecFunDynamic.solve]).  Only clauses of [p] as the
     preprocessor gave it are ever candidates for the dynamic step, never
     the clauses an encoding produced.  The preprocessor's elimination
     records belong to the problem it holds, which this does not change, so
     completing a solution with the eliminated predicates is as without the
     switches; a solution's entries for graph unknowns are extra. *)
  let post_preprocessing_solve solve p =
    if not rec_fun_graph_post then solve p
    else
      let p' =
        if
          config.rec_fun_graph_after_preprocessing
          && not config.rec_fun_graph_after_elimination
        then (
          let p', added =
            Common.PhaseTime.with_phase "rec-fun-graph-post" @@ fun () ->
            PCSP.RecFunGraph.encode_clauses ~unknown_free_only:true
              ~graph_candidates:config.rec_fun_graph_candidates
              ~keep_functions:config.rec_fun_graph_dynamic p
          in
          Debug.print
          @@ lazy
               (sprintf
                  "rec_fun_graph_after_preprocessing: %d unknown(s) \
                   introduced%s"
                  (List.length added)
                  (String.concat
                     (List.map added ~f:(fun v ->
                          " " ^ Ast.Ident.name_of_tvar v))));
          p')
        else p
      in
      if not config.rec_fun_graph_dynamic then solve p'
      else
        match
          ( PCSP.Problem.clauses_of_opt ~full_clauses:false p,
            PCSP.Problem.clauses_of_opt ~full_clauses:false p' )
        with
        | Some before, Some after ->
            Atomic.set PCSatCommon.RecFunDynamic.on true;
            PCSatCommon.RecFunDynamic.solve ~solve
              ~candidates:(Set.inter before after) p'
        | _ -> solve p'

  (* [rec_fun_graph_after_elimination]: the same static encoding as
     [post_preprocessing_solve]'s, handed to the preprocessor as its
     [post_elim] hook so that the passes after elimination see the graph
     unknowns; [None] (the hook is not passed) otherwise *)
  let post_elim_encoding =
    if
      rec_fun_graph_post && config.rec_fun_graph_after_preprocessing
      && config.rec_fun_graph_after_elimination
    then
      Some
        (fun p ->
          let p', added =
            Common.PhaseTime.with_phase "rec-fun-graph-post-elim" @@ fun () ->
            (* right after elimination the problem may still be in formula
               form (the clausal form comes later in preprocessing); either
               entry point encodes exactly its constraints that mention no
               unknown *)
            if PCSP.Problem.is_raw p then
              PCSP.RecFunGraph.encode ~unknown_free_only:true
                ~graph_candidates:config.rec_fun_graph_candidates
                ~keep_functions:config.rec_fun_graph_dynamic p
            else
              PCSP.RecFunGraph.encode_clauses ~unknown_free_only:true
                ~graph_candidates:config.rec_fun_graph_candidates
                ~keep_functions:config.rec_fun_graph_dynamic p
          in
          Debug.print
          @@ lazy
               (sprintf
                  "rec_fun_graph_after_elimination: %d unknown(s) introduced%s"
                  (List.length added)
                  (String.concat
                     (List.map added ~f:(fun v ->
                          " " ^ Ast.Ident.name_of_tvar v))));
          p')
    else None

  (* [rec_fun_graph_every_reading]: a problem obtained by reading the input
     again (the forced-true reading, and the readings of the least-definition,
     true-precondition and lower-bound probes) gets the encoding decision the
     problem read first got, by the same function applied to it.  Without it
     those readings are solved as read, so whether the encoding is in force
     depends on whether some unrelated clause makes a reading happen (an
     unknown forced [true] replaces the encoded problem by an unencoded one).
     Each verdict stays sound: the encoding is equisatisfiable on any problem
     (see [PCSP.RecFunGraph]), and every reading's verdict was already sound
     for the problem it solves. *)
  let encode_reading pcsp =
    if config.rec_fun_graph_every_reading then encode_rec_fun_graph pcsp
    else pcsp

  (* set while the probe below runs, so that nothing it starts probes again *)
  let probing = ref false

  (* whether [true_precondition_probe] can try anything: a name given or the
     witness-causing selection on (the file checks are made by the probe) *)
  let true_precondition_probe_on () =
    (not (List.is_empty config.true_precondition_probe))
    || config.true_precondition_probe_witness_causing

  (* [true_precondition_probe]: [Some] only with a [sat] answer of the input
     re-read with the named unknowns defined as [true], extended with those
     definitions; [None] otherwise, and then the caller solves [pcsp] as given.

     Why the answer is sound.  Let [Q] be the unknowns the reader replaced and
     [P'] the problem it built.  A solution [s] of [P'] assigns every unknown
     of [P] but those of [Q], and [s] together with [q := fun x -> true] makes
     each constraint of [P] the corresponding constraint of [P'] under [s],
     which holds -- [P'] is [P] with [q] replaced before its existentials were
     skolemised, so the functional predicates [P] has for an existential an
     unknown of [Q] occurs under are absent from [P'], and their witnesses are
     the ones [s] gives inside the formulas.  So [sat] transfers.  [unsat] does
     not, [P'] having fixed a choice [P] leaves open, and it is never read; nor
     is anything else.  Re-reading the file sets the reader's process-wide
     record of the input assertions, which is put back before returning. *)
  let true_precondition_probe ?(forced = []) ~filename ~solve_one pcsp =
    match (config.true_precondition_probe, filename) with
    | [], _ when not config.true_precondition_probe_witness_causing -> None
    | _, None -> None
    | _ when !probing -> None
    | names, Some file
      when not
             (String.is_suffix file ~suffix:".smt2"
             && Sys_unix.file_exists_exn file) ->
        ignore names;
        None
    | names, Some file -> (
        let saved_inputs = Ast.LogicOld.get_input_record () in
        let defined = ref [] in
        let restricted =
          try
            Some
              (Common.PhaseTime.with_phase "read-true-precondition"
              @@ fun () ->
              PCSP.Parser.from_smt2_file
                 ~print:(fun _ -> ())
                 ~inline:true ~skolem_pred:true
                 ~define_true_names:(names @ forced)
                 ~define_true_witness_causing:
                   config.true_precondition_probe_witness_causing
                 ~defined_true:defined file)
          with exn_ when not (Common.Timer.is_async exn_) -> None
        in
        Ast.LogicOld.set_input_record saved_inputs;
        PCSatCommon.TruePrecondition.last_probe := `Not_tried;
        match restricted with
        | None -> None
        | Some _ when List.is_empty !defined -> None
        | Some _
          when config.true_precondition_probe_skip_forced_only
               && PCSatCommon.TruePrecondition.only_forced ~forced
                    (List.map !defined ~f:Ast.Ident.name_of_tvar) ->
            (* every unknown defined here was already defined as [true] by the
               forced-true reading, so the re-read problem is the one the
               caller solves as given: solving it again here could answer only
               what the caller answers, at the cost of a second solve *)
            Debug.print
            @@ lazy
                 "[true-precondition probe] not tried: nothing to define \
                  beyond the forced-true unknowns";
            None
        | Some restricted -> (
            Debug.print
            @@ lazy
                 (sprintf "[true-precondition probe] trying true for %s"
                    (String.concat ~sep:", "
                       (List.map !defined ~f:Ast.Ident.name_of_tvar)));
            let started = Common.Clock.now_s () in
            let answer =
              probing := true;
              Exn.protect
                ~finally:(fun () -> probing := false)
                ~f:(fun () ->
                  try
                    PCSatCommon.SolveDeadline.with_preprocessing_check
                      config.probe_deadline_in_preprocessing
                    @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                      ~seconds:
                        (Float.of_int config.true_precondition_probe_budget_ms
                        /. 1000.)
                      (fun () ->
                        Common.PhaseTime.with_phase "probe-true-precondition"
                          (fun () -> solve_one (encode_reading restricted)))
                  with exn_ when not (Common.Timer.is_async exn_) ->
                    Or_error.of_exn exn_)
            in
            let took = Common.Clock.now_s () -. started in
            match answer with
            | Ok (PCSP.Problem.Sat sol, info) ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[true-precondition probe] sat in %.2f s; answering it"
                        took);
                PCSatCommon.TruePrecondition.last_probe := `Answered;
                let trues =
                  PCSatCommon.TruePrecondition.true_subst pcsp
                    (List.filter !defined
                       ~f:(Map.Poly.mem (PCSP.Problem.senv_of pcsp)))
                in
                Some
                  (Ok
                     ( PCSP.Problem.Sat
                         (Map.Poly.fold trues ~init:sol
                            ~f:(fun ~key ~data acc ->
                              Map.Poly.set acc ~key ~data)),
                       info ))
            | _ ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[true-precondition probe] no sat in %.2f s; solving \
                         the problem as given"
                        took);
                PCSatCommon.TruePrecondition.last_probe := `Discarded;
                None))

  (* [lower_bound_probe]: [Some] only with an [unsat] answer of the input
     re-read with the named unknowns relaxed ([PCSP.Parser.lower_bound_relax]:
     [true] where demanded, a lower bound derived from the input where
     assumed); [None] otherwise, and then the caller solves [pcsp] as given.

     Why the answer is sound.  The read problem [P'] is a relaxation of the
     input [P]: in every model of the background theory, an interpretation
     satisfying [P] satisfies [P'] once the relaxed unknowns are dropped.  So
     a model in which [P'] has no satisfying interpretation, which is what its
     [unsat] reports, is one in which [P] has none.  A [sat] of [P'] says
     nothing about [P] and is never read; nor is anything else.  The
     refutation of [P'] is not one of [P], so the answer carries none.
     Re-reading the file sets the reader's process-wide record of the input
     assertions, which is put back before returning. *)
  (* [lower_bound_probe_skip_unrelaxable]: every reading records which unknowns the relaxation
     would start from, so that the probe can see from the forced-true reading that it has none *)
  let () =
    if config.lower_bound_probe_skip_unrelaxable then
      PCSP.Parser.record_relaxable := true

  let lower_bound_probe ?(forced = []) ~filename ~solve_one () =
    match (config.lower_bound_probe, filename) with
    | [], _ when not config.lower_bound_probe_witness_causing -> None
    | _, None -> None
    | _ when !probing -> None
    | [], Some file
      when config.lower_bound_probe_skip_unrelaxable
           && Option.equal (List.equal String.equal)
                (PCSP.Parser.relaxable_known ~file
                   ~defined:forced
                   ~switches:(PCSP.Parser.relaxable_switches ()))
                (Some []) ->
        (* the reading would define [forced], find no unknown to relax and be discarded unread
           ([Some _ when List.is_empty !relaxed] below); an earlier reading with [forced]
           defined under the same switches has shown that, so the reading is not taken *)
        if read_stages then
          eprintf "[lower-bound probe] not read: nothing to relax, forced %d\n%!"
            (List.length forced);
        Debug.print
        @@ lazy "[lower-bound probe] not tried: nothing to relax";
        PCSatCommon.TruePrecondition.last_lower_bound_probe := `Not_tried;
        None
    | _, Some file
      when not
             (String.is_suffix file ~suffix:".smt2"
             && Sys_unix.file_exists_exn file) ->
        None
    | _, Some file
      when Int64.(
             (Core_unix.stat file).st_size
             > of_int config.lower_bound_probe_max_input_bytes) ->
        Debug.print
        @@ lazy
             (sprintf "[lower-bound probe] not tried: %s is over %d bytes" file
                config.lower_bound_probe_max_input_bytes);
        None
    | names, Some file -> (
        let saved_inputs = Ast.LogicOld.get_input_record () in
        let relaxed = ref [] in
        let read =
          try
            Some
              (PCSP.Parser.lower_bound_linear_walk :=
                 config.lower_bound_relax_linear_walk;
               Common.PhaseTime.with_phase "read-lower-bound" @@ fun () ->
              PCSP.Parser.from_smt2_file
                 ~print:Debug.print ~inline:true ~skolem_pred:true
                 ~define_true_names:forced ~lower_bound_names:names
                 ~lower_bound_witness_causing:
                   config.lower_bound_probe_witness_causing
                 ~lower_bound_rounds:config.lower_bound_probe_rounds ~relaxed
                 file)
          with exn_ when not (Common.Timer.is_async exn_) -> None
        in
        Ast.LogicOld.set_input_record saved_inputs;
        PCSatCommon.TruePrecondition.last_lower_bound_probe := `Not_tried;
        if read_stages then
          eprintf "[lower-bound probe] read %s, relaxed %d, forced %d\n%!"
            (if Option.is_some read then "done" else "raised")
            (List.length !relaxed) (List.length forced);
        match read with
        | None -> None
        | Some _ when List.is_empty !relaxed -> None
        | Some relaxed_pcsp -> (
            Debug.print
            @@ lazy
                 (sprintf "[lower-bound probe] relaxing %s"
                    (String.concat ~sep:", "
                       (List.map !relaxed ~f:Ast.Ident.name_of_tvar)));
            let started = Common.Clock.now_s () in
            let answer =
              probing := true;
              Exn.protect
                ~finally:(fun () -> probing := false)
                ~f:(fun () ->
                  try
                    PCSatCommon.SolveDeadline.with_preprocessing_check
                      config.probe_deadline_in_preprocessing
                    @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                      ~seconds:
                        (Float.of_int config.lower_bound_probe_budget_ms
                        /. 1000.)
                      (fun () ->
                        Common.PhaseTime.with_phase "probe-lower-bound"
                          (fun () -> solve_one (encode_reading relaxed_pcsp)))
                  with exn_ when not (Common.Timer.is_async exn_) ->
                    Or_error.of_exn exn_)
            in
            let took = Common.Clock.now_s () -. started in
            match answer with
            | Ok (PCSP.Problem.Unsat _, info) ->
                Debug.print
                @@ lazy
                     (sprintf "[lower-bound probe] unsat in %.2f s; answering it"
                        took);
                PCSatCommon.TruePrecondition.last_lower_bound_probe :=
                  `Answered;
                Some (Ok (PCSP.Problem.Unsat None, info))
            | _ ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[lower-bound probe] no unsat in %.2f s; solving the \
                         problem as given"
                        took);
                PCSatCommon.TruePrecondition.last_lower_bound_probe :=
                  `Discarded;
                None))

  (* [solve] holds the problem it is given in a cell, and no closure or stack
     slot of it names the problem directly, so that once the cell is emptied
     nothing of [solve] keeps the problem alive.  After the solve the problem is
     read by the solution checker only (merging one answer is the identity, and
     the problem's id is taken before); without the checker the cell is
     emptied before solving, and the problem as given is then garbage as soon
     as preprocessing has built its normal form.  On a generated input of
     thousands of clauses that problem was a third of the live heap through
     preprocessing. *)
  (* [define_forced_true]: [Some (problem, names)] with the input re-read with
     its forced-true unknowns defined as [true], when there is at least one;
     [None] otherwise.  The caller solves that problem instead of the one given,
     and passes the names to the probes, which re-read the file themselves.

     Why both verdicts are read.  [PCSP.Parser.forced_true_unknowns] names only
     unknowns that are [true] at every argument in every solution, in every
     model of the theory, so the input and the re-read problem have the same
     solutions up to those unknowns: [sat] transfers with the [true]s added,
     and so does [unsat].  Re-reading the file sets the reader's process-wide
     record of the input assertions; it is left set to the re-read problem's,
     which is the one solved. *)
  (* [law_read_once]: whether the input was already read with the switches
     this configuration asks for ([set_law_reader_switches] before the first
     reading), so that reading it again would give the same problem *)
  let already_read file =
    config.law_read_once
    &&
    match !PCSP.Parser.last_plain_read with
    | Some r ->
        let reach, dedup, onepoint = law_reader_switches config in
        String.(r.file = file)
        && r.inline && r.skolem_pred
        && Bool.(r.law_reaches_dependents = reach)
        && Bool.(r.law_dedup_premises = dedup)
        && Bool.(r.onepoint_constructor_binders = onepoint)
        && Bool.(
             r.name_quantified_premises
             = (config.name_quantified_premises
               || !PCSP.Parser.name_quantified_premises))
    | None -> false

  (* [given], when passed, holds the problem the caller solves when this
     returns [None].  With [forced_true_release_given] and a non-empty list
     from the kept assertions, it is emptied before the reading, so that the
     two problems are never alive together; the caller must then not hold the
     problem anywhere else, and reads [!given = None] after a [None] as "read
     the input again". *)
  let forced_true_read ?(given = ref None) ~id ~filename () =
    match filename with
    | Some file
      when config.define_forced_true
           && String.is_suffix file ~suffix:".smt2"
           && Sys_unix.file_exists_exn file -> (
        let defined = ref [] in
        let valid phi =
          (not (Z3Smt.Z3interface.may_not_return phi))
          &&
          match
            Z3Smt.Z3interface.check_valid ~id ~timeout:(Some 1000)
              (Ast.LogicOld.get_fenv ()) phi
          with
          | `Valid -> true
          | _ -> false
        in
        (* [law_read_once]: the first reading kept its assertions, so the
           list this reading would define is computed from them; an empty
           list needs no reading (it would be discarded below), and a
           non-empty one is read once with it defined rather than first read
           to find it *)
        let known =
          if already_read file then
            Common.PhaseTime.with_phase "forced-true-kept" @@ fun () ->
            PCSP.Parser.forced_true_of_last_read ~file ~valid
          else None
        in
        PCSP.Parser.last_plain_assertions := None;
        if Option.equal (List.equal Ast.Ident.tvar_equal) known (Some []) then (
          LawDebug.print
          @@ lazy "[forced-true] nothing forced in the first reading; not re-read";
          None)
        else
        let saved_inputs = Ast.LogicOld.get_input_record () in
        (* a reading with a non-empty known list defines every unknown on it,
           so its answer is [Some] unless it raises: the given problem is
           needed afterwards only on that path, which reads the input again *)
        (match known with
        | Some (_ :: _) when config.forced_true_release_given ->
            LawDebug.print
            @@ lazy "[forced-true] first problem released before the reading";
            given := None
        | _ -> ());
        match
          Common.PhaseTime.with_phase "read-forced-true" @@ fun () ->
          match known with
          | Some known ->
              PCSP.Parser.from_smt2_file
                ~print:(fun _ -> ())
                ~inline:true ~skolem_pred:true ~define_true_known:known
                ~defined_true:defined file
          | None ->
              PCSP.Parser.from_smt2_file
                ~print:(fun _ -> ())
                ~inline:true ~skolem_pred:true ~define_forced_true:valid
                ~defined_true:defined file
        with
        | exception exn_ when not (Common.Timer.is_async exn_) ->
            Ast.LogicOld.set_input_record saved_inputs;
            None
        | _ when List.is_empty !defined ->
            if read_stages then
              eprintf "[forced-true] read, nothing defined (known %s)\n%!"
                (match known with None -> "none" | Some l -> Int.to_string (List.length l));
            Ast.LogicOld.set_input_record saved_inputs;
            None
        | restricted ->
            (* the reading set the record of the input assertions to the whole
               assertions; the Houdini pre-pass reads only their digest, which
               gives it what the assertions do *)
            Validation.Validator.HoudiniCandidates.digest_input_assertions ();
            if read_stages then
              eprintf "[forced-true] defined %d (known %s)\n%!" (List.length !defined)
                (match known with None -> "none" | Some l -> Int.to_string (List.length l));
            Debug.print
            @@ lazy
                 (sprintf "[forced-true] defined as true: %s"
                    (String.concat ~sep:", "
                       (List.map !defined ~f:Ast.Ident.name_of_tvar)));
            Some (restricted, !defined))
    | _ ->
        PCSP.Parser.last_plain_assertions := None;
        None

  (* [witness_seed_probe]: [Some] only with a [sat] of [pcsp] with its
     guarded witnesses defined as the last index ([PCSatCommon.WitnessSeed],
     which says why that [sat] is sound and nothing else is read) *)
  (* [least_definition_probe]: [Some] only with a [sat] answer of the input
     re-read with its witness-causing unknowns defined as their lower bounds
     ([PCSP.Parser.lower_bound_define]), extended with those definitions;
     [None] otherwise, and then the caller goes on as without the probe.

     Why the answer is sound.  The re-read problem is the input with the
     defined unknowns replaced, before the reader's skolemisation, by
     formulas that mention no unknown, so a solution of it together with the
     definitions makes each constraint of the input the corresponding
     constraint of the re-read one, which holds.  [unsat] does not transfer
     (the choice may be wrong) and is never read.  Re-reading the file sets
     the reader's process-wide record of the input assertions, which is put
     back before returning. *)
  let least_definition_probe ?(forced = []) ~filename ~solve_one given_senv =
    match filename with
    | _ when (not config.least_definition_probe) || !probing -> None
    | None -> None
    | Some file
      when not
             (String.is_suffix file ~suffix:".smt2"
             && Sys_unix.file_exists_exn file) ->
        None
    | Some file -> (
        let saved_inputs = Ast.LogicOld.get_input_record () in
        let defs = ref [] in
        let trues = ref [] in
        (* the assertions the problem in hand was made from, when their
           unknowns defined as [true] are exactly the ones this reading would
           define ([PCSP.Parser.least_definition_base]): the problem is then
           built from them, the same function of the same assertions, with no
           reading of the input *)
        let base =
          match !PCSP.Parser.least_definition_base with
          | Some b
            when String.(b.file = file)
                 && List.equal String.equal
                      (List.sort ~compare:String.compare
                         (List.map b.defined ~f:Ast.Ident.name_of_tvar))
                      (List.sort ~compare:String.compare forced) ->
              Some b
          | _ -> None
        in
        PCSP.Parser.least_definition_base := None;
        let read =
          try
            Some
              (PCSP.Parser.lower_bound_linear_walk :=
                 config.lower_bound_relax_linear_walk;
               match base with
               | Some b ->
                   Common.PhaseTime.with_phase "least-definition-from-read"
                   @@ fun () ->
                   trues := b.defined;
                   PCSP.Parser.least_definition_problem ~print:Debug.print
                     ~rounds:config.least_definition_probe_rounds
                     ~lower_bound_defined:defs b.phis b.envs
               | None ->
               Common.PhaseTime.with_phase "read-least-definition" @@ fun () ->
              PCSP.Parser.from_smt2_file ~print:Debug.print ~inline:true
                 ~skolem_pred:true ~define_true_names:forced
                 ~defined_true:trues
                 ~define_lower_bound_witness_causing:true
                 ~define_lower_bound_rounds:config.least_definition_probe_rounds
                 ~lower_bound_defined:defs file)
          with exn_ when not (Common.Timer.is_async exn_) -> None
        in
        Ast.LogicOld.set_input_record saved_inputs;
        match read with
        | None -> None
        | Some _ when List.is_empty !defs -> None
        | Some defined_pcsp -> (
            Debug.print
            @@ lazy
                 (sprintf "[least-definition probe] defining %s; true: %s"
                    (String.concat ~sep:", "
                       (List.map !defs ~f:(fun (x, _) ->
                            Ast.Ident.name_of_tvar x)))
                    (String.concat ~sep:", "
                       (List.map !trues ~f:Ast.Ident.name_of_tvar)));
            let started = Common.Clock.now_s () in
            let answer =
              probing := true;
              Exn.protect
                ~finally:(fun () -> probing := false)
                ~f:(fun () ->
                  try
                    PCSatCommon.SolveDeadline.with_preprocessing_check
                      config.probe_deadline_in_preprocessing
                    @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                      ~seconds:
                        (Float.of_int config.true_precondition_probe_budget_ms
                        /. 1000.)
                      (fun () ->
                        Common.PhaseTime.with_phase "probe-least-definition"
                          (fun () -> solve_one (encode_reading defined_pcsp)))
                  with exn_ when not (Common.Timer.is_async exn_) ->
                    Or_error.of_exn exn_)
            in
            let took = Common.Clock.now_s () -. started in
            match answer with
            | Ok (PCSP.Problem.Sat sol, info) ->
                Debug.print
                @@ lazy
                     (sprintf "[least-definition probe] sat in %.2f s" took);
                let sol =
                  Map.Poly.fold
                    (PCSatCommon.TruePrecondition.true_subst_senv given_senv
                       (List.filter !trues ~f:(Map.Poly.mem given_senv)))
                    ~init:sol
                    ~f:(fun ~key ~data acc -> Map.Poly.set acc ~key ~data)
                in
                Some
                  (Ok
                     ( PCSP.Problem.Sat
                         (List.fold !defs ~init:sol
                            ~f:(fun acc (x, (params, body)) ->
                              Map.Poly.set acc ~key:x
                                ~data:
                                  (Ast.Logic.Term.mk_lambda
                                     (Ast.Logic.of_old_sort_env_list params)
                                     (Ast.Logic.ExtTerm.of_old_formula body)))),
                       info ))
            | _ ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[least-definition probe] no sat in %.2f s; going on"
                        took);
                None))

  let witness_seed_probe ~solve_one pcsp =
    if (not config.witness_seed_probe) || !probing then None
    else
      match
        Common.PhaseTime.with_phase "witness-seed" (fun () ->
            PCSatCommon.WitnessSeed.seeds
              ~filter_disjuncts:config.witness_seed_filter_disjuncts pcsp)
      with
      | [] -> None
      | defs -> (
          let sub = Map.Poly.of_alist_exn defs in
          match PCSP.Problem.subst sub pcsp with
          | exception exn_ when not (Common.Timer.is_async exn_) -> None
          | seeded -> (
              Debug.print
              @@ lazy
                   (sprintf "[witness-seed probe] seeding %s"
                      (String.concat ~sep:", "
                         (List.map defs ~f:(fun (w, _) -> Ast.Ident.name_of_tvar w))));
              let answer =
                probing := true;
                Exn.protect
                  ~finally:(fun () -> probing := false)
                  ~f:(fun () ->
                    try
                      PCSatCommon.SolveDeadline.with_preprocessing_check
                      config.probe_deadline_in_preprocessing
                    @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                        ~seconds:
                          (Float.of_int config.true_precondition_probe_budget_ms
                          /. 1000.)
                        (fun () ->
                          Common.PhaseTime.with_phase "probe-witness-seed"
                            (fun () -> solve_one seeded))
                    with exn_ when not (Common.Timer.is_async exn_) ->
                      Or_error.of_exn exn_)
              in
              match answer with
              | Ok (PCSP.Problem.Sat sol, info) ->
                  Some
                    (Ok
                       ( PCSP.Problem.Sat
                           (List.fold defs ~init:sol ~f:(fun acc (w, d) ->
                                Map.Poly.set acc ~key:w ~data:d)),
                         info ))
              | _ -> None))

  (* [law_reach_dependents]: the input re-read with each [:law] premise also
     in the assertions that apply an unknown depending on the law's function;
     [law_dedup_premises = false]: every premise inserted whole, the reading
     before the reader's default deduplication (an equivalent problem);
     [onepoint_constructor_binders = false]: re-read WITHOUT the removal of
     the existentials a constructor equation fixes, which the reader otherwise
     applies before skolemisation (any combination).  The reader's switches
     are only ever moved away from their defaults here, as
     [evaluate_sequences] is, so a later re-read in this process (the
     forced-[true] reading) keeps them.  The re-read sets the reader's record
     of the input assertions to its own, which is the problem solved. *)
  let law_dependents_read ~filename =
    (* the reader applies the rewrite unless told not to, so only switching it
       OFF needs a second reading *)
    let rewritten_first = !PCSP.Problem.onepoint_constructor_binders in
    if not config.onepoint_constructor_binders then
      PCSP.Problem.onepoint_constructor_binders := false;
    (* [name_quantified_premises] is only ever turned on here, like the reader's other
       switches; a reading that has not named the premises is then read again *)
    let name_premises =
      config.name_quantified_premises && not !PCSP.Parser.name_quantified_premises
    in
    if config.name_quantified_premises then
      PCSP.Parser.name_quantified_premises := true;
    match filename with
    | Some file
      when (config.law_reach_dependents || (not config.law_dedup_premises)
           || ((not config.onepoint_constructor_binders) && rewritten_first)
           || name_premises)
           && String.is_suffix file ~suffix:".smt2"
           && Sys_unix.file_exists_exn file
           && already_read file ->
        LawDebug.print
        @@ lazy "[law premises] input already read with these switches; not re-read";
        None
    | Some file
      when (config.law_reach_dependents || (not config.law_dedup_premises)
           || ((not config.onepoint_constructor_binders) && rewritten_first)
           || name_premises)
           && String.is_suffix file ~suffix:".smt2"
           && Sys_unix.file_exists_exn file ->
        if config.law_reach_dependents then
          SMT.Smtlib2.law_reaches_dependents := true;
        if not config.law_dedup_premises then
          SMT.Smtlib2.law_dedup_premises := false;
        LawDebug.print
        @@ lazy
             (sprintf "[law premises] input re-read (reach dependents %b, dedup %b)"
                !SMT.Smtlib2.law_reaches_dependents
                !SMT.Smtlib2.law_dedup_premises);
        let pcsp =
          Common.PhaseTime.with_phase "read-law" @@ fun () ->
          PCSP.Parser.from_smt2_file
            ~print:(fun _ -> ())
            ~inline:true ~skolem_pred:true file
        in
        (* the reading set the record of the input assertions to the whole
           assertions again; the Houdini pre-pass reads only their digest, and
           the digest gives it what the assertions do, so keep only that *)
        Validation.Validator.HoudiniCandidates.digest_input_assertions ();
        Some pcsp
    | _ -> None

  (* a [sat] of the problem with [defined] read as [true], made one of the
     problem as given, whose unknowns' sorts are [given_senv] (only the
     signature is read, so the problem itself need not be kept for this) *)
  let with_trues given_senv defined = function
    | Ok (PCSP.Problem.Sat sol, info) when not (List.is_empty defined) ->
        let trues =
          PCSatCommon.TruePrecondition.true_subst_senv given_senv
            (List.filter defined ~f:(Map.Poly.mem given_senv))
        in
        Ok
          ( PCSP.Problem.Sat
              (Map.Poly.fold trues ~init:sol ~f:(fun ~key ~data acc ->
                   Map.Poly.set acc ~key ~data)),
            info )
    | answer -> answer

  (* [race_probe ~on ~name probe next]: the answers of a probe placed before
     [next] -- the probe's answer when it has one, [next ()] otherwise.  With
     [on], [probe] is raced in a forked copy against [next ()]
     ([PCSatCommon.ParallelRace]): the copy that has an answer becomes the run
     and returns it here, as the sequential order would have at this point;
     the process kills the copy before its own answer leaves, and when the
     process cannot fork (it has a domain) the order is the sequential one.

     Contract: [probe] returns [Some] only with an answer that is sound on its
     own, whatever [next] would answer -- a probe that reads one verdict
     only, by an argument that does not depend on running before or after
     anything else.  Then every answer the race can give is one the
     sequential order could give: the copy's is the probe's, and the
     process's is [next]'s, which the sequential order gives whenever the
     probe has none.  A copy forked here holds the process's heap as it was
     (the operating system copies it on write), so its memory counts against
     the run's beside the process's own. *)
  let race_probe ~on ~name probe next =
    let sequential () =
      match probe () with Some answer -> [ answer ] | None -> next ()
    in
    if not on then sequential ()
    else if
      config.probe_races_in_process_when_large
      && not
           (Common.ForkGuard.fork_fits
              ~heap_bytes:(Common.ForkGuard.major_heap_bytes ())
              ~headroom:(Common.ForkGuard.cgroup_headroom_bytes ()))
    then
      (* too large to copy: the probe in its sequential place *)
      match Common.PhaseTime.with_phase (name ^ "-in-process") probe with
      | Some answer -> [ answer ]
      | None -> next ()
    else
      match
        Common.PhaseTime.with_phase (name ^ "-fork") (fun () ->
            PCSatCommon.ParallelRace.start ~nice:config.probe_copy_nice
              ~report:(fun () ->
                Common.PhaseTime.report ~reason:(name ^ "-copy-answered"))
              ~log:(fun msg ->
                (* a line of the phase account, so only when it is on *)
                if !Common.PhaseTime.on || !Common.PhaseTime.in_child then (
                  prerr_endline
                    (sprintf "phase-time-race: at=%.3f %s: %s"
                       (Common.PhaseTime.now () -. Common.PhaseTime.t0)
                       name msg);
                  Out_channel.flush stderr))
              probe)
      with
      | `Won answer -> [ answer ]
      | `Racing race ->
          Exn.protect
            ~finally:(fun () -> PCSatCommon.ParallelRace.finish race)
            ~f:next
      | `Not_started -> sequential ()

  let rec solve ?(bpvs = Set.Poly.empty) ?(filename = None) ?(print_sol = false)
      ?(solution_read = true) pcsp =
    solve_cell ~bpvs ~filename ~print_sol ~solution_read (ref (Some pcsp))

  and solve_cell ~bpvs ~filename ~print_sol ~solution_read cell =
    let open Or_error in
    (* the input's own assertions are read by the Houdini pre-pass only, and
       only through a digest that is a fraction of them *)
    Common.PhaseTime.with_phase "digest-input"
      Validation.Validator.HoudiniCandidates.digest_input_assertions;
    (* only ever turned ON here: the switch is process-wide, and a second
       solver in the same process whose configuration leaves it off must not
       switch it off under one that is running with it on *)
    if config.evaluate_sequences then
      Atomic.set Ast.Evaluator.evaluate_sequences true;
    (* only ever turned ON here, for the same reason *)
    if config.race_drop_duplicate_copies then
      PCSatCommon.ParallelRace.Duplicate.drop_duplicates := true;
    if config.race_drop_duplicates_early then
      PCSatCommon.ParallelRace.Duplicate.early := true;
    (* only ever turned ON here, for the same reason *)
    if config.race_two_claims then PCSatCommon.ParallelRace.two_claims := true;
    sol_printer >>= fun (module SolPrinter : SolPrinter.SolPrinterType) ->
    preprocessor
    >>= fun (module Preprocessor : Preprocessor.PreprocessorType) ->
    coordinator >>= fun (module Coordinator : Coordinator.CoordinatorType) ->
    let id, pcsps =
      let pcsp = Option.value_exn !cell in
      ( PCSP.Problem.id_of pcsp,
        if config.solve_each_query then PCSP.Problem.divide pcsp else [ pcsp ]
      )
    in
    if not (config.check_solution || List.length pcsps > 1) then cell := None;
    let oracle =
      if config.load_oracle_sol then
        Option.(
          filename >>= fun filename ->
          let basename =
            fst @@ Filename.split_extension @@ snd @@ Filename.split filename
          in
          let problem_file = filename in
          let filename =
            match config.oracle_sol_dir with
            | None -> "./" ^ basename ^ ".sol"
            | Some dir -> Filename.concat dir (basename ^ ".sol")
          in
          if config.oracle_sol_smtlib2 then
            match
              PCSP.Parser.oracle_of_smt2_file
                ~print:(fun _ -> ())
                ~problem_file filename
            with
            | defs -> Some (Map.Poly.empty, Set.Poly.of_list defs)
            | exception exn when not (Common.Timer.is_async exn) ->
                failwith
                @@ sprintf "failed to load %s: %s" filename (Exn.to_string exn)
          else
            match SyGuS.Parser.solution_from_file filename with
            | Ok defs ->
                Some
                  ( Map.Poly.empty,
                    Set.Poly.of_list
                    @@ List.map defs ~f:Ast.CandSolOld.of_fundef )
            | Error _ -> failwith @@ sprintf "failed to load %s" filename)
      else None
    in
    let extend =
      solution_read || config.check_solution
      || (print_sol && SolPrinter.prints_solution)
    in
    (* [prune_unreached_definitions]: the problem the CEGIS loop starts from
       keeps in its function environment only the definitions its clauses
       reach (see [PCSP.Problem.prune_unreached_definitions]) *)
    let prune p =
      if config.prune_unreached_definitions then
        PCSP.Problem.prune_unreached_definitions p
      else p
    in
    let solve_one =
      Preprocessor.solve ~witness:config.witness ~bpvs ~oracle ~extend
        ?post_elim:post_elim_encoding ~nested_solver:(fun p ->
          Context.isolated context (fun () ->
              Coordinator.solve ~witness:config.witness ~oracle:None (prune p)))
        (fun ?oracle p ->
          post_preprocessing_solve
            (fun p ->
              Coordinator.solve ~witness:config.witness ?oracle
                (* under the dynamic encoding the function environment stays
                   whole: an example carried across a restart may mention a
                   counted function's terms *)
                (if rec_fun_graph_post && config.rec_fun_graph_dynamic then p
                 else prune p))
            p)
    in
    (* the problem solved when [law_reach_dependents] re-reads the input; the
       checker below checks against it, not against [!cell] *)
    let law_read =
      match pcsps with
      | [ _ ] -> law_dependents_read ~filename
      | _ -> None
    in
    (* what the checker reads it for; kept apart so that, without the checker,
       nothing holds the re-read problem once the forced-true reading has
       replaced it *)
    let checked_law_read = if config.check_solution then law_read else None in
    (match pcsps with
    | [ pcsp ] -> (
        let pcsp = Option.value law_read ~default:pcsp in
        let pcsp = encode_rec_fun_graph pcsp in
        (* only the signature of the problem as given is read after the
           forced-true reading ([with_trues], the least-definition probe), so
           the problem itself is held only by [given] during that reading,
           and not at all once it has answered *)
        let given_senv = PCSP.Problem.senv_of pcsp in
        let given = ref (Some pcsp) in
        let pcsp, forced =
          match forced_true_read ~given ~id ~filename () with
          | Some (restricted, defined) -> (encode_reading restricted, defined)
          | None -> (
              match !given with
              | Some pcsp -> (pcsp, [])
              | None ->
                  (* released before a reading that then raised: the input
                     read again under the switches of the first reading,
                     which gives its problem up to fresh names *)
                  let file = Option.value_exn filename in
                  let pcsp =
                    Common.PhaseTime.with_phase "read-forced-true-fallback"
                    @@ fun () ->
                    PCSP.Parser.from_smt2_file
                      ~print:(fun _ -> ())
                      ~inline:true ~skolem_pred:true file
                  in
                  Validation.Validator.HoudiniCandidates.digest_input_assertions ();
                  (encode_rec_fun_graph pcsp, []))
        in
        given := None;
        (* [reconstruct_rec_functions], [rec_function_lemmas]: applied to the
           problem that is solved, whichever reading produced it *)
        let pcsp =
          if config.reconstruct_rec_functions || config.rec_function_lemmas
          then (
            if config.reconstruct_rec_functions then
              Atomic.set PCSatCommon.RecFunReconstruct.qual_limit
                config.reconstructed_fun_quals;
            let out =
              Common.PhaseTime.with_phase "reconstruct-functions" @@ fun () ->
              PCSatCommon.RecFunReconstruct.reconstruct
                ~print:Debug.print ~names_apart:config.reconstruct_names_apart
                ~functions:config.reconstruct_rec_functions
                ~replace:config.reconstruct_replace_predicates
                ~lemmas:config.rec_function_lemmas pcsp
            in
            Debug.print
            @@ lazy
                 (sprintf
                    "reconstruct_rec_functions: %d reconstructed, %d \
                     refused, %d replaced, lemmas for %d function(s)"
                    (List.length out.reconstructed)
                    (List.length out.refused)
                    (List.length out.replaced)
                    (List.length out.lemmas));
            out.problem)
          else pcsp
        in
        let forced_names = List.map forced ~f:Ast.Ident.name_of_tvar in
        List.map ~f:(with_trues given_senv forced)
        @@
        (* The probes, in their sequential order: least-definition,
           witness-seed, true-precondition, lower-bound, then the problem as
           given.  Each probe answers with one verdict only and is discarded
           otherwise; each one switched to a race ([race_probe]) is started in
           a forked copy at its place in this order and everything after it
           runs concurrently in the process, so up to four copies race at
           once, nested: each race's [finish] encloses the races started after
           it, and the process hands itself over to at most one copy. *)
        let lower_bound () =
          lower_bound_probe ~forced:forced_names ~filename ~solve_one ()
        in
        let given_problem () = [ solve_one pcsp ] in
        (* [lower_bound_probe_parallel]: the probe raced against the problem
           as given.  The copy answers only with the probe's [unsat], sound on
           its own (see [lower_bound_probe]); a satisfiable input -- every
           input the probe does not answer by design -- no longer waits for
           the probe's whole time, which its budget does not bound. *)
        let after_true_precondition () =
          race_probe
            ~on:
              (config.lower_bound_probe_parallel
              && ((not (List.is_empty config.lower_bound_probe))
                 || config.lower_bound_probe_witness_causing)
              && not !probing)
            ~name:"probe-lower-bound" lower_bound given_problem
        in
        let true_precondition () =
          true_precondition_probe ~forced:forced_names ~filename ~solve_one pcsp
        in
        (* [true_precondition_probe_parallel]: the probe raced in a forked
           copy against the rest.  The copy answers only with the probe's
           [sat], which is sound on its own (see [true_precondition_probe]),
           and then runs the rest of the program as the sequential probe would
           have; the process kills the copy before its own answer leaves.  So
           each answer the process can give is one the sequential order could
           give, and the probe's time no longer delays the rest. *)
        let after_witness_seed () =
          race_probe
            ~on:
              (config.true_precondition_probe_parallel
              && true_precondition_probe_on ())
            ~name:"probe-true-precondition" true_precondition
            after_true_precondition
        in
        (* [witness_seed_probe_parallel]: the probe, its seeding included,
           raced against everything after it.  The copy answers only with the
           probe's [sat] extended with the seeds, sound on its own (see
           [witness_seed_probe]); an input the probe does not answer no longer
           waits for its seeding and its seeded solve, neither of which its
           budget bounds. *)
        let after_least () =
          (* the process's copy of the base the least-definition probe may
             build from; the probe has taken it (in a forked copy, or before
             this point in order) *)
          PCSP.Parser.least_definition_base := None;
          race_probe
            ~on:
              (config.witness_seed_probe && config.witness_seed_probe_parallel
              && not !probing)
            ~name:"probe-witness-seed"
            (fun () -> witness_seed_probe ~solve_one pcsp)
            after_witness_seed
        in
        let least () =
          least_definition_probe ~forced:forced_names ~filename ~solve_one
            given_senv
        in
        (* [least_definition_probe_parallel]: the probe raced in a forked copy
           against everything after it.  The copy answers only with the
           probe's [sat], sound on its own (see [least_definition_probe]).
           Sequentially the probe's whole time is added to every input it does
           not answer -- every unsatisfiable one, since an [unsat] of the
           defined problem is never read -- and on an input whose defined
           problem is the unsatisfiable twin of the lower-bound probe's
           relaxation, the probe solves nearly that relaxation (the same
           preprocessing and zero-unknown check) only to discard the answer
           the lower-bound probe then computes again. *)
        race_probe
          ~on:
            (config.least_definition_probe
            && config.least_definition_probe_parallel
            && not !probing)
          ~name:"probe-least-definition" least after_least)
    | _ -> List.map pcsps ~f:solve_one)
    |> Or_error.combine_errors
    >>= fun res ->
    let sols, infos = List.unzip res in
    let solution =
      match (sols, !cell) with
      | [ sol ], _ -> sol
      | _, Some pcsp -> PCSP.Problem.merge_sols pcsp sols
      | _, None -> assert false
    in
    let info = State.merge_infos infos in
    (* The tidied solution is computed only when something reads it: the
       printer when it shows solutions, or the checker.  Otherwise the answer
       printed is the verdict alone, and the tidying -- a quantifier
       elimination per definition, each with a budget of a second, over
       definitions that closing the eliminated predicates' records may have
       made large -- cost minutes on inputs whose every predicate was
       eliminated by resolution, before a verdict decided long before was
       printed.  The value returned is then the solution as assembled, which
       the callers that print read only for its verdict.  When only the
       checker reads it, the verdict is printed first, so that a tidying or a
       check that runs long does not withhold an answer already decided. *)
    let tidy_for_check =
      print_sol && config.witness.sat && config.check_solution
      && not SolPrinter.prints_solution
    in
    let solution =
      if print_sol && config.witness.sat && SolPrinter.prints_solution then
        Common.PhaseTime.with_phase "tidy" (fun () ->
            tidy_solution_for_printing solution)
      else solution
    in
    if print_sol then (
      (* a raced copy that took the run over without a final answer asks for
         the right to print here (with [race_two_claims]) *)
      Common.ForkGuard.before_verdict ();
      SolPrinter.print (solution, info));
    let solution =
      if tidy_for_check then
        Common.PhaseTime.with_phase "tidy" (fun () ->
            tidy_solution_for_printing solution)
      else solution
    in
    if print_sol then
      Debug.print @@ lazy (Z3Smt.Z3interface.fresh_retry_report ());
    if print_sol then
      SeqAxDebug.print @@ lazy (Z3Smt.Z3interface.seq_axiom_fallback_report ());
    if print_sol then
      SeqAxDebug.print @@ lazy (Z3Smt.Z3interface.clean_pool_report ());
    (* the simplifier's process-wide switches as this run saw them, so that a
       run configured to turn them on can be shown to have done so *)
    if print_sol then
      SeqAxDebug.print
      @@ lazy
           (sprintf "(simplify-switches (normal-forms %b) (skip-simplified %b))"
              (Atomic.get Ast.Evaluator.simplify_normal_forms)
              (Atomic.get Ast.Evaluator.simplify_skip_simplified));
    (* [check_solution] re-verifies the answer (WitnessChecker); the report
       goes to stdout with the answer, to stderr otherwise *)
    (if config.check_solution then
       match
         (* A CHECKER THAT CANNOT CHECK HAS TO SAY SO, NOT RAISE.  This runs
            after the answer has been printed, so anything escaping here ends
            the process with a backtrace and a non-zero status on a run that
            has already succeeded -- the answer is on stdout and the shell is
            told the tool failed.  The checker's own rule is to prefer
            "unchecked, and here is why" over a verdict it cannot justify, and
            an internal failure is the strongest case for it: a wrong
            accusation costs more than a missing one, and a crash costs more
            than either.  The timeout guard is kept, because the alarm raises
            into whichever frame is running and turning that into a report
            would lose the timeout. *)
         try
           (* With [law_reach_dependents], against the re-read problem, the one
              solved, and not the problem as first read.  The two differ only
              in premises: the re-read one has a law [L] also before each
              clause [C] that applies an unknown depending on the law's
              function.  The problem the laws state reads every such clause
              as "for every lawful interpretation of the function", that is
              [(forall L) => C].  So:
              - sat: a solution of the re-read problem makes [L => C] valid,
                which implies [(forall L) => C], so it solves the stated
                problem; checked against the first reading, which demands
                the bare [C] also for unlawful interpretations, a correct
                answer would be reported failed.
              - unsat: the witness is a derivation from the re-read problem's
                clauses and is checked against them; a refutation of the first
                reading would not be one of the problem solved.  Certified, it
                refutes the re-read problem; that is a refutation of the
                stated problem when every law is closed (then [L => C] is
                [(forall L) => C] exactly) and a lawful interpretation exists,
                and otherwise of a problem stronger than the stated one, an
                open law assuming only its instance at the clause's
                variables.
              The stated problem itself is not a pfwCSP the checker could be
              handed when a law is open, so the re-read problem is the
              nearest reference it can check; for closed laws it is the
              stated problem.
              And against the problem with every answer position of an
              admissible or integrable unknown relativised to the
              non-negative reals, which is the problem's meaning and what the
              preprocessor solves by default: a solution need not hold at a
              negative answer value, and a refutation resting on one is not a
              refutation *)
           Common.PhaseTime.with_phase "check-solution" @@ fun () ->
           WitnessChecker.check ~seq_as_array:config.seq_as_array_check_solution
             ~retry:config.retry_undecided_check_solution
             ?matched:checker_matched_forms
             ?ladder:(Result.ok (ExtFile.unwrap config.coordinator))
             ~id
             (PCSP.Problem.relativise_prop_positions
                (match checked_law_read with
                | Some read -> read
                | None -> Option.value_exn !cell))
             (solution, info)
         with exn_ when not (Common.Timer.is_async exn_) ->
           Some
             (sprintf "(check (unchecked 1) (reason \"%s\"))"
             @@ String.concat ~sep:" " @@ String.split_lines
             @@ String.substr_replace_all ~pattern:"\"" ~with_:"'"
             @@ Exn.to_string exn_)
       with
       | None -> ()
       | Some report ->
           if print_sol then (
             Out_channel.print_endline report;
             Out_channel.flush stdout)
           else Out_channel.prerr_endline report);
    Or_error.return (solution, info)

  let preprocess ?(bpvs = Set.Poly.empty) pcsp =
    let open Or_error in
    preprocessor
    >>= fun (module Preprocessor : Preprocessor.PreprocessorType) ->
    Or_error.return (snd @@ Preprocessor.preprocess ~bpvs pcsp)

  let reset () = Context.reset context
  let push () = Context.push context
  let pop () = ignore @@ Context.pop context
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
