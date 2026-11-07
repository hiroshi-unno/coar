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
    ?sygus_signature:SyGuS.Printer.signature ->
    PCSP.Problem.t ->
    State.output Or_error.t
  (** [solution_read] ([true] by default): whether the caller reads the
      solution returned with a [sat] verdict.  When it does not, the solution is
      not completed with the definitions of the predicates preprocessing
      eliminated, unless this solver prints it or checks it itself; the verdict
      and the printed answer are the same.  [sygus_signature]: the functions
      the SyGuS input the problem was read from requests, which a printed
      SyGuS-format answer defines exactly. *)

  val prints_solution : unit -> bool
  (** whether [solve ~print_sol:true] prints a [sat] answer's solution (the
      SyGuS format), which then is the whole answer: under that format every
      verdict is printed in the format's own words, so a caller adds no
      verdict line of its own *)

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
  ( (* the dependents' reading is the reader's own, asked for by every
       configuration; a test may have moved the reader off it *)
    true,
    config.reader.laws.dedup_premises && !SMT.Smtlib2.law_dedup_premises,
    config.reader.onepoint_constructor_binders
    && !PCSP.Problem.onepoint_constructor_binders )

(* [law_reader_switches config] applied to the reader, for a caller about to read the input that
   [config] will solve, so that the reading is the one the solver would otherwise make again *)
let set_law_reader_switches (config : Config.t) =
  let reach, dedup, onepoint = law_reader_switches config in
  SMT.Smtlib2.law_reaches_dependents := reach;
  SMT.Smtlib2.law_dedup_premises := dedup;
  PCSP.Problem.onepoint_constructor_binders := onepoint;
  if config.reader.fold_inlined_selector_reads then
    SMT.Smtlib2.fold_inlined_selector_reads := true;
  if config.reader.skolem_body_variables_only then
    PCSP.Problem.skolem_body_variables_only := true;
  if config.reader.name_quantified_premises then
    PCSP.Parser.name_quantified_premises := true;
  if config.reader.premise_witness_disjuncts then
    SMT.Smtlib2.premise_witness_disjuncts := true

(* The forced-collection rules before a new Z3 context that [config] asks for
   ([z3.collections]), written to the process-wide settings.
   Only a value other than the library's default is written, so a nested
   solver configured with the default does not undo what the top-level one
   asked for, and writing the same configuration twice changes nothing.

   It is called when the solver is built and, before that, by the solving
   entry for a problem this configuration will solve, so that the questions
   asked before the solver exists (the known-function context admission's
   fresh contexts) are collected for under the configured rule rather than
   the library's one-collection-per-context default.  Only the collector's
   timing depends on this; the questions asked are the same. *)
let set_z3_collector_policy (config : Config.t) =
  match config.z3.collections with
  | By_count { new_context; seq_axiom } ->
      if new_context <> 1 then
        Z3Smt.Z3interface.set_new_context_full_major_every new_context;
      if seq_axiom <> 1 then
        Z3Smt.Z3interface.set_seq_axiom_full_major_every seq_axiom
  | By_bytes { bytes } ->
      (* the byte rule replaces every count rule, so no count is set *)
      Z3Smt.Z3interface.set_new_context_full_major_bytes (Some bytes)
  | By_z3_memory { megabytes } ->
      (* the Z3 memory rule replaces every count rule and the byte rule *)
      Z3Smt.Z3interface.set_new_context_full_major_z3_mb (Some megabytes)

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

(* how many times a seeded problem was solved after preprocessing
   ([probes.witness_seed.after_preprocessing]); read by its property test *)
let seeded_after_preprocessing_solves = Atomic.make 0

(* how many times [probes.witness_seed.after_preprocessing] deferred seeds found on
   the problem as given (the sequential probe's own solve then skipped);
   read by its property test *)
let seeds_deferred_to_preprocessing = Atomic.make 0

(* how many times a solve at depth 1 found deferred seeds waiting and left
   them, because it was a probe's solve rather than the given problem's; read
   by its property test *)
let seeds_left_for_given_problem = Atomic.make 0

(* the configuration's types, named apart from the functor's parameter *)
module PCSatConfig = Config

(* [ub_filter_key phi]: [phi] printed, then its free variables with their
   sorts (which the printing leaves out), with every reader-drawn name
   [#tvar<n>] replaced by the number of distinct such names met before its
   first occurrence in the printed formula.  Guarantees: two formulas with the
   same key are the same formula up to a one-to-one renaming of their [#tvar]
   names, as far as the printer distinguishes formulas, with their free
   variables at the same sorts, and so are equivalent; a formula and its copy
   with those names drawn afresh (as a second reading of the same input draws
   them) have the same key, since the printer shows the copy's names where it
   shows the original's.  The upper-bound definition probe keys its candidate
   filter's answers on it. *)
let ub_filter_key phi =
  let s = Ast.LogicOld.Formula.str_of phi in
  let n = String.length s and prefix = "#tvar" in
  let names = Hashtbl.create (module String) in
  let canon v =
    match Hashtbl.find names v with
    | Some k -> k
    | None ->
        let k = sprintf "\001%d" (Hashtbl.length names) in
        Hashtbl.set names ~key:v ~data:k;
        k
  in
  let buf = Buffer.create n in
  let rec go i =
    if i < n then
      if
        String.is_substring_at s ~pos:i ~substring:prefix
        && i + 5 < n
        && Char.is_digit s.[i + 5]
      then (
        let j = ref (i + 5) in
        while !j < n && Char.is_digit s.[!j] do incr j done;
        Buffer.add_string buf (canon (String.sub s ~pos:i ~len:(!j - i)));
        go !j)
      else (
        Buffer.add_char buf s.[i];
        go (i + 1))
  in
  go 0;
  (* the free variables' sorts, each variable under its renamed name (a
     name the printing did not show is renamed after all the shown ones), in
     the order of those names, so that the list does not depend on the names
     drawn *)
  let renamed name =
    if
      String.is_prefix name ~prefix
      && String.length name > 5
      && String.for_all (String.drop_prefix name 5) ~f:Char.is_digit
    then canon name
    else name
  in
  Set.to_list (Ast.LogicOld.Formula.term_sort_env_of phi)
  |> List.map ~f:(fun (x, sort) ->
         ( renamed (Ast.Ident.name_of_tvar x),
           Ast.LogicOld.Term.str_of_sort sort ))
  |> List.sort ~compare:(fun (x1, s1) (x2, s2) ->
         match String.compare x1 x2 with 0 -> String.compare s1 s2 | c -> c)
  |> List.iter ~f:(fun (x, sort) ->
         Buffer.add_string buf (sprintf "\000%s:%s" x sort));
  Buffer.contents buf

(* [ub_filter_fingerprint phi]: what of [phi] does not depend on the order
   its disjuncts and binders come in, nor on the reader's [#tvar] names: the
   characters of its printing with every such name written [V], counted, and
   the sorts of its free variables, sorted.  Two formulas with different
   fingerprints differ; the converse does not hold, so the probe compares it
   only beside a position that already names the question (see its use). *)
let ub_filter_fingerprint phi =
  let s = Ast.LogicOld.Formula.str_of phi in
  let n = String.length s in
  let counts = Array.create ~len:256 0 in
  let rec go i =
    if i < n then
      if
        String.is_substring_at s ~pos:i ~substring:"#tvar"
        && i + 5 < n
        && Char.is_digit s.[i + 5]
      then (
        let j = ref (i + 5) in
        while !j < n && Char.is_digit s.[!j] do incr j done;
        counts.(Char.to_int 'V') <- counts.(Char.to_int 'V') + 1;
        go !j)
      else (
        counts.(Char.to_int s.[i]) <- counts.(Char.to_int s.[i]) + 1;
        go (i + 1))
  in
  go 0;
  String.concat ~sep:","
    (List.filter_mapi (Array.to_list counts) ~f:(fun c k ->
         if k = 0 then None else Some (sprintf "%d:%d" c k)))
  ^ "\000"
  ^ String.concat ~sep:"\000"
      (List.sort ~compare:String.compare
         (List.map
            (Set.to_list (Ast.LogicOld.Formula.term_sort_env_of phi))
            ~f:(fun (_, sort) -> Ast.LogicOld.Term.str_of_sort sort)))

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  (* Constructed before any solving domain exists, so setting the process-wide
     switch here is race-free; it is only ever turned on. *)
  let () =
    if config.simplifier.seq_read_range_guard then
      Ast.ClauseOld.enable_seq_read_range_guard ()

  (* the ground-range expansion of questions, set here for the same reason and
     only ever turned on *)
  let () =
    match config.ground_range_expansion with
    | Some w -> Ast.RangePin.set_ground_expansion_width (Some w)
    | None -> ()

  (* The simplifier's process-wide switches, written here for the same
     reason as the guard above and only ever turned on: a nested solver whose
     configuration leaves them off must not switch them off under one running
     with them on. *)
  let () =
    if config.simplifier.normal_forms then
      Atomic.set Ast.Evaluator.simplify_normal_forms true;
    if config.simplifier.abstract_oor_reads_under_binders then
      Atomic.set Ast.Evaluator.abstract_out_of_range_reads_under_binders true;
    if config.simplifier.skip_simplified then
      Atomic.set Ast.Evaluator.simplify_skip_simplified true;
    if config.simplifier.let_inline_by_expanded_size then
      Atomic.set Ast.Evaluator.inline_by_expanded_size true;
    if config.simplifier.binders_outer_first then
      Atomic.set Ast.Evaluator.merge_binders_outer_first true

  let () =
    if config.simplifier.hspace_normalize_memo then
      Atomic.set Ast.HypSpace.normalize_memo true

  let context = Context.create ()

  (* The sequence-axiom fallback is process-global, so it is written here,
     when the configuration is loaded and before any solving domain exists; a
     configuration that leaves it off does not switch off what another one
     asked for. *)
  let () =
    Option.iter config.z3.seq_axiom_fallback_ms
      ~f:Z3Smt.Z3interface.set_seq_axiom_fallback

  (* process-wide like the fallback above; see [set_z3_collector_policy] *)
  let () = set_z3_collector_policy config

  let () =
    match config.z3.pool with
    | Fresh_contexts -> ()
    | Clean_pool { max_uses } ->
        Z3Smt.Z3interface.set_clean_pool_max_uses max_uses;
        Z3Smt.Z3interface.set_clean_reset_pool true

  (* process-wide; the last configuration loaded decides *)
  let () =
    Z3Smt.Z3interface.set_seq_axiom_fork_runner
      (if config.z3.seq_axiom_fork then
         Some (fun ~ms ask -> PCSatCommon.ForkedQuery.run_forked ~ms ask)
       else None)

  (* process-wide like the fallback above; a configuration that leaves it off
     does not switch off what another one asked for *)
  let () =
    let definitions = config.recursive_functions.definitions in
    if Option.is_some definitions.open_residual_rlimit then
      Z3Smt.Z3interface.set_known_function_open_residual_rlimit
        definitions.open_residual_rlimit

  (* process-wide like the residual budget above; the default does not undo
     what another configuration asked for *)
  let () =
    match config.recursive_functions.definitions.residual_contexts with
    | Residual_fresh -> ()
    | Residual_clean_pool ->
        Z3Smt.Z3interface.set_known_function_residual_contexts
          Residual_clean_pool
    | Residual_full_major_every n ->
        Z3Smt.Z3interface.set_known_function_residual_contexts
          (Residual_full_major_every (Int.max 1 n))

  let () = if config.z3.flat_and_or then Z3Smt.Z3interface.set_flat_and_or true

  (* process-wide as well; a configuration that leaves it unset does not undo
     what another one set *)
  let () =
    Option.iter config.z3.flat_long_and_or_min ~f:(fun n ->
        Z3Smt.Z3interface.set_flat_long_and_or_min (Some n))

  let () =
    if config.z3.left_to_right_creation then
      Z3Smt.Z3interface.set_left_to_right_creation true

  (* the rewrite's switches are set only with the rewrite on, where they are
     read *)
  let () =
    match config.z3.int_to_bv with
    | No_int_to_bv -> ()
    | Range { mod_pow2; twins; split_ask_original } ->
        Z3Smt.Z3interface.set_int_to_bv_range true;
        if split_ask_original then
          Z3Smt.Z3interface.set_int_to_bv_split_ask_original true;
        if mod_pow2 then Z3Smt.Z3interface.set_int_to_bv_mod_pow2 true;
        if twins then Z3Smt.Z3interface.set_int_to_bv_twins true

  let () =
    if config.z3.unsigned_linear_bv_templates then
      Ast.LogicOld.set_bv_unsigned_linear_templates true

  let () =
    if config.z3.words.pow2_shifts then
      Z3Smt.Z3interface.set_int_to_bv_pow2_shifts true

  let () =
    if config.z3.words.interface then
      Z3Smt.Z3interface.set_words_interface true

  let () =
    if config.z3.words.seq_as_arrays then
      Z3Smt.Z3interface.set_words_seq_as_arrays true

  let () =
    let definitions = config.recursive_functions.definitions in
    if definitions.eval_ground_qualifiers then
      Atomic.set PCSatCommon.TruthTable.eval_recursive_qualifiers_ground true;
    if definitions.skip_induction_cells then
      Atomic.set PCSatCommon.TruthTable.skip_induction_cells true;
    if config.simplifier.truth_table_seq_length_form then
      Atomic.set PCSatCommon.SeqLengthForm.enabled true;
    (match config.simplifier.truth_table_long_sequence_bound with
    | Some k when k > 0 ->
        Atomic.set PCSatCommon.TruthTable.long_sequence_bound k
    | _ -> ());
    if definitions.declare_reached_only then
      Atomic.set Z3Smt.Z3interface.declare_reached_functions_only true

  (* the phase-time account, process-wide once on like the two above; also
     with [COAR_PHASE_TIME_REPORT] set (instrument only), so that a run can be
     given the account without changing how its configuration is written, and
     with [COAR_COPY_REPORT] set, whose per-copy reports need it *)
  let () =
    if
      config.phase_time_report
      || Option.is_some (Sys.getenv "COAR_PHASE_TIME_REPORT")
      || Common.ForkGuard.copy_report
    then Common.PhaseTime.enable ()

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
              if (not !SMT.Smtlib2.law_reaches_dependents)
                 || not config.reader.laws.dedup_premises
              then
                enable
              else disable)))

  (* its counters, on stderr at the end of a top-level run that set it *)
  module SeqAxDebug =
    Common.Debug.Make
      ((val Common.Debug.Config.(
              match config.z3.seq_axiom_fallback_ms with
              | None -> disable
              | Some _ -> enable)))

  (* the solver's own trace, and the fresh-context counters at the end of a
     top-level run: on exactly when the coordinator's [verbose] is, so that a
     [dbg_] configuration (whose coordinator is the verbose one) traces the
     solver together with its phases.  The top-level record has no [verbose]
     of its own; reading the coordinator's needs no configuration file to
     change.  Stderr only, no answer depends on it. *)
  module Debug =
    Common.Debug.Make
      ((val Common.Debug.Config.(
              match ExtFile.unwrap config.coordinator with
              | Ok (c : Coordinator.Config.t) when c.verbose -> enable
              | Ok _ | Error _ -> disable)))

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
            ~default:c.zero_unknown.matched_instances.forms
        then
          Some
            ( c.zero_unknown.matched_instances.aligned_hyps,
              c.zero_unknown.matched_instances.hyp_budget )
        else None

  let sol_printer =
    let open Or_error in
    ExtFile.unwrap config.sol_printer >>= fun cfg -> Ok (SolPrinter.make cfg)

  (* a printer that cannot be loaded makes [solve] fail before it prints *)
  let prints_solution () =
    match sol_printer with
    | Ok (module SolPrinter : SolPrinter.SolPrinterType) ->
        SolPrinter.prints_solution
    | Error _ -> false

  let tidy_solution_for_printing solution = tidy_solution solution

  (* where the encoding of counted recursion is applied; [None] when it is
     off *)
  (* whether every encoding of counted recursion in this run also recognises
     the guarded counted body ([PCSP.RecFunGraph.guarded_body]); passed to each
     entry point, so all of them recognise the same definitions *)
  let guarded_counter = config.recursive_functions.guarded_counter

  let graph_placement =
    match config.recursive_functions.graph with
    | PCSatConfig.Off -> None
    | Graph { placement } -> Some placement

  (* whether the encoding is applied to the problem the preprocessor hands
     the CEGIS loop ([post_preprocessing_solve]) rather than to the problem
     as read; then the read-time encoding below is off on every path, so no
     constraint is encoded by both *)
  let rec_fun_graph_post =
    match graph_placement with
    | None | Some (PCSatConfig.As_read _) -> false
    | Some (After_preprocessing _ | After_elimination _ | Dynamic_only) -> true

  (* whether undecided clauses are encoded as validation meets them
     ([PCSatCommon.RecFunDynamic]); implies [rec_fun_graph_post] *)
  let rec_fun_graph_dynamic =
    match graph_placement with
    | Some PCSatConfig.Dynamic_only -> true
    | Some (After_preprocessing post | After_elimination post) -> post.dynamic
    | Some (As_read _) | None -> false

  (* the read-time placement: the problem with its counted recursive
     applications encoded by graph unknowns ([PCSP.RecFunGraph.encode], which
     states why the result is equisatisfiable); the problem itself under any
     other placement or with the encoding off.  [candidates] also records
     each graph as the first candidate of its unknown. *)
  let encode_rec_fun_graph pcsp =
    match graph_placement with
    | Some (PCSatConfig.As_read { unknown_free_only; candidates; _ }) ->
      let pcsp', added =
        PCSP.RecFunGraph.encode ~guarded_counter ~unknown_free_only
          ~graph_candidates:candidates pcsp
      in
      Debug.print
      @@ lazy
           (sprintf "rec_fun_graph_unknowns: %d unknown(s) introduced%s"
              (List.length added)
              (String.concat
                 (List.map added ~f:(fun v -> " " ^ Ast.Ident.name_of_tvar v))));
      pcsp'
    | Some (After_preprocessing _ | After_elimination _ | Dynamic_only) | None ->
        pcsp

  (* [After_preprocessing], and the dynamic encoding ([rec_fun_graph_dynamic]):
     [solve] (the coordinator's entry point) given the problem the
     preprocessor leaves, encoded as the placement says.  Contract: under
     [As_read] or with the encoding off, [solve p]; otherwise [solve] of a
     problem equisatisfiable with [p] -- [p] with its clauses that mention no
     unknown encoded ([PCSP.RecFunGraph.encode_clauses], under
     [After_preprocessing]), and, with the dynamic encoding, re-solved with each clause of that problem that validation
     left undecided and that applies a counted function encoded in turn
     ([PCSatCommon.RecFunDynamic.solve]).  Only clauses of [p] as the
     preprocessor gave it are ever candidates for the dynamic step, never
     the clauses an encoding produced.  The preprocessor's elimination
     records belong to the problem it holds, which this does not change, so
     completing a solution with the eliminated predicates is as without the
     switches; a solution's entries for graph unknowns are extra. *)
  (* [refute_first]: [true] only when [decide], the coordinator's solve,
     answers [unsat] in a forked copy within the budget for the problem made
     of [p]'s constraints that mention no unknown of [p] and no unknown at all
     in its signature.  Such a constraint has the same truth value under
     every interpretation of the unknowns, so a refutation of those
     constraints alone is one of [p].  [false] under [No_refute_first], with
     no such constraint, or for any other outcome (the copy killed, lost, or
     answering anything else). *)
  let refutes_unknown_free_first ~(refute_first : PCSatConfig.refute_first) ~decide
      p =
    match refute_first with
    | No_refute_first -> false
    | Refute_first { kill_ms = ms; rlimit } -> (
        let senv = PCSP.Problem.senv_of p in
        let params =
          {
            (PCSP.Problem.params_of p) with
            senv = Map.Poly.empty;
            stable_clauses = Set.Poly.empty;
          }
        in
        let sub =
          match PCSP.Problem.clauses_of_opt ~full_clauses:false p with
          | Some _ ->
              let free =
                Set.filter (PCSP.Problem.clauses_of p)
                  ~f:(UnknownFreeSweep.unknown_free senv)
              in
              if Set.is_empty free then None
              else Some (PCSP.Problem.of_clauses ~params free)
          | None ->
              let free =
                Set.filter (PCSP.Problem.formulas_of p) ~f:(fun (_, term) ->
                    Set.for_all (Ast.Logic.Term.fvs_of term) ~f:(fun x ->
                        not (Map.Poly.mem senv x)))
              in
              if Set.is_empty free then None
              else
                Some (PCSP.Problem.to_cnf (PCSP.Problem.of_formulas ~params free))
        in
        match sub with
        | None -> false
        | Some sub ->
            let refuted =
              Common.PhaseTime.with_phase "rec-fun-graph-refute-first"
              @@ fun () ->
              Option.value ~default:false
              @@ ForkedQuery.run ~ms (fun () ->
                  (* only [unsat] is read: no stage that can only prove runs *)
                  PCSatCommon.ShapeProof.with_refutation_only @@ fun () ->
                  Z3Smt.Z3interface.with_rlimit ~label:"rgr_first" rlimit
                  @@ fun () ->
                  match decide sub with
                  | Ok (PCSP.Problem.Unsat _, _) -> true
                  | _ -> false)
            in
            Debug.print
            @@ lazy
                 (sprintf
                    "rec_fun_graph_refute_unknown_free_first: %d constraint(s) \
                     without an unknown %s"
                    (Set.length (PCSP.Problem.formulas_of sub))
                    (if refuted then "refuted" else "not refuted"));
            refuted)

  (* [drop_proved]: [p] without the constraints the encoding would rewrite
     that are proved valid, each asked in a forked copy under the resource
     limit and the kill ([PCSP.RecFunGraph.drop_valid_encodable] has the
     contract); [p] itself under [No_drop_proved] *)
  let recfun_drop_dump_count = Atomic.make 0

  (* [proves_abstracted ~budget phi]: [true] only when the weakening of
     [not phi] by [PCSP.RecFunGraph.abstracted_weakening] -- the conjuncts
     [Z3interface.may_not_return] refuses dropped, every counted application
     outside a binder a fresh variable, every conjunct still applying a
     counted function dropped -- is found unsatisfiable in a fresh context
     within [budget] ms, which proves [phi] valid (the contract there);
     [false] when [budget] is [None], nothing is left, or the answer is
     anything else.  Every kept conjunct passed [may_not_return], so the
     solver's budget holds on the question. *)
  let proves_abstracted ?(name_bv_to_int = false) ~budget phi =
    match budget with
    | None -> false
    | Some ms -> (
        let defs =
          PCSP.RecFunGraph.counted_defs ~guarded_counter (Ast.LogicOld.get_fenv ())
        in
        match
          PCSP.RecFunGraph.abstracted_weakening ~defs
            ~keep:(fun c -> not (Z3Smt.Z3interface.may_not_return c))
            phi
        with
        | None -> false
        | Some rest -> (
            (* [name_bv_to_int]: [rest] is satisfiable iff [not q] is, for
               the question [q = not rest] and its rewrite, so an [unsat] of
               the rewrite's negation still proves [phi] *)
            let rest =
              if not name_bv_to_int then rest
              else
                match
                  Ast.QuestionRewrites.name_bv_to_int
                    (Ast.LogicOld.Formula.mk_neg rest)
                with
                | Some q -> Ast.LogicOld.Formula.mk_neg q
                | None -> rest
            in
            (* the phase [ask] counts and times the solver calls (the
               enclosing phase also counts the constraints for which nothing
               is left to ask), the event [proved] the proofs *)
            try
              Common.PhaseTime.with_phase "ask" @@ fun () ->
              match
                Z3Smt.Z3interface.check_sat ~id:None ~timeout:(Some ms)
                  ~fresh_solver:true
                  (Z3Smt.Z3interface.fenv_reached_by (Ast.LogicOld.get_fenv ()) rest)
                  [ rest ]
              with
              | `Unsat ->
                  Common.PhaseTime.event "rec-fun-graph-drop-weakened-proved";
                  true
              | _ -> false
            with exn when not (Common.Timer.is_async exn) -> false))

  (* [proves_by_read_instances ~rlimit ~ms phi]: [true] only when the
     negation of the question [phi], with each integer universal among its
     conjuncts replaced by its instances at the positions its ground sequence
     reads and its function applications give
     ([Ast.QuestionRewrites.int_universals_at_positions]), is
     found unsatisfiable by a forked copy within [rlimit] and [ms]; [false]
     when no instance is offered or the answer is anything else.  The
     rewritten negation is implied by the negation of [phi], so its [unsat]
     proves [phi] valid; nothing else is read from it.  Asked in a forked copy
     as the native question is, since a premise quantified over sequences
     stays in the question and Z3 may not return on it at its limit.  The
     events count the questions offered an instance, those that were not, and
     the proofs. *)
  let proves_by_read_instances ~rlimit ~ms phi =
    match
      Ast.QuestionRewrites.int_universals_at_positions
        (Ast.LogicOld.Formula.mk_neg phi)
    with
    | None ->
        Common.PhaseTime.event "rec-fun-graph-drop-read-instances-none";
        false
    | Some w ->
        Common.PhaseTime.event "rec-fun-graph-drop-read-instances";
        let proved =
          match
            ForkedQuery.valid_within ~ms (fun () ->
                Z3Smt.Z3interface.with_rlimit ~label:"rgr_drop_inst" (Some rlimit)
                @@ fun () ->
                let fenv = Ast.LogicOld.get_fenv () in
                let q = Ast.LogicOld.Formula.mk_neg w in
                (* [COAR_DUMP_READ_INSTANCES=dir] (instrument only): as
                   [COAR_DUMP_RECFUN_DROP] for the native question *)
                Z3Smt.Z3interface.with_validity_dump ~native:true
                  ~var:"COAR_DUMP_READ_INSTANCES"
                  ~counter:recfun_drop_dump_count ~id:None ~timeout:ms
                  ~outcome:(function
                    | `Valid -> "valid"
                    | `Invalid _ -> "invalid"
                    | _ -> "undecided")
                  fenv q
                @@ fun () ->
                Z3Smt.Z3interface.check_valid ~timeout:(Some ms) ~id:None fenv q)
          with
          | `Valid -> true
          | _ -> false
        in
        if proved then
          Common.PhaseTime.event "rec-fun-graph-drop-read-instances-proved";
        proved

  let drop_proved_encodable ~(drop_proved : PCSatConfig.drop_proved) p =
    match drop_proved with
    | No_drop_proved -> p
    | Drop_proved
        {
          rlimit;
          kill_ms = ms;
          shape_proof_ms;
          weaken_refused_ms;
          name_bv_to_int;
          free_int_singletons;
          int_universal_read_instances_ms;
        } ->
        (* [free_int_singletons], [name_bv_to_int]: rewrites that keep the
           question's validity (not its models), so they are applied to the
           questions whose proof alone is read, the native and the weakened
           one; the shape forms are built from the constraint as it is *)
        let pinned phi =
          if not free_int_singletons then phi
          else
            match Ast.QuestionRewrites.pin_free_int_singletons phi with
            | Some q ->
                Common.PhaseTime.event "rec-fun-graph-drop-free-singleton";
                q
            | None -> phi
        in
        let named phi =
          if not name_bv_to_int then phi
          else
            match Ast.QuestionRewrites.name_bv_to_int phi with
            | Some q ->
                Common.PhaseTime.event "rec-fun-graph-drop-named-bv-to-int";
                q
            | None -> phi
        in
        (* the native question: asked after the one-point rule and the
           binder splits, an equivalence in every model (a [let] of the input
           reaches the constraint as a binder fixed by an equation, which
           Z3's default strategy can leave open), then the rewrites above *)
        let native phi =
          named @@ pinned
          @@ Ast.Evaluator.elim_onepoint_singleton_and_split_binders phi
        in
        let valid phi =
          let phi0 = phi in
          Common.PhaseTime.with_phase "rec-fun-graph-drop-proved" @@ fun () ->
          match
            ForkedQuery.valid_within ~ms (fun () ->
                Z3Smt.Z3interface.with_rlimit ~label:"rgr_drop" (Some rlimit)
                @@ fun () ->
                let fenv = Ast.LogicOld.get_fenv () in
                let phi = native phi in
                (* [COAR_DUMP_RECFUN_DROP=dir] (instrument only): each question
                   is written as [dir/qN-PID_native.smt2] (its negation) with
                   its outcome in [dir/index.tsv]; the answer is unchanged *)
                Z3Smt.Z3interface.with_validity_dump ~native:true
                  ~var:"COAR_DUMP_RECFUN_DROP" ~counter:recfun_drop_dump_count
                  ~id:None ~timeout:ms
                  ~outcome:(function
                    | `Valid -> "valid"
                    | `Invalid _ -> "invalid"
                    | _ -> "undecided")
                  fenv phi
                @@ fun () ->
                Z3Smt.Z3interface.check_valid ~timeout:(Some ms) ~id:None fenv
                  phi)
          with
          | `Valid -> true
          | _ when
              Common.PhaseTime.with_phase "rec-fun-graph-drop-weakened"
                (fun () ->
                  proves_abstracted ~name_bv_to_int ~budget:weaken_refused_ms
                    (pinned phi0)) ->
              true
          | _ when
              Option.value_map int_universal_read_instances_ms ~default:false
                ~f:(fun ms ->
                  Common.PhaseTime.with_phase "rec-fun-graph-drop-read-instances"
                    (fun () ->
                      try proves_by_read_instances ~rlimit ~ms (native phi0)
                      with exn when not (Common.Timer.is_async exn) -> false)) ->
              true
          | _ -> (
              match shape_proof_ms with
              | None -> false
              | Some ms ->
                  Common.PhaseTime.with_phase "rec-fun-graph-drop-shape"
                  @@ fun () ->
                  PCSatCommon.ShapeProof.valid_within ~print:Debug.print ~ms
                    ~id:None phi0)
        in
        let p', n = PCSP.RecFunGraph.drop_valid_encodable ~guarded_counter ~valid p in
        Debug.print
        @@ lazy
             (sprintf
                "rec_fun_graph_drop_proved: %d constraint(s) proved valid and \
                 dropped"
                n);
        p'

  (* the problem [p] replaced by the single constraint [false] *)
  let refuted_problem p =
    PCSP.Problem.of_formulas ~params:(PCSP.Problem.params_of p)
      (Set.Poly.singleton
         (Map.Poly.empty, Ast.Logic.BoolTerm.mk_bool false))

  let post_preprocessing_solve ~decide solve p =
    if not rec_fun_graph_post then solve p
    else
      let p' =
        match graph_placement with
        | Some (PCSatConfig.After_preprocessing post) ->
          let p = drop_proved_encodable ~drop_proved:post.drop_proved p in
          let p', added =
            Common.PhaseTime.with_phase "rec-fun-graph-post" @@ fun () ->
            PCSP.RecFunGraph.encode_clauses ~guarded_counter ~unknown_free_only:true
              ~graph_candidates:post.candidates ~keep_functions:post.dynamic p
          in
          let p', added =
            if
              (not (List.is_empty added))
              && refutes_unknown_free_first ~refute_first:post.refute_first
                   ~decide p
            then (refuted_problem p, [])
            else (p', added)
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
          p'
        | Some (After_elimination _ | Dynamic_only | As_read _) | None -> p
      in
      if not rec_fun_graph_dynamic then solve p'
      else
        match
          ( PCSP.Problem.clauses_of_opt ~full_clauses:false p,
            PCSP.Problem.clauses_of_opt ~full_clauses:false p' )
        with
        | Some before, Some after ->
            Atomic.set PCSatCommon.RecFunDynamic.on true;
            PCSatCommon.RecFunDynamic.solve ~guarded_counter ~solve
              ~candidates:(Set.inter before after) p'
        | _ -> solve p'

  (* [After_elimination]: the same static encoding as
     [post_preprocessing_solve]'s, handed to the preprocessor as its
     [post_elim] hook so that the passes after elimination see the graph
     unknowns; [None] (the hook is not passed) under any other placement *)
  let post_elim_encoding ~decide =
    match graph_placement with
    | Some (PCSatConfig.After_elimination post) ->
      Some
        (fun p ->
          let p = drop_proved_encodable ~drop_proved:post.drop_proved p in
          let p', added =
            Common.PhaseTime.with_phase "rec-fun-graph-post-elim" @@ fun () ->
            (* right after elimination the problem may still be in formula
               form (the clausal form comes later in preprocessing); either
               entry point encodes exactly its constraints that mention no
               unknown *)
            if PCSP.Problem.is_raw p then
              PCSP.RecFunGraph.encode ~guarded_counter ~unknown_free_only:true
                ~graph_candidates:post.candidates ~keep_functions:post.dynamic
                p
            else
              PCSP.RecFunGraph.encode_clauses ~guarded_counter ~unknown_free_only:true
                ~graph_candidates:post.candidates ~keep_functions:post.dynamic
                p
          in
          let p', added =
            if
              (not (List.is_empty added))
              && refutes_unknown_free_first ~refute_first:post.refute_first
                   ~decide p
            then (refuted_problem p, [])
            else (p', added)
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
    | Some (After_preprocessing _ | Dynamic_only | As_read _) | None -> None

  (* [As_read]'s [every_reading]: a problem obtained by reading the input
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
    match graph_placement with
    | Some (PCSatConfig.As_read { every_reading = true; _ }) ->
        encode_rec_fun_graph pcsp
    | Some (As_read _ | After_preprocessing _ | After_elimination _ | Dynamic_only)
    | None ->
        pcsp

  (* set while the probe below runs, so that nothing it starts probes again.
     Per domain: MuVal solves its primal and dual side at once in two domains,
     and one side's probe must not stop the other side from probing *)
  let probing_key =
    Domain.DLS.new_key ~split_from_parent:(fun r -> ref !r) (fun () -> ref false)

  let probing () = Domain.DLS.get probing_key

  (* every probe below runs between these two: they set [probing] and keep
     the race duplicate check's probe depth
     ([PCSatCommon.ParallelRace.Duplicate.enter_probe]), so that a race started
     before the probe is not compared with the probe's problem, which the
     process solves under a budget for one verdict and does not go on to solve *)
  let enter_probe () =
    probing () := true;
    PCSatCommon.ParallelRace.Duplicate.enter_probe ()

  let leave_probe () =
    probing () := false;
    PCSatCommon.ParallelRace.Duplicate.leave_probe ()

  let probes = config.probes

  let probe_on = PCSatConfig.probe_runs
  let raced = PCSatConfig.probe_raced

  (* whether [true_precondition_probe] can try anything: a name given or the
     witness-causing selection on (the file checks are made by the probe) *)
  let true_precondition_probe_on () =
    probe_on probes.true_precondition.mode
    && ((not (List.is_empty probes.true_precondition.names))
       || probes.true_precondition.witness_causing)

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
  (* the layers a probe's strict deadline is read by beyond the CEGIS loop,
     set for the probe's nested solve only: the predicate eliminator
     ([probes.deadline_in_preprocessing]) and the other stage boundaries before
     the loop's first phase ([probes.deadline_at_stages]) *)
  (* [probes.ladder_skips_unread_stages]: [f ()] with the zero-unknown
     verdict told which answer the probe reads *)
  let probe_reads r f =
    if probes.ladder_skips_unread_stages then
      PCSatCommon.NoUnknownLadder.with_read r f
    else f ()

  let with_probe_deadline_reads f =
    PCSatCommon.SolveDeadline.with_preprocessing_check
      probes.deadline_in_preprocessing
    @@ fun () ->
    PCSatCommon.SolveDeadline.with_stage_check probes.deadline_at_stages f

  (* [probes.inner_skolem]: the input read again with every functional witness
     given only the universals its existential's body mentions, and only the
     preprocessing's refuting stages run on it ([preprocess], which never
     solves).  [Some unsat] when they reduce it to [false], [None] otherwise.
     Assumes: [pcsp] is the problem as read (its functional witnesses at full
     arity).  Guarantees: an [unsat] only, and only of a reading equisatisfiable
     with the input in every model (inner Skolemisation: a witness that works
     can be replaced by one choosing, from the variables its body reads alone,
     a value the body accepts), so it is an [unsat] of the input.  Preserves:
     the reader's switch and the record of input assertions are restored on
     every exit; the datatype and function environments the reading writes are
     those of the same input, as for the other probes' readings. *)
  let inner_skolem_probe ~filename ~preprocess pcsp =
    let fn_arity p =
      let kinds = PCSP.Problem.kind_map_of p in
      Map.Poly.fold (PCSP.Problem.senv_of p) ~init:0
        ~f:(fun ~key ~data acc ->
          match Map.Poly.find kinds key with
          | Some k when Ast.Kind.is_fn k ->
              acc + List.length (Ast.Logic.Sort.args_of data)
          | _ -> acc)
    in
    match filename with
    | _ when not (probe_on probes.inner_skolem.mode) -> None
    | _ when !(probing ()) -> None
    | None -> None
    | Some file
      when not
             (String.is_suffix file ~suffix:".smt2"
             && Sys_unix.file_exists_exn file) ->
        None
    | Some _ when fn_arity pcsp = 0 -> None
    | Some file -> (
        (* act counters: the gates above passed, and (below) the re-reading
           removed a witness argument so the copy is solved *)
        Common.PhaseTime.event "inner-skolem/read";
        let saved_inputs = Ast.LogicOld.get_input_record () in
        let saved_switch = !PCSP.Problem.skolem_body_variables_only in
        let read =
          Exn.protect
            ~finally:(fun () ->
              PCSP.Problem.skolem_body_variables_only := saved_switch;
              Ast.LogicOld.set_input_record saved_inputs)
            ~f:(fun () ->
              PCSP.Problem.skolem_body_variables_only := true;
              try
                Some
                  (Common.PhaseTime.with_phase "read-inner-skolem" @@ fun () ->
                   PCSP.Parser.from_smt2_file ~print:Debug.print ~inline:true
                     ~skolem_pred:true file)
              with exn_ when not (Common.Timer.is_async exn_) -> None)
        in
        match read with
        | None -> None
        | Some reduced when fn_arity reduced >= fn_arity pcsp ->
            Debug.print
            @@ lazy "[inner-skolem probe] no witness loses an argument; not tried";
            None
        | Some reduced -> (
            Common.PhaseTime.event "inner-skolem/tried";
            let started = Common.Clock.now_s () in
            let refuted =
              enter_probe ();
              Exn.protect
                ~finally:leave_probe
                ~f:(fun () ->
                  try
                    PCSatCommon.SolveDeadline.with_preprocessing_check true
                    @@ fun () ->
                    PCSatCommon.SolveDeadline.with_stage_check true @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                      ~seconds:
                        (Float.of_int probes.inner_skolem.budget_ms /. 1000.)
                      (fun () ->
                        Common.PhaseTime.with_phase "probe-inner-skolem"
                          (fun () ->
                            match preprocess reduced with
                            | Ok p ->
                                Set.exists (PCSP.Problem.formulas_of p)
                                  ~f:(fun (_, t) -> Ast.Logic.BoolTerm.is_false t)
                            | Error _ -> false))
                  with exn_ when not (Common.Timer.is_async exn_) -> false)
            in
            let took = Common.Clock.now_s () -. started in
            Debug.print
            @@ lazy
                 (sprintf "[inner-skolem probe] %s in %.2f s"
                    (if refuted then "refuted" else "nothing refuted")
                    took);
            if read_stages then
              eprintf "[inner-skolem probe] %s in %.2f s\n%!"
                (if refuted then "refuted" else "nothing refuted")
                took;
            if refuted then
              Some
                (Ok
                   ( PCSP.Problem.Unsat None,
                     State.
                       {
                         num_cegis_iters = 0;
                         unsat_witness = None;
                         kind_certificates = Map.Poly.empty;
                       } ))
            else None))

  (* [opaque_definitions_probe]: [Some] only with a [sat] answer of the input
     re-read with its eligible definitions as universal functions without a
     body ([PCSP.Parser.opaque_definitions_sexps], which states why such a
     [sat] is one of the input); [None] otherwise, and then the caller solves
     the problem as given.  Not tried when [reads_solution]: the solution
     found is one of the re-read problem, whose unknowns may depend on the
     universal functions, and is not one of the input as it stands.  Re-reading
     the file sets the reader's process-wide record of the input assertions,
     which is put back before returning.  Phase-report events:
     [opaque-definitions/read] when something was made universal,
     [opaque-definitions/sat] when the probe answers. *)
  (* the reader's selection for the configuration's [selection] value [sel] *)
  let opaque_parser_selection sel =
    let p = probes.opaque_definitions in
    match sel with
    | PCSatConfig.Bodies ->
        PCSP.Parser.Bodies { keep_quantifier_free = p.keep_quantifier_free }
    | PCSatConfig.Goal_congruence -> PCSP.Parser.Goal_congruence
    | PCSatConfig.Goal_cone_congruence -> PCSP.Parser.Goal_cone_congruence
    | PCSatConfig.Bodies_or_goal_congruence ->
        PCSP.Parser.Bodies_or_goal_congruence
          { keep_quantifier_free = p.keep_quantifier_free }

  (* [selection] (default: the configuration's [selection]) is the one this
     reading uses; the copies of [also_raced] pass theirs *)
  let opaque_definitions_probe ?selection ~reads_solution ~filename ~solve_one
      () =
    let p = probes.opaque_definitions in
    let selection =
      opaque_parser_selection (Option.value selection ~default:p.selection)
    in
    (* [COAR_OPAQUE_CENSUS] (instrument only, decides nothing): phase-report
       events (and [opaque-census:] lines on stderr) [opaque-definitions/considered] whenever a solve reaches this
       probe's place, and [opaque-definitions/would-act] when every gate but
       the mode passes and the reading would make something universal, so
       that the probe's reach is counted with the field off *)
    if Option.is_some (Sys.getenv "COAR_OPAQUE_CENSUS") then (
      (* on stderr as well as in the phase report, so that a configuration
         without the report (a MuVal or RCaml one) is counted too *)
      let census name =
        Common.PhaseTime.event name;
        prerr_endline ("opaque-census: " ^ name)
      in
      census "opaque-definitions/considered";
      match filename with
      | Some file
        when (not reads_solution)
             && (not !(probing ()))
             && String.is_suffix file ~suffix:".smt2"
             && Sys_unix.file_exists_exn file
             && not
                  (List.is_empty
                     (PCSP.Parser.opaque_definitions_of_file ~selection file))
        ->
          census "opaque-definitions/would-act"
      | _ -> ());
    match filename with
    | _ when not (probe_on p.mode) -> None
    | _ when reads_solution -> None
    | _ when !(probing ()) -> None
    | None -> None
    | Some file
      when not
             (String.is_suffix file ~suffix:".smt2"
             && Sys_unix.file_exists_exn file) ->
        None
    | Some file -> (
        let saved_inputs = Ast.LogicOld.get_input_record () in
        let made = ref [] in
        let read =
          try
            Some
              (Common.PhaseTime.with_phase "read-opaque-definitions"
              @@ fun () ->
              PCSP.Parser.from_smt2_file
                ~print:(fun _ -> ())
                ~inline:true ~skolem_pred:true
                ~opaque_definitions:(selection, made)
                file)
          with exn_ when not (Common.Timer.is_async exn_) -> None
        in
        Ast.LogicOld.set_input_record saved_inputs;
        match read with
        | None -> None
        | Some _ when List.is_empty !made -> None
        | Some opaque -> (
            Common.PhaseTime.event "opaque-definitions/read";
            Debug.print
            @@ lazy
                 (sprintf "[opaque-definitions probe] %d universal: %s"
                    (List.length !made)
                    (String.concat ~sep:", " !made));
            if read_stages then
              eprintf "[opaque-definitions probe] %d made universal\n%!"
                (List.length !made);
            let started = Common.Clock.now_s () in
            let answer =
              enter_probe ();
              Exn.protect
                ~finally:leave_probe
                ~f:(fun () ->
                  try
                    with_probe_deadline_reads @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                      ~seconds:(Float.of_int p.budget_ms /. 1000.)
                      (fun () ->
                        Common.PhaseTime.with_phase "probe-opaque-definitions"
                          (fun () ->
                            probe_reads PCSatCommon.NoUnknownLadder.Proof_only
                              (fun () -> solve_one (encode_reading opaque))))
                  with exn_ when not (Common.Timer.is_async exn_) ->
                    Or_error.of_exn exn_)
            in
            let took = Common.Clock.now_s () -. started in
            match answer with
            | Ok ((PCSP.Problem.Sat _ as sat), info) ->
                Common.PhaseTime.event "opaque-definitions/sat";
                Debug.print
                @@ lazy
                     (sprintf
                        "[opaque-definitions probe] sat in %.2f s; answering it"
                        took);
                Some (Ok (sat, info))
            | _ ->
                Debug.print
                @@ lazy
                     (sprintf
                        "[opaque-definitions probe] no sat in %.2f s; solving \
                         the problem as given"
                        took);
                None))

  (* [~all:true]: the all-true probe ([probes.all_true]), the same probe with
     every Boolean-valued unknown of the ordinary kind selected
     ([PCSP.Parser.from_smt2_file]'s [define_true_all]) in place of the
     configured selection; its answer is sound for the same reason *)
  let true_precondition_probe ?(all = false) ?(forced = []) ~filename
      ~solve_one pcsp =
    let label = if all then "all-true" else "true-precondition" in
    let mode, names, witness_causing, budget_ms =
      if all then (probes.all_true.mode, [], false, probes.all_true.budget_ms)
      else
        ( probes.true_precondition.mode,
          probes.true_precondition.names,
          probes.true_precondition.witness_causing,
          probes.true_precondition.budget_ms )
    in
    match (names, filename) with
    | _ when not (probe_on mode) -> None
    | [], _ when (not witness_causing) && not all -> None
    | _, None -> None
    | _ when !(probing ()) -> None
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
              (Common.PhaseTime.with_phase ("read-" ^ label)
              @@ fun () ->
              PCSP.Parser.from_smt2_file
                 ~print:(fun _ -> ())
                 ~inline:true ~skolem_pred:true
                 ~define_true_names:(names @ forced)
                 ~define_true_witness_causing:witness_causing
                 ~define_true_all:all ~defined_true:defined file)
          with exn_ when not (Common.Timer.is_async exn_) -> None
        in
        Ast.LogicOld.set_input_record saved_inputs;
        if not all then PCSatCommon.TruePrecondition.last_probe := `Not_tried;
        match restricted with
        | None -> None
        | Some _ when List.is_empty !defined -> None
        | Some _
          when probes.true_precondition.skip_forced_only
               && PCSatCommon.TruePrecondition.only_forced ~forced
                    (List.map !defined ~f:Ast.Ident.name_of_tvar) ->
            (* every unknown defined here was already defined as [true] by the
               forced-true reading, so the re-read problem is the one the
               caller solves as given: solving it again here could answer only
               what the caller answers, at the cost of a second solve *)
            Debug.print
            @@ lazy
                 (sprintf
                    "[%s probe] not tried: nothing to define beyond the \
                     forced-true unknowns"
                    label);
            None
        | Some restricted -> (
            Debug.print
            @@ lazy
                 (sprintf "[%s probe] trying true for %s" label
                    (String.concat ~sep:", "
                       (List.map !defined ~f:Ast.Ident.name_of_tvar)));
            let started = Common.Clock.now_s () in
            let answer =
              enter_probe ();
              Exn.protect
                ~finally:leave_probe
                ~f:(fun () ->
                  try
                    with_probe_deadline_reads @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                      ~seconds:(Float.of_int budget_ms /. 1000.)
                      (fun () ->
                        Common.PhaseTime.with_phase ("probe-" ^ label)
                          (fun () ->
                            probe_reads PCSatCommon.NoUnknownLadder.Proof_only (fun () ->
                                solve_one (encode_reading restricted))))
                  with exn_ when not (Common.Timer.is_async exn_) ->
                    Or_error.of_exn exn_)
            in
            let took = Common.Clock.now_s () -. started in
            match answer with
            | Ok (PCSP.Problem.Sat sol, info) ->
                Debug.print
                @@ lazy
                     (sprintf "[%s probe] sat in %.2f s; answering it" label
                        took);
                if not all then
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
                        "[%s probe] no sat in %.2f s; solving the problem as \
                         given"
                        label took);
                if not all then
                  PCSatCommon.TruePrecondition.last_probe := `Discarded;
                None))

  (* [repeated_premises_probe]: [Some] only with a [sat] answer of [pcsp] in
     clausal form with the premises [PCSatCommon.RepeatedPremises.strengthen]
     drops; [None] otherwise, and then the caller solves [pcsp] as given.

     Why the answer is sound.  Each stripped clause implies the clause it
     came from (a premise fewer), and the unknowns, sorts and kinds are those
     of [pcsp], so a solution of the stripped problem is a solution of
     [pcsp] as it stands.  [unsat] does not transfer and is never read; nor
     is anything else.  Nothing is solved when no premise is dropped. *)
  let repeated_premises_probe ~solve_one pcsp =
    if not (probe_on probes.repeated_premises.mode) then None
    else if !(probing ()) then None
    else
      let stripped =
        Common.PhaseTime.with_phase "repeated-premises-strip" @@ fun () ->
        try
          let cnf =
            PCSP.Problem.to_cnf @@ PCSP.Problem.to_nnf
            @@ PCSP.Problem.normalize pcsp
          in
          match PCSP.Problem.clauses_of_opt cnf with
          | None -> None
          | Some clauses ->
              let clauses, stats =
                PCSatCommon.RepeatedPremises.strengthen (Set.to_list clauses)
              in
              Some (cnf, clauses, stats)
        with exn_ when not (Common.Timer.is_async exn_) -> None
      in
      (* [COAR_REPEATED_PREMISES_CENSUS] set (instrument only): one stderr
         line with what the strip would drop, then the process exits with
         status 0, so a census of where the probe acts solves nothing *)
      (if Option.is_some (Sys.getenv "COAR_REPEATED_PREMISES_CENSUS") then
         match stripped with
         | None ->
             eprintf "[repeated-premises-census] not in clausal form\n%!";
             Common.ProcessExit.exit 0
         | Some
             ( _,
               all,
               { PCSatCommon.RepeatedPremises.clauses; dropped; unknowns } )
           ->
             eprintf
               "[repeated-premises-census] clauses=%d stripped=%d dropped=%d \
                unknowns=%d\n\
                %!"
               (List.length all) clauses dropped unknowns;
             Common.ProcessExit.exit 0);
      match stripped with
      | None -> None
      | Some (_, _, { PCSatCommon.RepeatedPremises.dropped = 0; _ }) ->
          Common.PhaseTime.event "repeated-premises/none";
          None
      | Some
          ( cnf,
            all,
            { PCSatCommon.RepeatedPremises.clauses; dropped; unknowns } ) -> (
          (* one event per dropped premise, so a phase report shows how much
             the probe changed *)
          Common.PhaseTime.event "repeated-premises/tried";
          for _ = 1 to dropped do
            Common.PhaseTime.event "repeated-premises/dropped-premise"
          done;
          Debug.print
          @@ lazy
               (sprintf
                  "[repeated-premises probe] %d premise(s) dropped from %d \
                   clause(s) defining %d unknown(s)"
                  dropped clauses unknowns);
          (* handed over as formulas, one per clause, not as a clausal
             problem: the predicate elimination resolves only a problem
             that is not yet in clausal form, and without it each
             stripped definition would stay an unknown to be learnt *)
          let stripped =
            PCSP.Problem.of_formulas ~params:(PCSP.Problem.params_of cnf)
              (Set.Poly.of_list
                 (List.map all ~f:Ast.Clause.to_senv_formula))
          in
          let started = Common.Clock.now_s () in
          let answer =
            enter_probe ();
            Exn.protect
              ~finally:leave_probe
              ~f:(fun () ->
                try
                  with_probe_deadline_reads @@ fun () ->
                  PCSatCommon.SolveDeadline.within ~strict_budget:true
                    ~seconds:
                      (Float.of_int probes.repeated_premises.budget_ms /. 1000.)
                    (fun () ->
                      Common.PhaseTime.with_phase "probe-repeated-premises"
                        (fun () ->
                          probe_reads PCSatCommon.NoUnknownLadder.Proof_only
                            (fun () -> solve_one stripped)))
                with exn_ when not (Common.Timer.is_async exn_) ->
                  Or_error.of_exn exn_)
          in
          let took = Common.Clock.now_s () -. started in
          match answer with
          | Ok (PCSP.Problem.Sat _, _) as answer ->
              Common.PhaseTime.event "repeated-premises/answered";
              Debug.print
              @@ lazy
                   (sprintf
                      "[repeated-premises probe] sat in %.2f s; answering it"
                      took);
              Some answer
          | _ ->
              Debug.print
              @@ lazy
                   (sprintf
                      "[repeated-premises probe] no sat in %.2f s; solving the \
                       problem as given"
                      took);
              None)

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
  (* [probes.lower_bound.skip_unrelaxable]: every reading records which unknowns the relaxation
     would start from, so that the probe can see from the forced-true reading that it has none *)
  let () =
    if
      probes.lower_bound.skip_unrelaxable
      || probe_on probes.upper_bound_definition.mode
         && probes.upper_bound_definition.skip_no_targets
    then PCSP.Parser.record_relaxable := true

  let lower_bound_probe ?(forced = []) ~filename ~solve_one () =
    match (probes.lower_bound.names, filename) with
    | _ when not (probe_on probes.lower_bound.mode) -> None
    | [], _ when not probes.lower_bound.witness_causing -> None
    | _, None -> None
    | _ when !(probing ()) -> None
    | [], Some file
      when probes.lower_bound.skip_unrelaxable
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
             > of_int probes.lower_bound.max_input_bytes) ->
        Debug.print
        @@ lazy
             (sprintf "[lower-bound probe] not tried: %s is over %d bytes" file
                probes.lower_bound.max_input_bytes);
        None
    | names, Some file -> (
        let saved_inputs = Ast.LogicOld.get_input_record () in
        let relaxed = ref [] in
        let read =
          try
            Some
              (PCSP.Parser.lower_bound_linear_walk :=
                 probes.relax_linear_walk;
               Common.PhaseTime.with_phase "read-lower-bound" @@ fun () ->
              PCSP.Parser.from_smt2_file
                 ~print:Debug.print ~inline:true ~skolem_pred:true
                 ~define_true_names:forced ~lower_bound_names:names
                 ~lower_bound_witness_causing:
                   probes.lower_bound.witness_causing
                 ~lower_bound_rounds:probes.lower_bound.rounds ~relaxed
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
            (* answer-neutral: counts the runs in which the probe solves *)
            Common.PhaseTime.event "lower-bound-probe-solves";
            let answer =
              enter_probe ();
              Exn.protect
                ~finally:leave_probe
                ~f:(fun () ->
                  try
                    with_probe_deadline_reads @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                      ~seconds:
                        (Float.of_int probes.lower_bound.budget_ms
                        /. 1000.)
                      (fun () ->
                        Common.PhaseTime.with_phase "probe-lower-bound"
                          (fun () ->
                            (if probes.lower_bound.early_stages_only then
                               PCSatCommon.NoUnknownLadder.with_early_only
                             else
                               probe_reads
                                 PCSatCommon.NoUnknownLadder.Refutation_only)
                              (fun () ->
                                solve_one (encode_reading relaxed_pcsp))))
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
                Common.PhaseTime.event "lower-bound-probe-answers";
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
  (* [reader.define_forced_true]: [Some (problem, names)] with the input re-read with
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
  (* [reader.laws.read_once]: whether the input was already read with the switches
     this configuration asks for ([set_law_reader_switches] before the first
     reading), so that reading it again would give the same problem *)
  let already_read file =
    config.reader.laws.read_once
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
             = (config.reader.name_quantified_premises
               || !PCSP.Parser.name_quantified_premises))
        && Bool.(
             r.premise_witness_disjuncts
             = (config.reader.premise_witness_disjuncts
               || !SMT.Smtlib2.premise_witness_disjuncts))
    | None -> false

  (* [given], when passed, holds the problem the caller solves when this
     returns [None].  With [reader.forced_true_release_given] and a non-empty list
     from the kept assertions, it is emptied before the reading, so that the
     two problems are never alive together; the caller must then not hold the
     problem anywhere else, and reads [!given = None] after a [None] as "read
     the input again". *)
  let forced_true_read ?(given = ref None) ~id ~filename () =
    match filename with
    | Some file
      when config.reader.define_forced_true
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
        (* [reader.laws.read_once]: the first reading kept its assertions, so the
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
        | Some (_ :: _) when config.reader.forced_true_release_given ->
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
            Houdini.Candidates.digest_input_assertions ();
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
    | _ when (not (probe_on probes.least_definition.mode)) || !(probing ()) -> None
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
                 probes.relax_linear_walk;
               match base with
               | Some b ->
                   Common.PhaseTime.with_phase "least-definition-from-read"
                   @@ fun () ->
                   trues := b.defined;
                   PCSP.Parser.least_definition_problem ~print:Debug.print
                     ~rounds:probes.least_definition.rounds
                     ~lower_bound_defined:defs b.phis b.envs
               | None ->
               Common.PhaseTime.with_phase "read-least-definition" @@ fun () ->
              PCSP.Parser.from_smt2_file ~print:Debug.print ~inline:true
                 ~skolem_pred:true ~define_true_names:forced
                 ~defined_true:trues
                 ~define_lower_bound_witness_causing:true
                 ~define_lower_bound_rounds:probes.least_definition.rounds
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
              enter_probe ();
              Exn.protect
                ~finally:leave_probe
                ~f:(fun () ->
                  try
                    with_probe_deadline_reads @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                      ~seconds:
                        (Float.of_int probes.least_definition.budget_ms
                        /. 1000.)
                      (fun () ->
                        Common.PhaseTime.with_phase "probe-least-definition"
                          (fun () ->
                            probe_reads PCSatCommon.NoUnknownLadder.Proof_only (fun () ->
                                solve_one (encode_reading defined_pcsp))))
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

  (* [upper_bound_definition_probe]: [Some] only with a [sat] answer of the
     input re-read with its witness-causing unknowns defined by one of their
     upper-bound candidates ([PCSP.Parser.upper_bound_candidates]), tried in
     turn, extended with those definitions; [None] otherwise, and then the
     caller goes on as without the probe.

     Why the answer is sound.  The re-read problem is the input with the
     defined unknowns replaced, before the reader's skolemisation, by
     formulas that mention no unknown, so a solution of it together with the
     definitions makes each constraint of the input the corresponding
     constraint of the re-read one, which holds.  [unsat] does not transfer
     (the choice may be wrong) and is never read.  The candidate filter's
     validity questions are asked in forked copies killed after 5 s, since a
     question over sequences can ignore Z3's own budget; an undecided one
     drops nothing.  Re-reading the file sets the reader's process-wide record
     of the input assertions, which is put back before returning. *)
  let upper_bound_definition_probe ?(forced = []) ~filename ~solve_one () =
    match filename with
    | _ when (not (probe_on probes.upper_bound_definition.mode)) || !(probing ()) -> None
    | None -> None
    | Some file
      when probes.upper_bound_definition.skip_no_targets
           && Option.equal (List.equal String.equal)
                (PCSP.Parser.relaxable_known ~file ~defined:forced
                   ~switches:(PCSP.Parser.relaxable_switches ()))
                (Some []) ->
        (* the reading would define [forced] and find no unknown to build
           candidates for, so [defs] below would be empty and the reading
           discarded; an earlier reading with [forced] defined under the same
           switches has shown that, so the reading is not taken *)
        Common.PhaseTime.event_here "upper-bound-definition-not-read";
        Debug.print
        @@ lazy "[upper-bound definition probe] not tried: no target";
        None
    | Some file
      when not
             (String.is_suffix file ~suffix:".smt2"
             && Sys_unix.file_exists_exn file) ->
        None
    | Some file
      when Int64.(
             (Core_unix.stat file).st_size
             > of_int probes.upper_bound_definition.max_input_bytes) ->
        (* the probe's readings of a file this large can run for minutes each,
           while the inputs it answers are small; nothing is read *)
        Common.PhaseTime.event_here "upper-bound-definition-over-size";
        Debug.print
        @@ lazy
             (sprintf "[upper-bound definition probe] not tried: %s is over %d bytes"
                file probes.upper_bound_definition.max_input_bytes);
        None
    | Some file ->
        (* [probes.upper_bound_definition.whole_budget_ms]: with [Some], the
           whole loop over candidates runs under one strict deadline, and
           [whole_passed ()] says it (or an enclosing strict one) has passed;
           with [None] nothing here reads a deadline, as before the field *)
        let whole_on =
          Option.is_some probes.upper_bound_definition.whole_budget_ms
        in
        let whole_passed () =
          whole_on && PCSatCommon.SolveDeadline.expired_strict ()
        in
        (* the candidate filter's answers, kept for every reading of this
           probe: each candidate's reading builds the same candidates of the
           same file under the same switches and asks every filter question
           again, and on a Rust-derived input each of seven questions over
           sequences used its whole 5 s, 35 s per reading, deciding nothing.
           An answer is reused for a question that is the same formula up to
           the reader's [#tvar] names, which a re-reading draws afresh
           ([ub_filter_key]; its validity is then the same), or else for the
           question asked at the same position of the reading's sequence of
           filter questions with the same [ub_filter_fingerprint]: the
           readings build the same candidates in the same order, which the
           probe's candidate index [k] already presumes, so that question is
           the earlier one with its disjuncts and binders ordered by other
           names (sets ordered by names put them in another order: on a
           Rust-derived input three of five questions came back so).  Keeping
           an undecided answer also keeps the candidate list, and so the
           meaning of [k], the same in every reading, where asking again could
           drop a candidate in a later reading only and shift the indices past
           it.  Only which questions are asked changes: a [sat] of the probe
           holds for any candidate *)
        let filter_memo = Hashtbl.create (module String) in
        let filter_at = Hashtbl.create (module Int) in
        let filter_pos = ref 0 in
        let refuted phi =
          let pos = !filter_pos in
          incr filter_pos;
          (* past the whole-probe deadline the question is not asked: an
             unasked question drops no candidate, exactly as an undecided
             one does, and nothing is kept of it; counted as the event
             [ub-filter-not-asked/whole-budget], so that a run shows whether
             the whole budget changed which questions were asked *)
          (not
             (whole_passed ()
             && (Common.PhaseTime.event_here "ub-filter-not-asked/whole-budget";
                 true)))
          &&
          let keys =
            if probes.upper_bound_definition.filter_memo then
              Some (ub_filter_key phi, ub_filter_fingerprint phi)
            else None
          in
          let kept =
            Option.bind keys ~f:(fun (key, fingerprint) ->
                match Hashtbl.find filter_memo key with
                | Some r ->
                    Common.PhaseTime.event_here "ub-filter-reused";
                    Some r
                | None -> (
                    match Hashtbl.find filter_at pos with
                    | Some (fingerprint', r)
                      when String.equal fingerprint fingerprint' ->
                        Common.PhaseTime.event_here "ub-filter-reused-at";
                        Some r
                    | _ -> None))
          in
          (* the question's shape: quantifier-free, or quantified over a
             formula that mentions a sequence (refuted only by a model of a
             quantified formula over sequence reads), or neither *)
          let shape =
            lazy
            (if Ast.LogicOld.Formula.is_quantifier_free phi then "qf"
            else if Ast.SeqAxiomEncoding.mentions_seq phi then "quantified-seq"
            else "quantified")
          in
          match kept with
          | Some r -> r
          | None
            when probes.upper_bound_definition.filter_skips_quantified_seq
                 && String.equal (Lazy.force shape) "quantified-seq" ->
              (* not asked, and nothing kept: an unasked question drops no
                 candidate, as an undecided one does *)
              Common.PhaseTime.event_here "ub-filter-shape/quantified-seq/not-asked";
              false
          | None ->
              let r =
                Option.value ~default:false
                @@ PCSatCommon.ForkedQuery.run ~ms:5000 (fun () ->
                       match
                         Z3Smt.Z3interface.check_valid ~id:None
                           ~timeout:(Some 4000) (Ast.LogicOld.get_fenv ()) phi
                       with
                       | `Invalid _ -> true
                       | _ -> false)
              in
              (* counted only: which shapes the filter refutes *)
              Common.PhaseTime.event_here
                (sprintf "ub-filter-shape/%s/%s" (Lazy.force shape)
                   (if r then "refuted" else "kept"));
              Option.iter keys ~f:(fun (key, fingerprint) ->
                  Hashtbl.set filter_memo ~key ~data:r;
                  if not (Hashtbl.mem filter_at pos) then
                    Hashtbl.set filter_at ~key:pos ~data:(fingerprint, r));
              r
        in
        let rec attempt k =
          filter_pos := 0;
          let saved_inputs = Ast.LogicOld.get_input_record () in
          (* every reading clears the reader's kept least-definition base, and
             this probe runs before the least-definition probe: without
             putting it back, that probe would read the input again whenever
             this one has read it.  The base is a record of an earlier reading
             of the same file, which this reading does not change, and the
             least-definition probe still checks its file and defined set, so
             putting it back is exact *)
          let saved_base = !PCSP.Parser.least_definition_base in
          let defs = ref [] and count = ref 0 and trues = ref [] in
          let read =
            try
              Some
                (Common.PhaseTime.with_phase "read-upper-bound-definition"
                @@ fun () ->
                PCSP.Parser.from_smt2_file ~print:Debug.print ~inline:true
                  ~skolem_pred:true ~define_true_names:forced
                  ~defined_true:trues
                  ~define_upper_bound:(k, refuted) ~upper_bound_defined:defs
                  ~upper_bound_count:count file)
            with exn_ when not (Common.Timer.is_async exn_) -> None
          in
          Ast.LogicOld.set_input_record saved_inputs;
          PCSP.Parser.least_definition_base := saved_base;
          match read with
          | None -> None
          | Some _ when List.is_empty !defs -> None
          | Some _
            when (not probes.upper_bound_definition.quantified_candidates)
                 && List.exists !defs ~f:(fun (_, (_, body)) ->
                        not (Ast.LogicOld.Formula.is_quantifier_free body)) ->
              (* [quantified_candidates] off: a candidate that defines an
                 unknown by a quantified formula is not solved, and no later
                 one is read.  Each target's candidates come quantifier-free
                 first ([PCSP.Parser.upper_bound_definitions]), so every later
                 candidate defines that target by a quantified formula too, or
                 leaves it undefined; and only a [sat] is read, so ending here
                 loses only a [sat] such a candidate would have given *)
              Common.PhaseTime.event_here "ub-quantified-candidate-not-solved";
              Debug.print
              @@ lazy
                   (sprintf
                      "[upper-bound definition probe] candidate %d of %d \
                       defines an unknown by a quantified formula; not solved"
                      k !count);
              None
          | Some defined_pcsp -> (
              Debug.print
              @@ lazy
                   (sprintf
                      "[upper-bound definition probe] candidate %d of %d: %s"
                      k !count
                      (String.concat ~sep:"; "
                         (List.map !defs ~f:(fun (x, (_, body)) ->
                              sprintf "%s := %s" (Ast.Ident.name_of_tvar x)
                                (Ast.LogicOld.Formula.str_of body)))));
              let started = Common.Clock.now_s () in
              let answer =
                enter_probe ();
                Preprocessing.Preprocessor.in_upper_bound_probe () := true;
                (* only [sat] is read below, so the refuting stages of the
                   candidate's preprocessing may be skipped *)
                let unread = Preprocessing.Preprocessor.refutation_unread () in
                let saved_unread = !unread in
                if probes.upper_bound_definition.skip_refutations then
                  unread := true;
                Exn.protect
                  ~finally:(fun () ->
                    leave_probe ();
                    unread := saved_unread;
                    Preprocessing.Preprocessor.in_upper_bound_probe () := false)
                  ~f:(fun () ->
                    try
                      with_probe_deadline_reads @@ fun () ->
                      PCSatCommon.SolveDeadline.within ~strict_budget:true
                        ~seconds:
                          (Float.of_int probes.upper_bound_definition.budget_ms
                          /. 1000.)
                        (fun () ->
                          Common.PhaseTime.with_phase
                            "probe-upper-bound-definition" (fun () ->
                              probe_reads PCSatCommon.NoUnknownLadder.Proof_only (fun () ->
                                  solve_one (encode_reading defined_pcsp))))
                    with exn_ when not (Common.Timer.is_async exn_) ->
                      Or_error.of_exn exn_)
              in
              let took = Common.Clock.now_s () -. started in
              match answer with
              | Ok (PCSP.Problem.Sat sol, info) ->
                  Debug.print
                  @@ lazy
                       (sprintf
                          "[upper-bound definition probe] sat in %.2f s with \
                           candidate %d"
                          took k);
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
                          "[upper-bound definition probe] candidate %d: no sat \
                           in %.2f s"
                          k took);
                  if k + 1 < !count then
                    if whole_passed () then (
                      PCSatCommon.SolveDeadline.cut ();
                      (* the one place the whole budget ends the probe early:
                         counted, so that a run shows which inputs the field
                         acts on (a later candidate not read) *)
                      Common.PhaseTime.event_here "ub-whole-budget-cut";
                      Debug.print
                      @@ lazy
                           (sprintf
                              "[upper-bound definition probe] whole budget \
                               passed after candidate %d of %d"
                              k !count);
                      None)
                    else attempt (k + 1)
                  else None)
        in
        match probes.upper_bound_definition.whole_budget_ms with
        | None -> attempt 0
        | Some ms ->
            PCSatCommon.SolveDeadline.within ~strict_budget:true
              ~seconds:(Float.of_int ms /. 1000.)
              (fun () -> attempt 0)

  (* [probes.witness_seed.after_preprocessing]: the seeds read off the problem as
     given, each with its witness's sort there, waiting for the outermost
     solve of that problem to reach its preprocessed problem
     ([seeded_after_preprocessing]); set by [witness_seed_probe], cleared by
     the first such solve and when the given problem's solve returns *)
  let seeds_after_preprocessing :
      (Ast.Ident.tvar * Ast.Logic.Sort.t * Ast.Logic.term) list option ref =
    ref None

  (* The witnesses of [seeds_after_preprocessing] that the preprocessed
     problem [p] still has as functional unknowns with the same argument list:
     the same sort, no argument position dropped or erased (every position
     kept in the argument record, no entry in the erasure trail), and no stable clause applying it,
     since only [p]'s clauses are substituted.  A seed is a lambda over the
     witness's arguments by position, so these conditions are what makes it
     a definition of the same witness in [p]. *)
  let surviving_seeds p seeds =
    let params = PCSP.Problem.params_of p in
    let fns = PCSP.Problem.fnpvs_of p in
    let stable = Ast.ClauseSet.pvs_of params.PCSP.Params.stable_clauses in
    List.filter_map seeds ~f:(fun (w, sort, d) ->
        let pv = Ast.Ident.tvar_to_pvar w in
        match Map.Poly.find params.PCSP.Params.senv w with
        | Some sort'
          when Set.mem fns w
               && (not (Set.mem stable w))
               && (match Map.Poly.find params.PCSP.Params.args_record pv with
                  | None -> true
                  | Some (kept, _) -> Array.for_all kept ~f:Fn.id)
               && (not (Map.Poly.mem params.PCSP.Params.erasure_trail pv))
               && (try Stdlib.(compare sort sort' = 0)
                   with exn_ when not (Common.Timer.is_async exn_) -> false) ->
            Some (w, d)
        | _ -> None)

  (* [p] with each witness of [defs] replaced by its definition in the clauses
     applying it (the other clauses kept as they are) and removed from the
     signature and the kind map, as [PCSP.Problem.subst] removes it *)
  let subst_seeds_in_clauses defs p =
    let sub = Map.Poly.of_alist_exn defs in
    let keys = Map.key_set sub in
    match PCSP.Problem.clauses_of_opt ~full_clauses:false p with
    | None -> PCSP.Problem.subst sub p
    | Some cls ->
        let params = PCSP.Problem.params_of p in
        let exi_senv = params.PCSP.Params.senv in
        let cls =
          Set.Poly.map cls ~f:(fun c ->
              if Set.is_empty (Set.inter (Ast.Clause.pvs_of c) keys) then c
              else Ast.Clause.subst exi_senv sub c)
        in
        let keep = Fn.non (Set.mem keys) in
        PCSP.Problem.of_clauses cls
          ~params:
            {
              params with
              PCSP.Params.senv = Map.Poly.filter_keys exi_senv ~f:keep;
              kind_map = Map.Poly.filter_keys params.PCSP.Params.kind_map ~f:keep;
            }

  (* [solve p] after the seeded problem [p] with the surviving seeds
     substituted has been tried under the probe's budget; only a [sat] of it
     is read, extended with the seeds (see [witness_seed_probe] for why that
     is sound; here it is a solution of [p], which the caller extends to the
     input as it extends any solution of [p]).  Only the outermost solve of
     the problem as given takes the seeds: not a nested solve of the
     preprocessing's finite instantiation (depth above 1), and not the solve
     of a probe that runs after the witness-seed probe in the sequential
     order (the true-precondition and lower-bound probes, each solving its
     own re-read problem at depth 1 with [probing] set).  A probe's problem
     has other unknowns or other argument lists, so taking the seeds there
     loses them for the given problem; it cannot give a wrong answer, since
     only a [sat] of the seeded problem is read and it is extended by the
     seeds it was solved with. *)
  let seeded_after_preprocessing solve p =
    match !seeds_after_preprocessing with
    | Some _ when !(Preprocessing.Preprocessor.solve_depth ()) = 1 && !(probing ()) ->
        Atomic.incr seeds_left_for_given_problem;
        solve p
    | Some seeds when !(Preprocessing.Preprocessor.solve_depth ()) = 1 -> (
        seeds_after_preprocessing := None;
        match surviving_seeds p seeds with
        | [] ->
            Debug.print
            @@ lazy "[witness-seed probe] no seeded witness survives preprocessing";
            solve p
        | defs -> (
            Debug.print
            @@ lazy
                 (sprintf "[witness-seed probe] seeding after preprocessing %s"
                    (String.concat ~sep:", "
                       (List.map defs ~f:(fun (w, _) -> Ast.Ident.name_of_tvar w))));
            let answer =
              match
                Common.PhaseTime.with_phase "witness-seed-subst-post" (fun () ->
                    subst_seeds_in_clauses defs p)
              with
              | exception exn_ when not (Common.Timer.is_async exn_) ->
                  Or_error.of_exn exn_
              | seeded ->
                  Atomic.incr seeded_after_preprocessing_solves;
                  enter_probe ();
                  Exn.protect
                    ~finally:leave_probe
                    ~f:(fun () ->
                      try
                        PCSatCommon.SolveDeadline.within ~strict_budget:true
                          ~seconds:
                            (Float.of_int probes.witness_seed.budget_ms
                            /. 1000.)
                          (fun () ->
                            Common.PhaseTime.with_phase "probe-witness-seed-post"
                              (fun () ->
                                probe_reads PCSatCommon.NoUnknownLadder.Proof_only (fun () ->
                                    solve seeded)))
                      with exn_ when not (Common.Timer.is_async exn_) ->
                        Or_error.of_exn exn_)
            in
            match answer with
            | Ok (PCSP.Problem.Sat sol, info) ->
                Ok
                  ( PCSP.Problem.Sat
                      (List.fold defs ~init:sol ~f:(fun acc (w, d) ->
                           Map.Poly.set acc ~key:w ~data:d)),
                    info )
            | _ -> solve p))
    | _ -> solve p

  let witness_seed_probe ~solve_one pcsp =
    if (not (probe_on probes.witness_seed.mode)) || !(probing ()) then None
    else
      match
        Common.PhaseTime.with_phase "witness-seed" (fun () ->
            PCSatCommon.WitnessSeed.seeds
              ~filter_disjuncts:probes.witness_seed.filter_disjuncts pcsp)
      with
      | [] -> None
      | defs
        when probes.witness_seed.after_preprocessing
             && not (raced probes.witness_seed.mode) ->
          (* the one place this switch changes what is run: the seeded
             problem is not solved here; an answer-neutral row of the phase
             account says so *)
          Atomic.incr seeds_deferred_to_preprocessing;
          Common.PhaseTime.event_here "witness-seed-deferred";
          let senv = PCSP.Problem.senv_of pcsp in
          seeds_after_preprocessing :=
            Some
              (List.filter_map defs ~f:(fun (w, d) ->
                   Option.map (Map.Poly.find senv w) ~f:(fun s -> (w, s, d))));
          None
      | defs -> (
          let sub = Map.Poly.of_alist_exn defs in
          match
            Common.PhaseTime.with_phase "witness-seed-subst" (fun () ->
                PCSP.Problem.subst sub pcsp)
          with
          | exception exn_ when not (Common.Timer.is_async exn_) -> None
          | seeded -> (
              Debug.print
              @@ lazy
                   (sprintf "[witness-seed probe] seeding %s"
                      (String.concat ~sep:", "
                         (List.map defs ~f:(fun (w, _) -> Ast.Ident.name_of_tvar w))));
              let answer =
                enter_probe ();
                Exn.protect
                  ~finally:leave_probe
                  ~f:(fun () ->
                    try
                      with_probe_deadline_reads @@ fun () ->
                    PCSatCommon.SolveDeadline.within ~strict_budget:true
                        ~seconds:
                          (Float.of_int probes.witness_seed.budget_ms
                          /. 1000.)
                        (fun () ->
                          Common.PhaseTime.with_phase "probe-witness-seed"
                            (fun () ->
                              probe_reads PCSatCommon.NoUnknownLadder.Proof_only (fun () ->
                                  solve_one seeded)))
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

  (* the input re-read, when the reading in hand was made otherwise, with each
     [:law] premise also in the assertions that apply an unknown depending on
     the law's function (the reader's own reading; only a test moves it off);
     [law_dedup_premises = false]: every premise inserted whole, the reading
     before the reader's default deduplication (an equivalent problem);
     [onepoint_constructor_binders = false]: re-read WITHOUT the removal of
     the existentials a constructor equation fixes, which the reader otherwise
     applies before skolemisation (any combination).  The reader's switches
     are only ever moved away from their defaults here, as
     [simplifier.evaluate_sequences] is, so a later re-read in this process (the
     forced-[true] reading) keeps them.  The re-read sets the reader's record
     of the input assertions to its own, which is the problem solved. *)
  let law_dependents_read ~filename =
    (* the reader applies the rewrite unless told not to, so only switching it
       OFF needs a second reading *)
    let rewritten_first = !PCSP.Problem.onepoint_constructor_binders in
    if not config.reader.onepoint_constructor_binders then
      PCSP.Problem.onepoint_constructor_binders := false;
    (* [name_quantified_premises] is only ever turned on here, like the reader's other
       switches; a reading that has not named the premises is then read again *)
    let name_premises =
      config.reader.name_quantified_premises && not !PCSP.Parser.name_quantified_premises
    in
    if config.reader.name_quantified_premises then
      PCSP.Parser.name_quantified_premises := true;
    (* [premise_witness_disjuncts] likewise *)
    let witness_premises =
      config.reader.premise_witness_disjuncts
      && not !SMT.Smtlib2.premise_witness_disjuncts
    in
    if config.reader.premise_witness_disjuncts then
      SMT.Smtlib2.premise_witness_disjuncts := true;
    match filename with
    | Some file
      when ((not !SMT.Smtlib2.law_reaches_dependents)
           || (not config.reader.laws.dedup_premises)
           || ((not config.reader.onepoint_constructor_binders) && rewritten_first)
           || name_premises || witness_premises)
           && String.is_suffix file ~suffix:".smt2"
           && Sys_unix.file_exists_exn file
           && already_read file ->
        LawDebug.print
        @@ lazy "[law premises] input already read with these switches; not re-read";
        None
    | Some file
      when ((not !SMT.Smtlib2.law_reaches_dependents)
           || (not config.reader.laws.dedup_premises)
           || ((not config.reader.onepoint_constructor_binders) && rewritten_first)
           || name_premises || witness_premises)
           && String.is_suffix file ~suffix:".smt2"
           && Sys_unix.file_exists_exn file ->
        SMT.Smtlib2.law_reaches_dependents := true;
        if not config.reader.laws.dedup_premises then
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
        Houdini.Candidates.digest_input_assertions ();
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
     the run's beside the process's own.  [reads] (default [`Sat]) is what
     the probe answers with, for the duplicate check
     ([PCSatCommon.ParallelRace.start]): a probe that answers only [sat]
     passes the default, and one that answers only [unsat] passes [`None]
     (its copy is never dropped). *)
  let race_probe ?(reads = `Sat) ~on ~name probe next =
    let sequential () =
      match probe () with Some answer -> [ answer ] | None -> next ()
    in
    if not on then sequential ()
    else if
      probes.races_in_process_when_large
      && not
           (Common.ForkGuard.fits
             ~growth:(Common.ForkGuard.peak_excess_bytes ())
             ())
    then
      (* too large to copy: the probe in its sequential place *)
      match Common.PhaseTime.with_phase (name ^ "-in-process") probe with
      | Some answer -> [ answer ]
      | None -> next ()
    else
      match
        Common.PhaseTime.with_phase (name ^ "-fork") (fun () ->
            PCSatCommon.ParallelRace.start ~nice:probes.copy_nice ~reads
              ~report:(fun () ->
                Common.PhaseTime.report ~reason:(name ^ "-copy-answered"))
              ~log:(fun msg ->
                (* a line of the phase account, so only when it is on *)
                if !Common.PhaseTime.on || !Common.PhaseTime.in_child then (
                  prerr_endline
                    (sprintf "phase-time-race%s: at=%.3f %s: %s"
                       (Common.PhaseTime.copy_tag ())
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
      ?(solution_read = true) ?sygus_signature pcsp =
    solve_cell ~bpvs ~filename ~print_sol ~solution_read ~sygus_signature
      (ref (Some pcsp))

  and solve_cell ~bpvs ~filename ~print_sol ~solution_read ~sygus_signature
      cell =
    let open Or_error in
    (* the input's own assertions are read by the Houdini pre-pass only, and
       only through a digest that is a fraction of them *)
    Common.PhaseTime.with_phase "digest-input"
      Houdini.Candidates.digest_input_assertions;
    (* only ever turned ON here: the switch is process-wide, and a second
       solver in the same process whose configuration leaves it off must not
       switch it off under one that is running with it on *)
    if config.simplifier.evaluate_sequences then
      Atomic.set Ast.Evaluator.evaluate_sequences true;
    (* only ever turned ON here, for the same reason *)
    (match config.races.duplicates with
    | Keep -> ()
    | Drop_at_end -> PCSatCommon.ParallelRace.Duplicate.drop_duplicates := true
    | Drop_early_and_end ->
        PCSatCommon.ParallelRace.Duplicate.drop_duplicates := true;
        PCSatCommon.ParallelRace.Duplicate.early := true);
    (* only ever turned ON here, for the same reason *)
    if config.races.two_claims then PCSatCommon.ParallelRace.two_claims := true;
    Option.iter config.z3.qelim_max_subst_growth ~f:(fun n ->
        Atomic.set Ast.Qelim.max_subst_growth (Some n));
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
    (* [kind_recheck]: the problem a [sat] is re-checked against before it is
       reported, when a candidate could have broken a kind; [None] otherwise.
       The classification-based synthesizer builds candidates of only three
       kinds (Synthesis.CBSynthesizer.guarantees_kind), and validation checks
       the clauses alone, so with it in the phase list a [sat] giving an
       unknown of another kind a body (a total predicate given [false], say)
       may solve the clauses and not the problem.  Kept only then, so that
       freeing the problem below is unaffected elsewhere. *)
    let kind_recheck =
      let classification =
        match ExtFile.unwrap config.coordinator with
        | Error _ -> false
        | Ok (c : Coordination.Coordinator.Config.t) ->
            List.exists c.phase_list ~f:(function
              | Coordination.Coordinator.Config.S s -> (
                  match ExtFile.unwrap s with
                  | Ok { Synthesis.Synthesizer.Config.synthesizer =
                           Synthesis.Synthesizer.Config.Classification _; _ } ->
                      true
                  | _ -> false)
              | _ -> false)
      in
      match !cell with
      | Some pcsp
        when classification
             && Map.Poly.existsi (PCSP.Problem.senv_of pcsp) ~f:(fun ~key ~data:_ ->
                    let k = PCSP.Problem.kind_of pcsp key in
                    (not (Synthesis.CBSynthesizer.guarantees_kind k))
                    && Synthesis.CBSynthesizer.kind_checkable k) ->
          Some pcsp
      | _ -> None
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
    (* [definitions.prune_unreached]: the problem the CEGIS loop starts from
       keeps in its function environment only the definitions its clauses
       reach (see [PCSP.Problem.prune_unreached_definitions]) *)
    let prune p =
      if config.recursive_functions.definitions.prune_unreached then
        PCSP.Problem.prune_unreached_definitions p
      else p
    in
    (* the coordinator's solve of a problem on its own, as the nested solve
       of the finite instantiation runs it; what
       [refute_first] asks in a forked copy *)
    let decide p =
      Context.isolated context (fun () ->
          Coordinator.solve ~witness:config.witness ~oracle:None (prune p))
    in
    let solve_one =
      Preprocessor.solve ~witness:config.witness ~bpvs ~oracle ~extend
        ?post_elim:(post_elim_encoding ~decide) ~nested_solver:decide
        (fun ?oracle p ->
          seeded_after_preprocessing
            (post_preprocessing_solve ~decide (fun p ->
                 Coordinator.solve ~witness:config.witness ?oracle
                   (* under the dynamic encoding the function environment
                      stays whole: an example carried across a restart may
                      mention a counted function's terms *)
                   (if rec_fun_graph_dynamic then p
                    else prune p)))
            p)
    in
    (* the problem solved when the law switches re-read the input; the
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
                  Houdini.Candidates.digest_input_assertions ();
                  (encode_rec_fun_graph pcsp, []))
        in
        given := None;
        (* reconstruction and the lemmas: applied to the problem that is
           solved, whichever reading produced it.  Under [No_reconstruction]
           the reconstruction-only arguments are passed [false]: with
           [~functions:false] the pass tries no unknown, so they are not
           read *)
        let rf = config.recursive_functions in
        let functions, result_guards, compositions, reuse_equal, replace =
          match rf.reconstruction with
          | PCSatConfig.No_reconstruction -> (false, false, false, false, false)
          | Reconstruct r ->
              ( true,
                r.result_guards,
                r.compositions,
                r.reuse_equal_functions,
                r.replace_predicates )
        in
        let pcsp =
          if
            functions || rf.lemmas.built_in
            || rf.lemmas.user
               && not (List.is_empty (Ast.LogicOld.get_user_lemmas ()))
          then (
            (match rf.reconstruction with
            | PCSatConfig.Reconstruct r ->
                Atomic.set PCSatCommon.RecFunReconstruct.qual_limit r.quals
            | No_reconstruction -> ());
            Atomic.set PCSatCommon.RecFunReconstruct.refuse_seq_quantified
              rf.refuse_seq_quantified_questions;
            let started = Core_unix.gettimeofday () in
            let out =
              Common.PhaseTime.with_phase "reconstruct-functions" @@ fun () ->
              PCSatCommon.RecFunReconstruct.reconstruct
                ~print:Debug.print ~names_apart:rf.names_apart
                ~user_lemmas:rf.lemmas.user ~reuse_equal ~result_guards
                ~compositions ~functions ~replace ~lemmas:rf.lemmas.built_in
                pcsp
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
            (* [COAR_RECON_TRACE] set: one summary line per pass on stderr,
               with the pass's wall time, so a census over a corpus can tell
               the runs where it acted from those where it found nothing,
               whatever the configuration's tracing.  Prints only. *)
            if PCSatCommon.RecFunReconstruct.trace then
              eprintf
                "[recon-summary] reconstructed %d refused %d replaced %d \
                 lemmas %d time %.3f\n%!"
                (List.length out.reconstructed)
                (List.length out.refused)
                (List.length out.replaced)
                (List.length out.lemmas)
                (Core_unix.gettimeofday () -. started);
            (* [COAR_RECON_EXIT=n] set as well: the process exits (status 0)
               after the n-th pass has printed its summary, so a census of
               where the pass acts needs no solving.  Unset: no effect. *)
            (match Sys.getenv "COAR_RECON_EXIT" with
            | Some n when PCSatCommon.RecFunReconstruct.trace ->
                if
                  Atomic.fetch_and_add PCSatCommon.RecFunReconstruct.census_passes 1 + 1
                  >= Option.value ~default:1 (Int.of_string_opt n)
                then Common.ProcessExit.exit 0
            | _ -> ());
            (* One answer-neutral event per predicate the pass reconstructed,
               so a phase report tells a run in which reconstruction enlarged
               the hypothesis space from one in which the pass ran and found
               nothing eligible (its phase row alone is printed on every run
               with the switch on).  A run with no such row solved the problem
               it would have solved with the switch off. *)
            List.iter out.reconstructed ~f:(fun _ ->
                Common.PhaseTime.event "reconstructed-function");
            out.problem)
          else pcsp
        in
        let forced_names = List.map forced ~f:Ast.Ident.name_of_tvar in
        List.map ~f:(with_trues given_senv forced)
        @@
        (* The probes, in their sequential order: all-true,
           opaque-definitions (and its further selections), repeated-premises,
           inner-Skolem, upper-bound-definition, least-definition,
           witness-seed, true-precondition, lower-bound, then the problem as given.  Each
           probe answers with one verdict only and is discarded otherwise;
           each one switched to a race ([race_probe]) is started in a forked
           copy at its place in this order and everything after it runs
           concurrently in the process, so one copy per raced probe races at
           once, nested: each race's [finish] encloses the races started after
           it, and the process hands itself over to at most one copy. *)
        let lower_bound () =
          Common.PhaseTime.with_phase "lower-bound-probe" @@ fun () ->
          lower_bound_probe ~forced:forced_names ~filename ~solve_one ()
        in
        let given_problem () =
          Common.PhaseTime.with_phase "given-problem" @@ fun () ->
          Exn.protect
            ~finally:(fun () -> seeds_after_preprocessing := None)
            ~f:(fun () -> [ solve_one pcsp ])
        in
        (* [probes.lower_bound.mode = Raced]: the probe raced against the problem
           as given.  The copy answers only with the probe's [unsat], sound on
           its own (see [lower_bound_probe]); a satisfiable input -- every
           input the probe does not answer by design -- no longer waits for
           the probe's whole time, which its budget does not bound. *)
        let after_true_precondition () =
          (* [`None]: the copy refutes a relaxation by a budgeted solve;
             the process's problem containing the relaxation's constraints
             makes it unsatisfiable too, but does not make the process find
             that refutation, in the copy's time or at all *)
          race_probe ~reads:`None
            ~on:
              (raced probes.lower_bound.mode
              && ((not (List.is_empty probes.lower_bound.names))
                 || probes.lower_bound.witness_causing)
              && not !(probing ()))
            ~name:"probe-lower-bound" lower_bound given_problem
        in
        let true_precondition () =
          true_precondition_probe ~forced:forced_names ~filename ~solve_one pcsp
        in
        (* [probes.true_precondition.mode = Raced]: the probe raced in a forked
           copy against the rest.  The copy answers only with the probe's
           [sat], which is sound on its own (see [true_precondition_probe]),
           and then runs the rest of the program as the sequential probe would
           have; the process kills the copy before its own answer leaves.  So
           each answer the process can give is one the sequential order could
           give, and the probe's time no longer delays the rest. *)
        let after_witness_seed () =
          race_probe
            ~on:
              (raced probes.true_precondition.mode
              && true_precondition_probe_on ())
            ~name:"probe-true-precondition" true_precondition
            after_true_precondition
        in
        let all_true () =
          true_precondition_probe ~all:true ~forced:forced_names ~filename
            ~solve_one pcsp
        in
        (* [probes.witness_seed.mode = Raced]: the probe, its seeding included,
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
              (raced probes.witness_seed.mode
              && not !(probing ()))
            ~name:"probe-witness-seed"
            (fun () -> witness_seed_probe ~solve_one pcsp)
            after_witness_seed
        in
        let least () =
          least_definition_probe ~forced:forced_names ~filename ~solve_one
            given_senv
        in
        (* [probes.least_definition.mode = Raced]: the probe raced in a forked copy
           against everything after it.  The copy answers only with the
           probe's [sat], sound on its own (see [least_definition_probe]).
           Sequentially the probe's whole time is added to every input it does
           not answer -- every unsatisfiable one, since an [unsat] of the
           defined problem is never read -- and on an input whose defined
           problem is the unsatisfiable twin of the lower-bound probe's
           relaxation, the probe solves nearly that relaxation (the same
           preprocessing and zero-unknown check) only to discard the answer
           the lower-bound probe then computes again. *)
        let after_upper () =
          race_probe
            ~on:
              (raced probes.least_definition.mode
              && not !(probing ()))
            ~name:"probe-least-definition" least after_least
        in
        let upper () =
          upper_bound_definition_probe ~forced:forced_names ~filename
            ~solve_one ()
        in
        (* [probes.upper_bound_definition.mode = Raced]: the probe raced in a
           forked copy against everything after it; the copy answers only with
           the probe's [sat], sound on its own (see
           [upper_bound_definition_probe]) *)
        let after_inner_skolem () =
          race_probe
            ~on:
              (raced probes.upper_bound_definition.mode
              && not !(probing ()))
            ~name:"probe-upper-bound-definition" upper after_upper
        in
        (* [probes.inner_skolem]: first of the probes after the
           repeated-premises one, since it only reads and preprocesses;
           [Raced], the copy answers only with its [unsat] *)
        let inner_skolem () =
          (* [`None]: the copy refutes the inner-Skolemised re-reading,
             which the process never solves *)
          race_probe ~reads:`None
            ~on:(raced probes.inner_skolem.mode && not !(probing ()))
            ~name:"probe-inner-skolem"
            (fun () ->
              inner_skolem_probe ~filename
                ~preprocess:(fun p ->
                  (* the preprocessor of this configuration, with the finite
                     instantiation's per-size budget the probe asks for *)
                  ExtFile.unwrap config.preprocessor >>= fun cfg ->
                  let cfg =
                    match
                      ( probes.inner_skolem.finite_query_timeout_ms,
                        cfg.Preprocessing.Preprocessor.Config.finite_forall_sorts )
                    with
                    | Some ms, Preprocessing.Preprocessor.Config.Instantiate r ->
                        {
                          cfg with
                          finite_forall_sorts =
                            Preprocessing.Preprocessor.Config.Instantiate
                              { r with query_timeout_ms = ms };
                        }
                    | _ -> cfg
                  in
                  let (module P : Preprocessing.Preprocessor.PreprocessorType) =
                    Preprocessing.Preprocessor.make cfg
                  in
                  Ok
                    (snd
                    @@ P.preprocess
                         ~purpose:
                           (Preprocessing.Preprocessor.Purpose.Decide
                              Set.Poly.empty)
                         p))
                pcsp)
            after_inner_skolem
        in
        (* [probes.opaque_definitions]: ahead of every other probe, since a
           [sat] it finds is found without unfolding a definition; [Raced],
           the copy answers only with its [sat] (see
           [opaque_definitions_probe]) *)
        let reads_solution = extend || Option.is_some kind_recheck in
        let opaque_on =
          raced probes.opaque_definitions.mode
          && (not reads_solution)
          && not !(probing ())
        in
        (* [probes.opaque_definitions.also_raced]: the further selections to
           race, each in a copy of its own after [selection]'s copy.
           Contract: computed here, in the process and before any copy of
           this place is forked, from the parse of the file alone; it keeps,
           in the configured order, exactly the further selections whose
           names are non-empty and differ (as sets: the reader returns them
           sorted) from [selection]'s names and from every earlier kept
           selection's, so no two copies solve the same reading and none
           solves a reading with nothing made universal.  [[]] when the
           opaque race is off or the input is no [.smt2] file, so the
           default (no further selection) reads nothing here.  Each copy
           answers only with its [sat], sound on its own whatever the
           selection ([opaque_definitions_probe]); the copies are forked by
           [race_probe] like the first, with its nice value, memory guard
           and duplicate check. *)
        let also_raced =
          let p = probes.opaque_definitions in
          match filename with
          | Some file
            when opaque_on
                 && (not (List.is_empty p.also_raced))
                 && String.is_suffix file ~suffix:".smt2"
                 && Sys_unix.file_exists_exn file ->
              Common.PhaseTime.with_phase "opaque-definitions-selections"
              @@ fun () ->
              let names sel =
                PCSP.Parser.opaque_definitions_of_file
                  ~selection:(opaque_parser_selection sel)
                  file
              in
              let first = names p.selection in
              snd
              @@ List.fold p.also_raced ~init:([ first ], [])
                   ~f:(fun (seen, kept) sel ->
                     let s = names sel in
                     if
                       List.is_empty s
                       || List.mem seen s ~equal:(List.equal String.equal)
                     then (seen, kept)
                     else (s :: seen, kept @ [ (sel, List.length s) ]))
          | _ -> []
        in
        (* [probes.all_true]: first of all, so that its copy is forked
           before any probe that runs in the process: a sequential
           witness-seed probe spent 102 s of a 120 s run preprocessing before
           a later place in the order was reached.  [Raced], the copy answers
           only with its [sat], sound on its own as the true-precondition
           probe's is (see [true_precondition_probe]) *)
        race_probe
          ~on:(raced probes.all_true.mode && not !(probing ()))
          ~name:"probe-all-true" all_true
        @@ fun () ->
        race_probe ~on:opaque_on ~name:"probe-opaque-definitions"
          (fun () ->
            opaque_definitions_probe ~reads_solution ~filename ~solve_one ())
        @@ fun () ->
        (* [probes.repeated_premises]: [Raced], the copy answers only with
           its [sat] *)
        let repeated () =
          race_probe
            ~on:(raced probes.repeated_premises.mode && not !(probing ()))
            ~name:"probe-repeated-premises"
            (fun () -> repeated_premises_probe ~solve_one pcsp)
            inner_skolem
        in
        (* [wrap next]: the copies of [also_raced] forked in their order,
           the first outermost, then [next ()] *)
        let wrap =
          List.foldi also_raced
            ~init:(fun next -> next ())
            ~f:(fun i outer (sel, n) next ->
            outer (fun () ->
                (* the firing count of a further selection: one event and,
                   with [COAR_READ_STAGES], one line per copy forked *)
                Common.PhaseTime.event "opaque-definitions/also-raced";
                if read_stages then
                  eprintf
                    "[opaque-definitions race] further copy %d forked: %s, %d \
                     names\n%!"
                    (i + 1)
                    (Yojson.Safe.to_string
                       (PCSatConfig.opaque_selection_to_yojson sel))
                    n;
                race_probe ~on:opaque_on
                  ~name:(sprintf "probe-opaque-definitions-%d" (i + 1))
                  (fun () ->
                    opaque_definitions_probe ~selection:sel ~reads_solution
                      ~filename ~solve_one ())
                  next))
        in
        wrap repeated)
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
    (* A [sat] re-checked for the kinds its synthesizer does not guarantee
       ([kind_recheck] above), against the problem the checker would read.  Only
       a check that passes for every such unknown lets it through: a failed
       one means the solution is not one (no total relation is [false]), and
       an undecided one (a solver timeout, a well-foundedness kind without a
       ranking certificate) means nothing is known; both are reported
       [unknown], with the reasons on stderr.  The loop is not resumed: a
       broken kind names no example that would exclude the candidate soundly
       (a totality failure at [x] asks for some [y] it does not name).
       [Adm] and [Integ] have no check; a problem with one never reaches a
       candidate of this synthesizer (it refuses the problem at its first
       round), so a [sat] for one was decided by a stage that does not use it
       and is passed through.
       Guarantees: a [sat] returned here satisfies the kind obligation of
       every unknown whose kind the synthesizer neither guarantees nor
       refuses. *)
    let solution =
      match (solution, kind_recheck) with
      | PCSP.Problem.Sat sol, Some given ->
          let pcsp = Option.value law_read ~default:given in
          let r =
            Common.PhaseTime.with_phase "kind-recheck" @@ fun () ->
            WitnessChecker.check_kind_constraints ~id
              ~certs:info.kind_certificates
              ~only:(fun k ->
                (not (Synthesis.CBSynthesizer.guarantees_kind k))
                && Synthesis.CBSynthesizer.kind_checkable k)
              pcsp sol
              WitnessChecker.empty
          in
          if List.is_empty r.failed && List.is_empty r.unchecked then solution
          else (
            prerr_endline
              ("sat withheld: the solution breaks or cannot be shown to meet \
                a kind its synthesizer does not guarantee: "
              ^ WitnessChecker.str_of_report "kind" r);
            PCSP.Problem.Unknown)
      | _ -> solution
    in
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
         the right to print here (with [races.two_claims]) *)
      Common.ForkGuard.before_verdict ();
      SolPrinter.print ?sygus_signature (solution, info));
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
           (* With the dependents' law reading, against the re-read problem, the one
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
    (* a satisfiability-deciding preprocessing, as it always was: the
       refuting stages run, and [bpvs] is the set of unknowns kept *)
    Or_error.return
      (snd
      @@ Preprocessor.preprocess
           ~purpose:(Preprocessing.Preprocessor.Purpose.Decide bpvs) pcsp)

  let reset () = Context.reset context
  let push () = Context.push context
  let pop () = ignore @@ Context.pop context
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
