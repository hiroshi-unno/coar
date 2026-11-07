open Core
open Common
open Common.Util
open Preprocessing
open Ast

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  let () =
    if config.simplify_inline_lets_once then
      Atomic.set Evaluator.simplify_inline_lets_once true

  let () =
    if config.simplify_skip_settled_bv_eval then
      Atomic.set Evaluator.simplify_skip_settled_bv_eval true

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let pcsp_solver () (* ToDo *) =
    let open Or_error in
    ExtFile.unwrap config.pcsp_solver >>= fun cfg ->
    Ok
      PCSPSolver.(
        (module Solver.Make (struct
          let config = cfg
        end) : Solver.SolverType))

  let preprocess ~print problem =
    let timed name f x = FrameSearch.phase_time name (fun () -> f x) in
    problem
    |> (if config.simplify then timed "pre-simplify" Problem.simplify else Fn.id)
    |> (if config.reduce then timed "pre-reduce" Problem.reduce else Fn.id)
    |> (if config.slice_forward then timed "pre-slice-fwd" Problem.slice_forward
        else Fn.id)
    |> (if config.slice_backward then timed "pre-slice-bwd" Problem.slice_backward
        else Fn.id)
    |> (if config.gen_lemmas_with_ai then Problem.gen_lemmas ~print else Fn.id)
    |>
    if config.gen_determ_conjs then Problem.gen_determ_conjs ~print ~config
    else Fn.id
  (*|> Problem.infer |> snd*)

  (* [with_user_lemmas lemmas problem]: [problem] with the user's lemmas
     ([lemmas]: closed formulas over its predicates) added as conjectures for
     the relational search, which uses one only once it has proved it
     ([Problem.add_user_lemmas]).  A lemma naming a predicate the problem
     does not define is refused with a line on stderr, never kept unread.
     The frame search has no use for lemmas: under it they are reported as
     ignored, and ignoring a claim is always sound. *)
  let with_user_lemmas lemmas problem =
    if List.is_empty lemmas then problem
    else
      match config.proof_search with
      | Config.Frame_search ->
          Out_channel.eprintf
            "[MuCyc] %d user lemma(s) ignored: only the relational proof \
             search reads lemmas\n%!"
            (List.length lemmas);
          problem
      | Config.Relational ->
          let problem, refused =
            Problem.add_user_lemmas ~timeout:config.timeout_prove_each_conj
              lemmas problem
          in
          List.iter refused ~f:(fun (phi, why) ->
              Out_channel.eprintf
                "[MuCyc relational] user lemma refused (%s): %s\n%!" why
                (LogicOld.Formula.str_of phi));
          if config.generalise_goals_by_containment then
            Problem.generalise_goals_by_containment
              ~timeout:config.timeout_prove_each_conj
              (List.filter lemmas ~f:(fun phi ->
                   not (List.exists refused ~f:(fun (r, _) -> phys_equal r phi))))
              problem
          else problem

  let solve_chc_shaped ?on_counterexample ?(lemmas = []) ~dtenv muclp =
    let open Or_error.Monad_infix in
    (FrameSearch.phase_time "pre-of-muclp" (fun () ->
         Problem.of_muclp ~dtenv muclp)
    |> preprocess ~print:Debug.print
    |> with_user_lemmas lemmas
    |>
    (* Instead of storing it inside Problem.t, pass it directly to FrameSearch here *)
    (* ToDo: Pass everything from pCSP to muCLP *)
    (* [proof_search] selects the procedure; the relational one ignores
       [dtenv] and the frame search's own fields *)
    match config.proof_search with
    | Config.Frame_search ->
        FrameSearch.solve ~dtenv ~print:Debug.print ~config ?on_counterexample
          pcsp_solver
    | Config.Relational ->
        InductiveEntailmentSearch.solve ~print:Debug.print ~config pcsp_solver)
    >>= fun (sol, _) -> Ok sol

  (* [FrameSearch] is a Spacer-style frame search whose frames over-approximate
     the least fixpoints; that is sound only for goals in which the predicates
     occur negatively (CHC shape: [body => false]).  A positive occurrence would
     be "proved" by the over-approximation, and greatest fixpoints are not
     supported at all.

     [is_closed_query muclp]: the query has no universal prefix and no free
     term variable.  It licenses the caller's negate-and-flip step, which is
     sound only for a sentence (the least fixpoints fix one interpretation, so
     a sentence is true there iff its negation is not): an open query means
     its universal closure, and the negation of [forall x. phi] is
     [exists x. not phi], not the [forall x. not phi] that solving the negated
     open query asks.  Counting only the universal prefix read a free [x] as
     closed, and [x < 0 \/ P x] with [P] a least fixpoint false at [x = -1]
     was answered [valid].  The readers close their queries, so this guards
     the callers that may not.  A positive occurrence under a universal stays
     refused: proving it needs an under-approximation of the least fixpoint,
     which a frame search does not build, and stripping the universal into
     free variables changes nothing about that. *)
  let is_closed_query muclp =
    let query = muclp.MuCLP.Problem.query in
    Set.is_empty (fst @@ LogicOld.Formula.rm_quant ~forall:true query)
    && Set.is_empty (LogicOld.Formula.tvs_of query)

  (* [polarity_of_query muclp]: whether the query, its universal prefix
     stripped, has negative and positive predicate occurrences, as read off
     its clausal form.  [Error] when that form cannot be built -- the clausal
     form refuses an existential over a predicate occurrence, as in
     [exists a. P (3 * a)] -- with the clausal form's own message. *)
  let polarity_of_query muclp =
    let exi_senv =
      LogicOld.Term.pred_to_sort_env_map @@ MuCLP.Problem.penv_of muclp
    in
    let _, query =
      LogicOld.Formula.rm_quant ~forall:true
      @@ LogicOld.Formula.aconv_tvar muclp.MuCLP.Problem.query
    in
    match Sequent.of_formula exi_senv query with
    | exception Failure msg -> Or_error.error_string msg
    | seqs ->
        let seqs = Set.to_list seqs in
        Ok
          ( List.exists seqs ~f:(fun s ->
                Fn.non List.is_empty s.Sequent.left_atms),
            List.exists seqs ~f:(fun s ->
                Fn.non List.is_empty s.Sequent.right_atms) )

  let solve_by_proof_search ?on_counterexample ?lemmas ~dtenv muclp =
    let open Or_error.Monad_infix in
    (* A muCLP predicate carries one of three fixpoint kinds, [Mu], [Nu] and
       [MuOrNu].  This guard used to test [= Nu], so a [MuOrNu] predicate slipped
       through and died deeper down in [FrameSearch.def_of], whose lookup
       matches [Some (Mu, _, _)] only, with the message "FrameSearch.def_of"
       and nothing else -- which is what every `-p ltsterm`/`ltsnsafe` run with
       this backend hit, because the LTS-to-muCLP reduction marks every
       non-cut-point location [MuOrNu].  Refusing anything that is not [Mu] gives
       those runs the explanation this branch was written to give.
       ([MuOrNu] means the kind is immaterial: every cycle through a
       non-cut-point location passes a cut point, so its least and greatest
       fixpoints coincide and the search could in principle treat it as
       [Mu].  That is a change to what
       this solver attempts, not to what it says, so it is left alone.) *)
    if
      List.exists muclp.MuCLP.Problem.preds ~f:(fun (p : MuCLP.Pred.t) ->
          Stdlib.(p.kind <> LogicOld.Predicate.Mu))
    then
      Or_error.error_string
        "MuCyc supports only least-fixpoint (mu) predicates; use MuVal or \
         MuStrat for this problem"
    else
      let closed = is_closed_query muclp in
      (* a closed query whose clausal form shows only positive occurrences,
         or has no clausal form at all (an existential over an occurrence):
         [lfp |= phi] iff the CHC [{defs} + {phi => false}] is unsat iff the
         query [not phi] is invalid; the negated query is tried when it is
         CHC-shaped *)
      let solve_negated () =
        let muclp' =
          {
            muclp with
            query = LogicOld.Formula.mk_neg muclp.MuCLP.Problem.query;
          }
        in
        match polarity_of_query muclp' with
        | Error e ->
            Error
              (Error.tag e
                 ~tag:
                   "MuCyc cannot handle this query: neither it nor its \
                    negation has a clausal form; use MuVal or MuStrat")
        | Ok (_, true) ->
            Or_error.error_string
              "MuCyc cannot handle this query: the negated query still has a \
               positive predicate occurrence; use MuVal or MuStrat"
        | Ok (_, false) -> (
          Debug.print
          @@ lazy
               "[MuCyc] the query has only positive predicate occurrences; \
                solving the negated query and flipping the verdict";
          (* the lemmas are facts of the same least fixpoints, so they
             serve the negated query as well *)
          solve_chc_shaped ?lemmas ~dtenv muclp' >>= fun sol ->
          Ok
            (match sol with
            | Verdict.Valid -> Verdict.Invalid
            | Verdict.Invalid -> Verdict.Valid
            | sol -> sol))
      in
      match polarity_of_query muclp with
      | Ok (_, false) ->
          solve_chc_shaped ?on_counterexample ?lemmas ~dtenv muclp
      | Ok (false, true) when closed -> solve_negated ()
      | Error _ when closed -> solve_negated ()
      | Error e ->
          (* an open query (a universal prefix or a free variable) whose
             clausal form fails, as [forall l. exists n. Len l n] does: the
             negate-and-flip step needs a sentence, so this is a refusal, and
             it says whose and why rather than passing on the clausal form's
             bare message *)
          Error
            (Error.tag e
               ~tag:
                 "MuCyc cannot handle this query: it has no clausal form and, \
                  being open (a universal prefix or a free variable), cannot \
                  be negated; use MuVal or MuStrat")
      | Ok _ ->
          Or_error.error_string
            "MuCyc cannot handle a query with a positive predicate occurrence \
             under a universal quantifier or mixed with negative occurrences \
             (its frame search is sound only for CHC-shaped goals); use MuVal \
             or MuStrat"

  (* [preprocess_muclp muclp]: the problem the ground-query solve and the
     proof search work on.  Under [As_converted], [muclp] itself.  Under
     [Optimize], the muCLP optimizer's output after [rounds] runs (at least
     one), each on its simplified input, as MuVal runs it; first comes the
     undefined-predicate check MuVal applies (it turns a predicate applied
     without a definition into an error that names the input, where the
     optimizer's passes would otherwise fail on a lookup).
     Contract: the result's query has the same truth value as [muclp]'s under
     the muCLP fixpoint semantics -- every optimizer step is obliged to preserve
     it -- so a verdict for the result is a verdict for [muclp].  Nothing else
     carries over: predicates may be inlined away, renamed, given fewer
     arguments or added (a quantifier the optimizer erases becomes a fresh
     predicate standing for the quantified projection, with its source's
     fixpoint sign), which costs nothing here because MuCyc reports a verdict
     and no interpretation.  The result is any muCLP; the proof search's own
     guards (least fixpoints only, a CHC-shaped or negatable query) are applied
     to it afterwards as to any input.  The optimizer draws fresh predicate
     names from the global counter, so this runs before any solver domain
     exists. *)
  let preprocess_muclp muclp =
    match config.muclp_preprocessing with
    | Config.As_converted -> Ok muclp
    | Config.Optimize { optimizer; rounds } ->
        let open Or_error.Monad_infix in
        ExtFile.unwrap optimizer >>= fun optimizer_cfg ->
        let (module Optimizer : MuCLP.Optimizer.OptimizerType) =
          MuCLP.Optimizer.make optimizer_cfg
        in
        let muclp = MuCLP.Problem.check_problem muclp in
        Debug.print
        @@ lazy (sprintf "before optimization: %s\n" @@ MuCLP.Problem.str_of muclp);
        let muclp =
          Common.PhaseTime.with_phase "mucyc-optimize" @@ fun () ->
          Fn.apply_n_times ~n:(max 1 rounds)
            (fun muclp -> Optimizer.f (MuCLP.Problem.simplify muclp))
            muclp
        in
        Debug.print
        @@ lazy (sprintf "after optimization: %s\n" @@ MuCLP.Problem.str_of muclp);
        Ok muclp

  let solve ?(print_sol = false) ?(dtenv = Map.Poly.empty) ?on_counterexample
      ?lemmas muclp =
    let open Or_error.Monad_infix in
    (* [ground_query_solve]: asked on the problem [preprocess_muclp] returns,
       the one the proof search would receive; an answer is that problem's,
       hence [muclp]'s.  [None] leaves the run as it was.  Its one-line
       account goes to the debug log, and also to stderr while the phase-time
       account is on (a diagnostic run), so that a run tells a ground-decided
       answer from a proof search's. *)
    preprocess_muclp muclp >>= fun muclp ->
    (match
       MuCLP.GroundSolve.run ~phase:"mucyc-ground-solve"
         ~report:(fun line ->
           Debug.print @@ lazy line;
           if !Common.PhaseTime.on then (
             Out_channel.output_string stderr (line ^ "\n");
             Out_channel.flush stderr))
         config.ground_query_solve muclp
     with
      | Some sol -> Ok sol
      | None -> solve_by_proof_search ?on_counterexample ?lemmas ~dtenv muclp)
    >>= fun sol ->
    if print_sol then print_endline @@ Verdict.str_of sol;
    Ok sol

  (* [lemmas]: claims about [pcsp]'s predicates the user states (RCaml's
     [[@@@lemma]], an SMT-LIB file's [(set-info :coar-lemma ...)]), closed
     formulas over its predicate variables.  They are not part of the
     problem: the relational search tries to prove each and uses only the
     proved ones, so they can change how fast an answer comes, never which
     answer.  Their predicates are kept through the predicate elimination
     below, which would otherwise be free to remove them. *)
  let solve_pcsp ?(print_sol = false) ?(lemmas = []) pcsp =
    (* This backend reduces a predicate constraint problem to fixpoint logic,
       and a fixpoint problem has no place to carry a predicate's KIND: the
       reduction makes every predicate an ordinary least fixpoint.  Every kind
       but the ordinary one states an obligation the clauses do not -- a
       functional predicate must be total and deterministic, a well-founded one
       may not contain a cycle, a non-empty one may not be false everywhere --
       so dropping it answers a weaker question, and the answer comes back
       "satisfiable" on inputs the kind is what refutes.  Measured over the
       eighteen shipped `.clp` files that declare such a kind, the predicate
       constraint solver refutes four and this path answered satisfiable on
       all eighteen of them, among them a three-line file whose two clauses force one
       functional predicate to take two values at the same argument.

       The problem constructor is shared -- the class name on the command line
       documents the input and nothing checks it -- so the compatibility table
       cannot refuse the pairing and the check has to happen here.  Naming the
       one kind that IS supported cannot go stale the way a list of kinds to
       refuse did: the kinds nobody thought of were accepted by such a list. *)
    PCSP.Problem.refuse_non_ord_kinds ~backend:"MuCyc" pcsp;
    let (module Preprocessor : Preprocessor.PreprocessorType) =
      Preprocessor.(
        make @@ Config.make config.enable_pvar_elim config.verbose 4 4 true)
    in
    Debug.print
    @@ lazy "************* converting pfwCSP to muCLP ***************";
    let bpvs =
      Set.Poly.union_list
      @@ List.map lemmas ~f:(fun phi ->
          Set.Poly.map ~f:Ident.pvar_to_tvar @@ LogicOld.Formula.pvs_of phi)
    in
    FrameSearch.phase_time "pre-pcsp" @@ fun () ->
    Preprocessor.solve ~bpvs
      (fun ?oracle pcsp ->
        ignore oracle;
        let open Or_error.Monad_infix in
        (* the counterexample of a refuted expansion, when the unwinding
           route gives one ([report_counterexample]); only the direct
           (CHC-shaped) query records it, never a negated one *)
        let cex = ref None in
        solve ~print_sol:false
          ~dtenv:(PCSP.Problem.dtenv_of pcsp)
          ~on_counterexample:(fun c -> cex := Some c)
          ~lemmas
          (FrameSearch.phase_time "pre-of-chc" (fun () ->
               MuCLP.Util.of_chc ~print:Debug.print ~only_pos:false pcsp))
        >>= fun sol ->
        let sol =
          match sol with
          | Verdict.Valid -> PCSP.Problem.Sat Map.Poly.empty (* ToDo *)
          | Verdict.Invalid ->
              PCSP.Problem.Unsat
                (Option.map !cex ~f:(fun c -> PCSP.Problem.Counterexample c))
          | Verdict.Unknown -> PCSP.Problem.Unknown
          | Verdict.Timeout -> PCSP.Problem.Timeout
        in
        if print_sol then print_endline (PCSP.Problem.str_of_solution sol);
        Or_error.return
          ( sol,
            {
              PCSatCommon.State.num_cegis_iters = -1 (*ToDo*);
              unsat_witness = None;
              kind_certificates = Map.Poly.empty;
            } ))
      pcsp

  (* This MuCyc has no stochastic solver: a problem with a [(random ...)]
     quantifier is refused, never handed to the QSAT solver below, which
     decides universal/existential prefixes only.  [threshold] is accepted
     for the caller's signature and unused. *)
  let solve_smt ?(print_sol = false) ?threshold:(_ : Q.t option) g =
    Debug.print
    @@ lazy (sprintf "original input: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      let senv = Set.to_list @@ LogicOld.Formula.sort_env_of g in
      LogicOld.Formula.mk_exists_if_bounded senv g
    in
    Debug.print @@ lazy (sprintf "closed: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      LogicOld.Formula.move_quantifiers_to_front @@ Normalizer.normalize
      @@ Evaluator.simplify @@ LogicOld.Formula.elim_ite @@ Normalizer.normalize
      @@ LogicOld.Formula.elim_let
      @@ Normalizer.normalize_let ~rename:true
      @@ Typeinf.typeinf_formula
           ~print:(*Debug.print*) (fun _ -> ())
           ~default:(Some LogicOld.T_int.SInt (*ToDo*))
      @@ LogicOld.Formula.aconv_tvar g
    in
    Debug.print
    @@ lazy (sprintf "prenex normal form: %s\n" @@ LogicOld.Formula.str_of g);
    (* Read before [elim_redundant_quantifiers], which drops a [random] binder
       whose variable does not occur and would leave a stochastic problem
       looking like a non-stochastic one. *)
    if
      List.exists (fst @@ LogicOld.Formula.split_quantifiers g) ~f:(function
        | LogicOld.Formula.Random _, _ -> true
        | _ -> false)
    then
      Common.Refusal.refuse
        "a stochastic problem (a random quantifier) is not supported by this \
         MuCyc";
    let g =
      Normalizer.normalize @@ Evaluator.simplify @@ LogicOld.Formula.rm_div_mod
      @@ LogicOld.Formula.elim_redundant_quantifiers g
    in
    Debug.print @@ lazy (sprintf "input: %s\n" (LogicOld.Formula.str_of g));
    let quantifiers, f = LogicOld.Formula.split_quantifiers g in
    let res =
      match Qsat.decide_theory quantifiers with
      | QBF ->
          let open Qsat.QSAT (Mbp.Boolean) in
          `Res (solve ~config ~print:Debug.print quantifiers f)
      | LRA ->
          let open Qsat.QSAT (Mbp.LRA) in
          `Res (solve ~config ~print:Debug.print quantifiers f)
      | LIA ->
          let open Qsat.QSAT (Mbp.LIA) in
          `Res (solve ~config ~print:Debug.print quantifiers f)
      | BV ->
          let open Qsat.QSAT (Mbp.BV) in
          `Res (solve ~config ~print:Debug.print quantifiers f)
    in
    let solution =
      match res with
      | `Res SAT -> SMT.Problem.Sat [ (*ToDo*) ]
      | `Res UNSAT -> SMT.Problem.Unsat
      | `Unknown -> SMT.Problem.Unknown
    in
    if print_sol then
      print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
    Ok solution
end
