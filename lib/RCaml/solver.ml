(* RCaml's entry point: refinement type checking and inference for OCaml.

   [solve_from_file] translates a [.ml] file with [Cgen.from_ml_file] into a
   list of problems and solves them in order: an assertion problem by the
   configured predicate constraint solver, with the least- and greatest-fixpoint
   predicates passed as [preds]/[copreds] and the constructors' refinement
   predicates renamed to their instantiated names; a type-optimization problem
   by the configured CHC optimizer.  One line per problem is printed:
   [verdict,iterations] followed by the assertion it answers.  An [unsat] of a
   problem with an integrable unknown is reported as [unknown] (see the comment
   at that branch). *)

open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Problem

module type SolverType = sig
  type solution = string * PCSP.Problem.solution * int

  val solve_all : ?print_sol:bool -> Problem.t list -> (unit, Error.t) Result.t
  val solve : ?print_sol:bool -> Problem.t -> (unit, Error.t) Result.t
  val solve_from_file : ?print_sol:bool -> string -> (unit, Error.t) Result.t

  val solutions_of_ml_string :
    filename:string -> string -> Problem.solution list Or_error.t
  (** the solutions of the problems of an OCaml structure given as text (named
      [filename] in messages), in order, without printing them *)
end

module Make (Config : Config.ConfigType) : SolverType = struct
  type solution = string * PCSP.Problem.solution * int

  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "RCaml"

  module Cgen = Cgen.Make (Config)

  let solver =
    let open Or_error in
    ExtFile.unwrap config.solver >>= fun cfg -> Ok (PCSPSolver.Solver.make cfg)

  (* the MuCyc solver [mucyc_solver] names, read from its file: a top-level
     solver configuration whose backend is MuCyc *)
  let mucyc =
    lazy
      (match config.mucyc_solver with
      | None -> Ok None
      | Some path -> (
          let open Or_error.Monad_infix in
          Or_error.try_with (fun () -> Yojson.Safe.from_file path)
          >>= function
          | `List [ `String "MuCyc"; r ] -> (
              match MuCyc.Config.of_yojson r with
              | Ok cfg ->
                  MuCyc.Config.instantiate_ext_files cfg >>= fun cfg ->
                  let module M = MuCyc.Solver.Make (struct
                    let config = cfg
                  end) in
                  Ok
                    (Some
                       (fun ~lemmas pcsp ->
                         M.solve_pcsp ~print_sol:false ~lemmas pcsp))
              | Error msg ->
                  Or_error.error_string (sprintf "%s: %s" path msg))
          | _ ->
              Or_error.error_string
                (sprintf "%s is not a MuCyc solver configuration" path)))

  let optimizer =
    let open Or_error in
    ExtFile.unwrap config.chc_optimizer >>= fun cfg ->
    Ok (CHCOptSolver.Solver.make cfg)

  (* An assertion problem with least or greatest fixpoint predicates (the
     temporal effects of recursive functions, defined by [preds] and
     [copreds]) asks whether some interpretation of the unknowns satisfies the
     clauses when the fixpoint predicates denote their definitions.  With a
     fixpoint solver configured it becomes the equivalent fixpoint-logic
     validity problem ([MuCLP.Util.of_chc_with_fixpoints], whose comment
     states the conditions and the argument) and is solved by MuVal.  [None]
     when no fixpoint solver is configured or the problem lacks the shape the
     equivalence needs; the caller then takes its old path.

     A refutation is withheld when a trace sort occurs: the solver reads the
     finite and infinite traces, their concatenation and their membership in
     a regular expression as uninterpreted, so its models include
     interpretations in which concatenation is not even associative, and a
     problem with no solution in one of those may still have one over real
     traces.  A proof holds in every interpretation, the intended one
     included, so it is kept. *)
  let solve_with_fixpoints info ~preds ~copreds pcsp =
    match config.fixpoint_solver with
    | None -> None
    | Some cfg -> (
        let fixpoints =
          List.map (Map.Poly.to_alist preds) ~f:(fun (p, (env, phi)) ->
              MuCLP.Pred.make LogicOld.Predicate.Mu p env phi)
          @ List.map (Map.Poly.to_alist copreds) ~f:(fun (p, (env, phi)) ->
              MuCLP.Pred.make LogicOld.Predicate.Nu p env phi)
        in
        match
          MuCLP.Util.of_chc_with_fixpoints ~print:Debug.print ~fixpoints pcsp
        with
        | Error reason ->
            prerr_endline
              ("the fixpoint solver declines this problem: " ^ reason);
            None
        | Ok muclp ->
            let is_trace = function
              | LogicOld.T_trace.STrace _ -> true
              | _ -> false
            in
            let uses_traces =
              List.exists muclp.preds ~f:(fun (pred : MuCLP.Pred.t) ->
                  List.exists pred.args ~f:(fun (_, s) -> is_trace s))
              || Map.Poly.exists (PCSP.Problem.senv_of pcsp) ~f:(fun s ->
                  List.exists ~f:(fun s ->
                      is_trace (Logic.ExtTerm.to_old_sort s))
                  @@ Logic.Sort.args_of s)
            in
            Debug.print
            @@ lazy
                 (* not [MuCLP.Problem.str_of], whose datatype prelude refuses
                    a parametric datatype such as a list *)
                 (sprintf "*** fixpoint logic problem of %s:\n%s\ns.t.\n%s" info
                    (LogicOld.Formula.str_of muclp.query)
                    (MuCLP.Pred.str_of_list muclp.preds));
            let module MuVal = MuVal.Solver.Make (struct
              let config = ExtFile.unwrap_or_abort cfg
            end) in
            let run () =
              MuVal.solve ~print_sol:false muclp
              |> Or_error.map ~f:(fun (sol, _, iter) -> (sol, iter))
            in
            let res =
              match config.timeout with
              | Some tm when tm > 0 ->
                  Timer.enable_timeout tm Fn.id ignore run
                    (fun _ res -> res)
                    (fun _ -> function
                      | Timer.Timeout -> Ok (MuCLP.Problem.Timeout, -1)
                      | e -> raise e)
              | _ -> run ()
            in
            Some
              (Or_error.map res ~f:(fun (sol, iter) ->
                   let sol =
                     match sol with
                     | MuCLP.Problem.Valid -> PCSP.Problem.Sat Map.Poly.empty
                     | Invalid when uses_traces ->
                         Debug.print
                         @@ lazy
                              (sprintf
                                 "[ret] %s : invalid withheld (traces are \
                                  uninterpreted), reported unknown"
                                 info);
                         PCSP.Problem.Unknown
                     | Invalid -> PCSP.Problem.Unsat None
                     | Unknown -> PCSP.Problem.Unknown
                     | Timeout -> PCSP.Problem.Timeout
                   in
                   (sol, iter))))

  (* Inspect the original problem: preprocessing may eliminate the sampled
     unknown before returning a refutation. *)
  let has_integrable_unknown pcsp =
    Map.Poly.existsi (PCSP.Problem.kind_map_of pcsp) ~f:(fun ~key ~data ->
        Kind.is_integ data && Map.Poly.mem (PCSP.Problem.senv_of pcsp) key)

  (* whether the constraint generator was told to assume that functions
     cannot fail, or cannot fail or cause temporal effects at a partial
     application: the options that replace predicate variables by [true] or
     by the effect of a value *)
  let placement_assumes_something =
    let c = config.cgen_config in
    c.never_fail || c.can_fail_only_at_total_apps
    || c.can_cause_temp_eff_only_at_total_apps

  let solve_problem (info, problem) =
    let open Or_error.Monad_infix in
    match problem with
    | POptimization chcopt_problem ->
        optimizer >>= fun (module Optimizer : CHCOptSolver.Solver.SolverType) ->
        let _, pcsp = chcopt_problem in
        let uses_midpoint = has_integrable_unknown pcsp in
        let solution, iter = Optimizer.solve chcopt_problem in
        let solution =
          match solution with
          | CHCOpt.Problem.Unsat when uses_midpoint ->
              Debug.print
              @@ lazy
                   (sprintf
                      "[ret] %s : optimization unsat withheld (an integrable \
                       unknown's sample is encoded at its midpoint), reported \
                       unknown"
                      info);
              CHCOpt.Problem.Unknown
          | _ -> solution
        in
        Ok (OptimizeSol (solution, iter))
    | PAssertion (preds, copreds, pcsp, lemmas) ->
        Debug.print @@ lazy ("assert: " ^ info);
        solver >>= fun (module PCSPSolver : PCSPSolver.Solver.SolverType) ->
        let bpvs =
          Set.Poly.of_list
          @@ List.map ~f:Ident.pvar_to_tvar
          @@ Map.Poly.keys preds @ Map.Poly.keys copreds
        in
        let ren_ref = ref Map.Poly.empty in
        let pren_ref = ref Map.Poly.empty in
        let pcsp =
          let pcsp =
            PCSP.Problem.map_raw_old_exn pcsp ~f:(fun constrs ->
                let pren =
                  let pvs_preds =
                    Set.Poly.of_list @@ Map.Poly.(keys preds @ keys copreds)
                  in
                  let penv_dtrenv = Cgen.get_penv_dtrenv pvs_preds in
                  (* the fixpoint bodies apply the same predicates and are
                     renamed with them (empty without fixpoint predicates) *)
                  Cgen.pren_of penv_dtrenv pvs_preds
                  @@ Set.union (Set.Poly.map ~f:snd constrs)
                  @@ Set.Poly.of_list
                  @@ List.map ~f:(fun (_, (_, phi)) -> phi)
                  @@ Map.Poly.to_alist preds @ Map.Poly.to_alist copreds
                in
                pren_ref := pren;
                ren_ref :=
                  Map.Poly.of_alist_exn
                  @@ List.map ~f:(fun ((name, _), pvar) ->
                      (Ident.Tvar name, Ident.pvar_to_tvar pvar))
                  @@ Map.Poly.to_alist pren;
                Set.Poly.map constrs ~f:(fun (senv, phi) ->
                    (senv, LogicOld.Formula.rename_sorted_pvars pren phi)))
          in
          (if config.cgen_config.instantiate_svars_to_int then
             PCSP.Problem.instantiate_svars_to_int
           else Fn.id)
          @@ PCSP.Problem.update_params pcsp
          @@
          let params = PCSP.Problem.params_of pcsp in
          {
            params with
            senv = Map.rename_keys_map !ren_ref params.senv;
            kind_map = Map.rename_keys_map !ren_ref params.kind_map;
          }
        in
        let timeout = config.timeout in
        ( (if Map.Poly.is_empty preds && Map.Poly.is_empty copreds then None
           else
             let ren (env, phi) =
               (env, LogicOld.Formula.rename_sorted_pvars !pren_ref phi)
             in
             solve_with_fixpoints info
               ~preds:(Map.Poly.map preds ~f:ren)
               ~copreds:(Map.Poly.map copreds ~f:ren)
               pcsp)
        |> function
          | Some res -> res
          | None -> (
              match Lazy.force mucyc with
              | Error e -> Error e
              | Ok (Some solve_mucyc)
                when Map.Poly.is_empty preds && Map.Poly.is_empty copreds ->
                  (* the lemmas name the predicates as the constraints did
                     before the renaming above, so they are renamed with
                     them *)
                  let lemmas =
                    List.map lemmas
                      ~f:(LogicOld.Formula.rename_sorted_pvars !pren_ref)
                  in
                  let run () =
                    Or_error.map (solve_mucyc ~lemmas pcsp) ~f:(fun (sol, info) ->
                        (sol, info.PCSatCommon.State.num_cegis_iters))
                  in
                  (* the per-problem timeout, as the constraint solvers
                     take it *)
                  (match timeout with
                  | Some tm when tm > 0 ->
                      Timer.enable_timeout tm Fn.id ignore run
                        (fun _ res -> res)
                        (fun _ -> function
                          | Timer.Timeout -> Ok (PCSP.Problem.Timeout, -1)
                          | e -> raise e)
                  | _ -> run ())
              | Ok _ ->
                  (* a lemma is read by MuCyc's relational search alone;
                     ignoring a claim is sound, and it is said, not done
                     silently *)
                  if not (List.is_empty lemmas) then
                    Out_channel.eprintf
                      "[RCaml] %d lemma(s) ignored: only the MuCyc route \
                       (mucyc_solver) reads lemmas\n%!"
                      (List.length lemmas);
                  PCSPSolver.solve ~timeout ~bpvs ~preds ~copreds pcsp))
        >>= fun (solution, iter) ->
        (* A refutation of a problem with an integrable unknown is not reported.
           The constraint generator writes the expectation of a uniform sample,
           [v <= int_0^1 N(y) dy], as the unknown's value at the midpoint,
           [P(dom, 1/2, v)]. That equals the integral only for integrands affine in
           the sample, which is the template's shape but not the kind's condition:
           for a step integrand such as [if 2y >= 1 then 1 else 0] the midpoint
           value is 1 while the integral is 1/2, so a program whose expectation
           bound holds can be refuted. The midpoint premise is exact on the [sat]
           side for the affine template, but a refutation through it proves
           nothing about the program, so [unsat] becomes [unknown] here. *)
        (* a counterexample is checked by evaluation (every clause instance
           of its derivation holds under its model) and its predicates are
           given back their names before the renaming above; one that fails
           the check is dropped, the verdict kept: the solver's refutation
           of the expansion is the verdict's evidence, the counterexample a
           report *)
        let solution =
          match solution with
          | PCSP.Problem.Unsat (Some (PCSP.Problem.Counterexample c)) ->
              if PCSP.Problem.counterexample_holds c then
                let back =
                  Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
                  @@ List.map (Map.Poly.to_alist !ren_ref) ~f:(fun (orig, ren) ->
                      (Ident.name_of_tvar ren, Ident.name_of_tvar orig))
                in
                let name p =
                  match Map.Poly.find back (Ident.name_of_pvar p) with
                  | Some n -> Ident.Pvar n
                  | None -> p
                in
                let rec node (n : PCSP.Problem.cex_node) : PCSP.Problem.cex_node =
                  {
                    n with
                    head = Option.map n.head ~f:(fun (p, ts) -> (name p, ts));
                    body = List.map n.body ~f:(fun (p, ts) -> (name p, ts));
                    children = List.map n.children ~f:node;
                  }
                in
                PCSP.Problem.Unsat
                  (Some
                     (PCSP.Problem.Counterexample
                        { c with derivation = node c.derivation }))
              else (
                Debug.print
                @@ lazy
                     (sprintf
                        "[ret] %s : the counterexample failed its check and \
                         is dropped"
                        info);
                PCSP.Problem.Unsat None)
          | _ -> solution
        in
        let solution =
          match solution with
          | PCSP.Problem.Unsat _ when has_integrable_unknown pcsp ->
              Debug.print
              @@ lazy
                   (sprintf
                      "[ret] %s : unsat withheld (an integrable unknown's \
                       sample is encoded at its midpoint), reported unknown"
                      info);
              PCSP.Problem.Unknown
          | _ -> solution
        in
        (* A refutation under a placement option that assumes something of
           the program is not reported.  [never_fail] makes the refinement of
           every function argument [true] (unless the function's result has
           an impure control effect), [can_fail_only_at_total_apps] does so
           for the arguments of functions whose result is again a function,
           and [can_cause_temp_eff_only_at_total_apps] gives such partial
           applications the temporal effect of a value.  Each replaces
           predicate variables by known formulas, so a solution of the
           constraints so generated is one of the general constraints and
           [sat] stands; the
           converse fails whenever a function is correct only on the
           arguments it is called with: [let f x = assert (x > 0)] used as
           [f 1] is typable, but not with [x]'s refinement [true], and the
           same holds of a specification such as [amb_find e [] = Failure],
           whose helper needs its list argument's refinement.  So an [unsat]
           here says only that no typing exists of that restricted shape, not
           that the program has none, and it becomes [unknown]. *)
        let solution =
          match solution with
          | PCSP.Problem.Unsat _ when placement_assumes_something ->
              Debug.print
              @@ lazy
                   (sprintf
                      "[ret] %s : unsat withheld (a placement option assumes \
                       that functions cannot fail or cause effects at partial \
                       applications), reported unknown"
                      info);
              PCSP.Problem.Unknown
          | _ -> solution
        in
        Debug.print
        @@ lazy
             (sprintf "[ret] %s : %s, %d" info
                (PCSP.Problem.str_of_solution solution)
                iter);
        Debug.print @@ lazy "=============================================";
        Ok (AssertSol (info, solution, iter))

  (* [problem] is read only for an optimisation answer *)
  let print_solution_opt ?(print_sol = true) problem i = function
    | OptimizeSol (sol, iter) ->
        if print_sol then
          print_endline
          @@ CHCOpt.Problem.str_of_solution
               (Problem.senv_of (Option.value_exn problem))
               iter sol
    | AssertSol (str, solution, iter) ->
        (* (match solution with
           | PCSP.Problem.Sat term_map ->
            Map.Poly.iteri term_map ~f:(fun ~key ~data ->
               let open Ast in let open Ast.Logic in
               Debug.print @@ lazy
                 (sprintf "%s : %s" (Ident.name_of_tvar key) (ExtTerm.str_of data)))
           | _ -> ()); *)
        if print_sol then (
          print_endline
          @@ sprintf "%s,%d   \t@assert %s [#%d] "
               (PCSP.Problem.str_of_solution solution)
               iter str (i + 1);
          match solution with
          | PCSP.Problem.Unsat (Some (PCSP.Problem.Counterexample c))
            when config.report_counterexample ->
              List.iter (PCSP.Problem.str_of_counterexample c) ~f:print_endline
          | _ -> ())

  let rec main_loop rets (problems : Problem.t list) =
    let open Or_error.Monad_infix in
    match problems with
    | problem :: problems' ->
        solve_problem problem >>= fun sol ->
        main_loop (rets @ [ sol ]) problems'
    | [] -> Ok rets

  let print_solution ?(print_sol = true) problem i sol =
    print_solution_opt ~print_sol (Some problem) i sol

  let print_all ?(print_sol = true) (problems : Problem.t list) sols =
    List.iteri sols ~f:(fun i ->
        print_solution ~print_sol (List.nth_exn problems i) i)

  let solve_all ?(print_sol = true) (problems : Problem.t list) =
    let open Or_error.Monad_infix in
    main_loop [] problems >>= fun sols ->
    print_all ~print_sol problems sols;
    Ok ()

  let solve ?(print_sol = true) problem = solve_all ~print_sol [ problem ]

  (* Whether the answer [sol] of the shared-instance problem [ptype] may
     stand for the assertion: only a [sat] does (a solution of the shared
     system gives one of the copying system, while a refutation of the
     shared system refutes nothing), and only of a problem without fixpoint
     predicates (whose definitions are copied per instance, outside the
     constraints the argument is about) and without a kind that ties
     several predicates together ([NWF], [Parity]: the argument needs each
     kind to be a property of one predicate's interpretation). *)
  let shared_answer_stands ptype sol =
    match (ptype, sol) with
    | ( Problem.PAssertion (preds, copreds, pcsp, _),
        AssertSol (_, PCSP.Problem.Sat _, _) ) ->
        Map.Poly.is_empty preds && Map.Poly.is_empty copreds
        && not
             (Map.Poly.exists (PCSP.Problem.kind_map_of pcsp) ~f:(function
               | Kind.NWF _ | Kind.Parity _ -> true
               | _ -> false))
    | _ -> false

  (* The shared-instance attempt ([merge_instantiation_copies]) itself: run
     in a raced copy ([race_shared]), or, when no copy can be made, before
     the ordinary run, which then answers what it leaves.

     Contract: every answer printed for an assertion the attempt does not
     answer is the one a run without the option gives, from the same state.
     The generator and the solvers keep process-wide state across a
     generation -- the datatype and function environments, the solver's
     datatype declarations, the fresh-name counters, the fixpoint
     definitions -- and a second generation in the same process met the
     first one's: it re-declared a datatype the first had declared (a
     crash), and on another input its problem solved in a minute where the
     plain run takes two seconds.  So the attempt runs in a forked child
     process, and this process, which never ran the shared generation,
     generates and solves as without the option.  The child generates with
     [Rtype.shared_instances] set, solves the assertion problems in order
     with its standard output discarded, and reports through a pipe, one
     marshalled record per problem as soon as it is solved, the position,
     the assertion and the iteration count of every answer that stands
     ([shared_answer_stands]); the parent kills it after
     [merged_attempt_timeout] seconds, keeping the records already
     received.  A generation that raises, a crash or a kill only loses
     answers.  An answer carried over is a [sat] without its model (the
     model names the shared system's predicates).  When every problem is
     answered the ordinary generation is not run at all (it is the one
     whose size doubles with each nesting of a polymorphic call); otherwise
     it runs, and an answer is carried over by position only when both
     generations made the same number of problems.  When this process
     cannot fork (OCaml refuses once a second domain exists), the attempt is
     skipped.

     The child never outlives this process and never outlives the attempt.
     It is forked by [ForkGuard], so the kernel kills it when this process
     dies, whatever kills it: the deadline above is kept by this process
     alone, and a child left behind by a parent killed on its own (a memory
     cap, a harness that signals one pid) ran unbounded, generating and
     solving every problem of the shared system.  A wall-clock limit's
     SIGTERM to the whole group does not stop it either when the phase
     account is on, since the child inherits the account's handler, which
     only records the signal for a watcher thread the child does not have.
     And when the wait is left by an exception (the run's own timer firing
     inside it), the child is killed and reaped on the way out rather than
     left computing beside the rest of the run. *)
  let shared_attempt gen =
    let records = ref [] and count = ref None in
    (try
       Out_channel.flush stdout;
       Out_channel.flush stderr;
       let rd, wr = Core_unix.pipe () in
       match ForkGuard.fork () with
       | `In_the_child ->
           Core_unix.close rd;
           (try
              let null = Core_unix.openfile "/dev/null" ~mode:[ O_WRONLY ] in
              Core_unix.dup2 ~src:null ~dst:Core_unix.stdout ();
              let oc = Core_unix.out_channel_of_descr wr in
              (* each record is written as soon as it exists, so that a
                 kill keeps the answers already found; the count first *)
              let send r =
                Stdlib.Marshal.to_channel oc r [];
                Stdlib.flush oc
              in
              Rtype.shared_instances := Some (Hashtbl.create (module String));
              Rtype.shared_instance_reuses := 0;
              (match gen () with
              | Error _ -> ()
              | Ok _ when !Rtype.shared_instance_reuses = 0 ->
                  (* no copy was shared: the shared system is the copying
                     one up to names, so solving it only repeats the
                     ordinary run (see [Rtype.shared_instance_reuses]) *)
                  send `Unshared
              | Ok problems ->
                  send (`Count (List.length problems));
                  List.iteri problems ~f:(fun i ((_, ptype) as problem) ->
                      match ptype with
                      | Problem.POptimization _ -> ()
                      | Problem.PAssertion _ -> (
                          let t0 = Core_unix.gettimeofday () in
                          let ret = solve_problem problem in
                          Debug.print
                          @@ lazy
                               (sprintf
                                  "[shared instances] problem %d: %s after \
                                   %.1f s"
                                  i
                                  (match ret with
                                  | Ok (AssertSol (_, sol, _)) ->
                                      PCSP.Problem.str_of_solution sol
                                  | Ok _ -> "not an assertion"
                                  | Error e -> Error.to_string_hum e)
                                  (Core_unix.gettimeofday () -. t0));
                          match ret with
                          | Ok (AssertSol (info, _, iter) as sol)
                            when shared_answer_stands ptype sol ->
                              send (`Answer (i, info, iter))
                          | Ok _ | Error _ -> ())))
            with _ -> () (* catch-all-ok: forked child before _exit; its only output is the pipe *));
           Caml_unix._exit 0
       | `In_the_parent pid ->
           Core_unix.close wr;
           let deadline =
             Time_float.add (Time_float.now ())
               (Time_float.Span.of_sec
                  (Float.of_int (max 1 config.merged_attempt_timeout)))
           in
           let rec wait () =
             match Core_unix.wait_nohang (`Pid pid) with
             | Some _ -> ()
             | None ->
                 if Time_float.(now () > deadline) then (
                   (try Signal_unix.send_i Signal.kill (`Pid pid)
                    with exn_ when not (Timer.is_async exn_) -> ());
                   ignore (Core_unix.waitpid pid : Core_unix.Exit_or_signal.t))
                 else (
                   ignore (Core_unix.nanosleep 0.02 : float);
                   wait ())
           in
           (* the pipe is drained after the child ends: a record is a few
              dozen bytes and a pipe holds 64 KB, far more than one file's
              assertions; a child blocked on a full pipe is killed at the
              deadline like any other *)
           let reaped = ref false in
           ForkGuard.register (Pid.to_int pid);
           Timer.protect
             ~finally:(fun () ->
               ForkGuard.unregister (Pid.to_int pid);
               if not !reaped then (
                 (try Signal_unix.send_i Signal.kill (`Pid pid)
                  with exn_ when not (Timer.is_async exn_) -> ());
                 try ignore (Core_unix.waitpid pid : Core_unix.Exit_or_signal.t)
                 with exn_ when not (Timer.is_async exn_) -> ()))
             (fun () ->
               wait ();
               reaped := true);
           let ic = Core_unix.in_channel_of_descr rd in
           let rec read () =
             match
               (Stdlib.Marshal.from_channel ic
                 : [ `Count of int | `Answer of int * string * int | `Unshared ])
             with
             | `Unshared ->
                 Debug.print
                 @@ lazy
                      "[shared instances] no instance shared: attempt not solved";
                 read ()
             | `Count n ->
                 count := Some n;
                 read ()
             | `Answer r ->
                 records := r :: !records;
                 read ()
             | exception exn_ when not (Timer.is_async exn_) -> ()
           in
           read ();
           In_channel.close ic
     with exn_ when not (Timer.is_async exn_) ->
       Debug.print
       @@ lazy ("[shared instances] attempt skipped: " ^ Exn.to_string exn_));
    (!count, List.rev !records)

  (* [race_shared gen]: the shared-instance attempt raced, in a forked copy
     of this process ([PCSatCommon.ParallelRace]), against the ordinary run
     this process goes on with.

     Why a race and not the attempt first: the attempt's cost on an input
     whose shared system it does not answer is otherwise added to the
     ordinary run's time -- up to the whole [merged_attempt_timeout] -- and
     an answer that took most of a caller's time limit passed it (a
     relational input that the ordinary run answers in 45-57 s of a 60 s
     limit lost its answer, and nine others took 15-20 s longer).  Raced,
     the attempt costs a second core for at most [merged_attempt_timeout]
     seconds and never delays the ordinary run.

     Contract.
     - [`Won answers] is returned only in the copy, and only when the shared
       generation made [n > 0] problems and every one of them is an assertion
       answered by an answer that stands ([shared_answer_stands]); [answers]
       lists them in order as [(position, assertion, iterations)].  The copy
       then answers the run: its standard output, discarded while it solved,
       is restored, and this process exits with the copy's status without
       printing anything ([ParallelRace.start]).
     - [`Racing (t, rd)] is returned in this process, which never ran the
       shared generation and so generates and solves exactly as without the
       option.  When the attempt ends without answering every problem, [rd]
       carries the marshalled records [`Count n] (the number of problems of
       the shared generation, when it made them) and [`Answer (i, info,
       iter)] (an answer that stands for the [i]-th problem), for the run to
       carry over.  The caller must [ParallelRace.finish t] before it prints,
       which kills the copy (and the attempt under it) unless the copy has
       already been given the run, in which case it never returns.
     - [`Not_started]: no copy was made (a memory budget, a second domain, a
       failed fork); nothing ran.
     - The attempt is [shared_attempt]'s, with its bounds: given up after
       [merged_attempt_timeout] seconds of wall-clock time, and at once when
       its generation shared no instance ([Rtype.shared_instance_reuses] is
       0: its system is then the copying one up to names, which this process
       is already solving). *)
  let race_shared gen =
    match Core_unix.pipe () with
    | exception exn_ when not (Timer.is_async exn_) -> `Not_started
    | rd, wr -> (
        let attempt () =
          Core_unix.close rd;
          (* the attempt itself runs one fork further down ([shared_attempt]):
             a constraint solver may race copies of its own, and the copy
             that wins such an inner race continues the program of the
             process that started it -- here it would return from the
             attempt in a process this race never forked, announce an
             answer, and wait for a grant that only the copy's own watcher
             thread can receive.  Behind [shared_attempt]'s fork every inner
             race has ended before its child reports, and the answers reach
             the copy as plain records. *)
          let n_shared, answers = shared_attempt gen in
          match n_shared with
          | Some n when n > 0 && n = List.length answers -> Some answers
          | _ ->
              (* for the run to carry over the answers found *)
              let send r =
                let b = Stdlib.Marshal.to_bytes r [] in
                try ignore (Core_unix.single_write wr ~buf:b : int)
                with exn_ when not (Timer.is_async exn_) -> ()
              in
              Option.iter n_shared ~f:(fun n -> send (`Count n));
              List.iter answers ~f:(fun r -> send (`Answer r));
              None
        in
        (* [`None]: the shared attempt answers for every assertion at once,
           and no inclusion between one of its PCSat problems and one of the
           ordinary run's says the run gives the attempt's answers *)
        match PCSatCommon.ParallelRace.start ~reads:`None attempt with
        | `Won answers -> `Won answers
        | `Racing t ->
            Core_unix.close wr;
            `Racing (t, rd)
        | `Not_started ->
            (try
               Core_unix.close rd;
               Core_unix.close wr
             with exn_ when not (Timer.is_async exn_) -> ());
            `Not_started)

  (* [read_records rd pending]: every complete record now readable from
     [rd] (see [race_shared]), without blocking; [pending] keeps the bytes
     of a record not yet complete *)
  let read_records rd pending =
    let chunk = Bytes.create 4096 in
    let rec drain () =
      match
        Core_unix.select ~restart:true ~read:[ rd ] ~write:[] ~except:[]
          ~timeout:`Immediately ()
      with
      | exception exn_ when not (Timer.is_async exn_) -> ()
      | ready when List.is_empty ready.read -> ()
      | _ -> (
          match Core_unix.read rd ~buf:chunk with
          | exception exn_ when not (Timer.is_async exn_) -> ()
          | 0 -> ()
          | k ->
              Stdlib.Buffer.add_subbytes pending chunk 0 k;
              drain ())
    in
    drain ();
    let s = Stdlib.Buffer.contents pending in
    let len = String.length s in
    let rec parse pos acc =
      if len - pos < Stdlib.Marshal.header_size then (pos, acc)
      else
        let total = Stdlib.Marshal.total_size (Bytes.of_string s) pos in
        if len - pos < total then (pos, acc)
        else
          parse (pos + total)
            ((Stdlib.Marshal.from_string s pos
               : [ `Count of int | `Answer of int * string * int ])
            :: acc)
    in
    let pos, records = parse 0 [] in
    Stdlib.Buffer.clear pending;
    Stdlib.Buffer.add_substring pending s pos (len - pos);
    List.rev records

  (* The shared-instance attempt ([merge_instantiation_copies]) and the
     ordinary run, raced ([race_shared]); the sequential order
     ([shared_attempt], then the ordinary run) when no copy can be made.

     Contract: every answer printed is either one the ordinary run (without
     the option) gives for that assertion, or a [sat] carried over from the
     shared generation that stands ([shared_answer_stands]; a solution of the
     shared system gives one of the copying system).  An answer is carried
     over by position only when both generations made the same number of
     problems.  When the copy answers every problem it answers the run and
     the ordinary run is abandoned wherever it is. *)
  let solve_shared_first ~gen =
    let open Or_error.Monad_infix in
    let carried answers i =
      List.find_map answers ~f:(fun (j, info, iter) ->
          if i = j then
            Some (AssertSol (info, PCSP.Problem.Sat Map.Poly.empty, iter))
          else None)
    in
    let plain_loop ~answers_for problems =
      let rec loop i rets = function
        | [] -> Ok (List.rev rets)
        | problem :: rest -> (
            match answers_for i with
            | Some sol -> loop (i + 1) ((Some problem, sol) :: rets) rest
            | None ->
                solve_problem problem >>= fun sol ->
                loop (i + 1) ((Some problem, sol) :: rets) rest)
      in
      loop 0 [] problems
    in
    match race_shared gen with
    | `Won answers ->
        Debug.print
        @@ lazy
             (sprintf "[shared instances] the raced attempt answered all %d"
                (List.length answers));
        Ok
          (List.init (List.length answers) ~f:(fun i ->
               (None, Option.value_exn (carried answers i))))
    | `Racing (t, rd) ->
        let pending = Stdlib.Buffer.create 256 in
        let count = ref None and answers = ref [] in
        let poll () =
          List.iter (read_records rd pending) ~f:(function
            | `Count n -> count := Some n
            | `Answer r -> answers := r :: !answers)
        in
        Timer.protect
          ~finally:(fun () ->
            PCSatCommon.ParallelRace.finish t;
            try Core_unix.close rd
            with exn_ when not (Timer.is_async exn_) -> ())
          (fun () ->
            gen () >>= fun problems ->
            let n_plain = List.length problems in
            plain_loop problems ~answers_for:(fun i ->
                poll ();
                if Option.equal Int.equal !count (Some n_plain) then
                  carried !answers i
                else None))
    | `Not_started -> (
        let n_shared, answers = shared_attempt gen in
        Debug.print
        @@ lazy
             (sprintf "[shared instances] %d of %s problem(s) answered"
                (List.length answers)
                (Option.value_map n_shared ~default:"?" ~f:Int.to_string));
        match n_shared with
        | Some n when n > 0 && n = List.length answers ->
            Ok (List.init n ~f:(fun i -> (None, Option.value_exn (carried answers i))))
        | _ ->
            gen () >>= fun problems ->
            let same_count =
              Option.equal Int.equal n_shared (Some (List.length problems))
            in
            plain_loop problems ~answers_for:(fun i ->
                if same_count then carried answers i else None))

  let solutions_of_ml_string ~filename text =
    let open Or_error.Monad_infix in
    let gen () = Cgen.from_ml_string config.cgen_config ~filename text in
    if config.merge_instantiation_copies then
      solve_shared_first ~gen >>| List.map ~f:snd
    else gen () >>= main_loop []

  let solve_from_file ?(print_sol = true) filename =
    match snd (Filename.split_extension filename) with
    | Some "ml" ->
        let open Or_error.Monad_infix in
        let gen () = Cgen.from_ml_file config.cgen_config filename in
        if config.merge_instantiation_copies then
          solve_shared_first ~gen >>| fun answered ->
          List.iteri answered ~f:(fun i (problem, sol) ->
              print_solution_opt ~print_sol problem i sol)
        else gen () >>= solve_all ~print_sol
    | _ -> Or_error.unimplemented "solve_from_file"
end
