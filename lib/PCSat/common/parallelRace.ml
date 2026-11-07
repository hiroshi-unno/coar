open Core

(* Race a computation in a forked copy of this process against the work the
   process goes on with, the first answer winning.

   Why a forked copy and not a domain: the computation raced here (the
   Houdini-style pre-pass) asks its own questions in forked copies, and OCaml
   refuses to fork a process that has ever spawned a domain, so a domain would
   disable every forked question of the run, in the domain and in the main
   loop alike.  A copy also shares no solver context, no global table and no
   counter with the process, so neither side can disturb the other.

   Why the copy continues rather than sending its answer back: what the copy
   finds is a value of the term language, whose constructors are extensible
   variants, and such a value does not survive [Marshal] (each constructor is
   matched by the identity of a slot created at start-up, which the
   unmarshalled value only copies).  So when the copy finds an answer it does
   not send it: it asks the process for the right to answer, and once given it
   returns that answer to its caller and runs the rest of the program -- the
   very continuation the process would have run had it computed the answer
   itself, sequentially, at the point of the fork.  The process then waits for
   the copy and exits with its status, having printed nothing more.

   Contract.
   - [start ?nice f] forks.  In the copy, which first lowers its own
     scheduling priority by [nice] ([lower_priority]; 0 by default, no change),
     [f ()] is computed; [None] (or a raise)
     ends the copy silently; [Some v] makes the copy ask for the right to
     answer and, once given it, [start] returns [`Won v] in the copy.  In the
     process [start] returns [`Racing t] (or [`Not_started] when the fork
     failed, the process having a domain for instance, or [f] could not be
     raced).
   - Exactly one of the two answers.  The right to answer is one atomic
     claim: the copy is given it only by the watcher thread of the process
     (which reads the copy's pipe every 50 ms, so a copy's answer is taken up
     while the process is inside a solver call or a long phase), and the process keeps its own answer only through [finish],
     which claims first.  [finish t] after a lost race never returns: the
     watcher thread is waiting for the copy and will exit the process.
   - The copy never outlives the race.  [finish] kills the copy's process
     group (the copy and the forked questions it asks) and reaps the copy; a
     copy whose process has died (killed by a wall-clock limit, say) notices
     at once (the kernel kills it with its parent, [Common.ForkGuard.fork];
     on a platform without that request, within 100 ms, when its pipe from
     the process reaches end of file or its parent changes) and its forked
     questions die with it in turn.
   - After a won race the process exits with the copy's exit status (128 + the
     signal for a copy killed by one), and before exiting it kills the forked
     questions of its own that are still alive ([ForkedQuery.kill_live]), which
     would otherwise run to the end of their solver call as orphans.
   - With the phase account ([Common.PhaseTime]) on, a won copy reports its
     own phases from the fork, labelled as the copy's, at its exit or on a
     termination signal, which the process passes on to it; the process's own
     report follows the copy's, never interleaved with it.  The process's
     report is [start]'s [report], by default the account's own report
     ([Common.PhaseTime.report], reason [copy-answered]; [sigterm] when a
     termination signal is being handled), printed once whichever of the
     hand-over's exit and the account's signal watcher reaches it first.
     With the account off nothing of this happens.
   - How a termination signal reaches the run after a hand-over.  The copy
     is in a process group of its own, so a signal sent to the run's group
     reaches the process only; with the account off the process has no
     handler, dies at once and the copy dies with it ([Common.ForkGuard]).
     With the account on, the process's signal watcher passes the signal on
     ([hand_over], [forward_signals]); that watcher is an OCaml thread, so
     the signal reaches the copy only once the process's main thread is at
     a safe point or inside a call that released the runtime lock.  The main
     thread parks at its next phase boundary or solver check after the
     hand-over ([Common.ForkGuard.park_if_handed]), so the delay is the rest
     of the native call the main thread is in, if that call keeps the lock;
     the copy's answer itself is taken only once such a call returns, the
     watcher that reads the copy's pipe needing the same lock.

   - Several races at once.  A process may have several copies racing at the
     same time, each started by its own [start] (the races nest: each one's
     [finish] encloses everything started after it).  At most one copy of a
     process is ever given the right to answer: the first watcher to read an
     answer claims its race and then the process ([handed]), and a later
     copy's answer claims its race only -- that copy waits for a right it
     will not get and dies with the process.  And [finish] after another race
     of the process was handed over never returns either, so the process
     cannot answer beside the copy whatever order its races finish in.

   Two claims ([two_claims], off by default).  A copy's answer is either final
   (a verdict: a probe's [sat], a refuted problem, a Houdini solution) or a
   point to continue from (the Houdini copy's failed fixed point with its
   counterexamples, from which the copy runs the CEGIS loop again); [start]'s
   [final] tells them apart.  With one claim the first copy to answer is
   given the whole run, and a continuing copy that takes over at 20 s locks
   out a probe's copy holding a sound [sat] at 40 s while it computes for a
   minute more.  With [two_claims] on, the run is split in two rights:
   - the computation ([handed]): given to the first copy that answers, final
     or not, exactly as before; the process's main thread then parks.  A
     continuing copy is given this right only, and remembers that it still
     has to ask for the second ([pending_verdict]);
   - the verdict ([verdict_given]): given to the first holder of a final
     answer to ask -- a copy whose answer is final, at the moment it answers,
     or a continuing copy at the point it is about to print its verdict
     ([claim_verdict], called on the program's ordinary output path through
     [Common.ForkGuard.before_verdict]).  When a final copy is given it while
     a continuing copy holds the computation, the process kills the latter
     (its group too), and the final copy becomes the run.  A copy refused the
     verdict waits and dies with the process.
   The process's own verdict needs no second claim: it leaves only through
   [finish] of every race, which claims each race first, so no copy of it can
   be given anything afterwards.  A copy that itself races copies asks its
   parent for the verdict before giving it to one of them ([claim_verdict]
   before the grant), so the rule holds up a chain of copies.  Exactly one
   verdict is printed: every printer holds the verdict claim of every process
   above it.  Every answer is one the race could give with one claim -- a
   raced copy's own (sound by the racing caller's contract) or the process's
   -- only which of them is printed changes.  In a copy, [finish] of a race it
   inherited from the process at the fork (the race of a sibling) leaves the
   sibling alone: a sibling given the verdict by their common parent must not
   be killed by a copy whose own claim was refused.  A continuing copy that
   exits without asking (an error, a verdict printed on a path without the
   hook) ends the run with its status, as with one claim, unless a final copy
   was given the verdict first.

   The caller's budget.  A race may be started inside
   a caller's [Common.Timer.enable_timeout] budget (PCSat run by MuStrat for
   a strategy check, by RCaml with a timeout, by MuVal's interactive mode).
   The fork gives the copy no alarm, so a copy that takes the run over would
   otherwise compute without a budget for as long as it likes.  So the copy,
   once given the computation, arms the alarm for what is left of the budget
   at that moment ([Common.Timer.resume_budget_in_copy]); its [Timeout] is
   raised where the process's would have been and reaches the same handlers,
   which give the same timed-out answer the process would have given, and the
   copy exits with that answer's status as the run.  The process, having
   handed the run over, cancels its own alarm and ignores SIGALRM
   ([Common.Timer.disarm_for_hand_over]), so that it cannot raise [Timeout]
   in its parked main thread and print a timed-out answer beside the copy's.
   With no budget armed nothing of this happens.  The copy's raced
   computation ([f]) itself runs without the alarm, as before: it ends by its
   own means or is killed by [finish].

   What it relies on: the process has one running domain (as [ForkedQuery]
   does); the watcher is a system thread, which runs while the main thread is
   inside a solver call because the Z3 bindings release the runtime lock
   there; output buffered before the fork is flushed first so that it is not
   written twice. *)

type state = Racing | Process_won | Copy_won | Copy_done

(* Which verdict a race's copy can answer with, which decides in which
   direction [Duplicate] may find the copy a duplicate of the process (see
   [Duplicate.covers_for]):
   - [`Sat]: the copy answers only with a solution (a probe's [sat]);
   - [`Unsat]: the copy answers only with a refutation;
   - [`Both]: either;
   - [`None]: the copy is never compared, whatever it answers -- for a copy
     that differs from the process by its solver, its budget or its scope
     rather than by its problem, so that no inclusion of problems says the
     process gives the copy's answer. *)
type reads = [ `Sat | `Unsat | `Both | `None ]

type t = {
  pid : Pid.t;
  from_copy : Core_unix.File_descr.t;  (** 'S' (an answer) or 'N' (none) *)
  to_copy : Core_unix.File_descr.t;  (** 'g': the copy may answer *)
  state : state Atomic.t;
  reaped : bool Atomic.t;
  stem : string;
      (** the path stem of the two files [checkpoint] compares through *)
  log : string -> unit;  (** the race's own log line *)
  owner : Pid.t;  (** the process that started the race (the copy's parent) *)
  probe_depth : int;
      (** [Duplicate.probe_depth ()] when the race started: [Duplicate.checkpoint]
          writes the process's digest for this race only at that depth *)
  reads : reads;
      (** what the copy answers with; the direction of [Duplicate.covers_for] *)
  settle_by : float option;
      (** [Some d]: a process whose own answer is not a verdict waits for this
          copy until [d] ([Common.PhaseTime.now]'s clock) before it kills it
          ([settle_then_finish]); [None]: it is killed at once *)
}

(* [two_claims]: see "Two claims" above; only ever turned on *)
let two_claims = ref false

(* in a process: set once a copy was given the right to print the verdict
   (with [two_claims] only) *)
let verdict_given = Atomic.make false

(* in a process: the race whose copy holds the computation without the
   verdict (with [two_claims] only), killed when a final copy is given the
   verdict *)
let computing : t option Atomic.t = Atomic.make None

(* in a copy given the computation only: its pipe to the parent and the
   count of grants its watcher has read (the first gave the computation, the
   second gives the verdict) *)
let pending_verdict :
    (Core_unix.File_descr.t * int Atomic.t) option ref =
  ref None

(* serialises [claim_verdict]: the main thread (about to print) and the
   watchers granting a final copy of this process's own may ask at once *)
let claim_mutex = Caml_threads.Mutex.create ()

(* the number of raced copies that exist; read by the tests *)
let racing = Atomic.make 0

(* the number of copies this process has forked by [start]; read by the
   tests, to tell a sequential order from a raced one *)
let started = Atomic.make 0

(* set once, by the watcher that hands this process over to a copy: from
   then on no other copy is given the right to answer and the process
   itself answers nothing.  It is [Common.ForkGuard.handed], so that the main
   thread's safe points below this library (entering and leaving a phase, each
   solver check) can stop the main thread after a hand-over
   ([Common.ForkGuard.park_if_handed]) *)
let handed = Common.ForkGuard.handed

(* in the process's main thread: never return (the watcher that handed the
   process over exits it once its copy has finished) *)
let wait_forever () =
  let rec wait () =
    Caml_threads.Thread.delay 1.;
    wait ()
  in
  wait ()
let quietly g = try g () with exn when not (Common.Timer.is_async exn) -> ()

(* [remove_own_files ()]: remove the comparison files of every race this very
   process started and has not finished ([Duplicate.remove_owned], installed
   there; a no-op until then).  [exit_now code] runs it and then ends the
   process at once: every way out of this module that ends a process without
   [finish] -- a hand-over, a copy leaving, a copy whose process died -- goes
   through it, since [finish] (which removes a race's files) never runs
   there. *)
let remove_own_files : (unit -> unit) ref = ref (fun () -> ())

let exit_now code =
  quietly (fun () -> !remove_own_files ());
  (* a copy under COAR_COPY_REPORT that leaves prints its report; nothing
     otherwise *)
  Common.PhaseTime.copy_end ~reason:(Printf.sprintf "copy-exits-%d" code);
  Common.ProcessExit.immediately code

let exit_status_code = function
  | Ok () -> 0
  | Error (`Exit_non_zero n) -> n
  | Error (`Signal s) -> 128 + Signal_unix.to_system_int s

(* [claim_verdict ()]: in a copy that was given the computation only (with
   [two_claims]), ask the parent for the right to print the verdict and wait
   until it is given; a copy refused it never returns (the parent kills it, or
   it dies with the parent).  Anywhere else -- the process itself, a copy
   given a final answer's right, a copy that has asked already -- it returns
   at once.  Called before the verdict is printed and before this process
   gives the verdict to a copy of its own. *)
let claim_verdict () =
  Caml_threads.Mutex.lock claim_mutex;
  Exn.protect
    ~finally:(fun () -> Caml_threads.Mutex.unlock claim_mutex)
    ~f:(fun () ->
      match !pending_verdict with
      | None -> ()
      | Some (to_parent, grants) ->
          (try
             ignore (Core_unix.single_write_substring to_parent ~buf:"V" : int)
           with _ (* catch-all-ok: the copy ends here whatever failed *) ->
             exit_now 1);
          while Atomic.get grants < 2 do
            Caml_threads.Thread.delay 0.01
          done;
          pending_verdict := None)

let () = Common.ForkGuard.verdict_hook := claim_verdict

(* in the process, under COAR_COPY_REPORT only ([Common.ForkGuard.copy_report]):
   the races it started, newest first, so that when it exits on a copy's
   behalf the copies still racing are first given their grace to print their
   reports ([stop_racing_copies]) rather than dying silently with it; always
   empty without the variable, and emptied in every copy at its fork *)
let started_races : t list Atomic.t = Atomic.make []

(* the copies of [started_races] not yet reaped, under COAR_COPY_REPORT:
   SIGTERM to each and its group, and up to the grace for them to end
   ([Common.ForkGuard.term_first]); nothing without the variable.  Called
   only on the process's way out, where these copies die anyway.  The grace
   is the 2 s a forwarded termination signal is given ([forward_signals]):
   a copy busy in a solver call that keeps the runtime lock reports only once
   the call returns, and at the default grace a copy that had raced the whole
   run was seen to die unreported. *)
let stop_racing_copies () =
  Common.ForkGuard.term_first ~group:true ~grace:2.
    (List.filter_map (Atomic.get started_races) ~f:(fun t ->
         if Atomic.get t.reaped then None else Some (Pid.to_int t.pid)))

(* in the process, after the run was given to a copy that has now exited
   with [status]: kill this process's own forked questions, flush, report
   and exit with the copy's status *)
let exit_as_copy ~report status =
  ForkedQuery.kill_live ();
  stop_racing_copies ();
  (try Stdlib.flush_all () with _ -> ());
  report ();
  exit_now (exit_status_code status)

(* with the phase account on, a termination signal is passed on to the copy,
   whose own account then reports, and the process prints its report only
   once the copy has been reaped (or 2 s later): the copy was put in a group
   of its own, so a signal sent to the run's group does not reach it, and the
   death of the process would kill it before it could report *)
let forward_signals t =
  if !Common.PhaseTime.on then
    Common.PhaseTime.at_signal (fun () ->
        if not (Atomic.get t.reaped) then (
          let signal =
            match Atomic.get Common.PhaseTime.term_signal with
            | 0 -> Stdlib.Sys.sigterm
            | n -> n
          in
          quietly (fun () ->
              Signal_unix.send_i (Signal.of_caml_int signal) (`Pid t.pid));
          let deadline = Common.PhaseTime.now () +. 2. in
          while
            (not (Atomic.get t.reaped))
            && Float.(Common.PhaseTime.now () < deadline)
          do
            Caml_threads.Thread.delay 0.01
          done))

(* in the process: give the copy the right to answer, wait for it and exit with
   its status *)
let hand_over ~report ~log t =
  log "the copy answered; handing over";
  (* the copy carries the caller's budget from here (see "The caller's budget" above) *)
  Common.Timer.disarm_for_hand_over ();
  (* with the phase account on, a termination signal is passed on to the copy,
     whose own account then reports, and the process prints its report only
     once the copy has been reaped (or 2 s later): the copy was put in a group
     of its own, so a signal sent to the run's group does not reach it, and
     the death of the process would kill it before it could report *)
  if !Common.PhaseTime.on then
    Common.PhaseTime.at_signal (fun () ->
        let signal =
          match Atomic.get Common.PhaseTime.term_signal with
          | 0 -> Stdlib.Sys.sigterm
          | n -> n
        in
        quietly (fun () ->
            Signal_unix.send_i (Signal.of_caml_int signal) (`Pid t.pid));
        let deadline = Common.PhaseTime.now () +. 2. in
        while
          (not (Atomic.get t.reaped))
          && Float.(Common.PhaseTime.now () < deadline)
        do
          Caml_threads.Thread.delay 0.01
        done);
  quietly (fun () ->
      ignore (Core_unix.single_write_substring t.to_copy ~buf:"g" : int));
  let status = Core_unix.waitpid t.pid in
  Atomic.set t.reaped true;
  ForkedQuery.kill_live ();
  stop_racing_copies ();
  (try Stdlib.flush_all () with _ -> ());
  report ();
  exit_now (exit_status_code status)

(* in the process, with [two_claims]: the copy of [t] (holding the
   computation only) is superseded by a copy given the verdict; kill it and
   its group.  Its watcher, seeing it exit, reaps it and finds the verdict
   given. *)
let kill_superseded t =
  t.log "a copy with a final answer is given the verdict; the copy that took over is killed";
  (* under COAR_COPY_REPORT the copy is first given its grace to report *)
  Common.ForkGuard.term_first ~group:true [ Pid.to_int t.pid ];
  quietly (fun () -> Signal_unix.send_i Signal.kill (`Group t.pid));
  quietly (fun () -> Signal_unix.send_i Signal.kill (`Pid t.pid))

(* in the process, with [two_claims]: the copy of [t] has a final answer and
   its race is claimed.  It is given the verdict when no one has it (after
   this process, if itself a copy given the computation only, has been given
   it by its parent), the copy holding the computation only being killed;
   otherwise it is left to die with the process. *)
let answer_final ~report ~log t =
  claim_verdict ();
  if Atomic.compare_and_set verdict_given false true then (
    Option.iter (Atomic.exchange computing None) ~f:kill_superseded;
    hand_over ~report ~log t)
  else log "the copy answered; the verdict is another's"

(* in the process, with [two_claims]: give the copy of [t], whose answer is
   a point to continue from, the computation, and then wait for it to ask
   for the verdict ('V') or to exit.  Asking, it is given the verdict unless
   a final copy has it; exiting without asking, its exit is the run's unless
   a final copy has the verdict (as with one claim). *)
let continue_copy ~report ~log t =
  log "the copy takes the computation over; handing it over";
  Common.Timer.disarm_for_hand_over ();
  Atomic.set computing (Some t);
  forward_signals t;
  quietly (fun () ->
      ignore (Core_unix.single_write_substring t.to_copy ~buf:"g" : int));
  let buf = Bytes.create 1 in
  let reap_and_end status =
    Atomic.set t.reaped true;
    if Atomic.compare_and_set verdict_given false true then (
      log "the copy that took over exited without asking for the verdict";
      exit_as_copy ~report status)
  in
  let rec loop () =
    match Core_unix.wait_nohang (`Pid t.pid) with
    | exception exn when not (Common.Timer.is_async exn) ->
        (* already reaped (it cannot be: only this thread reaps it) *)
        Atomic.set t.reaped true
    | Some (_, status) -> reap_and_end status
    | None -> (
        match
          Core_unix.select ~restart:true ~read:[ t.from_copy ] ~write:[]
            ~except:[] ~timeout:(`After (Time_ns.Span.of_ms 50.)) ()
        with
        | exception exn when not (Common.Timer.is_async exn) ->
            Caml_threads.Thread.delay 0.05;
            loop ()
        | ready when List.is_empty ready.read -> loop ()
        | _ -> (
            match Core_unix.read t.from_copy ~buf ~pos:0 ~len:1 with
            | 1 when Char.equal (Bytes.get buf 0) 'V' ->
                claim_verdict ();
                if Atomic.compare_and_set verdict_given false true then (
                  ignore (Atomic.exchange computing None : t option);
                  log "the copy that took over asks for the verdict; given";
                  quietly (fun () ->
                      ignore
                        (Core_unix.single_write_substring t.to_copy ~buf:"g"
                          : int));
                  let status = Core_unix.waitpid t.pid in
                  Atomic.set t.reaped true;
                  exit_as_copy ~report status)
                else (
                  log "the copy that took over asks for the verdict; refused";
                  (* it is being killed; reap it *)
                  quietly (fun () ->
                      ignore (Core_unix.waitpid t.pid : Core_unix.Exit_or_signal.t));
                  Atomic.set t.reaped true)
            | 1 -> loop ()
            | _ | (exception _) ->
                (* end of file: the copy is exiting; wait_nohang sees it *)
                Caml_threads.Thread.delay 0.05;
                loop ()))
  in
  loop ()

(* in the process: read what the copy said, without blocking; [true] when the
   process must hand over *)
let read_copy t =
  if not (Atomic.get t.state |> function Racing -> true | _ -> false) then false
  else
    match
      Core_unix.select ~restart:true ~read:[ t.from_copy ] ~write:[] ~except:[]
        ~timeout:`Immediately ()
    with
    | exception exn when not (Common.Timer.is_async exn) -> false
    | ready when List.is_empty ready.read -> false
    | _ -> (
        let buf = Bytes.create 1 in
        match Core_unix.read t.from_copy ~buf ~pos:0 ~len:1 with
        | exception exn when not (Common.Timer.is_async exn) -> false
        | 1 when Char.equal (Bytes.get buf 0) 'S' ->
            (* this race first, then the process.  Once the race is claimed
               the main thread's [finish] of it waits; if a copy of another
               race has the process already, this copy is never given the
               right to answer (it dies with the process, which that other
               hand-over exits).  [handed] is never set back, so the main
               thread reading it set always finds a hand-over under way. *)
            Atomic.compare_and_set t.state Racing Copy_won
            && Atomic.compare_and_set handed false true
        | _ ->
            (* 'N' or end of file: the copy found nothing and left *)
            if Atomic.compare_and_set t.state Racing Copy_done then (
              quietly (fun () ->
                  ignore (Core_unix.waitpid t.pid : Core_unix.Exit_or_signal.t));
              Atomic.set t.reaped true;
              Atomic.decr racing);
            false)

(* in the process, with [two_claims]: [read_copy]'s counterpart.  'S' (a
   final answer) claims the race and the computation (already another copy's
   when one continues), and asks for the verdict ([answer_final]); 'C' (a
   point to continue from) claims the race and then the computation, as 'S'
   does with one claim *)
let read_copy_two t =
  if not (Atomic.get t.state |> function Racing -> true | _ -> false) then `Nothing
  else
    match
      Core_unix.select ~restart:true ~read:[ t.from_copy ] ~write:[] ~except:[]
        ~timeout:`Immediately ()
    with
    | exception exn when not (Common.Timer.is_async exn) -> `Nothing
    | ready when List.is_empty ready.read -> `Nothing
    | _ -> (
        let buf = Bytes.create 1 in
        match Core_unix.read t.from_copy ~buf ~pos:0 ~len:1 with
        | exception exn when not (Common.Timer.is_async exn) -> `Nothing
        | 1 when Char.equal (Bytes.get buf 0) 'S' ->
            if Atomic.compare_and_set t.state Racing Copy_won then (
              (* the main thread parks from here on, whoever computes *)
              Atomic.set handed true;
              `Final)
            else `Nothing
        | 1 when Char.equal (Bytes.get buf 0) 'C' ->
            if
              Atomic.compare_and_set t.state Racing Copy_won
              && Atomic.compare_and_set handed false true
            then `Continue
            else `Nothing
        | _ ->
            if Atomic.compare_and_set t.state Racing Copy_done then (
              quietly (fun () ->
                  ignore (Core_unix.waitpid t.pid : Core_unix.Exit_or_signal.t));
              Atomic.set t.reaped true;
              Atomic.decr racing);
            `Nothing)

(* [has_spoken t]: whether the copy of [t] has written to its pipe and the
   process has not read it yet -- an answer ('S', 'C') or that it found
   nothing ('N'), or end of file.  Non-blocking; [false] when the pipe cannot
   be polled. *)
let has_spoken t =
  match
    Core_unix.select ~restart:true ~read:[ t.from_copy ] ~write:[] ~except:[]
      ~timeout:`Immediately ()
  with
  | exception exn when not (Common.Timer.is_async exn) -> false
  | ready -> not (List.is_empty ready.read)

(* [take_announced t]: in the process that started [t], before it kills the
   copy of [t] for a reason other than having its own answer (the copy found
   a duplicate, the process's wait for it ended): when the copy has already
   written to its pipe, wait until the watcher thread has read what it wrote
   and moved the race on -- to [Copy_won], when it was an answer, and the run
   is then the copy's; to [Copy_done], when it was none -- and return [true];
   [false] when the copy had said nothing, or the race is no longer
   [Racing], at the call.
   Why: the watcher reads the pipe once every 50 ms, so a copy's answer can
   sit there unread while the main thread decides to kill the copy; without
   this, a copy was killed 13 ms after it had announced a sound [sat] that was
   the run's only route to an answer, and the process then went on to the end
   of its budget without one.
   Guarantee: when it returns [true] the race has left [Racing], unless the
   watcher has not read a readable pipe within 2 s (it reads within 50 ms of
   being scheduled; the main thread waits without the runtime lock, so the
   watcher can run).  An answer written after this call has looked is not
   seen: the decision the caller makes next is the instant at which an answer
   counts as announced. *)
let take_announced t =
  (match Atomic.get t.state with Racing -> true | _ -> false)
  && has_spoken t
  &&
  let deadline = Common.PhaseTime.now () +. 2. in
  while
    (match Atomic.get t.state with Racing -> true | _ -> false)
    && Float.(Common.PhaseTime.now () < deadline)
  do
    Caml_threads.Thread.delay 0.005
  done;
  true

let spawn_process_watcher ~report ~log t =
  let rec loop () =
    match Atomic.get t.state with
    | Racing when !two_claims -> (
        match read_copy_two t with
        | `Final -> answer_final ~report ~log t
        | `Continue -> continue_copy ~report ~log t
        | `Nothing ->
            Caml_threads.Thread.delay 0.05;
            loop ())
    | Racing ->
        if read_copy t then hand_over ~report ~log t
        else (
          Caml_threads.Thread.delay 0.05;
          loop ())
    | _ -> ()
  in
  ignore
    (Caml_threads.Thread.create
       (fun () ->
         (* the run's timer signals belong to the main thread *)
         Common.Timer.keep_off_this_thread ();
         loop ())
       ()
      : Caml_threads.Thread.t)

(* in the copy: watch the process; on its death kill the copy's group, on 'g'
   count a grant in [go] *)
let spawn_copy_watcher ~parent ~from_process (go : int Atomic.t) =
  let buf = Bytes.create 1 in
  let die () =
    quietly (fun () ->
        Signal_unix.send_i Signal.kill (`Group (Core_unix.getpid ())));
    exit_now 1
  in
  let rec loop () =
    if not (Pid.equal (Core_unix.getppid_exn ()) parent) then die ();
    match
      Core_unix.select ~restart:true ~read:[ from_process ] ~write:[] ~except:[]
        ~timeout:(`After (Time_ns.Span.of_ms 100.))
        ()
    with
    | exception _ -> die ()
    | ready when List.is_empty ready.read -> loop ()
    | _ -> (
        match Core_unix.read from_process ~buf ~pos:0 ~len:1 with
        | 1 ->
            if Char.equal (Bytes.get buf 0) 'g' then Atomic.incr go;
            loop ()
        | _ | (exception _) -> die ())
  in
  ignore
    (Caml_threads.Thread.create
       (fun () ->
         (* the run's timer signals belong to the main thread *)
         Common.Timer.keep_off_this_thread ();
         loop ())
       ()
      : Caml_threads.Thread.t)

(* [lower_priority n]: in a copy just forked, add [n] to its niceness (the
   Unix [nice]), so that on a CPU it shares with processes of lower niceness
   -- the process it races against among them -- the copy gets a smaller share
   (Linux weighs niceness 19 at 15 against 1024 for niceness 0), while a CPU no
   one else wants is still the copy's whole.  Every process the copy forks later (its forked
   questions) inherits the niceness.  Nothing the copy computes depends on its
   niceness, only when it computes it; what can change is an outcome that reads
   the wall clock -- a cooperative deadline or a solver's time budget that
   fires having had less CPU -- and then the copy gives a weaker answer (none,
   for a probe) and never a different one.  [n <= 0] does nothing: a copy is
   never made more urgent than the process.  A failure (the system refusing)
   leaves the copy at the process's niceness. *)
let lower_priority n =
  if n > 0 then quietly (fun () -> ignore (Core_unix.nice n : int))

(* Dropping a copy that computes what the process computes
   ([drop_duplicates], off by default).

   A probe raced here solves a problem built from the input (a re-reading
   with some unknowns defined, say), and after preprocessing that problem can
   be the very problem the process goes on to solve: on a Rust-derived input
   whose unknowns preprocessing eliminates entirely, defining an unknown as
   [true] that the eliminator would have set to [true] anyway leaves both
   sides with the same clauses, and the copy then asks the process's
   questions, one for one, on a second core -- or on the same one, halving
   the process's speed on a loaded machine.  Such a copy can only answer what
   the process answers by the same questions, so dropping it removes no answer
   the process could not give.

   Mechanism.  After preprocessing, the outermost solve of each side calls
   [checkpoint d] once with a digest [d] of the problem it is about to solve.
   The process writes [d] beside each race it has running ([stem].p), the copy
   beside its own race ([stem].c), each through a rename so that the other
   side never reads half a file.  Whichever side writes second finds the other
   side's digest: when every answer the copy can give is an answer of the
   process's problem ([covers_for], in the direction the race's [reads]
   names), the copy leaves silently (as a probe that found nothing does) if
   it is the second, and the process kills and reaps it if the process is.
   Neither side waits for the other.  Only the two sides of a race compare:
   the copy itself until it is given the run (not a process it forks, and
   not afterwards), and the process that started the race (not a process it
   forks).

   Contract.  Only a copy is ever stopped, and a copy that is stopped has
   given no answer -- not even one still unread in its pipe: the process
   kills a copy only when, at its decision, the copy has written nothing
   there ([drop]), so an announced answer is never discarded.  The
   process's answers are those of the sequential order in which the probe
   found nothing, which is one the race can always give.
   So the switch changes no answer the run can give, only whether a second
   process works on the same problem.  A digest collision between different
   problems can only drop a copy that might have answered first; it cannot
   produce an answer.  With [drop_duplicates] off nothing is written or read. *)
module Duplicate = struct
  let drop_duplicates = ref false

  (* in the process: the races started and not yet finished, newest first *)
  let active : t list ref = ref []

  (* in a copy, while it has not been given the run: its race's stem, how
     the copy leaves, the copy's own pid, and what the copy answers with.
     Invariant: [Some (_, _, pid, reads)] only in the process [pid], with
     [reads <> `None], between the fork and the grant of the computation
     ([start] resets it then); [None] everywhere else -- in the process, in
     a process forked from a copy (it inherits the value but not the pid),
     and in a copy that has been handed the run, which is no longer a copy
     that may be dropped but the run itself. *)
  let mine : (string * (unit -> unit) * Pid.t * reads) option ref = ref None

  (* in a copy: the checkpoints ([checkpoint ~at]) at which it has compared
     with the copy's race, each once *)
  let checked : string list ref = ref []

  (* in the process: the stems of the races [checkpoint] has written for,
     each with the checkpoint, compared once per checkpoint, at the first one
     of that name after its start *)
  let written : (string * string) list ref = ref []

  (* Whether the preprocessor also compares at its early checkpoint, after the
     predicate elimination and before the refutation-only passes (the
     unknown-free sweep, the unfolding refutation, the finite instantiation),
     besides the final one after the whole preprocessing.  Those passes return
     the problem they are given unless they refute it, so a copy whose problem
     there is the process's would only ask the process's refutation questions
     again; set from the PCSat configuration ([races.duplicates = Drop_early_and_end]) *)
  let early = ref false

  (* Probe scope.  A probe run in the process's sequential order (a
     re-reading of the input with unknowns defined or relaxed, solved under a
     budget, of whose answers one verdict only is read and everything else
     discarded) solves at depth 1 too, so it passes the checkpoints the
     problem as given passes.  Its problem is not one the process goes on to
     solve to the end: a copy whose problem covers the probe's may well find
     the [sat] that the probe, discarding [sat] or stopped by its budget, never
     returns, and the process then solves the given problem, where nothing
     says it reaches that [sat] in the copy's time.  So a race compares only
     with checkpoints at the probe depth at which it started: the races
     started outside every probe with the problem the process solves as its
     own answer, a race started inside a probe (a copy forked by the probe's
     preprocessing) with that probe's problem, whose answer is the one its
     race's continuation returns.  [enter_probe]/[leave_probe] bracket every
     probe of the caller; the depth is per domain, as the solving is. *)
  let probe_depth_key =
    Domain.DLS.new_key ~split_from_parent:(fun r -> ref !r) (fun () -> ref 0)

  let probe_depth () = !(Domain.DLS.get probe_depth_key)
  let enter_probe () = incr (Domain.DLS.get probe_depth_key)
  let leave_probe () = decr (Domain.DLS.get probe_depth_key)

  (* the number of copies dropped by [checkpoint], on either side; read by the
     tests *)
  let dropped = Atomic.make 0

  let counter = ref 0

  let fresh_stem () =
    incr counter;
    Filename.concat
      (Filename.temp_dir_name)
      (sprintf "coar_race_%d_%d"
         (Core_unix.getpid () |> Pid.to_int)
         !counter)

  (* The comparison files.  Contract: a race's files are named
     [coar_race_<pid>_<n>] in the temporary directory, [pid] being the
     process that started the race ([owner]), followed by one of
     [suffixes]; only [checkpoint] writes them (the process the [.p] ones,
     the copy the [.c] ones), and only while the race is [Racing].  They are
     removed
     - when the race ends in the process: [finish] ([forget]), [drop], and
       a copy leaving as a duplicate;
     - when the process ends without finishing it: every exit of this module
       ([exit_now]: a hand-over, a copy leaving or dying with its process),
       an ordinary exit, through [at_exit], and a termination signal with the phase
       account on ([Common.PhaseTime.at_signal]) remove the files of every
       race the exiting process itself started ([remove_owned]);
     - when nothing could: a process killed outright (SIGKILL, or SIGTERM
       without the phase account) leaves its files, and the first race a
       later process registers removes every file of this scheme whose pid
       no process has ([sweep_dead]).
     Losing a file never changes an answer: a side that reads no file
     compares nothing ([read] gives [None]), so the worst a removal racing
     with a live run can do is keep a copy that would have been dropped. *)
  (* [checkpoint ~at] writes [stem ^ "." ^ side ^ at] through a temporary
     [... ^ ".tmp"] ([write]); [at] is [""] or ["e"], the only
     checkpoint names in use -- a new one must be added here, or its files
     are neither removed nor swept *)
  let suffixes =
    List.concat_map [ ""; "e" ] ~f:(fun at ->
        List.concat_map [ ".p"; ".c" ] ~f:(fun side ->
            [ side ^ at; side ^ at ^ ".tmp" ]))

  let remove_files stem =
    List.iter suffixes ~f:(fun sfx ->
        quietly (fun () -> Core_unix.unlink (stem ^ sfx)))

  (* the files of the races this very process started and has not finished;
     a process forked from it inherits [active] but owns none of them *)
  let remove_owned () =
    let me = Core_unix.getpid () in
    List.iter !active ~f:(fun t ->
        if Pid.equal t.owner me then remove_files t.stem)

  let () = remove_own_files := remove_owned

  (* [pid_of_race_file name]: [Some pid] when [name] is exactly
     [coar_race_<pid>_<n>] followed by one of [suffixes], both numbers
     non-empty runs of decimal digits; [None] for any other name *)
  let pid_of_race_file name =
    let digits s =
      (not (String.is_empty s)) && String.for_all s ~f:Char.is_digit
    in
    match String.chop_prefix name ~prefix:"coar_race_" with
    | None -> None
    | Some rest -> (
        match String.lsplit2 rest ~on:'_' with
        | None -> None
        | Some (pid, tail) ->
            let ok_tail =
              List.exists suffixes ~f:(fun sfx ->
                  match String.chop_suffix tail ~suffix:sfx with
                  | Some n -> digits n
                  | None -> false)
            in
            if digits pid && ok_tail && String.length pid <= 9 then
              Some (Int.of_string pid)
            else None)

  (* [sweep_dead ()]: remove from the temporary directory every file of this
     naming scheme ([pid_of_race_file]) whose pid no process has, by
     [kill(pid, 0)] failing with ESRCH; returns the number removed.  A pid
     that answers, or that the system refuses to say anything of (EPERM),
     keeps its files: a pid reused by a live process keeps a dead run's files
     (left for a later sweep), never the other way round.  One directory
     listing and one signal-0 probe per distinct pid.  The caveat is a
     temporary directory shared across pid namespaces, where a live run's
     pid can look dead here; by the contract above that can only keep a copy
     alive, never change an answer. *)
  let sweep_dead () =
    let dir = Filename.temp_dir_name in
    match Sys_unix.ls_dir dir with
    | exception exn when not (Common.Timer.is_async exn) -> 0
    | names ->
        let dead = Hashtbl.create (module Int) in
        let is_dead pid =
          Hashtbl.find_or_add dead pid ~default:(fun () ->
              pid > 0
              &&
              match Signal_unix.send Signal.zero (`Pid (Pid.of_int pid)) with
              | `No_such_process -> true
              | `Ok -> false
              | exception exn when not (Common.Timer.is_async exn) -> false)
        in
        List.count names ~f:(fun name ->
            match pid_of_race_file name with
            | Some pid when is_dead pid -> (
                match Core_unix.unlink (Filename.concat dir name) with
                | () -> true
                | exception exn when not (Common.Timer.is_async exn) -> false)
            | Some _ | None -> false)

  (* set at the first race registered in a process (and inherited by every
     process forked after it): the exit hooks are installed and the sweep
     has run, once per run *)
  let set_up = ref false

  let register t =
    if !drop_duplicates then (
      if not !set_up then (
        set_up := true;
        at_exit (fun () -> quietly remove_owned);
        Common.PhaseTime.at_signal (fun () -> quietly remove_owned);
        ignore (sweep_dead () : int));
      active := t :: !active)

  let forget t =
    if !drop_duplicates then (
      active := List.filter !active ~f:(fun t' -> not (phys_equal t t'));
      remove_files t.stem)

  (* in the child, right after the fork: the races inherited from the
     process are not the copy's; the copy compares with its own race only,
     and not at all when its race reads [`None] *)
  let in_copy ~stem ~leave ~reads =
    active := [];
    written := [];
    checked := [];
    match reads with
    | (`Sat | `Unsat | `Both) when !drop_duplicates ->
        mine := Some (stem, leave, Core_unix.getpid (), reads)
    | `Sat | `Unsat | `Both | `None -> mine := None

  (* in a copy given the computation: from here it is the run, and the run
     is never dropped -- a copy leaves only while it has given no answer *)
  let handed_the_run () = mine := None

  let write file d =
    quietly (fun () ->
        Out_channel.write_all (file ^ ".tmp") ~data:d;
        Core_unix.rename ~src:(file ^ ".tmp") ~dst:file)

  let read file =
    match In_channel.read_all file with
    | s -> Some s
    | exception exn when not (Common.Timer.is_async exn) -> None

  (* in the process: kill and reap a racing copy found to be a duplicate;
     [true] when it did.  The claim is the same one [finish] and the watcher
     make, so a copy whose answer the watcher has read is left to its
     hand-over; and a copy that has written to its pipe, read or not, is never
     killed here ([take_announced]): its answer, if it was one, is taken, and
     if the watcher has not read it yet the copy is kept (keeping a copy is
     always allowed: it only costs a core).  So a copy dropped here had
     announced nothing when the process decided. *)
  let drop t =
    if take_announced t || has_spoken t then false
    else if Atomic.compare_and_set t.state Racing Copy_done then (
      (* under COAR_COPY_REPORT the copy is first given its grace to report *)
      Common.ForkGuard.term_first ~group:true [ Pid.to_int t.pid ];
      quietly (fun () -> Signal_unix.send_i Signal.kill (`Group t.pid));
      quietly (fun () -> Signal_unix.send_i Signal.kill (`Pid t.pid));
      quietly (fun () ->
          ignore (Core_unix.waitpid t.pid : Core_unix.Exit_or_signal.t));
      Atomic.set t.reaped true;
      Atomic.decr racing;
      Atomic.incr dropped;
      remove_files t.stem;
      true)
    else false

  (* whether [checkpoint] would read its digest: the switch on, not yet
     checked, and a race to compare with *)
  (* A digest is lines: the first stands for everything but the problem's
     constraints (its environments), each later one for one constraint.
     [covers ~copy ~process]: the first lines agree and every constraint of
     the process's problem is one of the copy's -- the copy solves the
     process's problem or one with more constraints over the same unknowns,
     every solution of which solves the process's, so its [sat] is one the
     process reaches by a subset of its questions. *)
  let covers ~copy ~process =
    match (String.split_lines copy, String.split_lines process) with
    | c0 :: cs, p0 :: ps ->
        String.equal c0 p0
        && List.for_all ps ~f:(fun l -> List.mem cs l ~equal:String.equal)
    | _ -> false

  (* [covers_for reads ~copy ~process]: whether a copy that answers with
     [reads] and whose problem has digest [copy] may be dropped beside a
     process whose problem has digest [process] (the same environments
     throughout).  Contract: it holds only when every answer the copy can
     give is an answer of the process's problem:
     - [`Sat]: the copy's constraints include the process's, so every
       solution the copy can return solves the process's problem;
     - [`Unsat]: the process's constraints include the copy's, so a
       refutation of the copy's problem uses only constraints the process
       has, and the process's problem is unsatisfiable too;
     - [`Both]: the two sets are equal, so both of the above hold;
     - [`None]: never.
     What it does not establish is that the process reaches that answer in
     the copy's time: that is the assumption every caller passing [reads]
     other than [`None] makes, and a caller whose copy reaches its answer by
     a procedure the process does not run on its problem passes [`None]. *)
  let covers_for (reads : reads) ~copy ~process =
    match reads with
    | `Sat -> covers ~copy ~process
    | `Unsat -> covers ~copy:process ~process:copy
    | `Both -> covers ~copy ~process && covers ~copy:process ~process:copy
    | `None -> false

  (* the races the process compares with here: started by this very process
     (a process forked from it inherits [active], but its races are not its
     own and it is neither side of them), racing, comparing at all, started
     at this probe depth, and not yet written for at this checkpoint *)
  let pending ~at =
    let depth = probe_depth () in
    let me = Core_unix.getpid () in
    List.filter !active ~f:(fun t ->
        Pid.equal t.owner me
        && (match Atomic.get t.state with Racing -> true | _ -> false)
        && (match t.reads with `None -> false | `Sat | `Unsat | `Both -> true)
        && t.probe_depth = depth
        && not
             (List.mem !written (t.stem, at) ~equal:(fun (a, b) (c, d) ->
                  String.equal a c && String.equal b d)))

  let copy_unchecked ~at = not (List.mem !checked at ~equal:String.equal)

  (* in a copy not yet given the run: its stem, how it leaves and what it
     reads, when this process is that copy itself and has not compared at
     [at]; [None] in a process forked from the copy, which inherits [mine]
     but whose leaving would end the copy's work on the strength of a
     comparison the copy never made *)
  let mine_here ~at =
    match !mine with
    | Some (stem, leave, pid, reads)
      when Pid.equal pid (Core_unix.getpid ()) && copy_unchecked ~at ->
        Some (stem, leave, reads)
    | Some _ | None -> None

  let wanted ~at =
    !drop_duplicates
    && (Option.is_some (mine_here ~at) || not (List.is_empty (pending ~at)))

  (* [at] names the checkpoint ([""], the final one, by default); the two
     sides compare digests written at checkpoints of the same name only *)
  let checkpoint ?(log = fun (_ : string) -> ()) ?(at = "")
      (digest : string Lazy.t) =
    if wanted ~at then (
      let d = Lazy.force digest in
      (match mine_here ~at with
      | Some (stem, leave, reads) -> (
          checked := at :: !checked;
          write (stem ^ ".c" ^ at) d;
          match read (stem ^ ".p" ^ at) with
          | Some d' when covers_for reads ~copy:d ~process:d' ->
              Atomic.incr dropped;
              remove_files stem;
              leave ()
          | _ -> ())
      | None -> ());
      List.iter (pending ~at) ~f:(fun t ->
          written := (t.stem, at) :: !written;
          match Atomic.get t.state with
          | Racing -> (
              write (t.stem ^ ".p" ^ at) d;
              match read (t.stem ^ ".c" ^ at) with
              | Some d' when covers_for t.reads ~copy:d' ~process:d ->
                  let where = if String.is_empty at then "" else " (at " ^ at ^ ")" in
                  if drop t then (
                    log ("a raced copy solves the same problem; dropped" ^ where);
                    t.log ("the copy solves the process's problem; dropped" ^ where))
                  else (
                    (* the copy had spoken before the process decided: its
                       answer, if it was one, is the run's *)
                    Common.PhaseTime.event_here "race-duplicate-kept/copy-spoke";
                    t.log
                      ("the copy solves the process's problem but had already \
                        spoken; not dropped" ^ where))
              | _ -> ())
          | Process_won | Copy_won | Copy_done -> ()))
end

(* The memory a race may take.  [start] forks only when the copy fits the
   memory budget shared by every copy of the run alive at once
   ([Common.ForkGuard.fits]): the copy's duplicate heap plus [growth], beside
   what the copies already racing (or asking questions) may still add.  The
   copy of a race may be handed the whole run, beside a parked process that
   keeps its own memory, so [growth] is by default the excess of the
   process's own peak heap over its current one
   ([Common.ForkGuard.peak_excess_bytes]): such a copy may need again what the
   process once needed.  A race that does not fit is [`Not_started], which
   every caller already handles by running the raced computation in its
   sequential place (or, where the caller says so, not at all); the refusal
   is logged through [log] and counted ([Common.ForkGuard.refused]).  This
   changes when a raced computation runs, never which answers the race can
   give: a race's possible answers are those of the sequential order.
   [reads] (default [`Sat]) says which verdict the copy answers with, and so
   in which direction [Duplicate] may drop it (see [reads] and
   [Duplicate.covers_for]); a caller whose copy's answer is not an answer of
   the process's problem by an inclusion of constraints passes [`None]. *)
let start
    ?(report = fun () -> Common.PhaseTime.report ~reason:"copy-answered")
    ?(log = fun (_ : string) -> ()) ?(nice = 0) ?settle_by
    ?growth ?(final = fun (_ : 'a) -> true) ?(reads = (`Sat : reads))
    (f : unit -> 'a option) :
    [ `Racing of t | `Won of 'a | `Not_started ] =
  Stdlib.flush_all ();
  let growth =
    match growth with
    | Some g -> g
    | None -> Common.ForkGuard.peak_excess_bytes ()
  in
  if not (Common.ForkGuard.fits ~growth ()) then (
    Atomic.incr Common.ForkGuard.refused;
    Common.PhaseTime.event_here "race-refused/memory";
    log "not started: the copy does not fit the memory budget";
    `Not_started)
  else
  match (Core_unix.pipe (), Core_unix.pipe ()) with
  | exception exn when not (Common.Timer.is_async exn) -> `Not_started
  | (c_rd, c_wr), (p_rd, p_wr) -> (
      let close_all () =
        List.iter [ c_rd; c_wr; p_rd; p_wr ] ~f:(fun fd ->
            quietly (fun () -> Core_unix.close fd))
      in
      let parent = Core_unix.getpid () in
      let stem = Duplicate.fresh_stem () in
      let bytes = Common.ForkGuard.copy_need ~growth () in
      match
        Common.PhaseTime.around_fork (Common.ForkGuard.fork_reserving ~bytes)
      with
      | exception exn when not (Common.Timer.is_async exn) ->
          close_all ();
          `Not_started
      | `In_the_child ->
          (* the claims of the process are not the copy's *)
          Atomic.set started_races [];
          Atomic.set verdict_given false;
          Atomic.set computing None;
          pending_verdict := None;
          Core_unix.close c_rd;
          Core_unix.close p_wr;
          (* a group of its own, so that [finish] can kill the copy together
             with the forked questions it asks *)
          quietly (fun () ->
              let me = Core_unix.getpid () in
              Core_unix.setpgid ~of_:me ~to_:me);
          lower_priority nice;
          (* under COAR_PHASE_OPEN_DIR, where the copy is, written once a
             second, for a copy killed without a chance to report *)
          Common.PhaseTime.track_in_copy ();
          let go = Atomic.make 0 in
          spawn_copy_watcher ~parent ~from_process:p_rd go;
          let say c =
            ignore (Core_unix.single_write_substring c_wr ~buf:c : int)
          in
          (* the copy compares with this race's process only, and once *)
          Duplicate.in_copy ~stem ~reads
            ~leave:(fun () ->
              log "the copy is a duplicate of the process; it leaves";
              ForkedQuery.kill_live ();
              quietly (fun () -> say "N");
              exit_now 0);
          (* every exception ends the copy: one that escaped would run the
             process's continuation in the copy without an answer *)
          let answer = try f () with _ -> None in
          log
            (if Option.is_some answer then "the copy has an answer"
             else "the copy has none");
          (match answer with
          | None ->
              quietly (fun () -> say "N");
              exit_now 0
          | Some v -> (
              let letter = if !two_claims && not (final v) then "C" else "S" in
              try say letter
              with _ (* catch-all-ok: the copy ends here whatever failed *) ->
                exit_now 1));
          while Atomic.get go < 1 do
            Caml_threads.Thread.delay 0.01
          done;
          (* given the computation, the copy is the run: a later checkpoint
             (the rest of the preprocessing after a raced pass, a later solve)
             must not find it a duplicate of a process that has parked, or the
             run would end with neither side answering *)
          Duplicate.handed_the_run ();
          (* given the computation only: the verdict is asked for later *)
          (match answer with
          | Some v when !two_claims && not (final v) ->
              pending_verdict := Some (c_wr, go)
          | _ -> ());
          (* the copy is now the run: it answers and leaves through the
             ordinary exit path, within what is left of the caller's budget
             (see "The caller's budget" above) *)
          Common.Timer.resume_budget_in_copy ();
          (* with the process's phase account on, the copy's own account
             takes over from here: it reports the copy's phases at its exit
             or on a termination signal, labelled as the copy's *)
          Common.PhaseTime.resume_in_copy ();
          `Won (Option.value_exn answer)
      | `In_the_parent pid ->
          Core_unix.close c_wr;
          Core_unix.close p_rd;
          let t =
            {
              pid;
              from_copy = c_rd;
              to_copy = p_wr;
              state = Atomic.make Racing;
              reaped = Atomic.make false;
              stem;
              log;
              owner = parent;
              probe_depth = Duplicate.probe_depth ();
              reads;
              settle_by;
            }
          in
          Duplicate.register t;
          if Common.ForkGuard.copy_report then
            Atomic.set started_races (t :: Atomic.get started_races);
          Atomic.incr racing;
          Atomic.incr started;
          spawn_process_watcher ~report ~log t;
          `Racing t)

(* [park_if_handed ()]: called by the process's main thread at its own safe
   points; after any race of the process was handed over it never returns, so
   the process stops computing while the copy runs the rest of the program
   (the watcher thread, waiting for the copy, exits the process).  The same
   check is made on entering and leaving every phase and before every solver
   check ([Common.ForkGuard.park_if_handed]). *)
let park_if_handed = Common.ForkGuard.park_if_handed

(* [park_if_lost t]: [park_if_handed], also when this race was claimed by its
   copy ([Copy_won] is set only on the way to [handed] being true, so the
   two tests agree but for an instant; this one also parks a caller outside
   the main thread, which [park_if_handed] leaves running) *)
let park_if_lost t =
  match Atomic.get t.state with
  | Copy_won -> wait_forever ()
  | (Racing | Process_won | Copy_done) when Atomic.get handed ->
      wait_forever ()
  | Racing | Process_won | Copy_done -> ()

(* [wait_settled t ~ms]: in the process, wait until the copy of [t] has said
   what it found or [ms] milliseconds have passed, whichever is first, and
   return.  It decides nothing itself: a copy that answers within the wait is
   handed the run by the watcher thread, and the caller's [finish] then never
   returns; a copy that found nothing has left; a copy still at work is killed
   by the caller's [finish].  For a caller whose own computation has given up
   (a solver's budget spent) while a copy with the same budget, started a
   moment later, may still be about to answer. *)
let wait_settled t ~ms =
  let deadline = Common.PhaseTime.now () +. (Float.of_int ms /. 1000.) in
  while
    (match Atomic.get t.state with Racing -> true | _ -> false)
    && Float.(Common.PhaseTime.now () < deadline)
  do
    Caml_threads.Thread.delay 0.02
  done

(* [finish t]: the process keeps its own answer, killing and reaping the copy;
   after a lost race -- this one or another of the process's -- it never
   returns *)
let finish t =
  Duplicate.forget t;
  if !two_claims && not (Pid.equal t.owner (Core_unix.getpid ())) then (
    (* a race inherited at a fork: its copy is a sibling, which its parent
       may have given the verdict; it is not this copy's to kill *)
    quietly (fun () -> Core_unix.close t.from_copy);
    quietly (fun () -> Core_unix.close t.to_copy))
  else if Atomic.compare_and_set t.state Racing Process_won then (
    (* under COAR_COPY_REPORT the copy is first given its grace to report *)
    Common.ForkGuard.term_first ~group:true [ Pid.to_int t.pid ];
    quietly (fun () -> Signal_unix.send_i Signal.kill (`Group t.pid));
    quietly (fun () -> Signal_unix.send_i Signal.kill (`Pid t.pid));
    quietly (fun () ->
        ignore (Core_unix.waitpid t.pid : Core_unix.Exit_or_signal.t));
    Atomic.set t.reaped true;
    Atomic.decr racing;
    (* another race of this process was handed over to its copy *)
    if Atomic.get handed then wait_forever ())
  else
    match Atomic.get t.state with
    | Copy_won ->
        (* the watcher is waiting for the copy and exits the process *)
        wait_forever ()
    | Racing | Process_won | Copy_done ->
        quietly (fun () -> Core_unix.close t.from_copy);
        quietly (fun () -> Core_unix.close t.to_copy);
        if Atomic.get handed then wait_forever ()

(* [settle_then_finish ~verdict t]: [finish t], after waiting for the copy
   ([wait_settled]) until [t.settle_by] when [verdict] is false.
   For the caller whose race stands for a refutation-only computation that the
   sequential order would have run to the end before giving its own answer:
   - [verdict] true (the process answered [sat] or [unsat]): finished at once.
     A sound [sat] says there was no refutation for the copy to find; an
     [unsat] is the verdict the copy's refutation would give.
   - [verdict] false (an [unknown], an error, an exception): the copy is given
     until [settle_by], which the caller sets to where its own budget for the
     computation ends, so a refutation the sequential order would have found
     within that budget is still handed the run, and printed.
   The wait never outlasts the armed budget ([Common.Timer.remaining_budget]):
   a process that has spent it (a [Timeout] raised, or answered as one) does
   not wait, since a copy that has not answered by then refutes, if at all,
   later than the sequential order could have printed within that budget; and
   an alarm that arrives during the wait ends it, as it would have ended the
   computation in its sequential place.  With [verdict] false, an answer the
   copy has written to its pipe by the end of the wait is taken before the
   kill ([take_announced]), whatever the watcher's poll.  Guarantees:
   no copy outlives the call in the process; after a copy answered, the call
   never returns (as [finish]). *)
let settle_then_finish ~verdict t =
  Common.Timer.protect ~finally:(fun () -> finish t) @@ fun () ->
  match t.settle_by with
  | Some d when (not verdict) && Pid.equal t.owner (Core_unix.getpid ()) ->
      (* only the process that started the race waits: a copy forked later
         inherits the record but not the watcher that moves its state, so it
         would wait out the whole time for nothing *)
      let left = d -. Common.PhaseTime.now () in
      let left =
        match Common.Timer.remaining_budget () with
        | Some b -> Float.min left b
        | None -> left
      in
      let ms = Float.iround_up_exn (Float.max 0. left *. 1000.) in
      if ms > 0 then (
        t.log (sprintf "the process has no verdict; waiting up to %d ms" ms);
        wait_settled t ~ms);
      (* an answer the copy announced by now is taken, not killed unread *)
      ignore (take_announced t : bool)
  | _ when (not verdict) && Pid.equal t.owner (Core_unix.getpid ()) ->
      ignore (take_announced t : bool)
  | _ -> ()

(* [decide_in_copy ?log ~ms ~decisive f] computes [f ()] in a forked copy and
   waits for it at most [ms] milliseconds, for a caller whose own [f ()] might
   not return within any budget it sets (a solver call that ignores its
   cancel flag), and whose decisive value cannot be sent back ([Marshal] does
   not carry extensible variants, see the header).
   - [`Decided v], returned IN THE COPY: [f ()] gave [v] with [decisive v]
     there, the copy was given the run, and it continues from this call as
     the process would have continued from [f ()] returning [v]; the process
     exits with the copy's status (see the contract of [start]).
   - [`Undecided `Answered], returned in the process: the copy's [f ()] was
     not decisive, or raised, within [ms] milliseconds;
     [`Undecided `Killed]: the copy had not answered within [ms]
     milliseconds and was killed and reaped.  An answer the copy has written
     to its pipe by the deadline is taken ([take_announced]), not killed
     unread; one written after the process has looked is killed.
   - [`Not_started]: no copy was made (a domain running, the memory budget,
     a failed fork); [f] has run nowhere, and the caller may run it here.
   Contract: [`Decided v] carries only a value [f ()] computed with
   [decisive v]; the process never returns past this call once its copy has
   been given the run; no copy outlives the call in the process (the kill
   runs on every exit, a timeout of the caller's own included, through
   [Common.Timer.protect]).  So a caller that reads every non-decisive value
   of [f] as undecided gets from this call the answers of [f ()] itself,
   bounded in time, and loses only answers [f ()] would have given after
   [ms]. *)
let decide_in_copy ?log ~ms ~decisive f =
  match
    start ?log (fun () ->
        let v = f () in
        if decisive v then Some v else None)
  with
  | `Won v -> `Decided v
  | `Not_started -> `Not_started
  | `Racing t ->
      Common.Timer.protect
        ~finally:(fun () -> finish t)
        (fun () ->
          wait_settled t ~ms;
          ignore (take_announced t : bool);
          (* read before [finish], which sets [Process_won] on a copy still
             racing; a copy that has answered is [Copy_done] (nothing) or
             [Copy_won] (then [finish] never returns) *)
          match Atomic.get t.state with
          | Copy_done -> `Undecided `Answered
          | Racing | Process_won | Copy_won -> `Undecided `Killed)
