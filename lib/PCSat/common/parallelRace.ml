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
     report follows the copy's, never interleaved with it.  With the account
     off nothing of this happens.

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

   What it relies on: the process has one running domain (as [ForkedQuery]
   does); the watcher is a system thread, which runs while the main thread is
   inside a solver call because the Z3 bindings release the runtime lock
   there; output buffered before the fork is flushed first so that it is not
   written twice. *)

type state = Racing | Process_won | Copy_won | Copy_done

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
           with _ -> Core_unix.exit_immediately 1);
          while Atomic.get grants < 2 do
            Caml_threads.Thread.delay 0.01
          done;
          pending_verdict := None)

let () = Common.ForkGuard.verdict_hook := claim_verdict

(* in the process, after the run was given to a copy that has now exited
   with [status]: kill this process's own forked questions, flush, report
   and exit with the copy's status *)
let exit_as_copy ~report status =
  ForkedQuery.kill_live ();
  (try Stdlib.flush_all () with _ -> ());
  report ();
  Core_unix.exit_immediately (exit_status_code status)

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
  (try Stdlib.flush_all () with _ -> ());
  report ();
  Core_unix.exit_immediately (exit_status_code status)

(* in the process, with [two_claims]: the copy of [t] (holding the
   computation only) is superseded by a copy given the verdict; kill it and
   its group.  Its watcher, seeing it exit, reaps it and finds the verdict
   given. *)
let kill_superseded t =
  t.log "a copy with a final answer is given the verdict; the copy that took over is killed";
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
  ignore (Caml_threads.Thread.create loop () : Caml_threads.Thread.t)

(* in the copy: watch the process; on its death kill the copy's group, on 'g'
   count a grant in [go] *)
let spawn_copy_watcher ~parent ~from_process (go : int Atomic.t) =
  let buf = Bytes.create 1 in
  let die () =
    quietly (fun () ->
        Signal_unix.send_i Signal.kill (`Group (Core_unix.getpid ())));
    Core_unix.exit_immediately 1
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
  ignore (Caml_threads.Thread.create loop () : Caml_threads.Thread.t)

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
   side's digest: when the copy's covers the process's, the copy leaves silently (as a probe
   that found nothing does) if it is the second, and the process kills and
   reaps it if the process is.  Neither side waits for the other.

   Contract.  Only a copy is ever stopped, and a copy that is stopped has
   given no answer: the process's answers are those of the sequential order
   in which the probe found nothing, which is one the race can always give.
   So the switch changes no answer the run can give, only whether a second
   process works on the same problem.  A digest collision between different
   problems can only drop a copy that might have answered first; it cannot
   produce an answer.  With [drop_duplicates] off nothing is written or read. *)
module Duplicate = struct
  let drop_duplicates = ref false

  (* in the process: the races started and not yet finished, newest first *)
  let active : t list ref = ref []

  (* in a copy: its race's stem, and how the copy leaves *)
  let mine : (string * (unit -> unit)) option ref = ref None

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
     again; set from the PCSat configuration ([race_drop_duplicates_early]) *)
  let early = ref false

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

  let register t = if !drop_duplicates then active := t :: !active

  let remove_files stem =
    List.iter [ ""; "e" ] ~f:(fun at ->
        List.iter [ ".p"; ".c"; ".p.tmp"; ".c.tmp" ] ~f:(fun ext ->
            quietly (fun () -> Core_unix.unlink (stem ^ ext ^ at))))

  let forget t =
    if !drop_duplicates then (
      active := List.filter !active ~f:(fun t' -> not (phys_equal t t'));
      remove_files t.stem)

  (* in the child, right after the fork: the races inherited from the
     process are not the copy's; the copy compares with its own race only *)
  let in_copy ~stem ~leave =
    active := [];
    written := [];
    checked := [];
    if !drop_duplicates then mine := Some (stem, leave) else mine := None

  let write file d =
    quietly (fun () ->
        Out_channel.write_all (file ^ ".tmp") ~data:d;
        Core_unix.rename ~src:(file ^ ".tmp") ~dst:file)

  let read file =
    match In_channel.read_all file with
    | s -> Some s
    | exception exn when not (Common.Timer.is_async exn) -> None

  (* in the process: kill and reap a racing copy found to be a duplicate.
     The claim is the same one [finish] and the watcher make, so a copy that
     has just answered is left to its hand-over. *)
  let drop t =
    if Atomic.compare_and_set t.state Racing Copy_done then (
      quietly (fun () -> Signal_unix.send_i Signal.kill (`Group t.pid));
      quietly (fun () -> Signal_unix.send_i Signal.kill (`Pid t.pid));
      quietly (fun () ->
          ignore (Core_unix.waitpid t.pid : Core_unix.Exit_or_signal.t));
      Atomic.set t.reaped true;
      Atomic.decr racing;
      Atomic.incr dropped;
      remove_files t.stem)

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

  let pending ~at =
    List.filter !active ~f:(fun t ->
        (match Atomic.get t.state with Racing -> true | _ -> false)
        && not
             (List.mem !written (t.stem, at) ~equal:(fun (a, b) (c, d) ->
                  String.equal a c && String.equal b d)))

  let copy_unchecked ~at = not (List.mem !checked at ~equal:String.equal)

  let wanted ~at =
    !drop_duplicates
    && ((Option.is_some !mine && copy_unchecked ~at)
       || not (List.is_empty (pending ~at)))

  (* [at] names the checkpoint ([""], the final one, by default); the two
     sides compare digests written at checkpoints of the same name only *)
  let checkpoint ?(log = fun (_ : string) -> ()) ?(at = "")
      (digest : string Lazy.t) =
    if wanted ~at then (
      let d = Lazy.force digest in
      (match !mine with
      | Some (stem, leave) when copy_unchecked ~at -> (
          checked := at :: !checked;
          write (stem ^ ".c" ^ at) d;
          match read (stem ^ ".p" ^ at) with
          | Some d' when covers ~copy:d ~process:d' ->
              Atomic.incr dropped;
              remove_files stem;
              leave ()
          | _ -> ())
      | _ -> ());
      List.iter (pending ~at) ~f:(fun t ->
          written := (t.stem, at) :: !written;
          match Atomic.get t.state with
          | Racing -> (
              write (t.stem ^ ".p" ^ at) d;
              match read (t.stem ^ ".c" ^ at) with
              | Some d' when covers ~copy:d' ~process:d ->
                  let where = if String.is_empty at then "" else " (at " ^ at ^ ")" in
                  log ("a raced copy solves the same problem; dropped" ^ where);
                  t.log ("the copy solves the process's problem; dropped" ^ where);
                  drop t
              | _ -> ())
          | Process_won | Copy_won | Copy_done -> ()))
end

let start ?(report = fun () -> ()) ?(log = fun (_ : string) -> ()) ?(nice = 0)
    ?(final = fun (_ : 'a) -> true) (f : unit -> 'a option) :
    [ `Racing of t | `Won of 'a | `Not_started ] =
  Stdlib.flush_all ();
  match (Core_unix.pipe (), Core_unix.pipe ()) with
  | exception exn when not (Common.Timer.is_async exn) -> `Not_started
  | (c_rd, c_wr), (p_rd, p_wr) -> (
      let close_all () =
        List.iter [ c_rd; c_wr; p_rd; p_wr ] ~f:(fun fd ->
            quietly (fun () -> Core_unix.close fd))
      in
      let parent = Core_unix.getpid () in
      let stem = Duplicate.fresh_stem () in
      match Common.PhaseTime.around_fork Common.ForkGuard.fork with
      | exception exn when not (Common.Timer.is_async exn) ->
          close_all ();
          `Not_started
      | `In_the_child ->
          (* the claims of the process are not the copy's *)
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
          let go = Atomic.make 0 in
          spawn_copy_watcher ~parent ~from_process:p_rd go;
          let say c =
            ignore (Core_unix.single_write_substring c_wr ~buf:c : int)
          in
          (* the copy compares with this race's process only, and once *)
          Duplicate.in_copy ~stem
            ~leave:(fun () ->
              log "the copy is a duplicate of the process; it leaves";
              ForkedQuery.kill_live ();
              quietly (fun () -> say "N");
              Core_unix.exit_immediately 0);
          (* every exception ends the copy: one that escaped would run the
             process's continuation in the copy without an answer *)
          let answer = try f () with _ -> None in
          log
            (if Option.is_some answer then "the copy has an answer"
             else "the copy has none");
          (match answer with
          | None ->
              quietly (fun () -> say "N");
              Core_unix.exit_immediately 0
          | Some v -> (
              let letter = if !two_claims && not (final v) then "C" else "S" in
              try say letter with _ -> Core_unix.exit_immediately 1));
          while Atomic.get go < 1 do
            Caml_threads.Thread.delay 0.01
          done;
          (* given the computation only: the verdict is asked for later *)
          (match answer with
          | Some v when !two_claims && not (final v) ->
              pending_verdict := Some (c_wr, go)
          | _ -> ());
          (* the copy is now the run: it answers and leaves through the
             ordinary exit path *)
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
            }
          in
          Duplicate.register t;
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
