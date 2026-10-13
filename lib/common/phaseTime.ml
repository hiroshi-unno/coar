(* A wall-clock account of where a run spends its time, by phase.

   Off by default and then free: every entry point first reads one boolean.
   When on ([enable]), a phase is a named interval of wall time; phases nest,
   and the account is keyed by the PATH of the phases open on the calling
   domain ("preprocess/elim/valid"), so a parent's time includes its children's
   and two phases with one parent never overlap on one domain.  Hence, for a
   run on one domain, the top-level entries (paths without a '/') are disjoint
   intervals and their sum is at most the wall clock; a run whose phases ran on
   several domains reports how many, and its top-level sum can exceed it.

   The report is one line per path on stderr, printed once: at exit, or when
   the process receives SIGTERM or SIGINT (what `timeout` sends).  A run killed
   at its budget is usually inside a solver call that does not return to OCaml
   for a long time, and OCaml runs a signal handler only at a safe point; so
   [enable] starts a small watcher thread that sleeps in short steps (each
   wake-up is a safe point while the main thread is inside a call that
   released the runtime lock, as a Z3 check does), and the handler itself only
   sets a flag the watcher reads.  The phases still
   open at that moment are charged up to the moment of the report and marked
   [open].  After a signal the process exits with status 128 + signal, without
   running other exit handlers, which might wait on the domain that is stuck.
   A fork goes through [around_fork], which leaves the account off in the
   child.  The parent's account sees a forked computation only as the time it
   waits for it; so a copy of a process whose account is on totals its own
   solver checks, and [child_line] prints that total and the copy's wall time
   as one [phase-time-child:] line on stderr, which is how a run whose
   questions go to forked copies tells their solver time from the rest.
   A forked copy that is given the rest of the run (a raced copy that won)
   turns its account back on with [resume_in_copy]: it then reports its own
   phases from the fork, every line labelled [phase-time-copy:] in place of
   [phase-time:], at its exit or on SIGTERM; the process that handed over
   waits for that report before printing its own ([at_signal] on a signal),
   so the two never interleave and together cover the run.

   Contract: [with_phase name f] returns what [f ()] returns and raises what it
   raises; nothing here changes a computation's result. *)

let on = ref false

(* The clock of the account: CLOCK_MONOTONIC, in seconds from an arbitrary
   origin.  Not the time of day: where the system's time of day is stepped by a
   synchronisation with a host (observed in a virtual machine whose own clock
   ran about 10% slow, the time of day stepped forward by about 3 s every 35 s),
   a duration taken from it charges each step to whichever phase is open, and
   a report's [wall] exceeds a `timeout` limit by the steps, `timeout` counting
   on the monotonic clock.  On this clock the wall time of a run killed at its
   limit is that limit (less its start-up). *)
external now : unit -> (float[@unboxed])
  = "coar_monotonic_seconds" "coar_monotonic_seconds_unboxed"
[@@noalloc]

let t0 = now ()

(* [start] is mutable only so that a forked copy that takes over the run can
   move the frames it inherited to the moment of the fork ([resume_in_copy]);
   a frame is otherwise never changed, and is told apart by its identity *)
type frame = { path : string; mutable start : float }

(* the open phases of one domain, innermost first; written only by that domain,
   read (racily, which can only make the report one frame stale) by the
   reporter *)
type stack = frame list ref

let stacks : stack list Atomic.t = Atomic.make []

let stack_key : stack Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () ->
      let s = ref [] in
      let rec register () =
        let old = Atomic.get stacks in
        if not (Atomic.compare_and_set stacks old (s :: old)) then register ()
      in
      register ();
      s)

type acc = { mutable total : float; mutable count : int }

let table : (string, acc) Stdlib.Hashtbl.t = Stdlib.Hashtbl.create 64
let mutex = Stdlib.Mutex.create ()

let add path secs =
  Stdlib.Mutex.lock mutex;
  (match Stdlib.Hashtbl.find_opt table path with
  | Some a ->
      a.total <- a.total +. secs;
      a.count <- a.count + 1
  | None -> Stdlib.Hashtbl.replace table path { total = secs; count = 1 });
  Stdlib.Mutex.unlock mutex

type token = (stack * frame) option

let start name : token =
  if not !on then None
  else
    let s = Stdlib.Domain.DLS.get stack_key in
    let path = match !s with [] -> name | f :: _ -> f.path ^ "/" ^ name in
    let fr = { path; start = now () } in
    s := fr :: !s;
    Some (s, fr)

(* the innermost open phase of the calling domain, "" when none is open or
   the account is off; for diagnostics that tag what they log with where it
   was asked *)
let current_path () =
  if not !on then ""
  else
    match !(Stdlib.Domain.DLS.get stack_key) with
    | [] -> ""
    | f :: _ -> f.path

(* removes exactly this frame, so a stop out of order (a stage switched while a
   phase opened after it was left open by an exception) cannot pop another
   phase's frame *)
let stop (tok : token) =
  match tok with
  | None -> ()
  | Some (s, fr) ->
      if List.memq fr !s then (
        s := List.filter (fun f -> f != fr) !s;
        add fr.path (now () -. fr.start))

(* [stop] for [tok] and every frame opened after it on this domain and still
   open: what a phase left open when an exception went through it *)
let stop_through (tok : token) =
  match tok with
  | None -> ()
  | Some (s, fr) ->
      if List.memq fr !s then
        let now = now () in
        let rec go = function
          | [] -> []
          | f :: rest ->
              add f.path (now -. f.start);
              if f == fr then rest else go rest
        in
        s := go !s

(* Entering and leaving a phase are also the main thread's safe points for
   stopping after the run was handed to a forked copy
   ([ForkGuard.park_if_handed]), with the account on or off: a phase is never
   opened inside an output operation or the account's own critical section,
   and a solver check is a phase ([z3]), so a main thread that goes on working
   after a hand-over stops at its next phase or solver check.  Off a
   hand-over this is one atomic read. *)
let with_phase name f =
  ForkGuard.park_if_handed ();
  if not !on then (
    let v = f () in
    ForkGuard.park_if_handed ();
    v)
  else
    let tok = start name in
    match f () with
    | v ->
        stop_through tok;
        ForkGuard.park_if_handed ();
        v
    | exception e ->
        let bt = Printexc.get_raw_backtrace () in
        stop_through tok;
        Printexc.raise_with_backtrace e bt

(* A sequence of stages inside one phase: [next name] closes the previous
   stage and opens [name]; [finish] closes the last.  A stage left open by an
   exception is closed by the enclosing [with_phase]. *)
let stages () =
  let cur = ref None in
  let next name =
    if !on then (
      stop !cur;
      cur := start name)
  in
  let finish () =
    stop !cur;
    cur := None
  in
  (next, finish)

(* [true] in a forked copy of a process whose account was on (see
   [around_fork]); the copy then keeps only the total time of its solver
   checks, in [child_z3], for [child_line] *)
let in_child = ref false
let child_z3 = ref 0.
let child_z3_n = ref 0

(* the moment of the fork, in a copy (see [around_fork]) *)
let fork_time = ref t0

(* what the report is about: the whole process ("phase-time", from [t0]), or,
   in a copy that took over the run, the copy from its fork
   ("phase-time-copy", from [fork_time]; see [resume_in_copy]) *)
let label = ref "phase-time"
let origin = ref t0

(* the time of a solver's check call, under the enclosing phase's path as
   ".../z3" *)
let z3 f =
  if !in_child then (
    let t = now () in
    Fun.protect
      ~finally:(fun () ->
        child_z3 := !child_z3 +. (now () -. t);
        incr child_z3_n)
      f)
  else with_phase "z3" f

(* In a forked copy of a process whose account was on, one line on stderr:
   the wall time since [started] and the part of it spent in solver checks.
   Nothing anywhere else. *)
let child_line ~started =
  if !in_child then (
    prerr_string
      (Printf.sprintf "phase-time-child: wall=%.3f z3=%.3f\n"
         (now () -. started)
         !child_z3);
    flush stderr)

(* An event with no duration, counted under [name]: a row of the report
   ([add name 0.], so its count is the number of events) when the account is
   on; in a forked copy of a process whose account was on, where nothing is
   accounted, one line [phase-time-child-event: name] on stderr at once, so
   that an event inside a copy (a probe's nested solve) is not invisible.
   Nothing otherwise. *)
let event name =
  if !on then add name 0.
  else if !in_child then (
    prerr_string (Printf.sprintf "phase-time-child-event: %s\n" name);
    flush stderr)

(* [event] counted under the innermost phase open on this domain, as the row
   [<path>/<name>], so that one event raised from many places is told apart by
   where it was raised.  In a forked copy of a process whose account was on,
   the path is that of the innermost phase open at the fork (no phase is opened
   in a copy), and the line is printed only when [in_copy] holds, so that a
   frequent event can be counted in the process without flooding a copy's
   stderr. *)
let event_here ?(in_copy = true) name =
  if !on || (!in_child && in_copy) then
    let path =
      match !(Stdlib.Domain.DLS.get stack_key) with
      | [] -> name
      | f :: _ -> f.path ^ "/" ^ name
    in
    if !on then add path 0.
    else (
      prerr_string (Printf.sprintf "phase-time-child-event: %s\n" path);
      flush stderr)

let reported = Atomic.make false

let is_z3 path =
  path = "z3"
  ||
  let n = String.length path in
  n > 3 && String.sub path (n - 3) 3 = "/z3"

let term_signal = Atomic.make 0

(* when the OCaml handler of the first termination signal ran (0. before
   one): the report prints it, from its origin, as [signal=], so that a report
   that lands late after its run's wall-clock limit tells a handler that ran
   late (the main thread was held where OCaml does not run a handler) from a
   report that was slow to make *)
let term_time = Atomic.make 0.

(* phase names whose totals over all paths the report adds as their own
   lines: the solver contexts made, the forced collections before them, and
   the leases of a clean pooled context *)
let summed = [ "new-context"; "gc-full-major"; "clean-pool-lease" ]

let report ~reason =
  (* a report made while a termination signal is being handled says so,
     whichever thread makes it *)
  let reason =
    match Atomic.get term_signal with
    | 0 -> reason
    | n -> if n = Stdlib.Sys.sigint then "sigint" else "sigterm"
  in
  if !on && Atomic.compare_and_set reported false true then (
    let now = now () in
    Stdlib.Mutex.lock mutex;
    let rows = Stdlib.Hashtbl.create 64 in
    Stdlib.Hashtbl.iter
      (fun k a -> Stdlib.Hashtbl.replace rows k (a.total, a.count, 0))
      table;
    let domains = List.length (Atomic.get stacks) in
    List.iter
      (fun s ->
        List.iter
          (fun f ->
            let t, c, o =
              Option.value
                (Stdlib.Hashtbl.find_opt rows f.path)
                ~default:(0., 0, 0)
            in
            Stdlib.Hashtbl.replace rows f.path (t +. (now -. f.start), c, o + 1))
          !s)
      (Atomic.get stacks);
    Stdlib.Mutex.unlock mutex;
    let rows =
      List.sort compare
      @@ Stdlib.Hashtbl.fold (fun k v acc -> (k, v) :: acc) rows []
    in
    let wall = now -. !origin in
    let top =
      List.fold_left
        (fun acc (k, (t, _, _)) -> if String.contains k '/' then acc else acc +. t)
        0. rows
    in
    let z3t, z3n =
      List.fold_left
        (fun (t', n') (k, (t, n, _)) ->
          if is_z3 k then (t' +. t, n' + n) else (t', n'))
        (0., 0) rows
    in
    let b = Buffer.create 1024 in
    let lbl = !label in
    Printf.bprintf b
      "%s: reason=%s%s wall=%.3f top-level=%.3f unaccounted=%.3f z3=%.3f \
       z3-checks=%d ocaml=%.3f domains=%d%s\n"
      lbl reason
      (if !origin = t0 then ""
       else Printf.sprintf " from=%.3f" (!origin -. t0))
      wall top (wall -. top) z3t z3n (wall -. z3t) domains
      (match Atomic.get term_time with
      | 0. -> ""
      | t -> Printf.sprintf " signal=%.3f" (t -. !origin));
    (* the totals, over every path, of the phases named [suffix]: one line
       for each name in [summed], printed only when such a phase ran *)
    List.iter
      (fun suffix ->
        let t, n =
          List.fold_left
            (fun (t', n') (k, (t, n, _)) ->
              let m = String.length suffix and l = String.length k in
              if
                k = suffix
                || (l > m && String.sub k (l - m - 1) (m + 1) = "/" ^ suffix)
              then (t' +. t, n' + n)
              else (t', n'))
            (0., 0) rows
        in
        if n > 0 then
          Printf.bprintf b "%s: total %s %.3f %d\n" lbl suffix t n)
      summed;
    List.iter
      (fun (k, (t, c, o)) ->
        Printf.bprintf b "%s: %s %.3f %d%s\n" lbl k t c
          (if o > 0 then Printf.sprintf " open=%d" o else ""))
      rows;
    prerr_string (Buffer.contents b);
    flush stderr)

(* what the watcher runs on a termination signal before it reports: a process
   that has handed the run to a forked copy waits there for the copy's own
   report ([ParallelRace]) *)
let signal_hooks : (unit -> unit) list Atomic.t = Atomic.make []

let rec at_signal f =
  let old = Atomic.get signal_hooks in
  if not (Atomic.compare_and_set signal_hooks old (f :: old)) then at_signal f

(* The watcher is a system thread, not a domain: OCaml refuses [Unix.fork]
   in a process that has ever spawned a domain, so a watcher domain made
   every forked query of a run fail at once.  A thread can run while the main
   thread is inside a Z3 check, because the Z3 bindings release the runtime
   lock around [Solver.check] and [simplify]; a call that keeps the lock delays
   the report until it returns. *)
let spawn_watcher () =
  let rec loop () =
    Thread.delay 0.05;
    match Atomic.get term_signal with
    | 0 -> loop ()
    | n ->
        let code, name =
          if n = Stdlib.Sys.sigint then (130, "sigint") else (143, "sigterm")
        in
        (* the forked copies die with this process anyway (see [ForkGuard]);
           killing them first makes it immediate on every platform *)
        List.iter
          (fun f -> try f () with _ -> ())
          (Atomic.get signal_hooks);
        ForkGuard.kill_live ();
        (try flush stdout with Sys_error _ -> ());
        report ~reason:name;
        Core_unix.exit_immediately code
  in
  ignore (Thread.create loop () : Thread.t)

(* [around_fork fork] calls [fork] (a function that forks this process) and
   switches the account off in the child, which then sends no report and
   behaves as a child of a run without the account; the watcher thread does
   not exist in a forked child.  Without the account it is [fork ()]. *)
let around_fork fork =
  if not !on then fork ()
  else
    let pid = Unix.getpid () in
    let v = fork () in
    if Unix.getpid () <> pid then (
      on := false;
      in_child := true;
      fork_time := now ();
      child_z3 := 0.;
      child_z3_n := 0);
    v

let enable () =
  if not !on then (
    on := true;
    at_exit (fun () -> report ~reason:"exit");
    let handler =
      Stdlib.Sys.Signal_handle
        (fun n ->
          if Atomic.get term_time = 0. then
            Atomic.set term_time (now ());
          Atomic.set term_signal n)
    in
    Stdlib.Sys.set_signal Stdlib.Sys.sigterm handler;
    Stdlib.Sys.set_signal Stdlib.Sys.sigint handler;
    spawn_watcher ())

(* In a forked copy of a process whose account was on, that has just been given
   the rest of the run (a raced copy that won, [ParallelRace]): switch the
   account back on, as the copy's own.  What the process accounted before the
   fork is dropped (the process reports it), the phases open at the fork are
   charged from the fork, the solver time the copy totalled while its account
   was off is one row under the innermost open phase, and the report -- at
   exit, or on SIGTERM or SIGINT through a watcher of the copy's own -- is
   printed with the label "phase-time-copy" and its wall clock taken from the
   fork ([from=] in its header, in seconds since the process started).
   Elsewhere it does nothing. *)
let resume_in_copy () =
  if !in_child then (
    let ft = !fork_time in
    Stdlib.Mutex.lock mutex;
    Stdlib.Hashtbl.reset table;
    Stdlib.Mutex.unlock mutex;
    List.iter
      (fun s -> List.iter (fun f -> if f.start < ft then f.start <- ft) !s)
      (Atomic.get stacks);
    if !child_z3_n > 0 then (
      let path =
        match !(Stdlib.Domain.DLS.get stack_key) with
        | [] -> "z3"
        | f :: _ -> f.path ^ "/z3"
      in
      Stdlib.Hashtbl.replace table path { total = !child_z3; count = !child_z3_n });
    in_child := false;
    label := "phase-time-copy";
    origin := ft;
    on := true;
    (* the exit handler and the signal handlers of [enable] were inherited;
       the watcher thread was not *)
    spawn_watcher ())
