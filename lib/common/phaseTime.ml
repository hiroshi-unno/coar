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

   COAR_COPY_REPORT set (an instrument, read once at start-up, with the
   account on; the PCSat solver also switches the account on for it): every
   forked copy keeps an account of its own from its fork ([copy_acc]) and
   prints it, labelled [phase-time-copy[<copy_id>]], when it ends -- a forked
   question's copy after sending its answer, a raced copy that leaves, a
   raced copy that took over at its exit as above, and any of them on
   SIGTERM or SIGINT, which a parent stopping a copy then sends before its
   SIGKILL ([ForkGuard.term_first]).  Its events and its [child_line] are
   labelled the same way; [copy_id] names the phase each fork was made in,
   the fork's number and the pids.  Every such line is written by one
   [write] of its own ([write_lines]), so lines from copies sharing a stderr
   are never cut.  A copy killed outright (its parent's death, a memory cap)
   still prints nothing: the events it printed as they happened, and
   COAR_PHASE_OPEN_DIR's snapshots, are what remain of it.  Unset, nothing
   here behaves differently; set, no computation's result changes (only the
   moment a stopped copy dies, by at most the grace).

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
(* Every critical section on [mutex] goes through [Mutex.protect], which
   unlocks on any exception.  The sections allocate, so they contain safe
   points, and [Timer] raises its timeout from a signal handler at whatever
   safe point is running: a section written as [lock; ...; unlock] that a
   timeout interrupted kept the mutex, and the next phase to close on the same
   thread failed with [Sys_error "Mutex.lock: Resource deadlock avoided"],
   aborting the run (seen on MuStrat runs with the account on, closing a phase
   around a refinement whose solver timed out). *)
let mutex = Stdlib.Mutex.create ()

let add path secs =
  Stdlib.Mutex.protect mutex (fun () ->
      match Stdlib.Hashtbl.find_opt table path with
      | Some a ->
          a.total <- a.total +. secs;
          a.count <- a.count + 1
      | None -> Stdlib.Hashtbl.replace table path { total = secs; count = 1 })

type token = (stack * frame) option

(* COAR_PHASE_TRACE set (with the account on): every phase entered is also
   printed on stderr as it is entered, with its seconds from the start; for a
   run that dies inside a call (a solver's own out-of-memory abort) and so
   prints no report, the last line names the phase it died in; an [event]
   is printed the same way *)
let trace = Option.is_some (Stdlib.Sys.getenv_opt "COAR_PHASE_TRACE")
(* [true] in a raced copy whose account is off ([track_in_copy]): its phases
   are still kept on the domain's stack, so that the open-phase snapshots can
   say where the copy is, but nothing is added to the account. *)
let track = ref false

(* [true] in a forked copy of a process whose account was on, when
   COAR_COPY_REPORT is set ([ForkGuard.copy_report]; set by [around_fork]):
   the copy keeps an account of its own from the moment of the fork -- its
   phases (on the stack [track] keeps), its solver checks under their
   phases, its events -- and prints it when it ends ([copy_end]), each line
   labelled with [copy_id].  [on] stays false in such a copy, so every reader
   of [on] or [in_child] elsewhere behaves exactly as in a copy without it;
   the account is written only by the copy, in the copy's own memory. *)
let copy_acc = ref false

(* the copy's identity under COAR_COPY_REPORT, "" elsewhere: for each fork
   from the process down to this copy, the innermost phase open where it was
   forked, the forking process's count of its forks ([#n]), and the copy's
   pid and its parent's, joined by " > " from the outermost fork *)
let copy_id = ref ""

(* [copy_tag ()]: "[<copy_id>]" in a copy under COAR_COPY_REPORT, "" elsewhere;
   for a diagnostic line printed in a copy to say which copy printed it *)
let copy_tag () = if !copy_id = "" then "" else "[" ^ !copy_id ^ "]"

(* [write_lines s]: [s] (lines ending in newlines) on stderr, each line by
   one [write] of its own after what the channel holds was flushed, so that
   the lines of copies writing to one stderr at once never cut into each
   other (a pipe writes up to 4096 bytes at once; a file shared across a
   fork shares one offset).  Never raises but an asynchronous exception. *)
let write_lines s =
  (try flush stderr with Sys_error _ -> ());
  let n = String.length s in
  let rec line i =
    if i < n then
      let j = match String.index_from_opt s i '\n' with Some j -> j + 1 | None -> n in
      let rec write k =
        if k < j then
          match Unix.write_substring Unix.stderr s k (j - k) with
          | w -> write (k + w)
          | exception Unix.Unix_error (Unix.EINTR, _, _) -> write k
          | exception Unix.Unix_error _ -> ()
      in
      write i;
      line j
  in
  line 0

let start name : token =
  if not (!on || !track) then None
  else
    let s = Stdlib.Domain.DLS.get stack_key in
    let path = match !s with [] -> name | f :: _ -> f.path ^ "/" ^ name in
    let fr = { path; start = now () } in
    s := fr :: !s;
    if trace && !on then
      Printf.eprintf "phase> %s %.3f\n%!" path (fr.start -. t0);
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
        if !on || !copy_acc then add fr.path (now () -. fr.start))

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
              if !on || !copy_acc then add f.path (now -. f.start);
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
  if not (!on || !track) then (
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
    if !on || !track then (
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
      (if !copy_acc then fun () -> with_phase "z3" f else f))
  else with_phase "z3" f

(* the report of a copy under COAR_COPY_REPORT ([copy_end], defined with the
   report below) *)
let copy_end_ref : (reason:string -> unit) ref = ref (fun ~reason:_ -> ())

(* In a forked copy of a process whose account was on, one line on stderr:
   the wall time since [started] and the part of it spent in solver checks;
   under COAR_COPY_REPORT the line is labelled with the copy and followed by
   the copy's own report ([copy_end]).  Nothing anywhere else. *)
let child_line ~started =
  if !in_child then
    if !copy_acc then (
      write_lines
        (Printf.sprintf "phase-time-child%s: wall=%.3f z3=%.3f\n" (copy_tag ())
           (now () -. started)
           !child_z3);
      !copy_end_ref ~reason:"end")
    else (
      prerr_string
        (Printf.sprintf "phase-time-child: wall=%.3f z3=%.3f\n"
           (now () -. started)
           !child_z3);
      flush stderr)

(* the line of an event in a copy: as it always was, or, under
   COAR_COPY_REPORT, labelled with the copy and written whole *)
let child_event_line name =
  if !copy_acc then
    write_lines
      (Printf.sprintf "phase-time-child-event%s: %s\n" (copy_tag ()) name)
  else (
    prerr_string (Printf.sprintf "phase-time-child-event: %s\n" name);
    flush stderr)

(* An event with no duration, counted under [name]: a row of the report
   ([add name 0.], so its count is the number of events) when the account is
   on; in a forked copy of a process whose account was on, where nothing is
   accounted, one line [phase-time-child-event: name] on stderr at once, so
   that an event inside a copy (a probe's nested solve) is not invisible
   (under COAR_COPY_REPORT also a row of the copy's own account).
   Nothing otherwise. *)
let event name =
  if !on then (
    if trace then Printf.eprintf "event> %s %.3f\n%!" name (now () -. t0);
    add name 0.)
  else if !in_child then (
    if !copy_acc then add name 0.;
    child_event_line name)

(* [event] counted under the innermost phase open on this domain, as the row
   [<path>/<name>], so that one event raised from many places is told apart by
   where it was raised.  In a forked copy of a process whose account was on,
   the path is that of the innermost phase open at the fork (no phase is opened
   in a copy, except that a raced copy under COAR_PHASE_OPEN_DIR keeps its own,
   [track_in_copy], and then the path is the copy's innermost), and the line is printed only when [in_copy] holds, so that a
   frequent event can be counted in the process without flooding a copy's
   stderr.  Under COAR_COPY_REPORT a copy keeps its own phases, so the path is
   the copy's innermost, and every event is also a row of the copy's account,
   [in_copy] or not. *)
let event_here ?(in_copy = true) name =
  if !on || (!in_child && (in_copy || !copy_acc)) then
    let path =
      match !(Stdlib.Domain.DLS.get stack_key) with
      | [] -> name
      | f :: _ -> f.path ^ "/" ^ name
    in
    if !on then add path 0.
    else (
      if !copy_acc then add path 0.;
      if in_copy then child_event_line path)

(* [add_here name ~secs ~count]: [secs] and [count] added to the row
   [<innermost open phase>/<name>] when the account is on; nothing otherwise.
   For a cost spread over many small calls inside one phase (a test asked at
   every node of a formula), timed by the caller and added once, where a phase
   per call would cost more than the call.  Also in a copy under
   COAR_COPY_REPORT, to the copy's own account. *)
let add_here name ~secs ~count =
  if !on || !copy_acc then (
    let path =
      match !(Stdlib.Domain.DLS.get stack_key) with
      | [] -> name
      | f :: _ -> f.path ^ "/" ^ name
    in
    Stdlib.Mutex.protect mutex (fun () ->
        match Stdlib.Hashtbl.find_opt table path with
        | Some a ->
            a.total <- a.total +. secs;
            a.count <- a.count + count
        | None -> Stdlib.Hashtbl.replace table path { total = secs; count }))

(* Open-phase snapshots, for a process that can be killed without a chance to
   report (a raced copy killed by its process, by the process's death, or by a
   memory cap: all SIGKILL).  With COAR_PHASE_OPEN_DIR set to a directory, a
   process whose account is on, and every raced copy of it ([track_in_copy]),
   writes the file [<dir>/open.<pid>] once a second: its pid, its parent's,
   what it is (the process, a copy racing, a copy that took over), the time of
   the snapshot (seconds since the process started), and its open phases,
   outermost first, each with the time it has been open.  The file is written
   whole and renamed into place, so a reader never sees half of it; the last
   one a killed process wrote says where it was, to within a second.
   Nothing is written without the variable. *)
let snapshot_dir = Stdlib.Sys.getenv_opt "COAR_PHASE_OPEN_DIR"

let snapshot_kind = ref "process"

let write_snapshot dir =
  let pid = Unix.getpid () in
  let t = now () in
  let b = Buffer.create 256 in
  Printf.bprintf b "pid=%d ppid=%d kind=%s at=%.3f\n" pid (Unix.getppid ())
    !snapshot_kind (t -. t0);
  List.iter
    (fun s ->
      List.iter
        (fun f -> Printf.bprintf b "open %s %.3f\n" f.path (t -. f.start))
        (List.rev !s))
    (Atomic.get stacks);
  let file = Filename.concat dir (Printf.sprintf "open.%d" pid) in
  let tmp = file ^ ".tmp" in
  try
    let oc = open_out tmp in
    output_string oc (Buffer.contents b);
    close_out oc;
    Sys.rename tmp file
  with Sys_error _ -> ()

let spawn_snapshot_writer () =
  match snapshot_dir with
  | None -> ()
  | Some dir ->
      ignore
        (Thread.create
           (fun () ->
             Timer.keep_off_this_thread ();
             let rec loop () =
               write_snapshot dir;
               Thread.delay 1.0;
               loop ()
             in
             loop ())
           ()
          : Thread.t)

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
   lines: the solver contexts made, the forced collections before them, the
   leases of a clean pooled context, and the kinds of Z3 work other than a
   check ([Z3Interface]'s wrappers) *)
let summed =
  [
    "new-context";
    "gc-full-major";
    "clean-pool-lease";
    "z3-reset";
    "z3-add";
    "z3-get-model";
    "z3-model-eval";
    "z3-simplify";
    "z3-tactic";
  ]

(* what the report runs, once, before it prints: another account that must be
   printed whichever way the process ends (normal exit, a termination signal,
   handing the run to a forked copy, which ends the process without running
   [at_exit]) registers its printer here *)
let report_hooks : (unit -> unit) list Atomic.t = Atomic.make []

let rec at_report f =
  let old = Atomic.get report_hooks in
  if not (Atomic.compare_and_set report_hooks old (f :: old)) then at_report f

let report ~reason =
  (* a report made while a termination signal is being handled says so,
     whichever thread makes it *)
  let reason =
    match Atomic.get term_signal with
    | 0 -> reason
    | n -> if n = Stdlib.Sys.sigint then "sigint" else "sigterm"
  in
  if (!on || !copy_acc) && Atomic.compare_and_set reported false true then (
    (* the hooks are the process's printers, inherited at the fork: a copy
       that has not taken over the run leaves them to the process *)
    if not !copy_acc then
      List.iter
        (fun f -> try f () with e when not (Timer.is_async e) -> ())
        (Atomic.get report_hooks);
    let now = now () in
    let rows, domains =
      Stdlib.Mutex.protect mutex @@ fun () ->
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
        (rows, domains)
    in
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
    (match snapshot_dir with
    | Some dir ->
        Printf.bprintf b "%s: open-phase snapshots in %s (open.<pid>)\n" lbl dir
    | None -> ());
    if !copy_id = "" then (
      prerr_string (Buffer.contents b);
      flush stderr)
    else write_lines (Buffer.contents b))

(* [copy_end ~reason]: in a copy under COAR_COPY_REPORT that has not taken
   over the run, its report, once (labelled [phase-time-copy[<copy_id>]]);
   nothing anywhere else.  Called where a copy ends: a forked question's copy
   after it sent its answer ([child_line]), a raced copy that leaves
   ([ParallelRace]), and the copy's watcher on SIGTERM or SIGINT. *)
let copy_end ~reason = if !copy_acc then report ~reason

let () = copy_end_ref := copy_end

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
   lock around [Solver.check] and [simplify] (and the [Z3Released] stubs
   around the fixedpoint query, [qe], [Optimize.check]); a call that keeps the
   lock delays the report until it returns.  After a hand-over the same holds
   of the copy's stop: this watcher passes the signal on ([at_signal]), so a
   lock-holding call of this process delays the copy's report too. *)
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
        ProcessExit.immediately code
  in
  ignore
    (Thread.create
       (fun () ->
         (* the run's timer signals belong to the main thread *)
         Timer.keep_off_this_thread ();
         loop ())
       ()
      : Thread.t)

(* the forks this process has made through [around_fork] with an account,
   for [copy_id] *)
let fork_serial = ref 0

(* In a copy under COAR_COPY_REPORT that has not taken over the run: on
   SIGTERM or SIGINT (the handler of [enable] only sets [term_signal]), stop
   the copy's own forked copies (each given its grace to report,
   [ForkGuard.kill_live]), print the copy's report and end the copy with
   128 + the signal.  A thread, for the reason given at [spawn_watcher]; it
   leaves once the copy has taken over the run ([resume_in_copy] then starts
   the process's watcher). *)
let spawn_copy_watcher () =
  let rec loop () =
    Thread.delay 0.05;
    if !copy_acc then
      match Atomic.get term_signal with
      | 0 -> loop ()
      | n ->
          let code, name =
            if n = Stdlib.Sys.sigint then (130, "sigint") else (143, "sigterm")
          in
          (try ForkGuard.kill_live ()
           with e when not (Timer.is_async e) -> ());
          (try flush stdout with Sys_error _ -> ());
          report ~reason:name;
          ProcessExit.immediately code
  in
  ignore
    (Thread.create
       (fun () ->
         Timer.keep_off_this_thread ();
         loop ())
       ()
      : Thread.t)

(* in the copy just forked, under COAR_COPY_REPORT: the copy's own account,
   from the fork ([copy_acc]) *)
let start_copy_account ~where ~serial ~parent =
  let ft = !fork_time in
  copy_id :=
    (if !copy_id = "" then "" else !copy_id ^ " > ")
    ^ Printf.sprintf "%s#%d pid=%d ppid=%d" where serial (Unix.getpid ())
        parent;
  Stdlib.Mutex.protect mutex (fun () -> Stdlib.Hashtbl.reset table);
  List.iter
    (fun s -> List.iter (fun f -> if f.start < ft then f.start <- ft) !s)
    (Atomic.get stacks);
  label := Printf.sprintf "phase-time-copy[%s]" !copy_id;
  origin := ft;
  Atomic.set reported false;
  Atomic.set term_signal 0;
  Atomic.set term_time 0.;
  track := true;
  copy_acc := true;
  let handler =
    Stdlib.Sys.Signal_handle
      (fun n ->
        if Atomic.get term_time = 0. then Atomic.set term_time (now ());
        Atomic.set term_signal n)
  in
  Stdlib.Sys.set_signal Stdlib.Sys.sigterm handler;
  Stdlib.Sys.set_signal Stdlib.Sys.sigint handler;
  spawn_copy_watcher ()

(* [around_fork fork] calls [fork] (a function that forks this process) and
   switches the account off in the child, which then sends no report and
   behaves as a child of a run without the account; the watcher thread does
   not exist in a forked child.  Without the account it is [fork ()].
   Under COAR_COPY_REPORT ([ForkGuard.copy_report]) the child also starts an
   account of its own ([start_copy_account]), and so does every copy forked
   by such a child; that changes nothing the child computes. *)
let around_fork fork =
  if not (!on || !copy_acc) then fork ()
  else
    let pid = Unix.getpid () in
    let where =
      match !(Stdlib.Domain.DLS.get stack_key) with
      | [] -> "top"
      | f :: _ -> f.path
    in
    incr fork_serial;
    let serial = !fork_serial in
    let v = fork () in
    if Unix.getpid () <> pid then (
      on := false;
      in_child := true;
      fork_time := now ();
      child_z3 := 0.;
      child_z3_n := 0;
      if ForkGuard.copy_report then start_copy_account ~where ~serial ~parent:pid);
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
    spawn_watcher ();
    spawn_snapshot_writer ())

(* In a raced copy forked by a process whose account was on, with
   COAR_PHASE_OPEN_DIR set: keep the copy's open phases ([track]) and write its
   snapshots.  Only the stack of open phases is kept; the account stays off,
   so the copy reports nothing and accounts nothing until it takes over
   ([resume_in_copy]).  Elsewhere it does nothing. *)
let track_in_copy () =
  if !in_child && Option.is_some snapshot_dir then (
    track := true;
    snapshot_kind := "copy-racing";
    spawn_snapshot_writer ())

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
    (* under COAR_COPY_REPORT the table already is the copy's own, from the
       fork, its solver checks included under their phases; it is kept *)
    let kept = !copy_acc in
    copy_acc := false;
    if not kept then
      Stdlib.Mutex.protect mutex (fun () -> Stdlib.Hashtbl.reset table);
    List.iter
      (fun s -> List.iter (fun f -> if f.start < ft then f.start <- ft) !s)
      (Atomic.get stacks);
    if !child_z3_n > 0 && not kept then (
      let path =
        match !(Stdlib.Domain.DLS.get stack_key) with
        | [] -> "z3"
        | f :: _ -> f.path ^ "/z3"
      in
      Stdlib.Hashtbl.replace table path { total = !child_z3; count = !child_z3_n });
    in_child := false;
    track := false;
    snapshot_kind := "copy-took-over";
    if not kept then label := "phase-time-copy";
    origin := ft;
    on := true;
    (* the exit handler and the signal handlers of [enable] were inherited;
       the watcher thread was not *)
    spawn_watcher ())
