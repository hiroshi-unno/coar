(* Backend that decides a HORS model checking problem with the external
   HorSat2 model checker, run as a separate process on a per-process input
   file.  HorSat2 is handed a scheme with an alternating tree automaton and
   no finite data; a problem specified by a trivial tree automaton (finite
   data included) is first translated by [HOMC.TrivialToAlternating.convert],
   which preserves the answer, and a problem it cannot translate is an
   [Error].  HorSat2 reads only the first rule for a state and a terminal,
   so an automaton with several is handed over with them joined into one
   disjunction ([Automata.ATA.merge_duplicates]), which preserves the
   answer.  The verdict is read positionally from HorSat2's output
   (satisfied, or not satisfied with a counterexample unless [-noce] is set).
   An EHMTT is not a HORS problem and is an [Error]: EffCaml reduces it to
   HORS problems and hands them here one by one.  A parse error, output in
   an unexpected shape, a non-zero exit and a HorSat2 killed by a signal
   (the memory cap's OOM killer included) become an [Error], never a verdict
   and never [unknown]: the problem was not decided, and the cause is not a
   property of the problem.  The error's message says which of these
   happened, with the tail of HorSat2's standard error. *)
open Core
open Common
open Automata

module type SolverType = sig
  val solve :
    ?print_sol:bool -> HOMC.Problem.t -> HOMC.Problem.solution Or_error.t

  (* Decide one HORS problem (not an EHMTT), of either automaton dialect,
     answering the verdict together with HorSat2's counterexample when it
     refutes the problem and [noce] is off. *)
  val solve_rsfd :
    HOMC.Problem.t -> (HOMC.Problem.solution * string option) Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* The query files and the HorSat2 processes of calls in flight, each with
     the process that made it.  A call removes its own files, and kills its
     HorSat2 if it is still running, when it returns or raises, a timeout
     included ([Common.Timer.protect]); these lists are what is cleaned up
     when the process ends before the call does:
     - at exit ([Stdlib.at_exit]), which covers a run that answers and exits
       while another domain is still inside a call;
     - on SIGTERM or SIGINT through [PhaseTime.at_signal], when the phase
       account has installed its signal handler;
     - on SIGTERM or SIGINT through [stop_on_signal] below, installed while a
       call is in flight wherever the signal still has its default action,
       which is the ordinary case: an outside [timeout] stopping a run with
       the account off.
     SIGKILL cannot be caught, so a run stopped that way (an outside
     [timeout -s KILL], a cgroup OOM kill of this process) still leaves its
     files; they are in the system's temporary directory, never in the
     directory the run started from, and their names are drawn afresh per
     call, so a left-over file is never read or overwritten by a later run.
     A forked copy inherits the lists and the hooks and cleans up only its
     own process's entries, never those of a call its parent is still
     inside. *)
  let live_files : (int * string) list Atomic.t = Atomic.make []
  let live_children : (int * Pid.t) list Atomic.t = Atomic.make []

  let rec update_atomic a f =
    let old = Atomic.get a in
    if not (Atomic.compare_and_set a old (f old)) then update_atomic a f

  let update_live = update_atomic live_files

  let unlink_quietly file =
    try Core_unix.unlink file with Core_unix.Unix_error _ -> ()

  (* Kill [child] with SIGKILL; one already gone is not an error.  Only a
     child that has not been reaped yet is ever registered (see
     [with_child]), so the pid cannot have been reused by another process. *)
  let kill_quietly child =
    try
      ignore
        (Signal_unix.send Signal.kill (`Pid child) : [ `Ok | `No_such_process ])
    with Core_unix.Unix_error _ -> ()

  let remove_live () =
    let self = Pid.to_int @@ Core_unix.getpid () in
    List.iter (Atomic.get live_children) ~f:(fun (pid, child) ->
        if pid = self then kill_quietly child);
    List.iter (Atomic.get live_files) ~f:(fun (pid, file) ->
        if pid = self then unlink_quietly file)

  (* registered when the functor is applied, before solver domains share it *)
  let () =
    PhaseTime.at_signal remove_live;
    Stdlib.at_exit remove_live

  (* The handler for SIGTERM and SIGINT while a call is in flight: clean up as
     [remove_live] does, then end the process by the same signal with its
     default action, so the exit status a caller sees ([128 + signal] from a
     shell, [timeout]'s 124) is the one it would have seen without the
     handler.  The handler runs at the next safe point of the runtime, which a
     thread blocked reading HorSat2's output or waiting for it reaches at
     once (the read and the wait are interrupted and resumed by the runtime's
     signal processing). *)
  let stop_on_signal n =
    remove_live ();
    Stdlib.Sys.set_signal n Stdlib.Sys.Signal_default;
    (try Signal_unix.send_i (Signal.of_caml_int n) (`Pid (Core_unix.getpid ()))
     with Core_unix.Unix_error _ -> ());
    (* the signal is normally delivered before [send_i] returns; should it go
       to another thread that has not ended the process yet, end it here with
       the status a shell would report *)
    Common.ProcessExit.exit (if n = Stdlib.Sys.sigint then 130 else 143)

  let signal_lock = Stdlib.Mutex.create ()
  let calls_in_flight = ref 0
  let armed_signals : int list ref = ref []

  (* [arm_signals ()] and [disarm_signals ()] bracket one call: the first
     call in flight installs [stop_on_signal] for SIGTERM and SIGINT where
     the signal has its default action (an ignored signal, or one another
     part of the tool already handles, such as the phase account's, is left
     as it is), and the last call to end puts the default back where the
     handler is still [stop_on_signal]. *)
  let arm_signals () =
    Stdlib.Mutex.protect signal_lock (fun () ->
        if !calls_in_flight = 0 then
          armed_signals :=
            List.filter [ Stdlib.Sys.sigterm; Stdlib.Sys.sigint ] ~f:(fun n ->
                match
                  Stdlib.Sys.signal n (Stdlib.Sys.Signal_handle stop_on_signal)
                with
                | Stdlib.Sys.Signal_default -> true
                | old ->
                    Stdlib.Sys.set_signal n old;
                    false);
        incr calls_in_flight)

  let disarm_signals () =
    Stdlib.Mutex.protect signal_lock (fun () ->
        decr calls_in_flight;
        if !calls_in_flight = 0 then (
          List.iter !armed_signals ~f:(fun n ->
              match Stdlib.Sys.signal n Stdlib.Sys.Signal_default with
              | Stdlib.Sys.Signal_handle h when phys_equal h stop_on_signal ->
                  ()
              | other -> Stdlib.Sys.set_signal n other);
          armed_signals := []))

  (* [with_temp_files names f]: create one fresh empty file in the system's
     temporary directory ([Filename.get_temp_dir_name], [TMPDIR] when set)
     per [(prefix, suffix)] of [names], run [f] on their paths (in the order
     of [names]), and remove them afterwards, whether [f] returns or raises;
     the exception, an alarm's timeout included, is re-raised unchanged (an
     alarm arriving during the removal is held until it is done).  A file
     already gone is not an error.  Each name is
     [prefix ^ "p<pid>_" ^ random ^ suffix], created exclusively
     ([Filename.temp_file]), so two concurrent calls -- in two processes or
     two domains of one -- and a file left behind by an earlier, killed run
     never share a name.  While [f] runs, a SIGTERM or SIGINT with its
     default action removes the files before ending the process
     ([arm_signals]). *)
  let with_temp_files names f =
    let pid = Pid.to_int @@ Core_unix.getpid () in
    let files = ref [] in
    Timer.protect
      ~finally:(fun () ->
        let mine = !files in
        List.iter mine ~f:unlink_quietly;
        update_live
          (List.filter ~f:(fun (_, f) ->
               not (List.mem mine f ~equal:String.equal)));
        disarm_signals ())
      (fun () ->
        (* armed before the first file exists, disarmed after the last is
           gone, so no signal finds a file the handler does not know *)
        arm_signals ();
        List.iter names ~f:(fun (prefix, suffix) ->
            let file =
              Stdlib.Filename.temp_file (sprintf "%sp%d_" prefix pid) suffix
            in
            update_live (List.cons (pid, file));
            files := !files @ [ file ]);
        f !files)

  (* [with_child cin f]: run [f], registering the process that writes [cin]
     (from [Common.Util.Command.read_process]) as this call's HorSat2 while
     [f] runs; if [f] raises (a timeout included), kill it first, so the
     wait that follows the read does not block until a HorSat2 whose answer
     nobody reads finishes on its own.  The registration ends before [f]'s
     caller reaps the process, so a registered pid is never a reused one. *)
  let with_child cin f =
    let self = Pid.to_int @@ Core_unix.getpid () in
    let child = Pid.of_int (Caml_unix.process_in_pid cin) in
    let entry = (self, child) in
    let unregister () =
      update_atomic live_children
        (List.filter ~f:(fun e -> not (phys_equal e entry)))
    in
    update_atomic live_children (List.cons entry);
    match f () with
    | v ->
        unregister ();
        v
    | exception exn ->
        kill_quietly child;
        unregister ();
        raise exn

  (* The cgroup's count of OOM kills ([oom_kill] in the cgroup v2 file
     [memory.events] of the cgroup this process is in, which counts the
     cgroup's descendants too), or [None] where there is no such file (cgroup
     v1, no memory controller, not Linux).  Never raises an ordinary
     exception. *)
  let cgroup_oom_kills () =
    try
      match
        List.find_map (In_channel.read_lines "/proc/self/cgroup") ~f:(fun l ->
            String.chop_prefix l ~prefix:"0::")
      with
      | None -> None
      | Some path ->
          List.find_map
            (In_channel.read_lines ("/sys/fs/cgroup" ^ path ^ "/memory.events"))
            ~f:(fun l ->
              match String.split l ~on:' ' with
              | [ "oom_kill"; n ] -> Int.of_string_opt n
              | _ -> None)
    with exn when not (Timer.is_async exn) -> None

  (* The last [n] non-blank lines of [file], joined by " | ", or [""] when
     it cannot be read. *)
  let tail_of_file ?(n = 5) file =
    match In_channel.read_lines file with
    | lines ->
        let lines =
          List.filter lines ~f:(fun l -> not (String.is_empty (String.strip l)))
        in
        String.concat ~sep:" | " (List.drop lines (List.length lines - n))
    | exception exn when not (Timer.is_async exn) -> ""

  (* Why a HorSat2 run gave no verdict, from its exit status, this process's
     cgroup's OOM kill count before and after the run, and the tail of its
     standard error.  HorSat2 is started through [/bin/sh -c "exec ..."], so
     its own status is reported; a shell that did not [exec] would report a
     child killed by signal [s] as exit status [128 + s], so such a status is
     still read as that signal (HorSat2 itself never exits with a status
     above 128).  Memory is
     named only for SIGKILL, the one signal an OOM killer sends, and as the
     cause only when the cgroup's count rose; a run hitting an address-space
     limit ([ulimit -v]) instead fails inside HorSat2, and its standard error
     says so. *)
  let describe_failure ~status ~oom_before ~oom_after ~stderr_tail =
    let signal =
      match status with
      | Error (`Signal s) -> Some (Signal.to_string s, Signal.equal s Signal.kill)
      | Error (`Exit_non_zero n) when n > 128 && n < 128 + 65 ->
          let name =
            match n - 128 with
            | 6 -> "sigabrt"
            | 9 -> "sigkill"
            | 11 -> "sigsegv"
            | 15 -> "sigterm"
            | k -> sprintf "signal %d" k
          in
          Some (name, n - 128 = 9)
      | _ -> None
    in
    let what =
      match (signal, status) with
      | Some (s, is_kill), _ -> (
          match (oom_before, oom_after) with
          | Some b, Some a when a > b ->
              sprintf
                "HorSat2 was killed by %s for memory: the OOM kill count of \
                 this process's cgroup rose from %d to %d during the run"
                s b a
          | Some _, Some _ when is_kill ->
              sprintf
                "HorSat2 was killed by %s, not by the OOM killer of this \
                 process's cgroup (another process, an outside limit or the \
                 kernel's global OOM killer sent it)"
                s
          | _ when is_kill ->
              sprintf
                "HorSat2 was killed by %s, possibly for memory (this \
                 process's cgroup keeps no OOM kill count to tell)"
                s
          | _ -> sprintf "HorSat2 was stopped by %s" s)
      | None, Error (`Exit_non_zero n) ->
          sprintf "HorSat2 exited with status %d" n
      | None, _ ->
          "HorSat2 exited normally but its output has an unexpected shape"
    in
    if String.is_empty stderr_tail then what
    else sprintf "%s; its standard error ends: %s" what stderr_tail

  (* Run HorSat2 on one HORS problem in the dialect it reads, answering the
     verdict together with its counterexample when it refutes the problem
     and [noce] is off. *)
  let run_horsat2 homc =
    match homc with
    | HOMC.Problem.RSFD (trs_in, rules, trs_out) ->
        Debug.print
        @@ lazy
             (sprintf "Size of HORS: %d (%d rules)" (HOMC.RSFD.sizeof rules)
                (List.length rules));
        Debug.print
        @@ lazy
             (sprintf "Number of states of input automaton: %d"
             @@ TreeAutomaton.number_of_states_trs trs_in);
        Debug.print
        @@ lazy
             (sprintf "Number of states of output automaton: %d"
             @@ TreeAutomaton.number_of_states trs_out);
        let res =
          (* the query file and the file HorSat2's standard error goes to are
             this call's alone and nothing reads them once HorSat2 has
             answered, so they are removed on every exit, an exception or a
             timeout included; otherwise every run leaves them in the
             directory it ran from *)
          with_temp_files
            [ ("temp_horsat2_", ".hors"); ("temp_horsat2_", ".err") ]
            (function
            | [ filename; errfile ] -> (
                (* output generated RSFD *)
                Out_channel.with_file filename ~f:(fun channel ->
                    HOMC.Problem.pr
                      (Format.formatter_of_out_channel channel)
                      homc);
                (* HorSat2 0.9.5 *)
                (* [exec]: the process [read_process] starts is then HorSat2
                   itself rather than a shell waiting for it, so killing it
                   ([with_child]) stops HorSat2 *)
                let cmd = "exec ./horsat2 " in
                let cmd = if config.noce then cmd ^ "-noce " else cmd in
                let cmd = if config.merge then cmd ^ "-merge " else cmd in
                let cmd = if config.gfp then cmd ^ "-gfp " else cmd in
                let cmd =
                  cmd ^ Stdlib.Filename.quote filename ^ " 2>"
                  ^ Stdlib.Filename.quote errfile
                in
                let oom_before = cgroup_oom_kills () in
                let (s0, s1, s2), status =
                  Common.Util.Command.read_process cmd ~f:(fun cin ->
                      with_child cin @@ fun () ->
                      let s0 =
                        ignore (In_channel.input_line cin);
                        ignore (In_channel.input_line cin);
                        In_channel.input_line cin
                      in
                      let s1 =
                        ignore (In_channel.input_line cin);
                        ignore (In_channel.input_line cin);
                        ignore (In_channel.input_line cin);
                        In_channel.input_line cin
                      in
                      let s2 =
                        ignore (In_channel.input_line cin);
                        In_channel.input_line cin
                      in
                      (* read the rest of the output too: closing the pipe
                         while HorSat2 still writes kills it with SIGPIPE, and
                         the exit status checked below would then report our
                         early close as HorSat2's failure, losing an answer
                         already printed *)
                      let buf = Bytes.create 65536 in
                      let rec drain () =
                        if
                          In_channel.input cin ~buf ~pos:0
                            ~len:(Bytes.length buf)
                          > 0
                        then drain ()
                      in
                      drain ();
                      (s0, s1, s2))
                in
                let stderr_tail = tail_of_file errfile in
                if not (String.is_empty stderr_tail) then
                  Debug.print
                  @@ lazy ("HorSat2's standard error ends: " ^ stderr_tail);
                match (status, s0, s1, s2) with
                | Error err, Some "Parse error", _, _ ->
                    Debug.print
                    @@ lazy (Core_unix.Exit_or_signal.to_string_hum (Error err));
                    Error "HorSat2 could not parse the query it was given"
                | Ok _, Some _, Some "The property is NOT satisfied.", Some s2
                  when not config.noce ->
                    Ok (Second (Some s2))
                | Ok _, Some _, Some "The property is NOT satisfied.", None
                  when config.noce ->
                    Ok (Second None)
                | Ok _, Some _, Some "The property is satisfied.", None ->
                    Ok (First ())
                | _, _, _, _ ->
                    Error
                      (describe_failure ~status ~oom_before
                         ~oom_after:(cgroup_oom_kills ()) ~stderr_tail))
            | _ -> assert false (* [with_temp_files] makes one per name *))
        in
        (match res with
        | Error why ->
            Or_error.error_string ("HORS verification failed: " ^ why)
        | Ok (First ()) ->
            Debug.print @@ lazy "verified";
            Ok (HOMC.Problem.Sat, None)
        | Ok (Second None) ->
            Debug.print @@ lazy "refuted";
            Ok (HOMC.Problem.Unsat, None)
        | Ok (Second (Some cex)) ->
            Debug.print @@ lazy "refuted with a counterexample:";
            Debug.print @@ lazy cex;
            Ok (HOMC.Problem.Unsat, Some cex))
    | HOMC.Problem.EHMTT _ -> Or_error.error_string "not a HORS problem"

  (* HorSat2 reads only the first rule for a state and a terminal (its
     automaton is looked up with [List.assoc]), so several rules for one pair
     are joined into one disjunction first, which accepts the same trees. *)
  let run_merged homc =
    match homc with
    | HOMC.Problem.RSFD (trs_in, rules, TreeAutomaton.ATA (ranks, trs)) ->
        let trs, merged = ATA.merge_duplicates trs in
        if not (List.is_empty merged) then
          Debug.print
          @@ lazy
               (sprintf
                  "joined several alternating transitions into one \
                   disjunction for %s"
                  (String.concat ~sep:", "
                     (List.map merged ~f:(fun (q, a) -> q ^ " " ^ a))));
        run_horsat2
          (HOMC.Problem.RSFD (trs_in, rules, TreeAutomaton.ATA (ranks, trs)))
    | _ -> run_horsat2 homc

  (* Decide one HORS problem of either dialect: an alternating one with its
     rules for one state and terminal joined, a trivial one after its
     translation (which builds one disjunction per state and terminal). *)
  let solve_rsfd homc =
    match homc with
    | HOMC.Problem.EHMTT _ -> Or_error.error_string "not a HORS problem"
    | HOMC.Problem.RSFD _ when HOMC.Problem.reads_alternating homc ->
        run_merged homc
    | HOMC.Problem.RSFD _ -> (
        match HOMC.TrivialToAlternating.convert homc with
        | homc' -> run_merged homc'
        | exception Failure msg ->
            Or_error.error_string
              ("cannot translate the problem for HorSat2: " ^ msg))

  let solve ?(print_sol = false) homc =
    (match homc with
    | HOMC.Problem.RSFD _ -> Or_error.map (solve_rsfd homc) ~f:fst
    | HOMC.Problem.EHMTT _ ->
        Or_error.error_string
          "HorSat2 decides a HORS problem; an EHMTT program is verified by \
           EffCaml (-c config/solver/effcaml.json)")
    |> Or_error.map ~f:(fun sol ->
           if print_sol then print_endline (HOMC.Problem.str_of_solution sol);
           sol)
end
