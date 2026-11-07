(* The child processes of Athena's route: the copy of this executable that
   runs Frama-C, and clang.

   Contract: a child started here never outlives this process (it is forked
   by [Common.ForkGuard], which has the kernel kill it when this process
   dies), reads this process's standard input and writes both its outputs to
   this process's standard error, so that standard output carries the answer
   alone.  Called only from the main thread while no other domain runs, as
   every fork in this tree is. *)

(* Starts [prog] with [argv] (its own name first) in environment [env], in
   directory [cwd] when given; [prog] is looked up in PATH when it has no
   slash.  The process id. *)
let spawn ?cwd prog argv env =
  match Common.ForkGuard.fork () with
  | `In_the_child -> (
      (* nothing of this process may run in the copy: whatever goes wrong
         before the new program starts ends the copy at once *)
      try
        Unix.dup2 Unix.stderr Unix.stdout;
        Option.iter Unix.chdir cwd;
        Unix.execvpe prog argv env
      with _ (* catch-all-ok: the forked copy ends here whatever failed *) ->
        Common.ProcessExit.immediately 127)
  | `In_the_parent pid -> Core.Pid.to_int pid

let rec wait pid =
  try snd (Unix.waitpid [] pid)
  with Unix.Unix_error (Unix.EINTR, _, _) -> wait pid

(* [prog args] run to its end, in [cwd] when given, with this process's
   environment: [Ok] when it exited with status 0, else how it ended *)
let run ?cwd prog args =
  match
    wait (spawn ?cwd prog (Array.of_list (prog :: args)) (Unix.environment ()))
  with
  | Unix.WEXITED 0 -> Ok ()
  | Unix.WEXITED n -> Error (Printf.sprintf "status %d" n)
  | Unix.WSIGNALED s -> Error (Printf.sprintf "killed by signal %d" s)
  | Unix.WSTOPPED s -> Error (Printf.sprintf "stopped by signal %d" s)

(* Starts [prog args] in a session of its own, with its standard output
   written to the file [stdout] (created or truncated) and its standard
   error this process's, so that [stop] can end it with everything it
   started.  The process id. *)
let spawn_session prog args ~stdout =
  match Common.ForkGuard.fork () with
  | `In_the_child -> (
      try
        ignore (Unix.setsid ());
        let fd =
          Unix.openfile stdout [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ]
            0o644
        in
        Unix.dup2 fd Unix.stdout;
        Unix.close fd;
        Unix.execv prog (Array.of_list (prog :: args))
      with _ (* catch-all-ok: the forked copy ends here whatever failed *) ->
        Common.ProcessExit.immediately 127)
  | `In_the_parent pid -> Core.Pid.to_int pid

(* whether the child [pid] has ended, reaping it if so *)
let ended pid =
  match Unix.waitpid [ Unix.WNOHANG ] pid with
  | 0, _ -> false
  | _ -> true
  | exception Unix.Unix_error (Unix.EINTR, _, _) -> false
  | exception Unix.Unix_error (Unix.ECHILD, _, _) -> true

(* SIGTERM to the session [spawn_session] started, then its leader reaped *)
let stop pid =
  (try Unix.kill (-pid) Sys.sigterm
   with Unix.Unix_error _ -> ( try Unix.kill pid Sys.sigterm with _ -> ()));
  try ignore (wait pid) with Unix.Unix_error _ -> ()
