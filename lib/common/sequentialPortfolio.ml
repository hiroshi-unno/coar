(* A sequential portfolio: one question answered by running several
   configurations of this program one after another, each in a forked copy of
   its own, until one of them gives a definite answer.

   Contract.  [run ~print stages] takes the stages in order, each as its name
   (for diagnostics only) and its time limit in seconds ([None]: no limit of
   its own; an outside limit on the whole run still applies).  It assumes
   [stages] is non-empty, that the calling process has spawned no domain
   (OCaml refuses to fork once one has been spawned), and that nothing has
   been written to standard output that a copy could print a second time
   (both standard channels are flushed before each fork).  It returns only in
   a forked copy, and there it returns the index [i] (from 0) of the stage
   that copy is to run, with the copy's standard output redirected into a pipe
   its parent reads and SIGTERM/SIGINT back at their default action; the copy
   then answers the question as a plain run of stage [i]'s configuration
   would, and ends as such a run ends.  In the calling process it never
   returns: it runs the stages and ends the process with [ProcessExit.exit].

   A stage runs until its copy exits, or until its time limit has passed since
   its fork; then the copy is sent SIGTERM and, if it has not exited [grace_s]
   seconds later, SIGKILL.  A stage's output is everything its copy wrote to
   standard output; it is definite when its first non-blank line begins with
   one of [definite_words], followed by the end of the line, a comma or a
   blank: the verdicts a backend prints for a decided question.  [unknown],
   [timeout], [MAYBE], an error (which goes to standard error) and silence are
   not definite, and neither is the output of a copy that crashed before
   printing.

   The answer.  The first stage whose output is definite ends the run: its
   output is copied to standard output and the process ends with that copy's
   status; no later stage runs.  If no stage is definite, the output copied is
   the last stage's when it is non-empty, and otherwise the last non-empty
   output of an earlier stage (an [unknown] or [MAYBE] rather than nothing),
   and the status is the last stage's.  So standard output carries exactly
   what one stage printed, never a mix of two.  The portfolio adds no answer
   of its own: every answer it prints was printed by a stage for the same
   question, so it is as sound as its least sound stage.

   Standard input is inherited, so a question read from standard input
   reaches only the first stage that reads it.  Standard error is not
   redirected: each copy writes its diagnostics, and its
   phase report, as it goes.  A termination signal to the calling process (an
   outside time limit) is passed on to the running copy, which is given
   [grace_s] seconds to end before SIGKILL; whatever it has written to
   standard output by then is printed, and the process ends with 143 (130 for
   SIGINT), as a plain run ended by that signal would.  A copy never outlives
   this process ([ForkGuard.fork]), and neither do the copies a copy forks.

   Why a fork per stage rather than the stages in turn in this process: a
   backend may return its answer while its own domains are still inside Z3
   (MuVal's primal and dual), it sets process-global state that may be set
   only before any solver domain exists (the function and datatype
   environments), and once one domain has been spawned no fork is possible;
   none of that can be undone between two stages, and a fresh copy has none of
   it.  The question is read again by each copy, which costs the reading time
   once per stage. *)

let definite_words = [ "valid"; "invalid"; "sat"; "unsat"; "YES"; "NO" ]

(* seconds a copy is given between SIGTERM and SIGKILL *)
let grace_s = 2.

(* [is_definite out]: [out]'s first non-blank line begins with a word of
   [definite_words] that ends at the end of the line, a comma or a blank *)
let is_definite out =
  let lines = String.split_on_char '\n' out in
  match List.find_opt (fun l -> String.trim l <> "") lines with
  | None -> false
  | Some line ->
      let line = String.trim line in
      let n = String.length line in
      let rec word_end i =
        if i < n && line.[i] <> ',' && line.[i] <> ' ' && line.[i] <> '\t' then
          word_end (i + 1)
        else i
      in
      List.mem (String.sub line 0 (word_end 0)) definite_words

(* the status a shell reports for a process ended by [signal] (an OCaml
   signal number) *)
let status_of_signal s =
  if s = Sys.sigkill then 137
  else if s = Sys.sigterm then 143
  else if s = Sys.sigint then 130
  else if s = Sys.sigabrt then 134
  else if s = Sys.sigsegv then 139
  else 1

let code_of_status = function
  | Unix.WEXITED c -> c
  | Unix.WSIGNALED s | Unix.WSTOPPED s -> status_of_signal s

let now = Unix.gettimeofday

(* the termination signal this process has received, 0 for none *)
let term_signal = Atomic.make 0

let rec waitpid_nohang pid =
  match Unix.waitpid [ Unix.WNOHANG ] pid with
  | 0, _ -> None
  | _, st -> Some st
  | exception Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_nohang pid

let rec waitpid_block pid =
  match Unix.waitpid [] pid with
  | _, st -> st
  | exception Unix.Unix_error (Unix.EINTR, _, _) -> waitpid_block pid

(* [collect ~pid ~rd ~limit]: reads the copy [pid]'s standard output from
   [rd] until the copy exits, its [limit] passes, or this process is sent a
   termination signal; returns the output, the copy's status and why it
   ended.  The copy has exited (and is reaped) when it returns. *)
let collect ~pid ~rd ~limit =
  let buf = Buffer.create 256 in
  let chunk = Bytes.create 65536 in
  let eof = ref false in
  (* waits up to [t] seconds for output and reads what is there *)
  let read_some t =
    if !eof then try Unix.sleepf t with Unix.Unix_error _ -> ()
    else
      match Unix.select [ rd ] [] [] t with
      | [], _, _ -> ()
      | _ -> (
          match Unix.read rd chunk 0 (Bytes.length chunk) with
          | 0 -> eof := true
          | k -> Buffer.add_subbytes buf chunk 0 k
          | exception Unix.Unix_error (Unix.EINTR, _, _) -> ())
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> ()
  in
  (* what is already in the pipe once the copy has exited; a copy's own
     forked copies may hold the pipe open a moment longer, and anything they
     write is not the copy's answer *)
  let rec drain () =
    if not !eof then
      match Unix.select [ rd ] [] [] 0. with
      | [], _, _ -> ()
      | _ ->
          (match Unix.read rd chunk 0 (Bytes.length chunk) with
          | 0 -> eof := true
          | k -> Buffer.add_subbytes buf chunk 0 k
          | exception Unix.Unix_error (Unix.EINTR, _, _) -> ());
          drain ()
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> drain ()
  in
  let stop () =
    (try Unix.kill pid Sys.sigterm with Unix.Unix_error _ -> ());
    let until = now () +. grace_s in
    let rec wait () =
      match waitpid_nohang pid with
      | Some st -> st
      | None ->
          if now () >= until then (
            (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
            waitpid_block pid)
          else (
            read_some 0.05;
            wait ())
    in
    let st = wait () in
    drain ();
    st
  in
  let started = now () in
  let rec loop () =
    match waitpid_nohang pid with
    | Some st ->
        drain ();
        (Buffer.contents buf, st, `Exited)
    | None -> (
        if Atomic.get term_signal <> 0 then
          let st = stop () in
          (Buffer.contents buf, st, `Signalled)
        else
          match limit with
          | Some l when now () -. started >= l ->
              let st = stop () in
              (Buffer.contents buf, st, `Time_limit)
          | Some l ->
              read_some
                (Float.max 0. (Float.min 0.1 (l -. (now () -. started))));
              loop ()
          | None ->
              read_some 0.1;
              loop ())
  in
  loop ()

let print_output out =
  print_string out;
  flush stdout

let run ~print (stages : (string * float option) list) : int =
  let n = List.length stages in
  (* installed before the first fork so that no signal falls between two
     stages unseen; each copy puts the default action back *)
  let handler = Sys.Signal_handle (fun s -> Atomic.set term_signal s) in
  Sys.set_signal Sys.sigterm handler;
  Sys.set_signal Sys.sigint handler;
  let rec go i fallback = function
    | [] -> assert false
    | (name, limit) :: rest -> (
        flush stdout;
        flush stderr;
        let rd, wr = Unix.pipe ~cloexec:true () in
        match ForkGuard.fork () with
        | `In_the_child ->
            Sys.set_signal Sys.sigterm Sys.Signal_default;
            Sys.set_signal Sys.sigint Sys.Signal_default;
            Unix.close rd;
            Unix.dup2 ~cloexec:false wr Unix.stdout;
            Unix.close wr;
            i
        | `In_the_parent pid -> (
            let pid = Core.Pid.to_int pid in
            Unix.close wr;
            let out, st, why = collect ~pid ~rd ~limit in
            Unix.close rd;
            let code = code_of_status st in
            let stage = Printf.sprintf "stage %d of %d (%s)" (i + 1) n name in
            match why with
            | `Signalled ->
                print_output out;
                let s = Atomic.get term_signal in
                ProcessExit.exit (if s = Sys.sigint then 130 else 143)
            | (`Exited | `Time_limit) when is_definite out ->
                print (lazy (Printf.sprintf "portfolio: %s answered" stage));
                print_output out;
                ProcessExit.exit code
            | `Exited | `Time_limit -> (
                print
                  (lazy
                    (Printf.sprintf
                       "portfolio: %s ended without a definite answer (%s, \
                        status %d)"
                       stage
                       (match why with
                       | `Time_limit -> "time limit"
                       | _ -> "exited")
                       code));
                let fallback =
                  if String.trim out <> "" then Some out else fallback
                in
                match rest with
                | [] ->
                    Option.iter print_output fallback;
                    ProcessExit.exit code
                | _ -> go (i + 1) fallback rest)))
  in
  go 0 None stages
