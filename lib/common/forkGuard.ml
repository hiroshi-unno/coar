(* Forking a copy of this process that never outlives it.

   Contract: a process created by [fork] never outlives the process that
   forked it, whatever ends the latter -- an orderly exit, a SIGTERM with or
   without a handler, a SIGKILL, a memory-cap kill.  A forked copy in this tree
   typically asks a solver with no timer of its own, the parent's kill being its
   only bound; a copy left behind by a parent that was killed mid-question was
   reparented to the session's reaper and ran at full CPU for as long as the
   question took, observed at more than thirteen minutes after a 60 s wall-clock
   limit had stopped its run.  This changes no answer: it only removes processes
   whose answer nobody can read any more.

   How: right after the fork, the child asks the kernel for SIGKILL when its
   parent dies ([prctl (PR_SET_PDEATHSIG, SIGKILL)] on Linux), and then
   compares its parent with the pid recorded before the fork, exiting at once
   if they differ: a parent that died between the fork and the request has
   already been replaced by the reaper, and the request would never fire.

   What it relies on: the kernel sends the signal when the THREAD that forked
   exits, not the process; every fork in this tree is made by the main thread
   (a forking process has one domain, and the system threads it runs only
   watch), whose exit is the process's.  Where the request does not exist
   (not Linux) only the parent check is made, and a copy's own watchers
   ([ParallelRace]) remain the bound.  The parent's own exit paths also kill
   the copies they know of ([kill_live]): the orderly ones that leave on
   another's behalf, and the phase account's SIGTERM report. *)

external set_pdeathsig_kill : unit -> bool = "coar_set_pdeathsig_kill"
[@@noalloc]

(* this process's id (a forked copy's own, not its parent's) *)
let self_pid () = Unix.getpid ()

(* the forked copies alive now that their parent may kill wholesale *)
let live : int list Atomic.t = Atomic.make []

let rec update_live f =
  let s = Atomic.get live in
  if not (Atomic.compare_and_set live s (f s)) then update_live f

let register pid = update_live (fun s -> pid :: s)
let unregister pid = update_live (List.filter (fun p -> p <> pid))

(* SIGKILL every registered copy; never raises *)
let kill_live () =
  List.iter
    (fun pid -> try Unix.kill pid Sys.sigkill with _ -> ())
    (Atomic.get live)

(* Set once, when this process has handed the rest of the run to a forked
   copy (a raced copy that won its race, [ParallelRace] of PCSat): from then on
   the process answers nothing, and the thread that set it waits for the copy
   and exits the process with the copy's status.  Never set back. *)
let handed = Atomic.make false

(* [before_verdict ()]: called on the program's ordinary output path just
   before a verdict is printed.  It runs [verdict_hook], which a racing
   library sets ([ParallelRace] of PCSat: a forked copy that was given the
   computation of the run but not yet the right to print asks its parent for
   that right here, and never returns when refused).  By default it does
   nothing.  It prints nothing and must be called outside any output
   operation. *)
let verdict_hook : (unit -> unit) ref = ref (fun () -> ())
let before_verdict () = !verdict_hook ()

(* the main thread of the main domain; module initialisation runs there *)
let main_thread = Thread.id (Thread.self ())

(* [park_if_handed ()]: a safe point of the main thread.  After a hand-over
   ([handed] set) it never returns: it kills the forked questions still
   registered ([kill_live]), whose answers nobody will read, and then sleeps
   forever, so that the main thread stops computing while the copy runs the
   rest of the program.  Otherwise, and always in any other thread, it returns
   at once; the test is one atomic read.

   Why this is exact.  After a hand-over the process's only remaining output
   is the copy's exit status, given by the thread that set [handed], which
   ends the process with [exit_immediately] at whatever instruction the main
   thread is then executing; nothing the main thread computes after the
   hand-over is ever read (the race's [finish], the only way its answer could
   leave, never returns after one).  Parking only moves the main thread's
   stop to an earlier instruction of the same computation.

   What a caller must ensure: it is called where the main thread holds no lock
   that the exit path takes -- the exit path flushes the standard channels,
   prints the phase report (its own mutex) and kills the registered copies, so
   a caller must not be inside an output operation or the report's critical
   section.  Parking prints nothing, answers nothing, and sleeps in short
   steps outside the runtime lock, so the other threads (the one exiting the
   process, the phase account's signal watcher) keep running and a signal
   handler still runs. *)
let park_if_handed () =
  if
    Atomic.get handed
    && Domain.is_main_domain ()
    && Thread.id (Thread.self ()) = main_thread
  then (
    kill_live ();
    let rec sleep () =
      Thread.delay 1.;
      sleep ()
    in
    sleep ())

(* [fork ()] is [Core_unix.fork ()] whose child dies with its parent *)
let fork () =
  let parent = Unix.getpid () in
  match Core_unix.fork () with
  | `In_the_child ->
      ignore (set_pdeathsig_kill () : bool);
      if Unix.getppid () <> parent then Core_unix.exit_immediately 1;
      (* the copies registered so far are the parent's, not this child's: a
         child that killed them on its own way out would kill its siblings *)
      Atomic.set live [];
      (* nor is a hand-over of the parent the child's: a child forked while
         the parent was being handed over must not park its own main thread *)
      Atomic.set handed false;
      `In_the_child
  | `In_the_parent _ as p -> p

(* What a fork may cost in memory, read off this process rather than guessed.

   A forked copy shares the parent's pages until either side writes one.  An
   OCaml copy writes to every page of the live major heap soon after it starts
   working: its own collector marks every reachable block, and marking writes
   the block's header.  So a copy of a process whose major heap is [h] bytes
   may come to hold up to [h] bytes more than the parent (plus whatever it
   allocates itself), measured as a second copy of a 3.4 GB process within
   15 s.

   [cgroup_headroom_bytes ()] is the least [memory.max - memory.current] over
   this process's cgroup (cgroup v2, read from [/proc/self/cgroup]) and every
   ancestor whose [memory.max] is a number; [None] when no such limit is
   readable (not Linux, cgroup v1, no limit anywhere).  [memory.current]
   includes reclaimable page cache, so the headroom errs low.

   [fork_fits ~heap_bytes ~headroom] holds when duplicating the whole major
   heap stays within the headroom: [headroom = None] (no limit to break) or
   [heap_bytes <= h].  Under it a fork cannot, by duplicating the parent's
   heap, push any cgroup on the path past its limit at the time of the
   question; what the copy allocates beyond the duplicate is not bounded by
   this test. *)
let read_first_line path =
  match open_in path with
  | ic ->
      let l = try Some (input_line ic) with End_of_file -> None in
      close_in_noerr ic;
      l
  | exception Sys_error _ -> None

let cgroup_headroom_bytes () =
  match read_first_line "/proc/self/cgroup" with
  | Some l when String.length l > 3 && String.sub l 0 3 = "0::" ->
      let rel = String.sub l 3 (String.length l - 3) in
      let parts = List.filter (fun s -> s <> "") (String.split_on_char '/' rel) in
      (* every prefix of the path, the cgroup itself included *)
      let rec prefixes acc cur = function
        | [] -> List.rev acc
        | p :: rest ->
            let cur = cur ^ "/" ^ p in
            prefixes (cur :: acc) cur rest
      in
      List.fold_left
        (fun best dir ->
          let dir = "/sys/fs/cgroup" ^ dir in
          match
            ( read_first_line (dir ^ "/memory.max"),
              read_first_line (dir ^ "/memory.current") )
          with
          | Some mx, Some cur -> (
              match (int_of_string_opt mx, int_of_string_opt cur) with
              | Some mx, Some cur ->
                  let h = max 0 (mx - cur) in
                  Some (match best with Some b -> min b h | None -> h)
              | _ -> best)
          | _ -> best)
        None (prefixes [] "" parts)
  | _ -> None

let fork_fits ~heap_bytes ~headroom =
  match headroom with None -> true | Some h -> heap_bytes <= h

(* the bytes of this domain's major heap, as [Gc.quick_stat] reports them *)
let major_heap_bytes () = (Gc.quick_stat ()).Gc.heap_words * (Sys.word_size / 8)
