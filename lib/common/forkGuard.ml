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

(* COAR_COPY_REPORT set (an instrument, read once at start-up): every forked
   copy keeps a phase account of its own and prints it when it ends
   ([PhaseTime.around_fork]), and a parent that stops a copy sends it SIGTERM
   first and gives it up to [copy_report_grace] seconds to print that report
   before the SIGKILL it always sends ([term_first]).  Unset, nothing in this
   file or at any kill site behaves differently.  Set, a copy is stopped up
   to that grace later than it would be (the kill was going to happen anyway;
   no answer is read from a copy being stopped), and nothing else changes. *)
let copy_report = Option.is_some (Sys.getenv_opt "COAR_COPY_REPORT")
let copy_report_grace = 0.5

(* [Some true] when [pid] has ended (a zombie or gone), from its
   [/proc/PID/stat]; set below, where that reading is defined *)
let ended_for_grace : (int -> bool) ref = ref (fun _ -> true)

(* [term_first ?group pids]: with [copy_report], SIGTERM to each of [pids]
   (and to its process group, with [group]), then wait until each has ended
   or [grace] seconds (default [copy_report_grace]) have passed; without it, nothing.  It never
   reaps (a caller's own [waitpid] still finds the copy) and never raises
   except an asynchronous exception (a run's timeout raised at a safe point
   of the wait), and then only after it has SIGKILLed [pids] (and their
   groups), so that a caller whose own kill is skipped by that exception
   leaves no copy running. *)
let term_first ?(group = false) ?(grace = copy_report_grace) pids =
  if copy_report && pids <> [] then (
    let send sg pid =
      (if group then try Unix.kill (-pid) sg with Unix.Unix_error _ -> ());
      try Unix.kill pid sg with Unix.Unix_error _ -> ()
    in
    List.iter (send Sys.sigterm) pids;
    let deadline = Unix.gettimeofday () +. grace in
    try
      while
        List.exists (fun p -> not (!ended_for_grace p)) pids
        && Unix.gettimeofday () < deadline
      do
        Thread.delay 0.01
      done
    with e ->
      List.iter (send Sys.sigkill) pids;
      raise e)

(* SIGKILL every registered copy; never raises.  With [copy_report], after
   [term_first] on them all, which can pass on an asynchronous exception
   raised during its grace, only once it has SIGKILLed every copy itself. *)
let kill_live () =
  term_first (Atomic.get live);
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
   ends the process with [ProcessExit.immediately] (an [_exit]: no C exit
   handler runs under it) at whatever instruction the main thread is then
   executing; nothing the main thread computes after the
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
      if Unix.getppid () <> parent then ProcessExit.immediately 1;
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

   [cgroup_headroom_bytes ()] is the least headroom (limit less usage) over
   every cgroup on this process's path, in either cgroup version, and [None]
   when no limit is readable in either (not Linux, no limit anywhere); see
   [cgroup_headroom_bytes_at] for what is read.  Usage includes reclaimable
   page cache in both versions, so the headroom errs low.

   [fork_fits ~heap_bytes ~headroom] holds when duplicating the whole major
   heap stays within the headroom: [headroom = None] (no limit to break) or
   [heap_bytes <= h].  It is the one-copy case of [fits] below, which every
   fork of this tree now asks. *)
(* [read_first_line path]: the first line of [path], [None] when the file
   cannot be opened or read.  A [/proc/PID/...] file of a copy that exits
   between the open and the read fails the read with [Sys_error "No such
   process"]; that is an absent reading like a failed open, never an
   exception out of a fit test (which would end the run that asked it). *)
let read_first_line path =
  match open_in path with
  | ic ->
      let l = try Some (input_line ic) with End_of_file | Sys_error _ -> None in
      close_in_noerr ic;
      l
  | exception Sys_error _ -> None

(* [read_lines path]: every line of [path], [None] when the file cannot be
   opened; a read that fails part-way keeps the lines read before it *)
let read_lines path =
  match open_in path with
  | ic ->
      let rec go acc =
        match input_line ic with
        | l -> go (l :: acc)
        | exception (End_of_file | Sys_error _) -> List.rev acc
      in
      let ls = go [] in
      close_in_noerr ic;
      Some ls
  | exception Sys_error _ -> None

(* [path_prefixes rel]: every prefix of the cgroup path [rel] that names a
   cgroup below the hierarchy's root, shortest first, [rel] itself last
   ("/a/b" gives "/a" and "/a/b"; "/" gives none) *)
let path_prefixes rel =
  let parts = List.filter (fun s -> s <> "") (String.split_on_char '/' rel) in
  let rec prefixes acc cur = function
    | [] -> List.rev acc
    | p :: rest ->
        let cur = cur ^ "/" ^ p in
        prefixes (cur :: acc) cur rest
  in
  prefixes [] "" parts

(* [least_headroom ~limit_file ~usage_file ~is_limit dirs]: the least
   [limit - usage] (never negative) over the directories [dirs] whose
   [limit_file] and [usage_file] both read as integers and whose limit
   satisfies [is_limit]; [None] when there is no such directory *)
let least_headroom ~limit_file ~usage_file ~is_limit dirs =
  List.fold_left
    (fun best dir ->
      match
        ( read_first_line (dir ^ "/" ^ limit_file),
          read_first_line (dir ^ "/" ^ usage_file) )
      with
      | Some mx, Some cur -> (
          match (int_of_string_opt mx, int_of_string_opt cur) with
          | Some mx, Some cur when is_limit mx ->
              let h = max 0 (mx - cur) in
              Some (match best with Some b -> min b h | None -> h)
          | _ -> best)
      | _ -> best)
    None dirs

(* [physical_bytes_at ~root]: [MemTotal] of [root/proc/meminfo] in bytes,
   [None] when unreadable *)
let physical_bytes_at ~root =
  match read_lines (root ^ "/proc/meminfo") with
  | None -> None
  | Some ls ->
      List.find_map
        (fun l ->
          let key = "MemTotal:" in
          let n = String.length key in
          if String.length l > n && String.sub l 0 n = key then
            match
              List.filter (fun s -> s <> "")
                (String.split_on_char ' ' (String.sub l n (String.length l - n)))
            with
            | kb :: _ -> Option.map (fun k -> k * 1024) (int_of_string_opt kb)
            | [] -> None
          else None)
        ls

(* [v1_memory_dir_at ~root rel]: the directory, under [root], of the cgroup
   v1 memory hierarchy holding the cgroup path [rel], read off
   [root/proc/self/mountinfo]: the first mount of filesystem type [cgroup]
   whose super options name the [memory] controller.  A mount's own root (the
   fourth field; not "/" inside a container that sees only a subtree) is
   stripped from [rel]; [None] when no such mount exists or [rel] lies
   outside the mounted subtree.  Mountinfo's fields are "id parent dev root
   mount-point options [optional fields] - fstype source super-options". *)
let v1_memory_dir_at ~root rel =
  match read_lines (root ^ "/proc/self/mountinfo") with
  | None -> None
  | Some ls ->
      List.find_map
        (fun l ->
          let fields = String.split_on_char ' ' l in
          let rec after_dash = function
            | "-" :: rest -> Some rest
            | _ :: rest -> after_dash rest
            | [] -> None
          in
          match (fields, after_dash fields) with
          | _ :: _ :: _ :: mroot :: mpoint :: _, Some ("cgroup" :: _ :: sopts :: _)
            when List.mem "memory" (String.split_on_char ',' sopts) ->
              if mroot = "/" then Some (root ^ mpoint, rel)
              else
                let n = String.length mroot in
                if
                  String.length rel >= n
                  && String.sub rel 0 n = mroot
                  && (String.length rel = n || rel.[n] = '/')
                then Some (root ^ mpoint, String.sub rel n (String.length rel - n))
                else None
          | _ -> None)
        ls

(* [cgroup_headroom_bytes_at ~root ()]: the headroom of this process's
   cgroups, every absolute path read prefixed by [root] (["" ] for the real
   system; a test passes a directory holding a fake tree).

   What it reads, from the lines of [/proc/self/cgroup]:
   - cgroup v2 (the line "0::PATH"): for PATH and every ancestor below the
     root, [/sys/fs/cgroup/DIR/memory.max] less [memory.current]; a
     [memory.max] of "max" is no limit.
   - cgroup v1 (a line "N:CONTROLLERS:PATH" whose comma-separated
     controllers include [memory]): for PATH and every ancestor below the
     hierarchy's root, inside the memory hierarchy's mount point
     ([v1_memory_dir_at]), [memory.limit_in_bytes] less
     [memory.usage_in_bytes].  v1 writes "unlimited" as a huge number
     (9223372036854771712 on a 4 KB-page kernel, beyond OCaml's [int]); any
     limit above physical memory ([MemTotal] of [/proc/meminfo]) is no limit,
     since it can never be the one that is reached first.  Ancestors count
     because v1 charges a child to its ancestors (hierarchical accounting,
     the only mode of current kernels).
   Result: the least headroom over every limit found in either version
   (both are read on a hybrid system; a v2 path whose directories carry no
   [memory.max] contributes nothing), [None] when there is none.  On a system
   with only v2 the v1 reading finds no [memory] line and the result is the v2
   reading alone. *)
let cgroup_headroom_bytes_at ~root () =
  match read_lines (root ^ "/proc/self/cgroup") with
  | None -> None
  | Some lines ->
      let v2 =
        match
          List.find_opt
            (fun l -> String.length l > 3 && String.sub l 0 3 = "0::")
            lines
        with
        | Some l ->
            let rel = String.sub l 3 (String.length l - 3) in
            least_headroom ~limit_file:"memory.max"
              ~usage_file:"memory.current" ~is_limit:(fun _ -> true)
              (List.map
                 (fun d -> root ^ "/sys/fs/cgroup" ^ d)
                 (path_prefixes rel))
        | None -> None
      in
      let v1 =
        let memory_path l =
          match String.split_on_char ':' l with
          | _ :: ctrls :: (_ :: _ as rest)
            when List.mem "memory" (String.split_on_char ',' ctrls) ->
              Some (String.concat ":" rest)
          | _ -> None
        in
        match List.find_map memory_path lines with
        | None -> None
        | Some rel -> (
            match v1_memory_dir_at ~root rel with
            | None -> None
            | Some (mount, rel) ->
                let is_limit =
                  match physical_bytes_at ~root with
                  | Some phys -> fun mx -> mx <= phys
                  | None -> fun _ -> true
                in
                least_headroom ~limit_file:"memory.limit_in_bytes"
                  ~usage_file:"memory.usage_in_bytes" ~is_limit
                  (List.map (fun d -> mount ^ d) (path_prefixes rel)))
      in
      match (v2, v1) with
      | Some a, Some b -> Some (min a b)
      | (Some _ as h), None | None, (Some _ as h) -> h
      | None, None -> None

let cgroup_headroom_bytes () = cgroup_headroom_bytes_at ~root:"" ()

let fork_fits ~heap_bytes ~headroom =
  match headroom with None -> true | Some h -> heap_bytes <= h

(* the bytes of this domain's major heap, as [Gc.quick_stat] reports them *)
let major_heap_bytes () = (Gc.quick_stat ()).Gc.heap_words * (Sys.word_size / 8)

(* the largest the major heap has been in this process, in bytes *)
let top_heap_bytes () =
  (Gc.quick_stat ()).Gc.top_heap_words * (Sys.word_size / 8)

(* [process_alive pid]: [pid] names a process that still holds its memory --
   it exists and is neither a zombie ([Z]) nor dead ([X]) in
   [/proc/PID/stat]; false when that file cannot be read *)
let process_alive pid =
  match read_first_line (Printf.sprintf "/proc/%d/stat" pid) with
  | None -> false
  | Some l -> (
      (* the state is the first field after the parenthesised command name,
         which may itself contain spaces and parentheses *)
      match String.rindex_opt l ')' with
      | Some i when i + 2 < String.length l -> (
          match l.[i + 2] with 'Z' | 'X' -> false | _ -> true)
      | _ -> false)

let () = ended_for_grace := fun pid -> not (process_alive pid)

(* [private_bytes pid]: the memory [pid] holds as its own, the
   [Private_Clean] plus [Private_Dirty] lines of [/proc/PID/smaps_rollup]:
   the pages mapped by that process alone, which for a forked copy are the
   pages it (or its parent, writing the shared original) has copied since
   the fork.  [None] when the file cannot be read *)
let private_bytes pid =
  match open_in (Printf.sprintf "/proc/%d/smaps_rollup" pid) with
  | exception Sys_error _ -> None
  | ic ->
      let total = ref 0 and seen = ref false in
      (try
         while true do
           let l = input_line ic in
           let field name =
             let n = String.length name in
             if String.length l > n && String.sub l 0 n = name then
               match
                 List.filter (fun s -> s <> "")
                   (String.split_on_char ' '
                      (String.sub l n (String.length l - n)))
               with
               | kb :: _ -> (
                   match int_of_string_opt kb with
                   | Some k ->
                       seen := true;
                       total := !total + (k * 1024)
                   | None -> ())
               | [] -> ()
           in
           field "Private_Clean:";
           field "Private_Dirty:"
         done
       with End_of_file | Sys_error _ -> ());
      close_in_noerr ic;
      if !seen then Some !total else None

(* The readings the fit test takes, as functions so that a test can replace
   them by fixed figures ([readings]); [real_readings] reads this process and
   its cgroups as described above. *)
type readings = {
  headroom : unit -> int option;
  heap : unit -> int;
  top_heap : unit -> int;
  alive : int -> bool;
  charged : int -> int option;
}

let real_readings =
  {
    headroom = cgroup_headroom_bytes;
    heap = major_heap_bytes;
    top_heap = top_heap_bytes;
    alive = process_alive;
    charged = private_bytes;
  }

let readings = ref real_readings

(* The shared budget of the copies alive at once.

   Every fork made through [fork_reserving] records, in the process that
   forked, the copy's pid and the bytes the copy was expected to come to hold
   as its own when it was forked (its reservation).  A copy keeps the records
   it inherits: its siblings and cousins charge the same cgroups it does.  A
   record whose process is gone (exited, a zombie, unreadable) is dropped at
   the next reading, so no reaping site has to release it.

   [pending_bytes ()] is what the live copies may still add to the cgroups:
   the sum, over live records, of the reservation less what the copy already
   holds as its own ([charged]; the whole reservation when that cannot be
   read).  The part already held is in [memory.current], hence in the
   headroom, so the two are not counted twice. *)
let reservations : (int * int) list Atomic.t = Atomic.make []

let rec update_reservations f =
  let s = Atomic.get reservations in
  if not (Atomic.compare_and_set reservations s (f s)) then
    update_reservations f

let reserve pid bytes = update_reservations (fun s -> (pid, max 0 bytes) :: s)

let pending_bytes () =
  let r = !readings in
  update_reservations (List.filter (fun (pid, _) -> r.alive pid));
  List.fold_left
    (fun acc (pid, bytes) ->
      let held = match r.charged pid with Some c -> c | None -> 0 in
      acc + max 0 (bytes - held))
    0 (Atomic.get reservations)

(* [peak_excess_bytes ()]: how far above its current major heap this
   process's major heap has already been ([top_heap - heap], never
   negative).  The estimate of a copy's own growth for a copy that does work
   of the kind the process has done (a probe or a pass that preprocesses and
   solves the problem again, a raced copy that may continue the whole run):
   such a copy may come to need the heap the process once needed. *)
let peak_excess_bytes () =
  let r = !readings in
  max 0 (r.top_heap () - r.heap ())

(* [copy_need ?growth ()]: the bytes a copy forked now is expected to come to
   hold as its own: the whole major heap, which its collector writes, plus
   [growth] (an estimate of what it allocates beyond that; 0 by default) *)
let copy_need ?(growth = 0) () = !readings.heap () + max 0 growth

(* [fits_figures ~headroom ~need ~pending]: the decision, from figures:
   [headroom = None] (no limit to break) or [need + pending <= h] *)
let fits_figures ~headroom ~need ~pending =
  match headroom with None -> true | Some h -> need + pending <= h

(* [fits ?growth ()]: may a copy be forked now?

   Guarantee (under no other process's growth): when it holds and the copy is
   forked at once, then even if every live copy grows to its reservation and
   the new copy holds [copy_need ?growth ()] bytes of its own, no cgroup on
   this process's path exceeds the limit read now -- the headroom is read
   after the live copies' current holding is already charged, and their
   remaining growth ([pending_bytes]) and the new copy's need are added.
   With no readable limit it holds.

   What it estimates and does not bound: a copy's own allocation beyond its
   duplicate heap is [growth], which the caller supplies (0 by default;
   [peak_excess_bytes] where the copy repeats the process's work); memory
   outside the OCaml heap (Z3's own) is not counted; the growth of the
   process that forks, and of processes outside this one's copies (a parked
   parent, another run in the same slice), is seen only through what they
   already hold.  So it errs high when a copy ends before its first major
   cycle, and low when the copy or its parent allocates beyond the estimate;
   a test that holds can still be followed by a cap kill, but a test that
   fails names a copy the readings say cannot fit. *)
let fits ?growth () =
  let r = !readings in
  fits_figures ~headroom:(r.headroom ()) ~need:(copy_need ?growth ())
    ~pending:(pending_bytes ())

(* forks refused by [fits] in this process, for the phase account and tests *)
let refused = Atomic.make 0

(* [fork_reserving ~bytes ()] is [fork ()] that, in the parent, records the
   copy's reservation of [bytes] in the shared budget ([reserve]) *)
let fork_reserving ~bytes () =
  match fork () with
  | `In_the_child -> `In_the_child
  | `In_the_parent pid as p ->
      reserve (Core.Pid.to_int pid) bytes;
      p
