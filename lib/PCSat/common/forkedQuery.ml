open Core

(* Run a computation in a forked copy of this process and give up on it after
   a wall-clock budget, killing the copy.

   Why a process: a Z3 call over a formula that binds a sequence under a
   quantifier can run in the sequence theory's own loops without reaching the
   points where Z3 checks its [timeout] parameter or a cancellation, and the
   alarm-based timer of this tree cannot interrupt a foreign call either.  One
   such validation query was observed running for minutes under a 5 s budget,
   with every sample of a profile inside the sequence theory.  Killing a
   process is the one bound that holds whatever the callee does.

   Contract: [run ~ms f] returns [Some (f ())] when a forked copy computed it
   and sent it back within [ms] milliseconds, and [None] when the copy ran out
   of time, died, raised, or could not be forked.  The copy is always killed
   and reaped before [run] returns or raises (an exception from the parent's
   own timer included).  [f] runs in the copy, so any state it changes --
   solver contexts, global tables, counters -- is changed in the copy only and
   the parent continues exactly as if [f] had not been called; the value is
   sent back with [Marshal] (closures allowed, the copy being this very
   program).  So [f] must return a value that survives marshalling, and a
   value of an EXTENSIBLE variant does not: its constructor is matched by
   the identity of a slot created at start-up, the unmarshalled value carries
   a copy of that slot, and every match on it falls to the catch-all -- a
   solver model sent back whole raised "unknown sort" on its first use.  Send
   back plain data (a verdict, an integer, a string) and recompute the rest in
   the parent.  Output buffered before the call is flushed first, so that it
   is not written twice.

   What it relies on: the copy is forked from a process with one running
   domain (OCaml refuses to fork otherwise, and [run] then answers [None]; the
   phase-time account therefore watches with a thread, not a domain, and
   [Common.PhaseTime.around_fork] switches it off in the copy);
   interval timers are not inherited by a forked process, so the parent's
   alarm cannot fire in the copy; and the copy leaves through
   [Common.ProcessExit.immediately] (an [_exit]), so no finaliser or exit
   hook of the parent, OCaml or C, runs twice;
   and the copy never outlives this process, whatever kills it
   ([Common.ForkGuard.fork]), so a run stopped mid-question leaves no solver
   running.
   A Z3 call made in the copy should not arm Z3's own timer: the thread that
   serves it does not exist in a forked process, so the timer cannot fire, and
   its teardown may wait for that thread (expected from the design of Z3's
   timer, not observed); the kill is the budget instead. *)

(* the forked copies alive now, so that a process about to exit on another's
   behalf ([ParallelRace]) or on a SIGTERM report can kill them at once; a copy
   also dies with its parent whatever kills the latter ([Common.ForkGuard]) *)
let kill_live = Common.ForkGuard.kill_live

(* [fits_or_count ?growth ()]: [Common.ForkGuard.fits ?growth ()], and when
   it fails the refusal is counted ([Common.ForkGuard.refused]) and shown in
   the phase account as the event [fork-refused/memory], so that a question
   not asked for want of memory is never silent *)
let fits_or_count ?growth () =
  Common.ForkGuard.fits ?growth ()
  || begin
       Atomic.incr Common.ForkGuard.refused;
       Common.PhaseTime.event_here "fork-refused/memory";
       false
     end

(* [run_forked ?growth ~ms f] is [run] with the two ways of getting nothing
   told apart: [`Value v] when a forked copy computed [v = f ()] and sent it
   back within [ms] milliseconds; [`Lost] when a copy was forked and ran out
   of time, died or raised (it has been killed and reaped); [`Not_forked]
   when no copy could be made (no pipe, or a fork refused, as OCaml refuses
   one while other domains run, or a copy that does not fit the memory
   budget: [Common.ForkGuard.fits ?growth ()] fails, [growth] being the
   caller's estimate of what the copy allocates beyond its duplicate heap, 0
   by default), in which case [f] has not run anywhere and a caller may run
   it in this process instead.  A copy that is forked reserves its expected
   size in the budget for as long as it lives. *)
let run_forked ?growth ~ms (f : unit -> 'a) :
    [ `Value of 'a | `Lost | `Not_forked ] =
  Stdlib.flush_all ();
  if not (fits_or_count ?growth ()) then `Not_forked
  else
  match Core_unix.pipe () with
  | exception exn when not (Common.Timer.is_async exn) -> `Not_forked
  | rd, wr -> (
      (* the fork's own cost, charged in the parent only: the child leaves the
         frame open in an account that is off there *)
      let fork_tok = Common.PhaseTime.start "fork" in
      let bytes = Common.ForkGuard.copy_need ?growth () in
      match
        Common.PhaseTime.around_fork
          (Common.ForkGuard.fork_reserving ~bytes)
      with
      | exception exn when not (Common.Timer.is_async exn) ->
          Common.PhaseTime.stop fork_tok;
          Core_unix.close rd;
          Core_unix.close wr;
          `Not_forked
      | `In_the_child ->
          let started = Common.PhaseTime.now () in
          Core_unix.close rd;
          (try
             let payload =
               Stdlib.Marshal.to_string (f ()) [ Stdlib.Marshal.Closures ]
             in
             let oc = Core_unix.out_channel_of_descr wr in
             Stdlib.output_string oc payload;
             Stdlib.flush oc
           with exn when not (Common.Timer.is_async exn) ->
             (* the parent reads a copy that raised as one that sent nothing
                (its caller's undecided answer); with [COAR_FORK_EXN] set
                (instrument only) the exception is named on stderr, so that
                a question that fails is told apart from one that runs out *)
             if Option.is_some (Sys.getenv "COAR_FORK_EXN") then (
               prerr_endline ("forked-query-raised: " ^ Exn.to_string exn);
               Stdlib.flush stderr));
          Common.PhaseTime.child_line ~started;
          Common.ProcessExit.immediately 0
      | `In_the_parent pid ->
          Common.PhaseTime.stop fork_tok;
          Common.ForkGuard.register (Pid.to_int pid);
          Core_unix.close wr;
          let reaped = ref false in
          let buf = Buffer.create 4096 in
          let chunk = Bytes.create 65536 in
          let deadline =
            Time_float.add (Common.Clock.now_float ())
              (Time_float.Span.of_ms (Float.of_int ms))
          in
          Exn.protect
            ~f:(fun () ->
              (* [true] once the copy closed its end, i.e. sent everything *)
              let rec read_until_eof () =
                let left = Time_float.diff deadline (Common.Clock.now_float ()) in
                if Time_float.Span.(left <= zero) then false
                else
                  let ready =
                    Core_unix.select ~restart:true ~read:[ rd ] ~write:[]
                      ~except:[]
                      ~timeout:
                        (`After
                           (Time_ns.Span.of_sec (Time_float.Span.to_sec left)))
                      ()
                  in
                  if List.is_empty ready.read then read_until_eof ()
                  else
                    let n = Core_unix.read rd ~buf:chunk ~pos:0 ~len:65536 in
                    if n = 0 then true
                    else (
                      Buffer.add_subbytes buf chunk ~pos:0 ~len:n;
                      read_until_eof ())
              in
              if Common.PhaseTime.with_phase "wait" read_until_eof then (
                ignore (Core_unix.waitpid pid : Core_unix.Exit_or_signal.t);
                reaped := true;
                if Buffer.length buf = 0 then `Lost
                else `Value (Stdlib.Marshal.from_string (Buffer.contents buf) 0))
              else `Lost)
            ~finally:(fun () ->
              let quietly g =
                try g () with exn when not (Common.Timer.is_async exn) -> ()
              in
              quietly (fun () -> Core_unix.close rd);
              if not !reaped then (
                (* under COAR_COPY_REPORT the copy is first given its grace
                   to report; nothing otherwise *)
                Common.ForkGuard.term_first [ Pid.to_int pid ];
                quietly (fun () -> Signal_unix.send_i Signal.kill (`Pid pid));
                quietly (fun () ->
                    ignore (Core_unix.waitpid pid : Core_unix.Exit_or_signal.t)));
              Common.ForkGuard.unregister (Pid.to_int pid))
      )

let run ?growth ~ms (f : unit -> 'a) : 'a option =
  match run_forked ?growth ~ms f with
  | `Value v -> Some v
  | `Lost | `Not_forked -> None

(* [first_in_copy ~ms ~event ~ask ~here_for ~label ~lost] answers one solver
   question [ask], first in a forked copy killed after [ms] milliseconds.

   A WORKAROUND for Z3 5.1.0 (the newest z3 in opam-repository): in a context
   that has been in a scope (a push, a reset), Z3 can ignore its own
   [timeout] on a question that reads a sequence under a quantifier and grow
   without bound in this process; remove it, with the fields that select it
   ([pins.seq_lengths.fork_unreturning],
   [preprocessor.elimination.questions.fork.seq_unreturning]), when the
   reproducer row for
   [benchmarks/SMT/simple/z3_seq_pin_scoped_timeout_unsat.smt2] in
   [script/rerun_external_reproducers.sh] reports GONE for the z3 that opam
   installs.

   [ask ~timeout] is the question asked in process with that Z3 budget; the
   copy asks [ask ~timeout:copy_timeout] ([None]: no Z3 timer, the kill is the
   budget).  A caller passes its own budget as [copy_timeout] (and a kill
   [ms] beyond it) when the question must be the same computation as in
   process: Z3 chooses its strategy by whether a timeout is set, and an
   elimination question asked with no timeout ran to its kill in a copy where
   the same question with its 5 s budget was answered in milliseconds in
   process.  Z3's timer thread is not copied by [fork], so in the copy the
   timeout may not fire: the kill bounds it either way.  An answer the copy can send back ([here_for r] false: a
   verdict, a reason, no model, since a value of extensible variants does not
   survive marshalling) is returned as it is; an answer with [here_for r] (one
   carrying a model) is asked again here, [ask ~timeout:(Some ms)], from the
   state the copy was forked from, so a model is always an in-process one.  A
   copy that runs out, dies or raises gives [lost], which the caller chooses
   to be the answer it reads as a timeout; when no copy can be made (another
   domain runs, or the copy does not fit the memory budget, with the
   process's peak excess as the copy's growth) the question is asked here as
   without the copy.  Each outcome is counted as the phase event
   [<event>/<label r>], [<event>/lost] or [<event>/not-forked].
   Contract: every answer returned is one [ask] gave, in the copy or here,
   except [lost]; so a caller that reads [lost] as it reads a timeout decides
   nothing the in-process call would not have decided before the kill. *)
let first_in_copy ~copy_timeout ~ms ~event
    ~(ask : timeout:int option -> 'r) ~(here_for : 'r -> bool)
    ~(label : 'r -> string) ~(lost : 'r) : 'r =
  let note s = Common.PhaseTime.event_here (event ^ "/" ^ s) in
  match
    run_forked ~growth:(Common.ForkGuard.peak_excess_bytes ()) ~ms (fun () ->
        let r = ask ~timeout:copy_timeout in
        if here_for r then `Here (label r) else `Sent r)
  with
  | `Value (`Here l) ->
      note l;
      ask ~timeout:(Some (Option.value copy_timeout ~default:ms))
  | `Value (`Sent r) ->
      note (label r);
      r
  | `Lost ->
      note "lost";
      lost
  | `Not_forked ->
      note "not-forked";
      ask ~timeout:(Some (Option.value copy_timeout ~default:ms))

(* [kill_ms ~kill_ms ~timeout] is the wall-clock budget after which the
   validator kills a forked copy asking a counterexample query whose own budget
   is [timeout] (10 s when none is set).  With [kill_ms = None] it is that
   budget, as before.  With [kill_ms = Some k] it is the larger of the two, so
   the copy is never killed before the query's own budget and a query that
   overruns its budget but does return -- which an in-process call waits for --
   is given up to [k] ms.  The copy asks without a Z3 timer, so what it sends
   back within the kill budget is what an unbounded in-process call would
   answer. *)
let kill_ms ~kill_ms ~timeout =
  let budget = Option.value timeout ~default:10000 in
  match kill_ms with None -> budget | Some k -> Int.max budget k

(* [ladder_kill_ms ~floor ~margin ~timeout] is the wall-clock budget after
   which the zero-unknown ladder kills a forked copy asking a question whose
   own budget is [timeout] ms: with [margin = None] the larger of [floor] and
   [timeout], so that no copy is killed before [floor]; with [margin = Some m]
   the budget plus [max m 0], whatever [floor] is, so that a short budget --
   a first pass asked at a fraction of the full one -- bounds the copy as Z3's
   own timeout bounds a question asked in process, the margin covering what
   the copy does besides the solver call.  Never below [timeout] either way:
   a copy is not killed before the question's own budget runs out. *)
let ladder_kill_ms ~floor ~margin ~timeout =
  match margin with
  | None -> Int.max floor timeout
  | Some m -> timeout + Int.max m 0

(* [valid_within ~ms ask] asks a validity question [ask] (a function of no
   argument returning the answer of [Z3interface.check_valid]'s kind) in a
   forked copy killed after [ms] milliseconds, for a caller that reads only a
   proof: [`Valid] when the copy answered valid, [`Timeout] when it was killed,
   died or could not be forked, and [`Unknown reason] for every other answer, a
   refutation included (its model, a value of extensible variants, does not
   survive the trip back; see [run]).  Contract: the result is [`Valid] only if
   [ask ()] returned [`Valid] in the copy, so a caller that treats every other
   result as undecided loses only proofs [ask] would have given after [ms]. *)
(* The reason [valid_within] gives for a copy whose question was answered
   invalid: the copy's countermodel is not sent back, so the answer comes back
   undecided, and [is_invalid_reason] tells this undecided answer from the
   others (a caller may treat it as the in-process [`Invalid] it was). *)
let invalid_reason = "invalid in a forked copy (its model not sent back)"
let is_invalid_reason r = String.equal r invalid_reason

(* [fallback_unless_invalid ~skip ~fallback answer] is [fallback answer],
   except that with [skip] an answer a forked copy reported invalid is
   returned as it is, as [Z3interface.with_seq_axiom_fallback] returns an
   in-process [`Invalid]: a fallback that can only turn an undecided answer
   into a proof has nothing to prove on a question with a countermodel. *)
let fallback_unless_invalid ~skip ~fallback answer =
  match answer with
  | `Unknown r when skip && is_invalid_reason r -> answer
  | _ -> fallback answer

let valid_within ~ms ask =
  match
    run ~ms (fun () ->
        match ask () with
        | `Valid -> `V
        | `Invalid _ -> `K invalid_reason
        | `Timeout -> `T
        | `Unknown r -> `K r
        | `Sat _ | `Unsat -> `K "unexpected answer")
  with
  | Some `V -> `Valid
  | Some `T | None -> `Timeout
  | Some (`K r) -> `Unknown r

(* [race ~ms ~decisive fs] runs every [f] of [fs] in a forked copy of its own,
   all at once, and returns [Some v] for the first value [v] a copy sends back
   with [decisive v], or [None] when every copy has sent back an undecisive
   value, died, raised, or not finished within [ms] milliseconds.  Copies
   share the memory budget ([Common.ForkGuard.fits]): each is forked only if
   it fits beside the copies already forked; one that does not is asked after
   the race, in a copy of its own ([run_forked]) within what is left of [ms],
   once the racing copies are gone, and is not asked at all only when it does
   not fit then either (counted, [fits_or_count]).  So memory changes only
   when a question is asked, never which values it may return.  Contract:
   when [race] returns or raises, every copy it forked has been killed and
   reaped -- the losers at the moment a decisive value arrives -- so no copy
   outlives the call; and each copy also dies with this process whatever
   kills it ([Common.ForkGuard.fork]).  The values cross [Marshal] as in [run], with the same
   restriction (no extensible-variant value). *)
let race ~ms ~decisive (fs : (unit -> 'a) list) : 'a option =
  Stdlib.flush_all ();
  let started_kids = ref [] in
  let quietly g = try g () with exn when not (Common.Timer.is_async exn) -> () in
  let kill_all () =
    (* under COAR_COPY_REPORT the copies still running are first given their
       grace to report, all at once; nothing otherwise *)
    Common.ForkGuard.term_first
      (List.filter_map !started_kids ~f:(fun (pid, _, reaped) ->
           if !reaped then None else Some (Pid.to_int pid)));
    List.iter !started_kids ~f:(fun (pid, rd, reaped) ->
        quietly (fun () -> Core_unix.close rd);
        if not !reaped then (
          quietly (fun () -> Signal_unix.send_i Signal.kill (`Pid pid));
          quietly (fun () ->
              ignore (Core_unix.waitpid pid : Core_unix.Exit_or_signal.t));
          reaped := true);
        Common.ForkGuard.unregister (Pid.to_int pid))
  in
  let started_at = Common.Clock.now_float () in
  (* the questions that did not fit beside the copies already racing *)
  let deferred = ref [] in
  let raced =
  Exn.protect ~finally:kill_all ~f:(fun () ->
      List.iter fs ~f:(fun f ->
          if not (Common.ForkGuard.fits ()) then deferred := f :: !deferred
          else
          match Core_unix.pipe () with
          | exception exn when not (Common.Timer.is_async exn) -> ()
          | rd, wr -> (
              let bytes = Common.ForkGuard.copy_need () in
              match
                Common.PhaseTime.around_fork
                  (Common.ForkGuard.fork_reserving ~bytes)
              with
              | exception exn when not (Common.Timer.is_async exn) ->
                  Core_unix.close rd;
                  Core_unix.close wr
              | `In_the_child ->
                  let started = Common.PhaseTime.now () in
                  Core_unix.close rd;
                  (try
                     let payload =
                       Stdlib.Marshal.to_string (f ()) [ Stdlib.Marshal.Closures ]
                     in
                     let oc = Core_unix.out_channel_of_descr wr in
                     Stdlib.output_string oc payload;
                     Stdlib.flush oc
                   with exn when not (Common.Timer.is_async exn) -> ());
                  Common.PhaseTime.child_line ~started;
                  Common.ProcessExit.immediately 0
              | `In_the_parent pid ->
                  Common.ForkGuard.register (Pid.to_int pid);
                  Core_unix.close wr;
                  started_kids :=
                    (pid, rd, ref false) :: !started_kids));
      let deadline =
        Time_float.add (Common.Clock.now_float ()) (Time_float.Span.of_ms (Float.of_int ms))
      in
      let bufs = Hashtbl.Poly.create () in
      let chunk = Bytes.create 65536 in
      (* the copies still running, by their read end *)
      let rec loop open_ =
        let left = Time_float.diff deadline (Common.Clock.now_float ()) in
        if List.is_empty open_ || Time_float.Span.(left <= zero) then None
        else
          let ready =
            Core_unix.select ~restart:true
              ~read:(List.map open_ ~f:(fun (_, rd, _) -> rd))
              ~write:[] ~except:[]
              ~timeout:(`After (Time_ns.Span.of_sec (Time_float.Span.to_sec left)))
              ()
          in
          let rec take open_ = function
            | [] -> loop open_
            | rd :: rest -> (
                let ((pid, _, reaped) as kid) =
                  List.find_exn open_ ~f:(fun (_, r, _) ->
                      Core_unix.File_descr.equal r rd)
                in
                let buf =
                  Hashtbl.find_or_add bufs pid ~default:(fun () -> Buffer.create 4096)
                in
                let n = Core_unix.read rd ~buf:chunk ~pos:0 ~len:65536 in
                if n > 0 then (
                  Buffer.add_subbytes buf chunk ~pos:0 ~len:n;
                  take open_ rest)
                else (
                  ignore (Core_unix.waitpid pid : Core_unix.Exit_or_signal.t);
                  reaped := true;
                  let open_ =
                    List.filter open_ ~f:(fun k -> not (phys_equal k kid))
                  in
                  if Buffer.length buf = 0 then take open_ rest
                  else
                    let v = Stdlib.Marshal.from_string (Buffer.contents buf) 0 in
                    if decisive v then Some v else take open_ rest))
          in
          take open_ ready.read
      in
      Common.PhaseTime.with_phase "race-wait" (fun () -> loop !started_kids))
  in
  match raced with
  | Some _ -> raced
  | None ->
      (* one at a time, in their order, each within what is left of [ms] *)
      List.fold (List.rev !deferred) ~init:None ~f:(fun acc f ->
          match acc with
          | Some _ -> acc
          | None -> (
              let left =
                ms
                - Float.iround_down_exn
                    (Time_float.Span.to_ms
                       (Time_float.diff (Common.Clock.now_float ()) started_at))
              in
              if left <= 0 then None
              else
                match run_forked ~ms:left f with
                | `Value v when decisive v -> Some v
                | `Value _ | `Lost | `Not_forked -> None))
