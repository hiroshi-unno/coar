open Core

(** {6 Timer} *)

let timers = ref []

let make () =
  let st = Core_unix.times () in
  fun () ->
    let en = Core_unix.times () in
    en.Core_unix.tms_utime -. st.Core_unix.tms_utime
    +. (en.Core_unix.tms_cutime -. st.Core_unix.tms_cutime)

let start () = timers := make () :: !timers

let stop () =
  match !timers with
  | [] -> assert false
  | tm :: tms ->
      timers := tms;
      tm ()

let get_user_time () =
  let en = Core_unix.times () in
  en.Core_unix.tms_utime +. en.Core_unix.tms_cutime

(** {6 Interval Timer} *)
let start_time = ref (Core_unix.times ()) (*dummy*)

let start_interval () = start_time := Core_unix.times ()

let stop_interval () =
  let en = Core_unix.times () in
  en.Core_unix.tms_utime -. !start_time.Core_unix.tms_utime
  +. (en.Core_unix.tms_cutime -. !start_time.Core_unix.tms_cutime)

exception Timeout

(* Exceptions that a [with _ ->] handler must never swallow: they carry the
   control flow of a timeout or an interrupt (or a resource exhaustion) and
   belong to the enclosing [enable_timeout] / driver, not to the local
   fallback.  Handlers inside timed regions are written
   [with e when not (Timer.is_async e) -> default]. *)
(* A timeout raised while a [~finally] clean-up runs comes wrapped:
   [Stdlib.Fun.protect] turns any exception of its [finally] into
   [Fun.Finally_raised e], and Base's [Exn.protect] turns a [finally]
   exception raised after the body raised into [Exn.Finally (body, final)].
   Wrapped, the timeout is matched by no [| Timeout ->] handler and is taken
   by every [when not (is_async e)] fallback as an ordinary failure, so a
   budget that ended in a clean-up crashed the run with an uncaught
   [Fun.Finally_raised Common.Timer.Timeout] instead of being answered as a
   timeout.  So a wrapper holding an asynchronous exception is asynchronous,
   and [unwrap_async] recovers the exception it carries. *)
let rec is_async = function
  | Timeout | Sys_unix.Break | Stack_overflow | Out_of_memory -> true
  | Stdlib.Fun.Finally_raised e -> is_async e
  | Base.Exn.Finally (a, b) -> is_async a || is_async b
  | _ -> false

(* [unwrap_async e]: the asynchronous exception a clean-up wrapper carries
   (the innermost one; of [Exn.Finally]'s two, the body's when both are), or
   [e] itself when it is not such a wrapper.  Never raises. *)
let rec unwrap_async e =
  match e with
  | Stdlib.Fun.Finally_raised e' when is_async e' -> unwrap_async e'
  | Base.Exn.Finally (a, _) when is_async a -> unwrap_async a
  | Base.Exn.Finally (_, b) when is_async b -> unwrap_async b
  | _ -> e

(* The interrupts alone: a timeout or a user break, without the resource
   exhaustions [is_async] also names.  For a handler that must let the
   caller's budget through but should still turn a stack or heap exhaustion
   into a local failure -- the solution checker, which runs after the answer
   is printed and must not end the run. *)
let is_interrupt = function Timeout | Sys_unix.Break -> true | _ -> false

(* [Option.try_with] with the asynchronous exceptions let through: [Some (f ())]
   when [f] returns, [None] when it raises an ordinary exception, and a
   [Timeout], break or resource exhaustion re-raised.  [Option.try_with]
   itself catches everything, so under an armed budget it turns a timeout
   raised anywhere inside [f] into [None] and the computation carries on past
   its deadline. *)
let try_with_sync f =
  match f () with
  | v -> Some v
  | exception exn_ when not (is_async exn_) -> None

let sigalrm_catched = ref false

let disable_timeout f arg =
  sigalrm_catched := false;
  let reset_sigalrm_handler =
    let old_handler =
      let sigalrm_delayed_handler =
        Stdlib.Sys.Signal_handle
          (fun _ -> (* Format.printf "Timeout!@,"; *) sigalrm_catched := true)
      in
      Stdlib.Sys.signal Stdlib.Sys.sigalrm sigalrm_delayed_handler
    in
    fun () -> Stdlib.Sys.set_signal Stdlib.Sys.sigalrm old_handler
  in
  try
    let ret = f arg in
    reset_sigalrm_handler ();
    if !sigalrm_catched then
      raise Timeout (* @todo may differ from the behavior of [old_handler] *)
    else ret
  with exc ->
    reset_sigalrm_handler ();
    raise exc

(** Set timeout for a function.
    E.g. Set 1 second time out to [hoge ()]
    {[ enable_timeout 1 ident ident
        (fun () -> hoge ())
        (fun time ret -> Format.printf "Fast (time = %f)" time)
        (fun time ret -> Format.printf "Too slow (time = %f)" time)
    ]}
    Setting timeout to 0 ignore timeout.
    Please note some counterintuitive points:
    {ul
      {- If the function call is nested, the previous timeout is masked }
      {- [Unix.sleep] do not tick [Unix.times] }
      {- The signal is delayed if [hoge ()] do not allocate memory (True?) }
    } *)
(* [keep_off_this_thread ()]: called first thing in a system thread that
   only watches (a race's watcher, the phase account's), so that the timer's
   signals ([SIGALRM], [SIGVTALRM]) are never handled in it.

   Why: the timer raises [Timeout] from the signal's OCaml handler in
   whichever thread of the domain next reaches a safe point, and a watcher
   waking every few milliseconds from [select] or [Thread.delay] is often
   that thread.  The exception then ends the watcher (or is read by its
   catch-all as its pipe failing) instead of interrupting the computation
   the budget was set for: a raced copy that had taken a run over killed
   itself at the first alarm of the run's next timed solve, and the timed
   solve itself ran past its budget.  The OCaml 5 runtime runs a signal's
   handler only in a thread that does not block the signal, so blocking
   both here leaves them to the main thread, the one that sets them.  This
   complements [enable_timeout]'s handler, which raises only in the thread
   that armed the alarm and otherwise re-arms it: with the signals blocked
   here a watcher never even takes the handler's turn.  Never raises; a
   refusal leaves the thread as it was. *)
let keep_off_this_thread () =
  try
    ignore
      (Caml_threads.Thread.sigmask Caml_unix.SIG_BLOCK
         [ Stdlib.Sys.sigalrm; Stdlib.Sys.sigvtalrm ]
        : int list)
  with _ -> ()

let already_set = ref false
(* if enable_timer is invoked from the call to main, it is just ignored *)

(* The end of the budget armed by the outermost active [enable_timeout], on
   the monotonic clock ([Clock.monotonic_s], the clock [alarm] counts in);
   [None] when no budget is armed (no [enable_timeout] active, or one with a
   timeout of 0, which arms none).  Kept beside the alarm because a forked
   child inherits this value but not the alarm: see [resume_budget_in_copy]. *)
let budget_deadline : float option ref = ref None

(* Deferral of the alarm during a clean-up ([protect]).  [owner_thread] is
   the thread that armed the outermost active [enable_timeout] (the only one
   its handler raises in); [defer_depth] counts the [protect] clean-ups that
   thread is inside; [deferred] records an alarm that arrived meanwhile.
   Only the owner thread changes [defer_depth], so the handler, which runs
   in that thread, reads a count no other thread writes. *)
let owner_thread : int option ref = ref None
let defer_depth = ref 0
let deferred = ref false

let in_owner_thread () =
  match !owner_thread with
  | Some o -> o = Caml_threads.Thread.(id (self ()))
  | None -> false

(* [protect ~finally f]: [Stdlib.Fun.protect ~finally f], except that the
   budget of [enable_timeout] cannot interrupt [finally].
   Contract: [finally] runs once, to its end, after [f] returns or raises.
   An alarm that arrives while [finally] runs (in the thread that armed it)
   is held and raised as [Timeout] as soon as the outermost such clean-up
   has returned, in place of [f]'s result, or of [f]'s exception when that
   is not itself asynchronous (an asynchronous one is already ending the
   computation and is raised unchanged, the held alarm dropped).  So the
   budget still ends the computation, a moment later, and never in the
   middle of a clean-up.  An ordinary exception of [finally] is raised as
   [Fun.Finally_raised], as [Fun.protect] does.
   Why: a clean-up that releases a pooled resource (a solver scope, a lease,
   a mutex) and is cut short by the alarm leaves the resource held, and
   [Fun.protect] hands the timeout on wrapped, where no handler recognises
   it.  Outside an armed budget, or in another thread, it is
   [Fun.protect]. *)
let protect ~(finally : unit -> unit) f =
  let run_finally () =
    if not (in_owner_thread ()) then (
      try finally () with e -> raise (Stdlib.Fun.Finally_raised e))
    else (
      incr defer_depth;
      let r = try Ok (finally ()) with e -> Error e in
      decr defer_depth;
      match r with
      | Ok () -> ()
      | Error e when is_async e -> raise (unwrap_async e)
      | Error e -> raise (Stdlib.Fun.Finally_raised e))
  in
  let take_deferred () =
    if !defer_depth = 0 && !deferred && in_owner_thread () then (
      deferred := false;
      raise Timeout)
  in
  match f () with
  | v ->
      run_finally ();
      take_deferred ();
      v
  | exception e ->
      let bt = Stdlib.Printexc.get_raw_backtrace () in
      run_finally ();
      if is_async e then (if !defer_depth = 0 then deferred := false)
      else take_deferred ();
      Stdlib.Printexc.raise_with_backtrace e bt

let enable_timeout timeout before after main normal_handler exc_handler =
  (* Reset to restart the previous counter *)
  Combinator.hook true before after (fun () ->
      if !already_set then main ()
      else
        let finish =
          let old_handler =
            (* OCaml runs a signal handler in whichever system thread reaches a
               safe point first, and the phase account's watcher and a race's
               monitor threads keep running while this thread is inside a
               solver call that released the runtime lock.  Raised there,
               [Timeout] killed that thread and this one never saw its budget
               end.  So the handler raises only in the thread that armed the
               alarm; in any other thread it re-arms the timer for 50 ms, so the
               signal comes again until it lands in this thread, which happens
               once this thread runs OCaml code while the others sleep (the
               watcher and the monitors spend almost all their time in short
               sleeps). *)
            let owner = Caml_threads.Thread.(id (self ())) in
            let sigalrm_handler =
              Stdlib.Sys.Signal_handle
                (fun _ ->
                  if Caml_threads.Thread.(id (self ())) = owner then (
                    (* inside a [protect] clean-up: held until it returns *)
                    if !defer_depth > 0 then deferred := true
                    else raise Timeout)
                  else
                    ignore
                      (Caml_unix.setitimer Caml_unix.ITIMER_REAL
                         { Caml_unix.it_interval = 0.0; it_value = 0.05 }
                        : Caml_unix.interval_timer_status))
            in
            Stdlib.Sys.signal Stdlib.Sys.sigalrm sigalrm_handler
          in
          owner_thread := Some Caml_threads.Thread.(id (self ()));
          deferred := false;
          fun () ->
            ignore @@ Core_unix.alarm 0;
            already_set := false;
            budget_deadline := None;
            owner_thread := None;
            deferred := false;
            Stdlib.Sys.set_signal Stdlib.Sys.sigalrm old_handler
        in
        start ();
        already_set := true;
        budget_deadline :=
          if timeout > 0 then
            Some (Clock.monotonic_s () +. Float.of_int timeout)
          else None;
        ignore @@ Core_unix.alarm timeout;
        (*print_endline (string_of_float timeout);*)
        match main () with
        | ret ->
            finish ();
            normal_handler (stop ()) ret
        | exception exc ->
            finish ();
            (* a timeout that reached here wrapped by a clean-up is this
               budget's timeout all the same *)
            exc_handler (stop ()) (unwrap_async exc))

(* The budget across a fork that continues the computation.

   POSIX gives a forked child no pending alarm, but the child inherits
   everything else of [enable_timeout]'s state: the SIGALRM handler that
   raises [Timeout], [already_set], the handlers of the callers above, and
   [budget_deadline].  A forked copy that answers one question and is killed
   by its parent needs no budget of its own.  A forked copy that takes the run
   over from its parent -- it returns to the parent's caller and runs the rest
   of the program in the parent's place -- does: without one, a caller that
   asked for an answer within its budget (a strategy check of MuStrat, RCaml
   with a timeout) is never interrupted again once the copy has the run.

   Contract.
   - [resume_budget_in_copy ()], called in a forked child at the point it takes
     the computation over, arms the alarm for what is left of the budget that
     was armed in the parent at the fork ([budget_deadline] minus now on the
     monotonic clock, at least 1 ms, so a budget that ran out while the copy
     waited fires at once).  [Timeout] is then raised in the child exactly
     where the parent's alarm would have raised it, and travels through the
     same handlers to the same timed-out answer the parent would have given.
     With no budget armed at the fork it does nothing, so a run without a
     caller budget is unchanged.  The alarm resolution is that of [setitimer]
     (the parent's [alarm] counts whole seconds, so the copy's deadline is the
     parent's to within the scheduling of two clock readings).
   - [disarm_for_hand_over ()], called in the parent once it has handed the run
     to a copy, cancels its alarm and ignores SIGALRM from then on: the
     parent answers nothing more, and a [Timeout] raised in it afterwards would
     travel to the caller's handler and print a second, timed-out answer beside
     the copy's.  The copy carries the budget instead. *)
let resume_budget_in_copy () =
  match !budget_deadline with
  | Some deadline when !already_set ->
      let left = Float.max 0.001 (deadline -. Clock.monotonic_s ()) in
      ignore
        (Caml_unix.setitimer Caml_unix.ITIMER_REAL
           { Caml_unix.it_interval = 0.0; it_value = left }
          : Caml_unix.interval_timer_status)
  | Some _ | None -> ()

let disarm_for_hand_over () =
  if !already_set then (
    Stdlib.Sys.set_signal Stdlib.Sys.sigalrm Stdlib.Sys.Signal_ignore;
    ignore @@ Core_unix.alarm 0)

(* the time left of the armed budget, in seconds, [None] when no budget is
   armed; a native call that cannot be interrupted by the alarm (a Z3 tactic
   with the runtime released) takes it as its own bound *)
let remaining_budget () =
  match !budget_deadline with
  | Some deadline when !already_set ->
      Some (Float.max 0. (deadline -. Clock.monotonic_s ()))
  | Some _ | None -> None

(*(** Set timeout for a function.
      E.g. Set 1 second time out to [hoge ()]
    {[ Timer.block ~timeout:1 id id
        (fun () -> hoge ())
        (fun time ret -> Format.printf "Fast (time = %f)" time)
        (fun time ret -> Format.printf "Too slow (time = %f)" time)
  ]}
          Setting timeout to 0. ignore timeout.
          Please note some counterintuitive points:
          {ul
          {- If the block is nested, the previous timeout is masked }
          {- [Unix.sleep] do not tick [Unix.times] }
          {- The signal is delayed if [hoge ()] do not allocate memory (True?) }
          } *)
     let block ?(timeout = 0.) before after main normal_handler exc_handler =
     (* Reset to restart the previous counter *)
     let reset_to_previous_timer prev elapsed =
     let prev = {
     Unix.it_interval = 0.0;
     Unix.it_value =
      if prev.Unix.it_value = 0.0
      then prev.Unix.it_value (* Time was not set *)
      else
        let tmp = prev.Unix.it_value -. elapsed in
        if tmp <= 0.0 then 0.0 else tmp }
     in
     let _ = Unix.setitimer Unix.ITIMER_VIRTUAL prev in
     ()
     in
     hook true before after
     (fun () ->
     let t = Unix.ITIMER_VIRTUAL in
     let s = {
       Unix.it_interval = 0.0; (* Disable after its next expiration *)
       Unix.it_value = timeout;
     } in
     let prev = Unix.setitimer t s in
     Sys.set_signal Sys.sigvtalrm sigalrm_handler;
     start ();
     match main () with
     | ret ->
       let elapsed = stop () in
       reset_to_previous_timer prev elapsed;
       normal_handler elapsed ret
     | exception exc ->
       let elapsed = stop () in
       reset_to_previous_timer prev elapsed;
       exc_handler elapsed exc)*)
