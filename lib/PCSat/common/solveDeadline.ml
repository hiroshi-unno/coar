open Core

(* A wall-clock deadline for a constraint-solving run that is started from
   inside another one, checked cooperatively by the CEGIS loop at every phase
   boundary.

   Why cooperative rather than the alarm-based timer: that timer masks an
   enclosing timeout while a nested one is armed, so arming it here would
   silently suspend the run-wide time limit for as long as the nested run
   lasts.  A deadline read between phases cannot interfere with anything; its
   price is granularity -- a single phase that does not return (one synthesis
   step, one solver call) is not cut short, only the next phase is not
   started.

   Contract: [within ~seconds f] runs [f] with the deadline set to now plus
   [seconds] and restores the previous deadline on every exit, raising
   included.  A nested [within] can only shorten the deadline, never extend
   the enclosing one.  [expired ()] is [false] whenever no deadline is set, so
   a run that is not nested is untouched.  Every piece of state here is per
   domain: MuVal solves its primal and its dual side at once in two domains,
   and a probe on one side that set a process-wide deadline stopped the other
   side's CEGIS loop at its next phase boundary, which then answered
   [timeout] long before the run's own limit.  A domain spawned while a
   deadline is set inherits the spawning domain's state, so work a nested
   solve hands to a fresh domain is bounded as before; a domain that already
   exists (a pool's worker) keeps its own.

   A deadline set with [~strict_budget:true] is also read inside a phase: the
   synthesizer's own retry loop gives up at [expired_strict ()], and each of
   its solver calls is given at most [remaining_ms_strict ()].  Without that a
   synthesis step that keeps failing never returns to a phase boundary, and a
   nested solve given ten seconds was measured still running after 150.  The
   labeling phase reads it the same way: the evaluation of a new atom against
   every qualifier ([TruthTable]) and the pairing of positive with negative
   parametric atoms stop asking once it has passed, and give each call at most
   what is left ([cap_ms_strict]); an unasked evaluation is an undecided
   cell and an unasked pair is no conflict, so only answers can be lost.  A
   non-strict deadline leaves both [None]/[false], so behaviour is unchanged
   unless the caller asks.

   A deadline set with [~after_first_round:s] also holds a second, shorter
   one, [s] seconds from the start, that takes effect only when the CEGIS
   loop reports the end of a round without an answer ([round_ended ()]):
   from then on the deadline is the earlier of the two.  The first round is
   bounded by [seconds] alone.  The pending deadline is saved and restored
   with the other two, so [round_ended ()] outside such a [within] does
   nothing.  Pending round deadlines belong to their own [within]: an inner
   round does not consume an outer run's pending deadline.  The inner run
   inherits only the already active deadline and strictness; returning or
   raising restores the outer pending deadline. *)

(* one cell per domain, a spawned domain's initialised from its parent's
   current value *)
let per_domain init =
  let key =
    Domain.DLS.new_key
      ~split_from_parent:(fun a -> Atomic.make (Atomic.get a))
      (fun () -> Atomic.make init)
  in
  fun () -> Domain.DLS.get key

let deadline_cell : unit -> float option Atomic.t = per_domain None
let strict_cell : unit -> bool Atomic.t = per_domain false
let pending_cell : unit -> float option Atomic.t = per_domain None

(* seconds on [Common.Clock] (CLOCK_MONOTONIC outside tests); every deadline
   here is taken and read on it, so [expired] holds exactly when the budget's
   seconds have elapsed since [within] took its reading *)
let now () = Common.Clock.now_s ()

let expired () =
  match Atomic.get (deadline_cell ()) with None -> false | Some d -> Float.(now () >= d)

let expired_strict () = Atomic.get (strict_cell ()) && expired ()

(* whether this run is a nested one bounded by a deadline *)
let active () = Option.is_some (Atomic.get (deadline_cell ()))

(* the time left before a strict deadline, at least 1 ms; [None] without one *)
let remaining_ms_strict () =
  match Atomic.get (deadline_cell ()) with
  | Some d when Atomic.get (strict_cell ()) ->
      Some (Int.max 1 (Float.iround_down_exn ((d -. now ()) *. 1000.)))
  | _ -> None

(* the time left before any deadline, strict or not, at least 1 ms; [None]
   without one *)
let remaining_ms () =
  match Atomic.get (deadline_cell ()) with
  | Some d -> Some (Int.max 1 (Float.iround_down_exn ((d -. now ()) *. 1000.)))
  | None -> None

(* a solver call's budget [ms] (milliseconds, [None] for none) capped by the
   time left before a strict deadline; [ms] itself without one. The solver's
   zero timeout is unbounded, so it takes the remainder just like [None]. *)
let cap_ms_strict ms =
  match (remaining_ms_strict (), ms) with
  | None, ms -> ms
  | Some r, (None | Some 0) -> Some r
  | Some r, Some ms -> Some (Int.min r ms)

(* the end of a CEGIS round that gave no answer: a pending deadline set by
   [within ~after_first_round] takes effect, never extending the current one *)
let round_ended () =
  match Atomic.get (pending_cell ()) with
  | None -> ()
  | Some p ->
      Atomic.set (pending_cell ()) None;
      Atomic.set (deadline_cell ())
        (Some
           (match Atomic.get (deadline_cell ()) with
           | Some d when Float.(d < p) -> d
           | _ -> p))

(* Whether the preprocessing reads a strict deadline.  A probe's nested solve
   is bounded by a strict deadline, but the deadline is read only by the CEGIS
   loop and its phases, and the preprocessing runs before the loop's first
   phase: a probe given 60 s was measured still eliminating predicates at 113 s,
   so the solve it was meant to precede never started.  With this set, the
   predicate eliminator calls [check_in_preprocessing] before each predicate it
   resolves away and before each resolvent it normalises, and a strict deadline
   that has passed raises [Expired_in_preprocessing].  That exception is not
   asynchronous ([Common.Timer.is_async] is [false] on it), so the probe's own
   handler, which turns any ordinary exception into a discarded answer, catches
   it; a probe reads one verdict of its solve and discards the other (the
   upper-bound, true-precondition and least-definition probes read only
   [sat]), so a cut probe loses nothing but the answer it might have read
   after its own budget, never a verdict of the run.  Off ([false]), nothing reads it, and with no strict
   deadline set it never raises. *)
let in_preprocessing_cell : unit -> bool Atomic.t = per_domain false
let in_preprocessing () = Atomic.get (in_preprocessing_cell ())

exception Expired_in_preprocessing

(* The answer-neutral event raised where an enforcing switch ends work that
   would otherwise have gone on past a strict deadline: a phase report (or a
   forked copy's child-event line) then shows that the switch changed the run,
   and a run without it did what it would have done with the switch off. *)
let cut () = Common.PhaseTime.event_here ~in_copy:true "strict-deadline-cut"

let check_in_preprocessing () =
  if in_preprocessing () && expired_strict () then (
    cut ();
    raise Expired_in_preprocessing)

(* [with_preprocessing_check on f] runs [f] with [in_preprocessing] set to
   [on] (or kept, when it is already set) and restores it on every exit *)
let with_preprocessing_check on f =
  let saved = in_preprocessing () in
  Atomic.set (in_preprocessing_cell ()) (saved || on);
  Exn.protect ~finally:(fun () -> Atomic.set (in_preprocessing_cell ()) saved) ~f

(* Whether the stage boundaries outside the predicate eliminator read a strict
   deadline: the boundaries between the preprocessing's passes, the building of
   the CEGIS loop's phases (template initialisation included) and the
   qualifier generator's loops over predicates and clauses.  Each of these runs
   before the loop's first phase boundary, so a probe whose preprocessing ends
   inside its budget could still spend the rest of a run building its
   templates.  With this set, [check_at_stage] at such a boundary raises
   [Expired_at_stage] once a strict deadline has passed; like
   [Expired_in_preprocessing] it is an ordinary exception, so the probe's
   handler catches it and discards the probe's answer, which is the only thing
   that can be lost.  A boundary is a safe point: no solver call is in flight
   and no shared structure is half updated, so raising there leaves nothing to
   repair.  A pass that does not return between two boundaries is not cut
   short.  Off ([false]), nothing reads it, and with no strict deadline set it
   never raises. *)
let at_stages_cell : unit -> bool Atomic.t = per_domain false
let at_stages () = Atomic.get (at_stages_cell ())

exception Expired_at_stage

let check_at_stage () =
  if at_stages () && expired_strict () then (
    cut ();
    raise Expired_at_stage)

(* [with_stage_check on f] runs [f] with [at_stages] set to [on] (or kept, when
   it is already set) and restores it on every exit *)
let with_stage_check on f =
  let saved = at_stages () in
  Atomic.set (at_stages_cell ()) (saved || on);
  Exn.protect ~finally:(fun () -> Atomic.set (at_stages_cell ()) saved) ~f

let within ?(strict_budget = false) ?after_first_round ~seconds f =
  let saved = Atomic.get (deadline_cell ()) in
  let saved_strict = Atomic.get (strict_cell ()) in
  let saved_pending = Atomic.get (pending_cell ()) in
  let start = now () in
  let mine = start +. seconds in
  let d = match saved with Some d' when Float.(d' < mine) -> d' | _ -> mine in
  Atomic.set (deadline_cell ()) (Some d);
  Atomic.set (strict_cell ()) (saved_strict || strict_budget);
  Atomic.set (pending_cell ()) (Option.map after_first_round ~f:(fun s -> start +. s));
  let restore () =
    Atomic.set (deadline_cell ()) saved;
    Atomic.set (strict_cell ()) saved_strict;
    Atomic.set (pending_cell ()) saved_pending
  in
  match f () with
  | v ->
      restore ();
      v
  | exception e ->
      restore ();
      raise e
