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
   a run that is not nested is untouched.  The deadline is process-wide
   (one [Atomic.t]), which is safe for the one caller there is -- a nested
   solve that already holds the process-global environment bracket, so no
   other solving call runs beside it.

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

let deadline : float option Atomic.t = Atomic.make None
let strict : bool Atomic.t = Atomic.make false
let pending : float option Atomic.t = Atomic.make None

(* seconds on [Common.Clock]: the time of day, or CLOCK_MONOTONIC when the
   process's clock switch is on; every deadline here is taken and read on it *)
let now () = Common.Clock.now_s ()

let expired () =
  match Atomic.get deadline with None -> false | Some d -> Float.(now () >= d)

let expired_strict () = Atomic.get strict && expired ()

(* whether this run is a nested one bounded by a deadline *)
let active () = Option.is_some (Atomic.get deadline)

(* the time left before a strict deadline, at least 1 ms; [None] without one *)
let remaining_ms_strict () =
  match Atomic.get deadline with
  | Some d when Atomic.get strict ->
      Some (Int.max 1 (Float.iround_down_exn ((d -. now ()) *. 1000.)))
  | _ -> None

(* the time left before any deadline, strict or not, at least 1 ms; [None]
   without one *)
let remaining_ms () =
  match Atomic.get deadline with
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
  match Atomic.get pending with
  | None -> ()
  | Some p ->
      Atomic.set pending None;
      Atomic.set deadline
        (Some
           (match Atomic.get deadline with
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
   it; a probe answers only [unsat], so a cut probe loses nothing but its own
   chance to refute.  Off ([false]), nothing reads it, and with no strict
   deadline set it never raises. *)
let in_preprocessing : bool Atomic.t = Atomic.make false

exception Expired_in_preprocessing

let check_in_preprocessing () =
  if Atomic.get in_preprocessing && expired_strict () then
    raise Expired_in_preprocessing

(* [with_preprocessing_check on f] runs [f] with [in_preprocessing] set to
   [on] (or kept, when it is already set) and restores it on every exit *)
let with_preprocessing_check on f =
  let saved = Atomic.get in_preprocessing in
  Atomic.set in_preprocessing (saved || on);
  Exn.protect ~finally:(fun () -> Atomic.set in_preprocessing saved) ~f

let within ?(strict_budget = false) ?after_first_round ~seconds f =
  let saved = Atomic.get deadline in
  let saved_strict = Atomic.get strict in
  let saved_pending = Atomic.get pending in
  let start = now () in
  let mine = start +. seconds in
  let d = match saved with Some d' when Float.(d' < mine) -> d' | _ -> mine in
  Atomic.set deadline (Some d);
  Atomic.set strict (saved_strict || strict_budget);
  Atomic.set pending (Option.map after_first_round ~f:(fun s -> start +. s));
  let restore () =
    Atomic.set deadline saved;
    Atomic.set strict saved_strict;
    Atomic.set pending saved_pending
  in
  match f () with
  | v ->
      restore ();
      v
  | exception e ->
      restore ();
      raise e
