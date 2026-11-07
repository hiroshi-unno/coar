(* The clock that durations and deadlines are measured on.

   Two clocks are available to a process.  The time of day (CLOCK_REALTIME,
   what [gettimeofday], [Time_float.now] and [Time_ns.now] read) can be
   stepped: where a virtual machine's own clock runs slow and the host's time
   synchronisation corrects it, the time of day jumps forward by seconds at a
   time (observed: about 3 s every 35 s, the guest's clock running about 10%
   slow).  CLOCK_MONOTONIC is never stepped, and it is the clock every relative
   timer counts in: `timeout`, [alarm], [nanosleep] and a solver's own budget.
   A deadline taken on the time of day therefore fires up to one step early
   against those timers, and a duration taken on it includes every step that
   fell inside it.

   Every reader below reads CLOCK_MONOTONIC.  Its contract:

   - the four readers ([now_s], [now_float], [now_ns], [time_s]) return the
     same instant of CLOCK_MONOTONIC, as seconds, a [Time_float.t] or a
     [Time_ns.t] from an arbitrary origin (the boot), so the values mean
     nothing as dates and must only be compared with or subtracted from
     other readings of this module;
   - for two readings [a] then [b] of this module, [b -. a] is the time
     that elapsed between them, and no step of the time of day enters it.

   Exactness of a budget.  A budget of [n] seconds is a start reading [s] and
   the test [now () >= s +. n] (or [now () -. s >= n]).  Both sides are
   readings of this one clock, so the test holds exactly when [n] seconds
   have elapsed since [s] -- the meaning the budget always had, now without
   the time of day's steps, which made a deadline fire up to one step early
   against `timeout`, [alarm] and a solver's own budget, all of which count
   on CLOCK_MONOTONIC too.  Nothing may compare a reading of this module
   with a time-of-day value: a timestamp meant for a person (a date in a
   log) is not a duration and is read from the time of day directly, never
   from here and never against a reading from here.

   The time of day is kept for tests only: [set_monotonic false] moves the
   readers back to it (each then returns exactly what the call it replaced
   returned: [now_s] [Core_unix.gettimeofday ()], [now_float]
   [Time_float.now ()], [now_ns] [Time_ns.now ()], [time_s]
   [Core_unix.time ()]), or to a stand-in installed with
   [set_time_of_day_source], which is how a test injects a stepped or fixed
   clock.  A test that switches restores the setting before any solver
   reading is taken; switching while a deadline taken under the other
   setting is live makes that deadline meaningless. *)

open Core

external monotonic_s : unit -> (float[@unboxed])
  = "coar_monotonic_seconds" "coar_monotonic_seconds_unboxed"
[@@noalloc]

let monotonic = ref true

(* for tests only (see above): set before the readings it affects are taken *)
let set_monotonic b = monotonic := b

let is_monotonic () = !monotonic

(* for tests only: a stand-in for the time of day, in seconds *)
let time_of_day_source : (unit -> float) option ref = ref None
let set_time_of_day_source src = time_of_day_source := src

let now_s () =
  if !monotonic then monotonic_s ()
  else
    match !time_of_day_source with
    | None -> Core_unix.gettimeofday ()
    | Some f -> f ()

let float_of_s s =
  Time_float.of_span_since_epoch (Time_float.Span.of_sec s)

let ns_of_s s = Time_ns.of_int_ns_since_epoch (Float.to_int (s *. 1e9))

let now_float () =
  if !monotonic then float_of_s (monotonic_s ())
  else
    match !time_of_day_source with
    | None -> Time_float.now ()
    | Some f -> float_of_s (f ())

let now_ns () =
  if !monotonic then ns_of_s (monotonic_s ())
  else
    match !time_of_day_source with
    | None -> Time_ns.now ()
    | Some f -> ns_of_s (f ())

(* whole seconds under the time of day, as [Core_unix.time] gives them *)
let time_s () =
  if !monotonic then monotonic_s ()
  else
    match !time_of_day_source with
    | None -> Core_unix.time ()
    | Some f -> Float.round_down (f ())
