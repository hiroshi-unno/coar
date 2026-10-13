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

   [set_monotonic true] moves every reader below to CLOCK_MONOTONIC.  It is a
   process-wide switch, off by default, meant to be set once before solving
   starts (from the solver's configuration, which every solve of a process
   shares).  Its contract:

   - off: each reader returns exactly what the call it replaced returned
     ([now_s] is [Core_unix.gettimeofday ()], [now_float] is
     [Time_float.now ()], [now_ns] is [Time_ns.now ()], [time_s] is
     [Core_unix.time ()]), unless a test has installed a source of the time of
     day with [set_time_of_day_source], in which case all four are derived
     from it;
   - on: all four read CLOCK_MONOTONIC, so the difference of two readings is
     elapsed time that no time-of-day step enters; the values are seconds (or
     a [Time_float.t]/[Time_ns.t]) from an arbitrary origin, so they mean
     nothing as dates and must only be compared with or subtracted from other
     readings of this module.

   Hence every reading that is compared with another reading (a deadline
   against a later [now], a start against an end) must come from this module
   and from the same setting of the switch; changing the switch while a
   deadline taken under the other setting is live makes that deadline
   meaningless.  A timestamp meant for a person (a date in a log) is not a
   duration and is read from the time of day directly, not from here. *)

open Core

external monotonic_s : unit -> (float[@unboxed])
  = "coar_monotonic_seconds" "coar_monotonic_seconds_unboxed"
[@@noalloc]

let monotonic = ref false

(* set before the readings it affects are taken (see above) *)
let set_monotonic b = monotonic := b

(* [configure b]: the setting a solver's configuration asks for.  Only the
   first call of a process has an effect, so that a nested solve whose own
   configuration says otherwise cannot switch clocks under the deadlines the
   outer solve has already taken; [set_monotonic] (for tests) is not bound by
   it. *)
let configured = ref false

let configure b =
  if not !configured then (
    configured := true;
    monotonic := b)
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

(* whole seconds, as [Core_unix.time] gives when off *)
let time_s () =
  if !monotonic then monotonic_s ()
  else
    match !time_of_day_source with
    | None -> Core_unix.time ()
    | Some f -> Float.round_down (f ())
