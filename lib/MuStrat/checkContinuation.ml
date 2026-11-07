(* The schedule of a strategy check continued in a forked copy
   ([continue_check_in_copy]), kept apart from the race itself so that it can
   be checked by plain arithmetic.

   Setting.  Without the field, a check is asked at budget [b]; when it runs
   out, the run handles the timeout (other questions about the same
   strategies) and asks the same check again, from nothing, at [2b], then
   [4b], and so on.  So a check that needs [T] seconds of the solver is
   decided at the first rung [b * 2^k >= T].  With the field, one copy asks
   the check once with no budget, and the rungs become points in the copy's
   running time at which the process stops waiting for it.

   Every function here takes and returns times in seconds (floats) or
   milliseconds/budgets (ints); none reads a clock. *)

open Core

(* [rung_budget ~initial ~elapsed]: the smallest [initial * 2^k] (k >= 0) that
   is at least [elapsed], the budget of the rung at which the doubling
   schedule starting at [initial] decides a check needing [elapsed] seconds.
   [initial] below 1 is read as 1.  Postcondition: the result is [initial]
   (so read) when [elapsed <= initial], and otherwise is the least power-of-two
   multiple of it that is [>= elapsed]; a result that would overflow stops at
   the largest such multiple representable, which is already far beyond any
   check's running time. *)
let rung_budget ~initial ~elapsed =
  let rec go b =
    if Float.(of_int b >= elapsed) || b > Int.max_value / 2 then b
    else go (2 * b)
  in
  go (Int.max 1 initial)

let ms_of_s s =
  if Float.(s <= 0.) then 0
  else if Float.(s >= 1e9) then 1_000_000_000_000
  else Float.iround_up_exn (s *. 1000.)

(* [hold_ms ~budget ~elapsed]: how long a copy that decided the check
   [elapsed] seconds after it started waits before it claims the run: until
   [budget] seconds have passed since the start.  The process asks the same
   check of the same solver with budget [budget] at the same time, so a copy
   deciding before that point claims only once the process's own ask has
   either decided (the copy is then killed) or run out.  Never negative; 0
   when that point has passed. *)
let hold_ms ~budget ~elapsed = Int.max 0 ((budget * 1000) - ms_of_s elapsed)

(* [wait_ms ~budget ~elapsed]: at the retry of the check at budget [budget]
   (seconds), how long the process waits for the copy, which has been asking
   the check for [elapsed] seconds: until the copy has run [budget] seconds,
   the time the retry would have been given.  0 when it already has. *)
let wait_ms ~budget ~elapsed = Int.max 0 ((budget * 1000) - ms_of_s elapsed)
