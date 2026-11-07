(* The reading of a strategy check asked again, after it timed out, of a
   verdict-only solver whose rule transformations are on.

   Contract: [won ask] is [true] exactly when [ask ()] returns [Ok (Sat _, _)],
   the check's win (the query of the CHC not derivable).  Every other outcome
   -- a counter-play, an unsatisfiable answer without one, [Unknown],
   [Timeout], an error, or an exception that is not asynchronous -- is [false]
   and carries nothing out: a derivation claimed through transformed rules is
   not one of the original rules, so no counter-play from such a solver may
   reach the refinement.  An asynchronous exception (the caller's timeout, an
   interrupt) is re-raised, as everywhere else in a timed region. *)

open Core

let won (ask : unit -> (PCSP.Problem.solution * int) Or_error.t) =
  try
    match ask () with
    | Ok (PCSP.Problem.Sat _, _) -> true
    | Ok _ | Error _ -> false
  with exn when not (Common.Timer.is_async exn) -> false

(* The reading of a strategy check asked again, after it timed out, of a
   solver that differs from the ordinary check's only in a Spacer parameter
   and reads its answer back the same way (the plain Spacer of
   [reask_undecided_check_plain_spacer]: global guidance off, every rule
   transformation off as in the ordinary check, a counterexample requested).

   Contract: [answer ask] is [Some r] exactly when [ask ()] returns [Ok r]
   with [r] a win ([Sat _]) or a counter-play with its derivation
   ([Unsat (Some (Formula _))]); such an answer is read as the ordinary
   check's would be.  Every other outcome -- [Unknown], [Timeout], an
   unsatisfiable answer without a derivation, an error, or an exception
   that is not asynchronous -- is [None]: it decides nothing, and the
   caller handles its timeout as it would without the re-ask.  An
   asynchronous exception is re-raised. *)
let answer (ask : unit -> (PCSP.Problem.solution * int) Or_error.t) =
  try
    match ask () with
    | Ok ((PCSP.Problem.Sat _, _) as r)
    | Ok ((PCSP.Problem.Unsat (Some (PCSP.Problem.Formula _)), _) as r) ->
        Some r
    | Ok _ | Error _ -> None
  with exn when not (Common.Timer.is_async exn) -> None
