(* How many times each kind of phase has been started in this process: the
   coordinator counts a phase each time it hands one a continuing state.

   A diagnostic, read by tests to say in which order the loop did its work
   (for instance, that an answer came before any synthesis phase ran); no
   solving decision reads it.  It is process-wide and counts every solve,
   nested ones included, so a reader resets it before the solve it is about and
   reads it after.  The counters are atomic, since parallel domains run phases
   at once. *)

let synthesis = Atomic.make 0
let validation = Atomic.make 0

let reset () =
  Atomic.set synthesis 0;
  Atomic.set validation 0
