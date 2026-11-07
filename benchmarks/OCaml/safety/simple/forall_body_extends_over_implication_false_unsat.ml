(* A quantifier's body extends as far right as possible:
   [_forall k:int. k = n => v > n] is [forall k. (k = n => v > n)], which is
   [v > n].  Here [v = n], so the assertion fails.  Read with the quantifier
   stopping before [=>], it would be [(forall k. k = n) => v > n], whose
   premise is false, and the assertion would hold vacuously. *)
let f n = n

[@@@assert "typeof(f) <: (n:int) -> {v:int | _forall k:int. k = n => v > n}"]
