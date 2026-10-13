[@@@mode "hfl_prop_as_expectation"]

(* [loop]'s value is the least fixed point of [fun r -> 0 + r], which is 0, so
   the asserted lower bound 1 is false.  [loop] is let-polymorphic (its
   continuation is unused) and [b] is its second instance: the admissibility
   the fixpoint rule needs must hold at every instance, not only the first,
   or the second instance's return refinement may be empty and the bound
   holds vacuously (this input was answered sat). *)
let rec loop n k = 0.0 +. loop n k

let a = loop

let b = loop
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
