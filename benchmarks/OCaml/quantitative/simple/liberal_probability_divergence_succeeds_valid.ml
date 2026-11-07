[@@@mode "hfl_prop_as_liberal_probability"]

(* A loop that never stops: its least fixed point (the probability of
   terminating with success) is 0 and its greatest fixed point (the
   probability of not failing, divergence counted as success) is 1.  The
   liberal-probability mode reads the greatest fixed point, so the lower
   bound 1 holds. *)
let rec spin k = spin k

[@@@assert "typeof(spin) <: (unit -> { r : prop | r = 0.0 }) -> { ret : prop | ret >= 1.0 }"]
