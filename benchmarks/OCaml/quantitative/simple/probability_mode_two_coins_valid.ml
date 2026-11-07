[@@@mode "hfl_prop_as_probability"]

(* The probability that two independent coins (biased 1/2 and 1/3) agree, as a
   convex combination of the continuation's answers: a sub-probability term,
   accepted by the probability mode and typed as in the expectation mode. *)
let p1 = 1.0 /. 2.0
let p2 = 1.0 /. 3.0
let coins k =
  p1 *. (p2 *. k 0 0 +. (1.0 -. p2) *. k 0 1) +. (1.0 -. p1) *. (p2 *. k 1 0 +. (1.0 -. p2) *. k 1 1)

[@@@assert "typeof(coins) <: ((x:int) -> (y:int) -> { r : prop | x = y && r = 1.0 || x <> y && r = 0.0 }) -> { ret : prop | ret = 0.5 }"]
