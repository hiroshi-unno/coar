[@@@mode "hfl_prop_as_probability"]

(* An expected-cost term (one unit of cost per step) declared as a probability:
   p * k () + (1 - p) * (1 + f () k) has weights summing to 3/2, so it is not a
   sub-probability term and the probability mode refuses it before solving. *)
let p = 0.5
let rec f x k = p *. k () +. (1.0 -. p) *. (1.0 +. f () k)

[@@@assert "typeof(f) <: unit -> (unit -> { r : prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 1.0 }"]
