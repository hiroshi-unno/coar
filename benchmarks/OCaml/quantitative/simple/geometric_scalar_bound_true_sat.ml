(* The expected number of failed flips before a fair coin's first success
   is at most 1 (it is exactly 1).  The constraints left after predicate
   elimination are linear over reals, with a constant bound. *)
[@@@mode "hfl_prop_as_expectation"]

let p = 0.5
let rec f x k = p *. k () +. (1.0 -. p) *. (1.0 +. f () k)

[@@@assert "typeof(f) <: unit -> (unit -> { r : prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 1.0 }"]
