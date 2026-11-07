(* The expected number of failed flips before a fair coin's first success
   is exactly 1, so the bound 1/2 asserted here is false: no solver may
   answer sat. *)
[@@@mode "hfl_prop_as_expectation"]

let p = 0.5
let rec f x k = p *. k () +. (1.0 -. p) *. (1.0 +. f () k)

[@@@assert "typeof(f) <: unit -> (unit -> { r : prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 0.5 }"]
