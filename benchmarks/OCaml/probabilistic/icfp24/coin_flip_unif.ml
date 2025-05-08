[@@@mode "hfl_prop_as_expectation"]

external unif : (float -> float) -> float = "unknown"
let rec f x k = unif (fun p -> p *. k () +. (1.0 -. p) *. (1.0 +. f () k))

[@@@assert "typeof(f) <: unit -> (unit -> { r : prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 1.0 }"]
