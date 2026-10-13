[@@@mode "hfl_prop_as_expectation"]

external unif : (float -> float) -> float = "unknown"
let f () = unif (fun p -> if p >= 0.5 then 1.0 else 0.0)

[@@@assert "typeof(f) <: unit -> { ret : prop | ret <= 1.1 }"]
