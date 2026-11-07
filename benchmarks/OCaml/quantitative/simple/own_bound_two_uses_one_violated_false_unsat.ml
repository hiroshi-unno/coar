(* The second use violates the bound; the first stays satisfiable. *)
[@@@mode "hfl_prop_as_expectation"]
let restrict f = fun n k -> assert (n >= 0); f n k
let rec zero n k = zero n k
let b = restrict zero
let run_a n = b 2 (fun _ -> 0.0)
let run_b n = b (-3) (fun _ -> 0.5)
[@@@assert "typeof(run_a) <: int -> { ret : prop | ret <= 1.0 }"]
[@@@assert "typeof(run_b) <: int -> { ret : prop | ret <= 1.0 }"]
