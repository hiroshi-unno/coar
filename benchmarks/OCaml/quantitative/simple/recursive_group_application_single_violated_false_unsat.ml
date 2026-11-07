(* A single let rec application with a violated own bound. *)
[@@@mode "hfl_prop_as_expectation"]
let restrict f = fun n k -> assert (n >= 0); f n k
let rec zero n k = zero n k
let rec b = restrict zero
let run n = b (-1) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
