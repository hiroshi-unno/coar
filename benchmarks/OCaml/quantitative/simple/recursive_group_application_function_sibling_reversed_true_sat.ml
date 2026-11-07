(* As the function-sibling group, with the application first. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let rec b = identity zero and loop n = if n <= 0 then 0 else loop (n - 1)
let run n = b (loop n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
