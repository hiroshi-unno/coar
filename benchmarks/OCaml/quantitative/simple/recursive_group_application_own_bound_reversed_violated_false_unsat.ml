(* As the violated own-bound group, with the application first. *)
[@@@mode "hfl_prop_as_expectation"]
let restrict f = fun n k -> assert (n >= 0); f n k
let rec zero n k = zero n k
let rec b = restrict zero and loop n = if n <= 0 then 0 else loop (n - 1)
let run n = b (loop n - 1) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
