(* An application beside an independent recursive function in one let rec group. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let rec loop n = if n <= 0 then 0 else loop (n - 1) and b = identity zero
let run n = b (loop n) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
