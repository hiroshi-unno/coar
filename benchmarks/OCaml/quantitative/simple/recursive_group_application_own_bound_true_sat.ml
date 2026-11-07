(* The application own bound (its argument is nonnegative) holds at the call after the recursive group. *)
[@@@mode "hfl_prop_as_expectation"]
let restrict f = fun n k -> assert (n >= 0); f n k
let rec zero n k = zero n k
let rec loop n = if n <= 0 then 0 else loop (n - 1) and b = restrict zero
let run n = b (loop n + 1) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
