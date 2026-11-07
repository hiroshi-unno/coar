(* A false assertion about the reference sibling's contents is refuted. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let b = identity zero and r = ref 0
let run n = assert (!r = 1); b (n + !r) (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
