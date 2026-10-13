(* Annotations and application forms isolate the higher-order instantiation boundary. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let zero n k = 0.0
let b = identity zero
let run n = b n (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
