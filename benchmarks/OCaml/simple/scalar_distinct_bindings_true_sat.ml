(* Distinct predicate names are the control for scalar_shadow_true_sat.ml. *)
let initial_marker = 10
let marker = 1
let run (n : int) = marker + (n - n)
[@@@assert "typeof(run) <: int -> { ret : int | ret = 1 }"]
