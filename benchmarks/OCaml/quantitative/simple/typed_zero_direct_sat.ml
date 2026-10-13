(* A zero-valued function satisfies the upper bound even when its unused
   function argument has an ordinary OCaml type annotation. *)
[@@@mode "hfl_prop_as_expectation"]
let zero (n : int) (k : int -> float) = 0.0
[@@@assert "typeof(zero) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= 1.0 }"]
