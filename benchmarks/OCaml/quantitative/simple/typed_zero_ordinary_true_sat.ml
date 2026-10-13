(* An unused annotated function argument must permit this true upper bound. *)
let zero (n : int) (k : int -> float) = 0.0
[@@@assert "typeof(zero) <: int -> (int -> { r : float | r = 0.0 }) -> { ret : float | ret <= 1.0 }"]
