(* Ordinary partial correctness imposes no return bound on a diverging call. *)
[@@@mode "ocaml"]
let identity f = f
let rec zero (n : int) (k : int -> float) : float = zero n k
let b = identity zero
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
