(* An ordinary identity application preserves zero's true upper bound. *)
[@@@mode "ocaml"]
let identity f = f
let zero n k = 0.0
let b = identity zero
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= 1.0 }"]
