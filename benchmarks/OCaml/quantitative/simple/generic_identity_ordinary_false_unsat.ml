(* An ordinary identity application cannot make zero satisfy a positive lower bound. *)
[@@@mode "ocaml"]
let identity f = f
let zero n k = 0.0
let b = identity zero
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
