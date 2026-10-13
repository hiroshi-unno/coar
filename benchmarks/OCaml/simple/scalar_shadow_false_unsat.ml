(* The final scalar is 1, not the shadowed value 10. *)
let marker = 10
let marker = 1
let run (n : int) = marker + (n - n)
[@@@assert "typeof(run) <: int -> { ret : int | ret = 10 }"]
