(* Ordinary OCaml permits the second scalar to shadow the first. *)
let marker = 10
let marker = 1
let run (n : int) = marker + (n - n)
[@@@assert "typeof(run) <: int -> { ret : int | ret = 1 }"]
