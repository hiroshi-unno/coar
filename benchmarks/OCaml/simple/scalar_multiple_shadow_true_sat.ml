(* Each repeated declaration needs its own refinement predicate identity. *)
let marker = 10
let marker = 2
let marker = 1
let run (n : int) = marker + (n - n)
[@@@assert "typeof(run) <: int -> { ret : int | ret = 1 }"]
