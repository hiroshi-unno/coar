(* Shadowed function templates also receive distinct predicate identities. *)
let marker x = x + 10
let marker x = x + 1
let run (n : int) = marker 0 + (n - n)
[@@@assert "typeof(run) <: int -> { ret : int | ret = 1 }"]
