(* The guarded case is not taken for x <= 0, which answers 0, not 1. *)
let f (x : int) = match x with n when n > 0 -> 1 | _ -> 0
[@@@assert "typeof(f) <: int -> { r : int | r = 1 }"]
