(* The guarded case answers its scrutinee only when it is positive. *)
let f (x : int) = match x with n when n > 0 -> n | _ -> 1
[@@@assert "typeof(f) <: int -> { r : int | r > 0 }"]
