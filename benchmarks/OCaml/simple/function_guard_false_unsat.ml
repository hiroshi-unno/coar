(* A guard of a [function] case: Some 0 matches [Some y] and fails the guard,
   so the second case answers 0, not 1. *)
let g = function Some y when y > 0 -> 1 | Some _ -> 0 | None -> 0
let f (x : int) = g (Some x)
[@@@assert "typeof(f) <: int -> { r : int | r = 1 }"]
