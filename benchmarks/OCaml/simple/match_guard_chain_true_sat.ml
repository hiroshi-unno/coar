(* 4 fails the first guard and passes the second, which answers 2. *)
let f (x : int) = match x with n when n > 5 -> 1 | n when n > 3 -> 2 | _ -> 3
[@@@assert "typeof(f) <: { x : int | x = 4 } -> { r : int | r = 2 }"]
