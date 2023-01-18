(* the commutativity of max *)
let max x y = if x > y then x else y
let main x y = assert (max x y = max y x)

[@@@assert "typeof(main) <: int -> int -> unit"]
