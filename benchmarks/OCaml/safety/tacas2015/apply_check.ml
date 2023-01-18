let apply f x = f x
let check x y = assert (x = y)
let main n = apply (check n) n

[@@@assert "typeof(main) <: int -> unit"]
