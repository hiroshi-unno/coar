let apply f x = f x
let add x y = x + y
let main x = assert (apply (add x) 0 >= x)

[@@@assert "typeof(main) <: int -> unit"]
