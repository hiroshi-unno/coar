let f x y = assert (not (x>0 && y<=0))
let g x = f x x

[@@@assert "typeof(g) <: int -> unit"]
