let g y = assert (y () <= 0)
let f x y = if (x () > 0) then g y else ()
let h x y = x
let rec main n = f (h n) (h n)

[@@@assert "typeof(main) <: int -> unit"]
