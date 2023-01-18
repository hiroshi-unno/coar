let f g h = if g 0 = h 0 then () else assert false
let add x y = x + y
let main n = f (add n) (add n)

[@@@assert "typeof(main) <: int -> unit"]
