let rec f g x = if x>=0 then g x else f (f g) (g x)
let succ x = x+1
let main n = assert (f succ n >= 0)

[@@@assert "typeof(main) <: int -> unit"]
