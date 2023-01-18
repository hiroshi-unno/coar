let rec f g x = if g x>=3 then assert false else f (f g) (g x)
let rec succ x = x+1
let main () = f succ 0

[@@@assert "typeof(main) <: unit -> int"]
