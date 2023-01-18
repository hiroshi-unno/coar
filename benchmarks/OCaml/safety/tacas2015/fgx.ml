let rec f g x = if x<=0 then g x else f(f g) (x-1)
let succ x = x+1
let main () = assert (f succ 2 <1)

[@@@assert "typeof(main) <: unit -> unit"]
