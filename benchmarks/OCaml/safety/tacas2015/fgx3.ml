let rec  f g x = if x=0 then (if true then g x else g x) else f(f g) (x-1)
let succ x = x + 1
let main () = assert(f succ 5 = 0)

[@@@assert "typeof(main) <: unit -> unit"]
