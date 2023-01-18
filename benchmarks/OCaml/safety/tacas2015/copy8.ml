let id x = x
let succ x = x + 1
let comp f g x = f (g x)
let rec copy f x =
  if x = 0 then
    f 0
  else
     copy (comp succ f) (x - 1)
let main x = assert (copy id x = x)

[@@@assert "typeof(main) <: int -> unit"]
