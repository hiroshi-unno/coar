let id x = x
let succ x = x + 1
let comp f g x = f (g x)
let rec copy x f =
  if x = 0 then
    f 0
  else
     copy (x - 1) (comp succ f)
let main x = assert (copy x id = x)

[@@@assert "typeof(main) <: int -> unit"]
