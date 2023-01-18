let rec copy x =
  if x = 0 then
    0
  else
    1 + copy (x - 1)
let main x = assert (copy x = x)

[@@@assert "typeof(main) <: int -> unit"]
