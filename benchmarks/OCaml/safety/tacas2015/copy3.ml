let rec copy a x =
  if x <= 0 then
    a + x
  else
    copy (a + 1) (x - 1)
let main x = assert (copy 0 x = x)

[@@@assert "typeof(main) <: int -> unit"]
