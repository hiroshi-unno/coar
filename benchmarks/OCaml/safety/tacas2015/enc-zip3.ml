let rec loop x = loop ()
let rec zip x y =
  if x = 0
  then
    if y = 0
    then 0
    else loop ()
  else
    if y = 0
    then loop ()
    else 1 + zip (x-1) (y-1)

let main n =
  assert (zip n n = n)

[@@@assert "typeof(main) <: int -> unit"]
