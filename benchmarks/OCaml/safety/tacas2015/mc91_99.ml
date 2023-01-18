let rec m x =
  if x > 100
  then x - 10
  else m (m (x + 11))

let main n =
  if n <= 99
  then assert (m n = 91)
  else ()

[@@@assert "typeof(main) <: int -> unit"]
