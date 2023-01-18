let twice f x = f (f x)
let f x = 2 * x

let main n =
  if n > 0
  then assert (twice f n > n)

[@@@assert "typeof(main) <: int -> unit"]
