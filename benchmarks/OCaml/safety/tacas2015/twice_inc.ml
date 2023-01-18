let inc x = x + 1
let twice f x = f (f x)
let main n =  assert (twice inc n >= n + 2)

[@@@assert "typeof(main) <: int -> unit"]
