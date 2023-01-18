let rec even x = if x = 0 then true else odd (x - 1)
and odd x = if x = 0 then false else even (x - 1)
let main x y =
  if odd x && odd y then assert (even (x + y))

[@@@assert "typeof(main) <: int -> int -> unit"]
