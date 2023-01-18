let rec even x = if x = 0 then true else odd (x - 1)
and odd x = if x = 0 then false else even (x - 1)
let main x y =
  assert ((not (even x && odd y) || odd (x + y)) &&
          (not (odd x && odd y) || even (x + y)))

[@@@assert "typeof(main) <: int -> int -> unit"]
