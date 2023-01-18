let rec even n =
  if n = 0 then true else odd (n - 1)
and odd n =
  if n = 0 then false else even (n - 1)
let main m =
  assert (even (m + m))

[@@@assert "typeof(main) <: int -> unit"]
