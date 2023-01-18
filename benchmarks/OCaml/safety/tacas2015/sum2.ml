let rec sum n =
  if n <= 0 then
    0
  else
    n + sum (n-1)
let main n = assert (2*n-1 <= sum n)

[@@@assert "typeof(main) <: int -> unit"]
