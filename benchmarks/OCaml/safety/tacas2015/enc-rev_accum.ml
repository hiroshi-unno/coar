let rec rev n m =
  if n = 0
  then m
  else rev (n - 1) (m + 1)

let main n =
  assert (rev n 0 >= n)

[@@@assert "typeof(main) <: int -> unit"]
