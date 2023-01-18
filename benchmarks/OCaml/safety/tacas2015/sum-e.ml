(*
USED: PLDI2011 as sum-e
*)

let rec sum n =
  if n <= 0
  then 0
  else n + sum (n-1)

let main n =
  assert (n + 1 <= sum n)

[@@@assert "typeof(main) <: int -> unit"]
