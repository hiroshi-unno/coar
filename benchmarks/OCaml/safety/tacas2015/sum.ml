(*
USED: PLDI2011 as sum
USED: PEPM2013 as sum
*)
let rec sum n =
  if n <= 0
  then 0
  else n + sum (n-1)

let main n =
  assert (n <= sum n)

[@@@assert "typeof(main) <: int -> unit"]
