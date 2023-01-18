(*
USED: PEPM2013 as fact_notpos
*)

exception NotPositive

let rec fact n =
  if n <= 0
  then
    raise NotPositive
  else
    try
      n * fact (n-1)
    with NotPositive -> 1

let main n =
  try
    fact n
  with NotPositive -> assert (n <= 0) ; 0

[@@@assert "typeof(main) <: int -> unit"]
