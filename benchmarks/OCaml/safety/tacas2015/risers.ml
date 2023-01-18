(*
USED: PEPM2013 as risers
FROM: Example of [Ong and Ramsay, 2011]
*)

external nondet_int : unit -> int = "unknown"
[@@@rtype"nondet_int::unit -> int"]

let rec make_list m =
  if m <= 0
  then []
  else nondet_int () :: make_list (m-1)

let risersElse (x:int) = function
    [] -> assert false
  | s::ss -> [x]::s::ss

let risersThen (x:int) = function
    [] -> assert false
  | s::ss -> (x::s)::ss

let rec risers = function
    [] -> []
  | [x] -> [[x]]
  | x::y::etc ->
      if x < y
      then risersThen x (risers (y::etc))
      else risersElse x (risers (y::etc))

let main m = risers (make_list m)

[@@@assert "typeof(main) <: int -> int list list"]
