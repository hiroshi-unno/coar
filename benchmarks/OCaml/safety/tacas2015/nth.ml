(*
USED: PEPM2013 as nth
*)

let rec nth n (xs:int list) =
  match xs with
    | [] -> assert false
    | x::xs' -> if n = 0 then x else nth (n-1) xs'

let rec make_list n =
  if n < 0
  then []
  else n :: make_list (n-1)

let main n =
  if n > 0
  then nth (n-1) (make_list n)
  else 0

[@@@assert "typeof(main) <: int -> int"]
