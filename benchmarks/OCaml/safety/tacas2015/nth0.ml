(*
USED: PEPM2013 as nth0.ml
*)

let is_nil (xs:int list) =
  match xs with
      [] -> true
    | _ -> false

let rec nth n (xs:int list) =
  match xs with
    | [] -> assert false
    | x::xs' -> if n = 0 then x else nth (n-1) xs'

let rec make_list n =
  if n < 0
  then []
  else n :: make_list (n-1)

let main n =
  let xs = make_list n in
    if is_nil xs
    then 0
    else nth 0 xs

[@@@assert "typeof(main) <: int -> int"]
