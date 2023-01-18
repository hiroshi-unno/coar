(*
USED: PEPM2013 as isnil
*)

let is_nil (xs:int list) =
  match xs with
      [] -> true
    | _ -> false

let rec make_list n =
  if n = 0
  then []
  else n :: make_list (n-1)

let main n =
  let xs = make_list n in
    if n > 0
    then assert (not (is_nil xs))
    else ()

[@@@assert "typeof(main) <: int -> unit"]
