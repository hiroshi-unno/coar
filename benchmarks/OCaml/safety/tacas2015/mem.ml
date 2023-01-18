(*
USED: PEPM2013 as mem
*)

let rec mem (x:int) xs =
  match xs with
      [] -> false
    | x'::xs -> x = x' || mem x xs

let rec make_list n (x:int) =
  if n < 0
  then []
  else x :: make_list (n-1) x

let is_nil (xs:int list) =
  match xs with
      [] -> true
    | _ -> false

let main n m =
  let xs = make_list n m in
    assert (is_nil xs || mem m xs)

[@@@assert "typeof(main) <: int -> int -> unit"]
