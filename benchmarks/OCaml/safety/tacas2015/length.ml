(*
USED: PEPM2013 as length
*)

let rec length xs =
  match xs with
      [] -> 0
    | _::xs' -> 1 + length xs'

let rec make_list n =
  if n = 0
  then []
  else n :: make_list (n-1)

let main n =
  let xs = make_list n in
    assert (length xs = n)

[@@@assert "typeof(main) <: int -> unit"]
