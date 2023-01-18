(*
USED: PEPM2013 as fold_left
*)

let rec fold_left (f:int->int->int) acc xs =
  match xs with
      [] -> acc
    | x::xs' -> fold_left f (f acc x) xs'

let rec make_list n =
  if n < 0
  then []
  else n :: make_list (n-1)

let add x y = x + y

let main n m =
  let xs = make_list n in
    assert (fold_left add m xs >= m)

[@@@assert "typeof(main) <: int -> int -> unit"]
