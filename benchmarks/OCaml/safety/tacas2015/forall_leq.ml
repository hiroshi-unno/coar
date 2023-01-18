(*
USED: PEPM2013 as forall_leq
*)

let rec for_all f (xs:int list) =
  match xs with
      [] -> true
    | x::xs' ->
        f x && for_all f xs'

let rec check x = x >= 0

let rec make_list n =
  if n < 0
  then []
  else n :: make_list (n-1)

let main n = assert (for_all check (make_list n))

[@@@assert "typeof(main) <: int -> unit"]
