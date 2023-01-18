exception DivisionByZero

let rec fold_left f acc xs =
  match xs with
      [] -> acc
    | x::xs' -> fold_left f (f acc x) xs'

let rec randpos() =
 let n = Random.int(0) in
  if n>=0 then n else randpos()

let rec make_list n =
  if n <= 0
  then []
  else randpos() :: make_list (n-1)

let div x y =
  if y=0 then raise DivisionByZero
  else Random.int(0) (* "/" is not supported *)

let main n m =
  let xs = make_list n in
    fold_left div m xs

[@@@assert "typeof(main) <: int -> int -> int"]
