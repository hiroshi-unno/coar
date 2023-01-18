
let rec for_all f (xs:int list) =
  match xs with
      [] -> true
    | x::xs' ->
        f x && for_all f xs'

let rec map (f:(int->int)->int) xs =
  match xs with
      [] -> []
    | x::xs' -> f x :: map f xs'

let id (x:int) = x
let succ x = x + 1
let double x = x + x

let main (x:int) =
  let fs = [id;succ;double] in
  let xs' = map (fun f -> f 0) fs in
  let check x = x >= 0 in
    assert (for_all check xs')

[@@@assert "typeof(main) <: int -> unit"]
