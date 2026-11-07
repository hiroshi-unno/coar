type list = Nil | Cons of int * list

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let main xs =
  assert(take 0 xs = Nil)
