type list = Nil | Cons of int * list

let rec dbl l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    Cons(2 * x, dbl xs)

let rec sum l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    x + sum xs

let rec fus l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    2 * x + fus xs

let main l =
  assert( sum (dbl l) = fus l)

