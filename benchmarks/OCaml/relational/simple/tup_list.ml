type list = Nil | Cons of int * list

let rec length l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    1 + length xs

let rec sum l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    x + sum xs

let rec tup l =
  match l with
  | Nil -> (0, 0)
  | Cons(x, xs) ->
    let (ln, sm) = tup xs in
    (ln + 1, sm + x)

let main l =
  assert( (length l, sum l) = tup l)

