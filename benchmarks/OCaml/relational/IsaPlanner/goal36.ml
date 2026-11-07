type list = Nil | Cons of int * list

let rec takeWhile p l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if p x then Cons(x, takeWhile p xs)
    else Nil

let ftrue x = true

let main xs =
  assert(takeWhile ftrue xs = xs)

[@@@types
"takeWhile :: (t1: (x1: int) -> {x2: bool | pred(x1,x2)}) -> (t2: list) -> {t3: list | takeWhile[0:2](t2, t3)}
"]
