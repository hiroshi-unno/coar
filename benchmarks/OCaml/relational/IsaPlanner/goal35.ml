type list = Nil | Cons of int * list

let rec dropWhile p l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if p x then dropWhile p xs
    else Cons(x, xs)

let ffalse x = false

let main xs =
  assert(dropWhile ffalse xs = xs)


[@@@types
"dropWhile :: (t1: (x1: int) -> {x2: bool | pred(x1, x2)}) -> (t2: list) -> {t3: list | dropWhile[0:2](t2, t3)}
"]

