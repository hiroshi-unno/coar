type list = Nil | Cons of int * list

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let rec drop n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Cons(x, xs)
    else drop (n - 1) xs

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let main n xs =
  assert(append (take n xs) (drop n xs) = xs)

(*
[@@@types
"append :: (t1: list) -> (t2: list) -> {t3: list | append(t1, t2, t3)}
 drop :: (t1: int) -> (t2: list) -> {t3: list | drop(t1, t2, t3)}
 take :: (t1: int) -> (t2: list) -> {t3: list | take(t1, t2, t3)}"]
 *)
