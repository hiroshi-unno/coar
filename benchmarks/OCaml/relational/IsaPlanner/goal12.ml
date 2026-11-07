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

let rec map f l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) -> Cons(f x, map f xs)

let main f n xs =
  if n >= 0 then
    assert(drop n (map f xs) = map f (drop n xs))
  else ()

[@@@types
" map :: (t1: (tx: int) -> {ty: int | ty = (f tx)}) -> (t2: list) -> {t3: list | map[0:2](t2, t3)}
 main :: (t1: (tx: int) -> {ty: int | ty = (f tx)}) -> (n:int) -> (xs:list) -> unit"]
