type list = Nil | Cons of int * list

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let rec map f l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    let a = f x in
    Cons(x, map f xs)

let main f n xs =
  assert(take n (map f xs) = map f (take n xs))

[@@@types
"map :: (t1: (tx: int) -> {ty: int | ty = (f tx)}) -> (t2: list) -> {t3: list | map[0:2](t2, t3)}
 main :: (t1: (tx: int) -> {ty: int | ty = (f tx)}) -> (n:int) -> (xs:list) -> unit"]
