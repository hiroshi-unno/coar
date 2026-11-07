type list = Nil | Cons of int * list

let rec take n l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if n = 0 then Nil
    else Cons(x, take (n - 1) xs)

let succ x = 1 + x

let rec minus n m =
  if n <= m then 0
  else n - m

let rec len l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> 1 + len xs

let rec butlast l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if xs = Nil then Nil
    else Cons(x, butlast xs)

let main xs ys =
  assert(butlast xs = take (minus (len xs) (succ 0)) xs)
