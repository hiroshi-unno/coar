type list = Nil | Cons of int * list

let rec butlast l =
  match l with
  | Nil -> Nil
  | Cons(x, xs) ->
    if xs = Nil then Nil
    else Cons(x, butlast xs)

let rec last l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    if xs = Nil then x
    else last xs

let rec append l ys =
  match l with
  | Nil -> ys
  | Cons(x, xs) ->
    Cons(x, append xs ys)

let main xs ys =
  if ys = Nil then 
    assert(butlast (append xs ys) = butlast xs)
  else 
    assert(butlast (append xs ys) = append xs (butlast ys))
