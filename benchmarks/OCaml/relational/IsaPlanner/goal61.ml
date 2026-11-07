type list = Nil | Cons of int * list

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
  if ys <> Nil then
    assert(last (append xs ys) = last ys)
  else ()
