type list = Nil | Cons of int * list

let rec last l =
  match l with
  | Nil -> 0
  | Cons(x, xs) ->
    if xs = Nil then x
    else last xs

let main x xs =
  if xs <> Nil then
    assert(last (Cons(x, xs)) = last xs)
  else ()
