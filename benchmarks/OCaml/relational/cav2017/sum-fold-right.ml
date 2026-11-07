type list = Nil | Cons of int * list

let rec sum_list l =
  match l with
  | Nil -> 0
  | Cons(x, xs) -> x + sum_list xs

let rec fold_right f l s =
  match l with
  | Nil -> s
  | Cons(x, xs) ->
     f x (fold_right f xs s)

let plus x y = x + y

let main l =
  let s1 = sum_list l in
  let s2 = fold_right plus l 0 in
  assert(s1 = s2)
