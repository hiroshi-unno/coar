type tree = Node of int * tree * tree | Leaf

let rec mirror t =
  match t with
  | Leaf -> Leaf
  | Node(x, y, z) -> Node(x, mirror z, mirror y)


let nmax x y =
  if x < y then y else x

let rec height t =
  match t with
  | Leaf -> 0
  | Node(x, y, z) ->
    1 + nmax (height y) (height z)

let main a =
  assert(height (mirror a) = height a)

[@@@types
"height :: (t1: tree) -> {t2: int | height[0:1](t1, t2) && t2 >= 0}"]

