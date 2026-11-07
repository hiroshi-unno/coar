
type tree = Leaf | Node of tree * tree

let rec flip t =
  match t with
  | Leaf -> Leaf
  | Node (l, r) -> Node(flip r, flip l)

let main t =
  assert (flip (flip t) = t)
