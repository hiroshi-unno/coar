type tree = Leaf | Node of int * tree * tree
let rec tree_sum t = match t with
  | Leaf -> 0
  | Node(x,t1,t2) -> x + tree_sum t1 + tree_sum t2
let rec tree_sum_acc1 a t = match t with
  | Leaf -> a
  | Node(x,t1,t2) -> tree_sum_acc1 (tree_sum_acc1 (x + a) t1) t2
let main t = assert (tree_sum t = tree_sum_acc1 0 t)
