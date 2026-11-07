type tree = Leaf | Node of int * tree * tree
let rec tree_sum_acc1 a t = match t with
  | Leaf -> a
  | Node(x,t1,t2) -> tree_sum_acc1 (tree_sum_acc1 (x + a) t1) t2
let rec tree_sum_acc2 a t = match t with
  | Leaf -> a
  | Node(x,t1,t2) -> tree_sum_acc2 (tree_sum_acc2 (x + a) t2) t1
let main t = assert (tree_sum_acc1 0 t = tree_sum_acc2 0 t)
