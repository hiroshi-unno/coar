(* A recursive function over a nested datatype, a tree whose children are a
   [tree list]: a node with one leaf child has two nodes. *)
type tree = N of int * tree list

let rec cnt t = match t with N (_, []) -> 1 | N (m, c :: r) -> cnt c + cnt (N (m, r))
let main n = assert (cnt (N (n, [ N (n, []) ])) = 2)

[@@@assert "typeof(main) <: int -> unit"]
