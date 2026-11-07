(* Matching on a child taken from a nested datatype's list field: the first
   child's label is [n], not [n + 1]. *)
type tree = N of int * tree list

let first_child t =
  match t with N (_, c :: _) -> (match c with N (k, _) -> k) | N (m, []) -> m

let main n = assert (first_child (N (0, [ N (n, []) ])) = n + 1)

[@@@assert "typeof(main) <: int -> unit"]
