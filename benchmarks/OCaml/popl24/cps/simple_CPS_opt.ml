type emptyHnadler = EmptyHandler

let simple : emptyHnadler -> (int -> 'ans) -> 'ans =
    (fun x k_op ->
        fun h k -> (fun a -> (k_op a) h k) (x + 2))
    3
    (fun y -> (fun x -> fun h k -> k x) (y * 2))

[@@@assert "typeof(simple) <: emptyHnadler -> ({z: int | z = 10} -> ans) -> ans"]
