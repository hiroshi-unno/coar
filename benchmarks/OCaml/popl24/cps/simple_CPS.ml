type emptyHnadler = EmptyHandler

let simple : emptyHnadler -> (int -> 'ans) -> 'ans =
    (fun h k ->
        h 3 (fun y -> (fun h k ->
            k (y * 2)
        ) h k))
    (fun x k_op ->
        fun h k ->
            (fun h k -> k (x + 2)) h (fun a -> (
                k_op a
            ) h k))
    (fun x -> fun h k -> k x)

[@@@assert "typeof(simple) <: emptyHnadler -> ({z: int | z = 10} -> ans) -> ans"]
