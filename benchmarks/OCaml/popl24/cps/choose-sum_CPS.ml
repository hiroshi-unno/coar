type emptyHnadler = EmptyHandler

let choose_sum x y : emptyHnadler -> (int -> 'ans) -> 'ans =
    (fun h k ->
        (fun h k ->
            h (true, 0) (fun z -> (
                if z then (fun h k -> k x) else (fun h k -> k y)
            ) h k)
        ) h (fun a -> (fun h k ->
            (fun h k ->
                h (false, a) (fun z -> (
                    if z then (fun h k -> k x) else (fun h k -> k y)
                ) h k)
            ) h (fun b -> (fun h k ->
                k (a - b)
            ) h k)
        ) h k))
    (fun _ k_d ->
        fun h k ->
            (k_d true) h (fun r1 -> (fun h k ->
                (k_d false) h (fun r2 -> (fun h k ->
                    k (r1 + r2)
                ) h k)
            ) h k)
    )
    (fun x -> fun h k -> k x)

[@@@assert "typeof(choose_sum) <:
  int -> int ->
emptyHnadler -> ({z: int | z = 0} -> ans) -> ans
"]