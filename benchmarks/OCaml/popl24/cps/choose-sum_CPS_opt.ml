type emptyHnadler = EmptyHandler

let choose_sum x y : emptyHnadler -> (int -> 'ans) -> 'ans =
    (fun _ k_d ->
        fun h k ->
            (k_d true) h (fun r1 ->
                (k_d false) h (fun r2 ->
                    k (r1 + r2)
                )))
    (true, 0)
    (fun z ->
        if z then
            (fun a ->
                (fun _ k_d ->
                    fun h k ->
                        (k_d true) h (fun r1 ->
                            (k_d false) h (fun r2 ->
                                k (r1 + r2)
                            )))
                (false, a)
                (fun z ->
                    if z then (fun b -> (fun x -> fun h k -> k x) (a - b)) x
                    else (fun b -> (fun x -> fun h k -> k x) (a - b)) y)
            ) x
        else
            (fun a ->
                (fun _ k_d ->
                    fun h k ->
                        (k_d true) h (fun r1 ->
                            (k_d false) h (fun r2 ->
                                k (r1 + r2)
                            )))
                (false, a)
                (fun z ->
                    if z then (fun b -> (fun x -> fun h k -> k x) (a - b)) x
                    else (fun b -> (fun x -> fun h k -> k x) (a - b)) y)
            ) y
    )

[@@@assert "typeof(choose_sum) <:
  int -> int ->
emptyHnadler -> ({z: int | z = 0} -> ans) -> ans
"]