type emptyHnadler = EmptyHandler

let choose1_sum x y : emptyHnadler -> (int -> 'ans) -> 'ans =
        (fun h k ->
            h () (fun z -> (
                if z then (fun h k -> k x) else (fun h k -> k y)
            ) h k))
        (fun () k_d ->
            fun h k ->
                (k_d true) h (fun r1 -> (fun h k ->
                    (k_d false) h (fun r2 -> (fun h k ->
                        k (r1 + r2)
                    ) h k)
                ) h k))
        (fun x -> fun h k -> k x)

[@@@assert "typeof(choose1_sum) <:
  (x:int) -> (y:int) ->
  emptyHnadler -> ({z: int | z = x + y} -> ans) -> ans
"]