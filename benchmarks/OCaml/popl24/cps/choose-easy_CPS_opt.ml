type emptyHnadler = EmptyHandler

let choose1_sum x y : emptyHnadler -> (int -> 'ans) -> 'ans =
    (fun () k_d ->
        fun h k ->
            (k_d true) h (fun r1 ->
                (k_d false) h (fun r2 ->
                    k (r1 + r2)
                )
            ))
    ()
    (fun z ->
        if z then (fun x -> fun h k -> k x) x else (fun x -> fun h k -> k x) y)

[@@@assert "typeof(choose1_sum) <:
  (x:int) -> (y:int) ->
  emptyHnadler -> ({z: int | z = x + y} -> ans) -> ans
"]