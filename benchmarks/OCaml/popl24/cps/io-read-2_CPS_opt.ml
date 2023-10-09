type emptyHnadler = EmptyHandler

type result = Ok | Err

let read_n n l : emptyHnadler -> (result -> 'ans) -> 'ans = fun h k ->
  (
    let rec go m =
      if m <= 0 then (fun h k -> k Ok)
      else (fun h k -> h (fun _ -> (go (m - 1)) h k))
    in
    (fun go ->
      (go n)
      (fun k_read ->
        fun h k -> k (fun lst ->
          match lst with
          | (s :: lst' : int list) ->
            fun h k ->
              (k_read s)
              h
              (fun f -> (f lst') h k)
          | [] -> fun h k -> k Err
        ))
        (fun x -> fun h k -> k (fun _ -> fun h k -> k x))
    ) go
  )
  h
  (fun run -> (run l) h k)


[@@@assert "typeof(read_n) <:
  {z: int | z = 1} -> {z: int list | z <> []} ->
  emptyHnadler -> ({z:result | z = Ok} -> ans) -> ans"]
