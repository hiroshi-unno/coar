type emptyHnadler = EmptyHandler

type 'a result = Failure | Success of 'a

let test e l : emptyHnadler -> (bool -> 'ans) -> 'ans =
  (fun h k ->
    (fun h k -> k (fun e l ->
      (fun h k ->
        (fun h k ->
          let rec select_from l =
            match l with
            | [] -> (fun h k -> k None)
            | x::xs -> (fun h k ->
                h (fun b ->
                  (if b then (fun h k -> k (Some x)) else select_from xs)
                  h k
                )
              )
          in
          k select_from)
        h
        (fun select_from ->
          (fun h k ->
            (select_from l)
            h
            (fun r ->
              (match r with
                | Some x -> (fun h k ->
                    (fun h k -> k (x = e))
                    h
                    (fun b ->
                      (if b then (fun h k -> k (Success x)) else (fun h k -> k Failure))
                      h k
                    )
                  )
                | None -> (fun h k -> k Failure)
              )
              h k
            )
          )
          h k
        )
      )
      (fun k_sel -> fun h k ->
        (k_sel true)
        h
        (fun r ->
          (match r with Success y -> fun h k -> k (Success y)
            | Failure -> k_sel false)
          h k
        )
      )
      (fun x -> fun h k -> k x)
    ))
    h
    (fun amb_find ->
      (fun h k ->
        (amb_find e (e :: l))
        h
        (fun r ->
          (fun h k -> k (r = Success e))
          h k
        )
      )
      h k
    )
  )

[@@@assert "typeof(test) <:
  int -> int list ->
  emptyHnadler -> ({z: bool | z = true} -> ans) -> ans"]