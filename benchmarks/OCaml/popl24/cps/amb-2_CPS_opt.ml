type emptyHnadler = EmptyHandler

type 'a result = Failure | Success of 'a

let test e l : emptyHnadler -> (bool -> 'ans) -> 'ans =
  (fun h k ->
    (fun amb_find ->
      (amb_find e (e :: l))
      h
      (fun r ->
        k (r = Success e)
      )
    )
    (fun e l ->
      let rec select_from l =
        match l with
        | [] -> (fun h k -> k None)
        | x::xs -> (fun h k ->
            h (fun b ->
              if b then k (Some x) else select_from xs h k
            )
          )
      in
      (fun select_from ->
        (select_from l)
        (fun k_sel -> fun h k ->
          (k_sel true)
          h
          (fun r ->
            match r with
            | Success y -> k (Success y)
            | Failure -> k_sel false h k
          )
        )
        (fun r ->
          match r with
          | Some x ->
              (fun b ->
                if b then (fun x -> fun h k -> k x) (Success x)
                else (fun x -> fun h k -> k x) Failure
              )
              (x = e)
          | None -> (fun x -> fun h k -> k x) Failure
        )
      ) select_from
  ))

[@@@assert "typeof(test) <:
  int -> int list ->
  emptyHnadler -> ({z: bool | z = true} -> ans) -> ans"]