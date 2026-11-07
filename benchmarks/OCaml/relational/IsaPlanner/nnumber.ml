type nat = Zero | Succ of nat

let rec plus n m =
  match n with
  | Zero -> m
  | Succ n1 -> Succ (plus n1 m)

let rec minus n m =
  match n with
  | Zero -> Zero
  | Succ n1 ->
    match m with
    | Zero -> n
    | Succ m1 -> minus n1 m1

let main n m =
  assert (n = minus (plus n m) m)
