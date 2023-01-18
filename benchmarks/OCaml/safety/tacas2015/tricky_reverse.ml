let rec h xs ys =
  match xs with
  | [] ->
     ([], ys)
  | x :: xs' ->
     let (rs', y :: ys') = h xs' ys in
     (y :: rs', ys')
let reverse x =
  let (r, []) = h x x in r
let rec length xs =
  match xs with
  | [] -> 0
  | x :: xs' -> 1 + length xs'
let main xs =
  assert (length (reverse xs) = length xs)

[@@@assert "typeof(main) <: int list -> unit"]
