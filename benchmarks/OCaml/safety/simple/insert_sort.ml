let rec insert x xs =
  match xs with
  | [] -> [x]
  | y :: ys ->
    if x <= y then x :: y :: ys else y :: insert x ys

let rec sort xs =
  match xs with
  | [] -> []
  | y :: ys -> insert y (sort ys)

let rec sorted xs =
  match xs with
  | [] -> true
  | [_] -> true
  | y :: z :: zs ->
    y <= z && sorted (z :: zs)

let main xs = assert (sorted (sort xs))

[@@@assert "typeof(main) <: int list -> unit"]
