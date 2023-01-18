(* zip xs (rev ys) is not treeless but the following ziprev is treeless
   the following type is necessary to ensure the absence of assertion and pattern match failures:
   h: xs : list -> ys : {ys : list | len xs <= len ys} ->
      { (rs, ss) : list | len ss = len ys - len xs /\ len rs = len xs } *)
let rec h xs ys =
  match xs with
  | [] ->
     [], ys
  | x :: xs' ->
     let rs', y :: ys' = h xs' ys in
     (x, y) :: rs', ys'
let fst p = let (x, _) = p in x
let zip_reverse xs ys = fst (h xs ys)
let rec length xs =
  match xs with
  | [] -> 0
  | x :: xs' -> 1 + length xs'
let main xs ys =
  if length xs <= length ys then
    assert (length (zip_reverse xs ys) = length xs)

[@@@assert "typeof(main) <: int list -> int list -> unit"]
