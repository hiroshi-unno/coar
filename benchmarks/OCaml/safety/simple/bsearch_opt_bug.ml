let arraysize src = src
let sub src i = assert (0 <= i && i < src); 0

(* binary search algorithm with a bug *)
let rec bs_aux key vec l u =
  if l <= u then
    let m = l + (u - l) / 2 in
    let x = sub vec m in
    if x < key then
      bs_aux key vec (m - 1) u
    else if x > key then
      bs_aux key vec l (m - 1)
    else
      Some (m)
  else
    None

let bsearch key vec = bs_aux key vec 0 (arraysize vec - 1)

[@@@assert "typeof(bsearch) <: int -> int -> int option"]
