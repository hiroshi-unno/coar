
let make_array n = n
let arraysize src = src
let update des i x = assert (0 <= i && i < des)
let sub src i = assert (0 <= i && i < src); 0

let rec bs_aux key vec l u =
  if u < l
  then -1
  else
    let m = l + (u-l) / 2 in
    let x = sub vec m in
      if x < key then bs_aux key vec (m+1) u
      else if x > key then bs_aux key vec l (m-1)
             else m

let bsearch key vec = bs_aux key vec 0 (arraysize vec - 1)

let main n m =
  let v1 = make_array n in
  let v2 = make_array m in
  if 0<=n && n=m then (bsearch v1 v2; ()) else ()

[@@@assert "typeof(main) <: int -> int -> unit"]
