
let make_array n = n
let arraysize src = src
let update des i x = assert (0 <= i && i < des)
let sub src i = assert (0 <= i && i < src); 0

let rec dotprod_aux n v1 v2 i sum =
  if i = n
  then sum
  else dotprod_aux n v1 v2 (i+1) (sum + (sub v1 i) * (sub v2 i))

let dotprod v1 v2 = dotprod_aux (arraysize v1) v1 v2 0 0

let main n m =
  let v1 = make_array n in
  let v2 = make_array m in
  if 0<=n && n=m then (dotprod v1 v2; ()) else ()

[@@@assert "typeof(main) <: int -> int -> unit"]
