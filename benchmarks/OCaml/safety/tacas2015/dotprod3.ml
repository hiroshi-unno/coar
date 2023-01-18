
let make_array n i = assert (0 <= i && i < n); 0
let update des i x j = if i=j then x else des i

let rec dotprod n v1 v2 i sum =
  if i >= n
  then sum
  else dotprod n v1 v2 (i+1) (sum + v1 i * v2 i)

let main n =
  let v1 = make_array n in
  let v2 = make_array n in
  dotprod n v1 v2 0 0; ()

[@@@assert "typeof(main) <: int -> unit"]
