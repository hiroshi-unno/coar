let mk_array n i = if 0<=i && i<n then 0 else -1
let update i a x j = if j=i then x else a(j)
let rec init i n a =
  if i>=n then a
  else init (i+1) n (update i a 1)

let main n i =
  let x = init 0 n (mk_array n) in
   if 0<=i && i<n then
    assert (x i >=1) (* check that the array has been initialized *)
  else ()

[@@@assert "typeof(main) <: int -> int -> unit"]
