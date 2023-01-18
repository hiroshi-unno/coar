let make_array n i = assert (0 <= i && i < n); 0
let update i n a x = a i; let a j = if i=j then x else a j in a

let rec bcopy_aux m src des i =
  if i >= m
  then ()
  else bcopy_aux m src (update i m des (src i)) (i+1)

let main i n m =
  let array1 = make_array n in
  let array2 = make_array m in
  if i=0 && n<=m then bcopy_aux n array1 array2 i else ()

[@@@assert "typeof(main) <: int -> int -> int -> unit"]
