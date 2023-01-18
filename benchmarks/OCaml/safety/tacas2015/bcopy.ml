
let make_array n = n
let arraysize src = src
let update des i x = assert (0 <= i && i < des)
let sub src i = assert (0 <= i && i < src); 0

let rec bcopy_aux src des i m =
  if i >= m
  then ()
  else
    begin
      update des i (sub src i);
      bcopy_aux src des (i+1) m
    end

let bcopy src des = bcopy_aux src des 0 (arraysize src)

let main n m =
  let array1 = make_array n in
  let array2 = make_array m in
  if n<=m then bcopy array1 array2 else ()

[@@@assert "typeof(main) <: int -> int -> unit"]
