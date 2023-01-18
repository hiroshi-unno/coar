let make_array n i = assert (0 <= i && i < n); 0
let update (des:int->int) i (x:int) = let _ = des i in ()

let rec bcopy_aux m src des i =
  if i >= m
  then ()
  else
    begin
      update des i (src i);
      bcopy_aux m src des (i+1)
    end

let main n m =
  let array1 = make_array n in
  let array2 = make_array m in
  if n<=m then bcopy_aux n array1 array2 0 else ()

[@@@assert "typeof(main) <: int -> int -> unit"]
