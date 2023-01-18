
let array1 i = 0
let array2 i = 0
let update a i x j = if j=i then x else a j

let rec bcopy_aux m src des i =
  if i >= m
  then ()
  else
    begin
      assert (0<=i && i<=m);
      let des = update des i (src i) in
        bcopy_aux m src des (i+1)
    end

let main n =
  let bcopy (src : int -> int) des = bcopy_aux n src des 0 in
  bcopy array1 array2

[@@@assert "typeof(main) <: int -> unit"]
