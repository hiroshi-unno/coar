(*
USED: PLDI2011 as l-zipunzip
USED: PEPM2013 as l-zipunzip
*)

let f g x y = g (x+1) (y+1)
let rec unzip x k =
 if x=0 then k 0 0
 else
   unzip (x-1) (f k)

let rec zip x y =
 if x=0 then
  if y=0 then 0
    else assert false
 else if y=0 then assert false
  else 1 + zip (x-1) (y-1)

let main n =
 let x = unzip n zip in ()

[@@@assert "typeof(main) <: int -> unit"]
