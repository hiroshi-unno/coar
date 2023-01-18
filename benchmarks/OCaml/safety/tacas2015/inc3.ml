let make_array n i = assert(0<=i && i<n); 0
let update (i:int) (n:int) (des:int->int) (x:int) = let _ = des i in ()
let rec inc3 m src i =
 if i>=m
 then ()
 else
   begin
     update i m src ((src i)+1);
     inc3 m src (i+1)
   end
let main n =
 if n>0 then inc3 n (make_array n) 0 else ()

[@@@assert "typeof(main) <: int -> unit"]
