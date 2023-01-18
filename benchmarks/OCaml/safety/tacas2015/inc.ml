let rec ar i = 0
let update a i x j = if j=i then x else a j
let rec g e a j =
 if j<e then
   (assert(0<=j && j<e);
    g e (update a j (a(j)+1)) (j+1))
 else ()
let main n =
 g n ar 0

[@@@assert "typeof(main) <: int -> unit"]
