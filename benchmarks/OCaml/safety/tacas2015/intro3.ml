(*
USED: PLDI2011 as intro3
*)
let f x g :unit= g(x+1)
let h z y = assert (y>z)
let main n = if n>=0 then f n (h n)

[@@@assert "typeof(main) <: int -> unit"]
