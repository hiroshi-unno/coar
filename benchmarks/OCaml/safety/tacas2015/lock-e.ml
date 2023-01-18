(*
USED: PLDI2011 as r-lock-e
*)

let lock st = assert (st=0); 1
let unlock st = assert (st=1); 0
let f n st : int= if n > 0 then lock (st) else st
let g n st : int = if n >= 0 then unlock (st) else st
let main n = assert ((g n (f n 0)) = 0)

[@@@assert "typeof(main) <: int -> unit"]
