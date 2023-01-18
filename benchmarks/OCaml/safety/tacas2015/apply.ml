(*
USED: PLDI2011 as apply
*)

let apply (f:int->unit) x = f x
let g (y:int) (z:int) = assert (y=z)
let rec k n = apply (g n) n; k(n+1)
let main () = k 0

[@@@assert "typeof(main) <: unit -> unit"]
