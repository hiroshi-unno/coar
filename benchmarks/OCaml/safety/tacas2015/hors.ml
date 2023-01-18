(*
USED: PLDI2011 as hors
USED: PEPM2013 as hors
*)

let c q = ()
(* c q -> .  for any q *)
let b x q = x 1
(* b q -> q1 for any q *)
let a x y q = if q=0 then (x 0; y 0) else assert false
(* a q0 -> q0 q0 *)

let rec f n x q = if n <= 0 then x q else a x (f (n-1) (b x)) q
(* F n x = if n<=0 then x else a x (f (n-1) (b x)) *)
let s n q = f n c q
(* S -> F n c *)

let main n = s n 0
(* check whether S: q0 *)

[@@@assert "typeof(main) <: int -> unit"]
