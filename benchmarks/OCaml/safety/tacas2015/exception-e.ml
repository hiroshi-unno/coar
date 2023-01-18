(*
USED: PLDI2012 as excep-e
FROM: Leroy & Pessaux, "Type-Based Analysis of Uncaught Exceptionis, " TOPLAS, 2000

let ff n = if n >= 0 then () else raise 0 in
let main n = try ff n with Failer 0 -> ()
*)

let f n k = if n >= 0 then () else k 0
let g n = assert (n = 1)
let main n = f n g

[@@@assert "typeof(main) <: int -> unit"]
