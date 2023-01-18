(*
USED: PLDI2011 as mult-e
*)

let rec mult n m =
  if n <= 0 || m <= 0 then
    0
  else
    n + mult n (m-1)
let main n = assert (n+1 <= mult n n)

[@@@assert "typeof(main) <: int -> unit"]
