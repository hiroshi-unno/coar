(* @require nonlinear invariants
   @todo can we find an interpolant "r >= x * x / 2" by solving the following interpolation problem:
         "x = 0 /\ r = 0; not (2 * r >= x * x)" ?
   *)
let rec sum x = if x <= 0 then 0 else x + sum (x - 1)
let main x = assert (2 * sum x >= x * x)

[@@@assert "typeof(main) <: int -> unit"]
