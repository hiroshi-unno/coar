(* @require nonlinear invariants *)
let rec fact x = if x <= 1 then 1 else x * fact (x - 1)
let main x = assert (not (x >= 4) || fact x >= x)

[@@@assert "typeof(main) <: int -> unit"]
