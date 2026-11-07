(* The same least fixed point, asserted false: an upper bound, which the
   Boolean HFL mode's admissible refinement [v => theta] can prove. *)
[@@@mode "hfl_prop_as_bool"]

let rec pv_Main (x : int) : bool = pv_Loop x
[@@fix "mu"]
and pv_Loop (x : int) : bool = pv_Loop (x + 1)
[@@fix "mu"]

[@@@assert "typeof(pv_Main) <: int -> { v : prop | v = false }"]
