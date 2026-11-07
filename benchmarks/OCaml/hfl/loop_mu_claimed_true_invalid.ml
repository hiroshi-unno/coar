(* Loop is a least fixed point that never reaches a base case, so Main is
   false for every x, and the assertion that it is true does not hold.  In
   the Boolean HFL mode a least fixed point's result is refined only by
   upper bounds, so the assertion must not be typable; read as an ordinary
   OCaml program, the partial-correctness rule for let rec would type it,
   since Loop never returns. *)
[@@@mode "hfl_prop_as_bool"]

let rec pv_Main (x : int) : bool = pv_Loop x
[@@fix "mu"]
and pv_Loop (x : int) : bool = pv_Loop (x + 1)
[@@fix "mu"]

[@@@assert "typeof(pv_Main) <: int -> { v : prop | v = true }"]
