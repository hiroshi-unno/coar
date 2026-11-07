(* A greatest fixed point that is false everywhere: F x = F (x + 1) && x < 0
   fails at every x >= 0, and at x < 0 through F 0.  The assertion that it is
   true must not be typable. *)
[@@@mode "hfl_prop_as_bool"]

let rec pv_F (x : int) : bool = pv_F (x + 1) && x < 0
[@@fix "nu"]

[@@@assert "typeof(pv_F) <: int -> { v : prop | v = true }"]
