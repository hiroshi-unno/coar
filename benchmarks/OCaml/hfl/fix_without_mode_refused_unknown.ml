(* A [@@fix] binding outside the Boolean HFL mode: RCaml refuses to read it,
   since its ordinary reading of let rec (partial correctness) would type
   Loop as true although its least fixed point is false. *)
let rec loop (x : int) : bool = loop (x + 1)
[@@fix "mu"]

[@@@assert "typeof(loop) <: int -> { v : bool | v = true }"]
