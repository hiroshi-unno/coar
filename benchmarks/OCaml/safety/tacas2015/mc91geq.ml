(* mc91 : x:{v <= 101} -> {v = 91} /\ x:{v <= 111} -> {v <= 101} *)
let rec mc91 x =
  if x >= 101 then
    x - 10
  else
    mc91 (mc91 (x + 11))
let main n =
  if n <= 101 then
    assert (mc91 n = 91)

[@@@assert "typeof(main) <: int -> unit"]
