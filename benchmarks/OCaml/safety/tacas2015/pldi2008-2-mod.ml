(* a variation of pldi2008-2.ml *)

let rec f x y =
  if x <= 50 then g (x + 1) (y + 1)
  else g (x + 1) (y - 1)
and g x y =
  if y < 0 then assert (x >= 100)
  else f x y
and main y = f 0 0

[@@@assert "typeof(main) <: int -> unit"]
