(* The pattern Some a rebinds a to the old a + 1, so a - x = 1. *)
let f (x : int) =
  let a = x in
  match Some (a + 1) with Some a -> a - x | None -> 1
[@@@assert "typeof(f) <: int -> { r : int | r = 0 }"]
