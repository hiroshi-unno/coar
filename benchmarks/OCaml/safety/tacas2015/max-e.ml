let max max2 (x:int) (y:int) (z:int) : int = max2 (max2 x y) y
let f x y : int = if x >= y then x else y
let main (x:int) y z =
  let m = max f x y z in
    assert (f x m = m && f y m = m && f z m = m)

[@@@assert "typeof(main) <: int -> int -> int -> unit"]
