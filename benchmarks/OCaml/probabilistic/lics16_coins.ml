let p1 = 1.0 /. 2.0
let p2 = 1.0 /. 3.0
let coins k =
  p1 *. (p2 *. k 0 0 +. (1.0 -. p2) *. k 0 1) +. (1.0 -. p1) *. (p2 *. k 1 0 +. (1.0 -. p2) *. k 1 1)

[@@@assert "typeof(coins) <: ((x:int) -> (y:int) -> { r : prop | x = y && r = 1.0 || x <> y && r = 0.0 }) -> { ret : prop | ret = 0.5 }"]
