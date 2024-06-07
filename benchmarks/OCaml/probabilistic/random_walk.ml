[@@@mode "hfl_prop_as_expectation"]

let p = 2.0 /. 3.0
let rec f x k =
  if x = 0 then k () else p *. (1.0 +. f (x - 1) k) +. (1.0 -. p) *. (1.0 +. f (x + 1) k)

[@@@assert "typeof(f) <: { x:int | x = 1 } -> (unit -> { r:prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 3.0 }"]
