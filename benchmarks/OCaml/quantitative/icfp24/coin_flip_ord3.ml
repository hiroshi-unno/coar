[@@@mode "hfl_prop_as_expectation"]

let p = 0.5
let rec f x k =
  let r11, r12, r13 = k () in
  let r21, r22, r23 = f () k in
  p *. r11 +. (1.0 -. p) *. (r21 +. 1.0),
  p *. r12 +. (1.0 -. p) *. (r22 +. 2.0 *. r21 +. 1.0),
  p *. r13 +. (1.0 -. p) *. (r23 +. 3.0 *. r22 +. 3.0 *. r21 +. 1.0)

[@@@assert "typeof(f) <: unit -> (unit -> { r : prop * prop * prop | r = Tuple(0.0, 0.0, 0.0) }) -> { ret : prop * prop * prop | 0.0 <= $proj(0, ret) && $proj(0, ret) <= 1.0 && 0.0 <= $proj(1, ret) && $proj(1, ret) <= 3.0 && 0.0 <= $proj(2, ret) && $proj(2, ret) <= 13.0 }"]
