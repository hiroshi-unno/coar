[@@@mode "hfl_prop_as_conditional_expectation"]

let rec f m k =
  let (r11, r12) = f (m + 1) k in
  let (r21, r22) = k (m + 1) in
  (0.75 *. r11 +. 0.125 *. r21, 0.75 *. r12 +. 0.125 *. r22)

[@@@assert "typeof(f) <: { m : int | m = 0 } -> ((m:int) -> { r : prop * real | (m = 1 && $proj(0, r) = 1.0 || m <> 1 && $proj(0, r) = 0.0) && $proj(1, r) = 1.0 }) -> { ret : prop * real | 0.0 <= $proj(0, ret) && $proj(0, ret) <= 0.25 * $proj(1, ret) && 0.0 <= $proj(1, ret) && $proj(1, ret) <= 1.0 }"]
