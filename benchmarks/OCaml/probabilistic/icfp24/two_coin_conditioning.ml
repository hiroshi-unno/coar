[@@@mode "hfl_prop_as_conditional_expectation"]

let rec diverge () (k : unit -> float * float) : float * float = diverge () k

[@@@assert "typeof(diverge) <: unit -> (unit -> prop * real) -> { ret : prop * real | $proj(0, ret) = 0.0 && $proj(1, ret) = 1.0 }"]

let rec f m k =
  let (r11, r12) = f () k in
  let (r21, r22) = k () in
  let (r31, r32) = diverge () k in
  (0.25 *. r11 +. 0.25 *. r21 +. 0.25 *. r31, 0.25 *. r12 +. 0.25 *. r22 +. 0.25 *. r32)

[@@@assert "typeof(f) <: unit -> (unit -> { r : prop * real | $proj(0, r) = 1.0 && $proj(1, r) = 1.0 }) -> { ret : prop * real | 0.0 <= $proj(0, ret) && $proj(0, ret) <= 0.5 * $proj(1, ret) && 0.0 <= $proj(1, ret) && $proj(1, ret) <= 1.0 }"]
