(* Two expectations computed as a pair: the expected number of failed flips
   before a fair coin's first success (exactly 1), and the expected value of
   1/2 per failed flip, halved at each flip (exactly 1/2).  The value of the
   admissible unknowns is a tuple of reals, read component-wise. *)
[@@@mode "hfl_prop_as_expectation"]

let p = 0.5
let rec f x k =
  let r11, r12 = k () in
  let r21, r22 = f () k in
  p *. r11 +. (1.0 -. p) *. (r21 +. 1.0),
  p *. r12 +. (1.0 -. p) *. (r22 +. 0.5)

[@@@assert "typeof(f) <: unit -> (unit -> { r : prop * prop | r = Tuple(0.0, 0.0) }) -> { ret : prop * prop | 0.0 <= $proj(0, ret) && $proj(0, ret) <= 1.0 && 0.0 <= $proj(1, ret) && $proj(1, ret) <= 0.5 }"]
