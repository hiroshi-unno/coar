[@@@mode "hfl_prop_as_expectation"]

let rec gr0 k =
  let (p1, r1) = gr1 k in
  let (p2, r2) = gr0 k in
  let p12 = 0.5 *. p1 +. 0.5 *. p2 in
  let r12 = 0.5 *. (p1 *. 1.0 +. r1) +. 0.5 *. (p2 *. 1.0 +. r2) in
  let (pk, rk) = k true in
  (0.75 *. p12  +. 0.25 *. pk,
  0.75 *. (p12 *. 0.0 +. r12) +. 0.25 *. (pk *. 0.0 +. rk))
and gr1 k =
  let (p1, r1) = gr1 k in
  let (p2, r2) = gr1 k in
  let p12 = 0.5 *. p1 +. 0.5 *. p2 in
  let r12 = 0.5 *. (p1 *. 1.0 +. r1) +. 0.5 *. (p2 *. 1.0 +. r2) in
  let (pk, rk) = k false in
  (0.75 *. p12  +. 0.25 *. pk,
   0.75 *. (p12 *. 0.0 +. r12) +. 0.25 *. (pk *. 0.0 +. rk))

[@@@assert "typeof(gr0) <: ((ac : bool) -> { ans : prop * prop | ac () && $proj(0, ans) = 1.0 && $proj(1, ans) = 0.0 || not ac () && $proj(0, ans) = 0.0 && $proj(1, ans) = 0.0 }) -> { ret : prop * prop | 0.0 <= $proj(0, ret) && $proj(0, ret) <= 0.4 && 0.0 <= $proj(1, ret) && $proj(1, ret) <= 0.26 }"]
