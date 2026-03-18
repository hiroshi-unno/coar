[@@@mode "hfl_prop_as_expectation"]

let rec gr0 f k =
  let g k =
    let (p1, r1) = f k in
    let (p2, r2) = k in
    (0.5 *. p1 +. 0.5 *. p2,
     0.5 *. (p1 *. 0.0 +. r1) +. 0.5 *. (p2 *. 0.0 +. r2))
  in
  let (p1, r1) = gr1 f k in
  let (p2, r2) = gr0 g k in
  let p12 = 0.5 *. p1 +. 0.5 *. p2 in
  let r12 = 0.5 *. (p1 *. 1.0 +. r1) +. 0.5 *. (p2 *. 1.0 +. r2) in
  let (pk, rk) = f (k true) in
  (0.75 *. p12  +. 0.25 *. pk,
   0.75 *. (p12 *. 0.0 +. r12) +. 0.25 *. (pk *. 0.0 +. rk))
and gr1 f k =
  let g k =
    let (p1, r1) = f k in
    let (p2, r2) = k in
    (0.5 *. p1 +. 0.5 *. p2,
     0.5 *. (p1 *. 0.0 +. r1) +. 0.5 *. (p2 *. 0.0 +. r2))
  in
  let (p1, r1) = gr1 f k in
  let (p2, r2) = gr1 g k in
  let p12 = 0.5 *. p1 +. 0.5 *. p2 in
  let r12 = 0.5 *. (p1 *. 1.0 +. r1) +. 0.5 *. (p2 *. 1.0 +. r2) in
  let (pk, rk) = f (k false) in
  (0.75 *. p12  +. 0.25 *. pk,
   0.75 *. (p12 *. 0.0 +. r12) +. 0.25 *. (pk *. 0.0 +. rk))

[@@@assert "typeof(gr0) <: ((x : prop * prop) -> { y : prop * prop | y = x }) -> ((ac : bool) -> { ans : prop * prop | ac () && $proj(0, ans) = 1.0 && $proj(1, ans) = 0.0 || not ac () && $proj(0, ans) = 0.0 && $proj(1, ans) = 0.0 }) -> { ret : prop * prop | 0.0 <= $proj(0, ret) && $proj(0, ret) <= 0.5 && 0.0 <= $proj(1, ret) && $proj(1, ret) <= 1.0 / 3.0 }"]
