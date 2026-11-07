(* A [@@@chc] block whose loop adds one too many: started with c = y + 1,
   the loop computes (y + 1) * x, which differs from mult x y whenever
   x <> 0, so the query holds of some states and the answer is unsat. *)
let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

[@@@chc
"i c x y r :- c = y + 1 && r = 0.
 i c' x y r' :- c' = c - 1 && r' = r + x && i c x y r && c <> 0.
 mult_c x y r :- i 0 x y r.
 ?- mult x y = r1 && mult_c x y r2 && r1 <> r2.
"]
