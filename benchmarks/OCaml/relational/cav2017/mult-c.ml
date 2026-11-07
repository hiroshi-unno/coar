(* Note: This benchmark was updated on 2017/8/8 to fix the encoding *)

let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

(* int mult_c(int x,int y){ int c=y,r=0; while(c!=0){ c=c-1; r=r+x; } }
   as Horn clauses: [i c x y r] are the loop's states, [mult_c x y r] its
   results.  The query asks that [mult] and the loop agree. *)
[@@@chc
"i c x y r :- c = y && r = 0.
 i c' x y r' :- c' = c - 1 && r' = r + x && i c x y r && c <> 0.
 mult_c x y r :- i 0 x y r.
 ?- mult x y = r1 && mult_c x y r2 && r1 <> r2.
"]
(* Solution: mult x y = r  is  r = x * y,
             mult_c x y r  is  r = x * y,
             i c x y r     is  r = (y - c) * x *)

[@@@lemma "forall c x y r. i c x y r => c >= 1 => i (c - 1) x (y - 1) r"]
