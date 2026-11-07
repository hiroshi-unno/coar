(* The C function of cav2017/mult-c.ml, whose question that file states as a
   query over predicates, rewritten in OCaml:

     int mult_c(int x, int y) { int c = y, r = 0; while (c != 0) { c = c - 1; r = r + x; } return r; }

   [loop c x y r] runs the loop from counter [c] and accumulator [r] and
   returns the final [r].  It carries [y], which the loop does not change, as
   an argument, so that the loop's states are the tuples [(c, x, y, r)] it is
   entered with, as in the C program, where [y] is live throughout. *)
let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let rec loop c x y r =
  if c <> 0 then loop (c - 1) x y (r + x)
  else r

let mult_c x y = (loop y x y 0 [@copy entry])

(* The two functions agree wherever both return.  Solution: mult x y = x * y,
   mult_c x y = x * y, loop c x y r = r + c * x (for c >= 0). *)
[@@@property "forall x y r1 r2. mult x y = r1 => mult_c x y = r2 => r1 = r2"]

(* The original's lemma, over the loop's reachable states [i(c, x, y, r)]:
   the states with which [loop] is entered from the call in [mult_c],
   directly or through its own recursive calls. *)
[@@@lemma "forall c x y r. called loop@entry c x y r => c >= 1 => called loop@entry (c - 1) x (y - 1) r"]
