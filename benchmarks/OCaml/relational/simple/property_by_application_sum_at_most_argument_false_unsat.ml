(* A false property stated by application ([@@@property]): [sum 2 = 3], so
   "every value of [sum n] is at most [n]" fails.  Expected: unsat. *)
let rec sum n = if n <= 0 then 0 else n + sum (n - 1)

[@@@property "forall n r. sum n = r => r <= n"]
