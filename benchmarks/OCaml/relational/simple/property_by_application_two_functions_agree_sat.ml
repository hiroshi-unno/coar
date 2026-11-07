(* A relational property stated by application ([@@@property]): a recursive
   and a tail-recursive sum agree wherever both return.  Each application in a
   premise is replaced by RCaml's predicate for the graph of its function.
   Expected: sat. *)
let rec sum n = if n <= 0 then 0 else n + sum (n - 1)

let rec sum_acc n a = if n <= 0 then a else sum_acc (n - 1) (a + n)

[@@@property "forall n a r s. sum n = r => sum_acc n a = s => s = r + a"]
