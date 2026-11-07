(* A lemma about one call's copy of a function's refinement: [sum@top]
   denotes the graph of [sum] restricted to the arguments of the call
   labelled [top] (and of the recursive calls it starts). *)
let rec sum n =
  if n <= 0 then 0
  else n + sum (n - 1)

let main n =
  let s = (sum n [@copy top]) in
  assert (s >= 0)

[@@@lemma "forall n r. sum@top n = r => r >= 0"]
