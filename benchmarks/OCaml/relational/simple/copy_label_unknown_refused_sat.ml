(* Refused on stderr: a lemma naming a label no call carries, and [called] of
   an unlabelled function (its whole graph is entered with every argument).
   The assertion holds. *)
let rec sum n =
  if n <= 0 then 0
  else n + sum (n - 1)

let main n =
  let s = sum n in
  assert (s >= 0)

[@@@lemma "forall n r. sum@nowhere n = r => r >= 0"]
[@@@lemma "forall n. called sum n => n >= 0"]
