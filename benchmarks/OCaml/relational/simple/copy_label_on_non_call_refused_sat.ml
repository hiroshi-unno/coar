(* Refused on stderr: a label on an expression that is not a call of a
   top-level function (a label names the copy one call makes), and the lemma
   that names it.  The assertion holds. *)
let rec sum n =
  if n <= 0 then 0
  else n + sum (n - 1)

let main n =
  let m = (n [@copy here]) in
  let s = sum m in
  assert (s >= 0)

[@@@lemma "forall n r. sum@here n = r => r >= 0"]
