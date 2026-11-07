(* Refused on stderr: one label on two calls (a label names one call's copy),
   and the lemma that names it.  The assertion holds. *)
let rec sum n =
  if n <= 0 then 0
  else n + sum (n - 1)

let main n =
  let s1 = (sum n [@copy twice]) in
  let s2 = (sum (n + 1) [@copy twice]) in
  assert (s1 >= 0 && s2 >= 0)

[@@@lemma "forall n r. sum@twice n = r => r >= 0"]
