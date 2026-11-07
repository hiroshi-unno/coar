(* Commutativity of multiplication by repeated addition, proved by the
   relational proof search of MuCyc (config/solver/rcaml_mucyc_relational.json)
   with the help of the lemma below, which the search first proves by
   induction itself and only then uses.  The lemma refers to [mult] by
   application: an equation [mult x y = r] says that [mult x y] can evaluate
   to [r].  Expected: sat. *)
let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let main x y =
  let s1 = mult x y in
  let s2 = mult y x in
  assert (s1 = s2)

[@@@lemma "forall x y r. mult x y = r => mult (x - 1) y = r - y"]
