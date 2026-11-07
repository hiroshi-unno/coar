let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let rec fact x =
  if x = 0 then 1
  else mult x (fact (x - 1))

let main x y = if x = y then assert (fact x = fact y)

(* A proof by induction over the functions' graphs uses the lemma below.  It is
   left commented out, so the file asks the question without it; uncomment it
   to state it.
   [@@@lemma "forall x y z z'. mult x y = z => mult x y = z' => z = z'"]
*)
