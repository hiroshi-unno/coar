(* A lemma about a function's whole graph, written [f@def]: it moves the
   accumulator to values the program never passes ([a - x] at [a = 0]), so it
   is false of the copy of [mult_acc] that [main]'s call makes and true of
   [mult_acc]'s graph. *)
let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let rec mult_acc x y a =
  if y = 0 then a
  else mult_acc x (y - 1) (a + x)

let main x y =
  let s1 = mult x y in
  let s2 = mult_acc x y 0 in
  assert (s1 = s2)

[@@@lemma "forall x y a r. mult_acc@def x y a = r => mult_acc@def x y (a - x) = r - x"]
