(* [called f@lbl a~]: the argument tuples with which [f] is entered from the
   call labelled [lbl], directly or through its recursive calls -- here the
   reachable states of a loop.  The property is the C program's question as a
   Horn clause query: the state in which the loop stops holds [x * y]. *)
let rec mult x y =
  if y = 0 then 0
  else x + mult x (y - 1)

let rec loop c x y r =
  if c <> 0 then loop (c - 1) x y (r + x)
  else r

let mult_c x y = (loop y x y 0 [@copy entry])

[@@@property "forall x y r1 r. mult x y = r1 => called loop@entry 0 x y r => r1 = r"]

[@@@lemma "forall c x y r. called loop@entry c x y r => c >= 1 => called loop@entry (c - 1) x (y - 1) r"]
