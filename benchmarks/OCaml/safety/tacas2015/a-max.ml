(*
USED: PLDI2011 as a-max
*)

let make_array n i = n - i
let rec array_max (n:int) i (a:int->int) m =
  if i >= n then
    m
  else
    let x = a i in
    let z = if x>m then x else m in
    array_max n (i+1) a z
let main n i =
  if n>0 && i>=0 && i<=0 then
    let m = array_max n i (make_array n) (-1) in
    assert (m >= n)

[@@@assert "typeof(main) <: int -> int -> unit"]
