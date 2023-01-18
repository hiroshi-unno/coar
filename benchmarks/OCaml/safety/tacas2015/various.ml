external nondet_bool : unit -> bool = "unknown"
[@@@rtype"nondet_bool::unit -> bool"]

let f x g = g(x+1)
let h y = assert (y>0)
let main n = if n>0 then f n h else ()


let f x g = g(x+1)
let h y = assert (y>0)
let main n =
  if nondet_bool ()
  then main n
  else if n>=0 then f n h else ()


let f x g = g(x+1)
let h z y = assert (y>z)
let main n =
  if nondet_bool ()
  then main n
  else if n>=0 then f n (h n) else ()


let rec sum n =
  if n <= 0
  then 0
  else n + sum (n-1)
let main n =
  if nondet_bool ()
  then main n
  else assert (n <= sum n)


let rec mult n m =
  if n <= 0 || m <= 0
  then 0
  else n + mult n (m-1)
let main n =
  if nondet_bool ()
  then main n
  else
  assert (n <= mult n n)


let max max2 x y z =
  max2 (max2 x y) z
let f x y =
  if x >= y
  then x
  else y
let main n x y z =
  let m = max f x y z in
  if nondet_bool ()
  then main n
  else assert (f x m <= m)


let rec m x =
  if x > 100
  then x - 10
  else m (m (x + 11))
let main n x y z =
  if nondet_bool ()
  then main n x y z
  else
  if n <= 101
  then assert (m n = 91)
  else ()

[@@@assert "typeof(main) <: int -> int -> int -> int -> unit"]
