(*
USED: PLDI2011 as a-cppr
USED: PEPM2013 as a-cppr
*)

(* modified *)
let make_array n i = assert (0 <= i && i < n); 0
let a i des x (j:int) : int = if i=j then x else des i
let update (i:int) (n:int) des x : int -> int =
  des i;
  a i des x
let print_int (n:int) = ()
let rec bcopy (m:int) src des i =
  if i >= m then
    des
  else
    let des = update i m des (src i) in
    bcopy m src des (i+1)
let rec print_array m (array:int->int) des i =
  if i >= m then
    ()
    else
      (print_int (des i);
       print_array m array des (i + 1))
let f (m:int) src des =
  let array : int -> int = bcopy m src des 0 in
    print_array m array des 0
let main n =
  let array1 = make_array n in
  let array2 = make_array n in
    if n > 0 then f n array1 array2

[@@@assert "typeof(main) <: int -> unit"]

(**
(* original *)
let make_array n i = assert (0 <= i && i < n); 0
let update (i:int) (n:int) des x : int -> int =
  des i;
  let a j = if i=j then x else des i in a
let print_int (n:int) = ()
let f (m:int) src des =
  let rec bcopy (m:int) src des i =
    if i >= m then
      des
    else
      let des = update i m des (src i) in
      bcopy m src des (i+1)
  in
  let rec print_array m (array:int->int) i =
    if i >= m then
      ()
    else
      (print_int (des i);
       print_array m array (i + 1))
  in
  let array : int -> int = bcopy m src des 0 in
    print_array m array 0
let main n =
  let array1 = make_array n in
  let array2 = make_array n in
    if n > 0 then f n array1 array2
*)
