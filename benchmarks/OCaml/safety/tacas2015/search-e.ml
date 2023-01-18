(*
USED: PEPM2013 as search-e
*)

type my_option = MyNone | MySome of int

let rec exists test f n m =
  if n < m
  then
    if test (f n)
    then MySome n
    else exists test f (n+1) m
  else
    MyNone

let mult3 n = 3 * n

let main n m =
  let test x = x = m in
    match exists test mult3 0 n with
        MyNone -> ()
      | MySome x -> assert (0 < x && x < n)

[@@@assert "typeof(main) <: int -> int -> unit"]
