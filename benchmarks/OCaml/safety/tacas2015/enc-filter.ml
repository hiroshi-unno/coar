
(*
let rec filter f xs =
  match xs with
      [] -> []
    | x::xs' ->
        if f x
        then x :: filter f xs'
        else filter f xs'
*)

external nondet_bool : unit -> bool = "unknown"
[@@@rtype"nondet_bool::unit -> bool"]

let f n = n < 0
let rec filter (f:int->bool) n =
  if n = 0
  then 0
  else
    if nondet_bool ()
    then 1 + filter f (n-1)
    else filter f (n-1)

let main n =
  assert (filter f n <= n)

[@@@assert "typeof(main) <: int -> unit"]
