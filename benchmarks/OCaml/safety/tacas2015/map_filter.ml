(*
USED: PEPM2013 as map_filter
FROM: Example of [Ong and Ramsay, 2011]
*)

external nondet_int : unit -> int = "unknown"
[@@@rtype"nondet_int::unit -> int"]

let rec make_list m =
  if m <= 0
  then []
  else nondet_int () :: make_list (m-1)

let rec make_list_list m =
  if m <= 0
  then []
  else make_list (nondet_int ()) :: make_list_list (m-1)

let head : int list -> int= function
    [] -> assert false
  | x::xs -> x

let ne : int list -> int = function
    [] -> 0
  | x::xs -> 1

let rec filter (p:int list->int) = function
    [] -> []
  | x::xs -> if p x = 1 then x::(filter p xs) else filter p xs

let rec map (f:int list->int) = function
    [] -> []
  | x::xs -> f x :: map f xs

let main m = map head (filter ne (make_list_list m))

[@@@assert "typeof(main) <: int -> int list"]
