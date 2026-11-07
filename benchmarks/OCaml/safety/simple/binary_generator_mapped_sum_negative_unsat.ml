(* A recursive generator of binary trees whose leaves lie in [-10, 10], mapped
   leaf by leaf to non-positive numbers: the sum of the mapped tree is negative
   already at a single leaf, so the assertion fails.  The generator's clause
   has two calls of itself, the shape on which a resolver that keeps deriving
   trees from trees it derived enumerates the generator without end. *)
external nondet_bool : unit -> bool = "unknown"
[@@@rtype "nondet_bool::unit -> bool"]

external nondet_int : int -> int = "unknown"
[@@@rtype "nondet_int::(x:int) -> {r:int | 0 <= r && r < x}"]

type t = Leaf of int | Node of t * t

let rec gen () =
  if nondet_bool () then Leaf (nondet_int 21 - 10) else Node (gen (), gen ())

let rec map f t =
  match t with Leaf n -> Leaf (f n) | Node (l, r) -> Node (map f l, map f r)

let rec sum t = match t with Leaf n -> n | Node (l, r) -> sum l + sum r
let neg x = if x <= 0 then x else -x
let main () = assert (sum (map neg (gen ())) >= 0)

[@@@assert "typeof(main) <: unit -> unit"]
