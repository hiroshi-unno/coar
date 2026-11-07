type list = Nil | Cons of int * list

let rec map f = function
  | Nil -> Nil
  | Cons(x, xs) ->
    let b = f x in
    let r = map f xs in
    Cons (b, r)

(* [eqsize l1 l2]: the two lists have the same length *)
let rec eqsize l1 l2 =
  match l1 with
  | Nil -> (match l2 with Nil -> true | Cons (_, _) -> false)
  | Cons (_, xs) -> (match l2 with Nil -> false | Cons (_, ys) -> eqsize xs ys)

(* [g] is an arbitrary function: [map] preserves the length whatever it maps *)
external g : int -> int = "unknown"
[@@@rtype "g :: (x:int) -> int"]

let map_g l = map g l

[@@@property "forall l l' b. map_g l = l' => eqsize l l' = b => b = true"]
