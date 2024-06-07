open Core

(** Lazy lists *)

type 'a t = Nil | Cons of 'a * (unit -> 'a t)

let cons x xs = Cons (x, fun () -> xs)
let hd = function Cons (x, _xs) -> x | Nil -> failwith ""
let tl = function Cons (_x, xs) -> xs () | Nil -> failwith ""

let rec nth n = function
  | Cons (x, xs) -> if n = 1 then x else nth (n - 1) (xs ())
  | Nil -> failwith ""

let rec take n xs = if n = 0 then [] else hd xs :: take (n - 1) (tl xs)

let rec filter p = function
  | Nil -> Nil
  | Cons (x, xs') ->
      if p x then Cons (x, fun () -> filter p (xs' ())) else filter p (xs' ())

let rec zipWith f xs ys =
  match (xs, ys) with
  | Nil, Nil -> Nil
  | Cons (x, xs'), Cons (y, ys') ->
      Cons (f x y, fun () -> zipWith f (xs' ()) (ys' ()))
  | _ -> failwith "zipWith"

let rec from n = Cons (n, fun () -> from (n + 1))
let rec fib = Cons (1, fun () -> Cons (1, fun () -> zipWith ( + ) fib (tl fib)))

let rec sieve = function
  | Nil -> Nil
  | Cons (x, xs) ->
      Cons (x, fun () -> filter (fun y -> y mod x <> 0) (sieve (xs ())))

let prime = sieve (from 2)
