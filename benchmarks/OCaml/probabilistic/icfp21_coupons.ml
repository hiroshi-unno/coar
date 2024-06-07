[@@@mode "hfl_prop_as_expectation"]

let rec length = function [] -> 0 | _ :: xs -> 1 + length xs
let rec mem c = function [] -> false | x :: xs -> c = x || mem c xs
let rec is_subset cs os = match cs with [] -> true | c :: cs' -> mem c os && is_subset cs' os
let rec sum f = function [] -> 0.0 | x :: xs -> f x +. sum f xs
let rec collect cs os k =
  if is_subset cs os then k os
  else
    let len_inv = 1.0 /. float_of_int (length cs) in
    1.0 +. sum (fun c -> len_inv *. collect cs (c :: os) k) cs
let coupons cs k = collect cs [] k

[@@@assert "typeof(coupons) <: { x : int list | x = 1 :: 2 :: [] } -> (int list -> { r : prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 2.0 * (1.0 + 1.0 / 2.0) }"]
