(* an example program by Prof. Walid Taha *)
let rec f x = if x <= 0 then 0 else 2 + f (x -1)
let rec g x a = if x <= 0 then a else g (x - 1) (a +2)
let main x = assert (f x = g x 0)

[@@@assert "typeof(main) <: int -> unit"]
