let add x y = x + y
let rec iter f m n = if n <= 0 then m else f n (iter f m (n - 1))
let main n = assert (iter add 0 n >= n)

[@@@assert "typeof(main) <: int -> unit"]
