let twice f x = f(f x)
let rec g x = if x <=0 then 1 else 2+g(x-1)
let main n =  assert (twice g n = 0)

[@@@assert "typeof(main) <: int -> unit"]
