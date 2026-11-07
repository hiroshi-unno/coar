let rec fib1 x = if x <= 1 then 1 else fib1 (x-1) + fib1 (x-2)
let rec fib_aux x y z = if x <= 0 then y else fib_aux (x-1) z (y+z)
let fib2 x = fib_aux x 1 1
let main x = assert(fib1 x = fib2 x)
