let rec fib n =
  if n>=0 && n<=0 then 1
  else if n>=1 && n<=1 then 1
  else fib (n-1) + fib (n-2)

let main () = assert (fib 3 >= 4)

[@@@assert "typeof(main) <: unit -> unit"]
