let open_ x = true
let close fp = false
let read fp = assert fp
let rec read_n fp n m =
  if n <= 0
  then
    if m > 0
    then close fp
    else fp
  else
    ((if m > 0 then read fp else ());
     read_n fp (n-1) m)

let main n m =
  let fp = if m > 0 then open_ () else false in
  let fp = read_n fp n m in
  assert fp

[@@@assert "typeof(main) <: int -> int -> unit"]
