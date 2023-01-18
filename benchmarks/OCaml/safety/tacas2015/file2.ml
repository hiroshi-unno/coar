let open_ x = true
let close fp = false
let read fp = assert fp
let rec read_n fp n =
  if n <= 0
  then close fp
  else
    (read fp;
     read_n fp (n-1))

let main n =
  let fp = open_ () in
  let fp = read_n fp n in
  assert fp

[@@@assert "typeof(main) <: int -> unit"]
