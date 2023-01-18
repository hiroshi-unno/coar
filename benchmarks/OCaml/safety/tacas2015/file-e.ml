let open_ x = 1
let close fp = 0
let read fp = assert (fp = 0)
let rec read_n fp n =
  if n <= 0
  then fp
  else
    (read fp;
     read_n fp (n-1))

let main n =
  let fp = open_ () in
  let fp = read_n fp n in
  assert (fp = 0)

[@@@assert "typeof(main) <: int -> unit"]
