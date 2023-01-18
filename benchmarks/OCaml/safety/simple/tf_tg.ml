type t = T of (unit -> int)

let main () =
  let tf = T (fun () -> 1) in
  let T f = tf in
  let tg = T (fun () -> 2) in
  let T g = tg in
  f ()

[@@@assert "typeof(main) <: unit -> {z: int | z = 1}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 2}"]
[@@@assert "typeof(main) <: unit -> {z: int | z >= 1}"]
