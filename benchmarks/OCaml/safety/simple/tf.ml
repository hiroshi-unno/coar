type t = T of (unit -> int)

let main () =
  let tf = T (fun () -> 1) in
  let T f = tf in
  f ()

[@@@assert "typeof(main) <: unit -> {z: int | z = 1}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 2}"]
