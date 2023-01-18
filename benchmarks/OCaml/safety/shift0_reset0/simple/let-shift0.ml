external shift0 : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'a (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

let main () = reset (fun () ->
  let x = shift0 (fun k -> (k 1) + (k 2)) in x
)

[@@@assert "typeof(main) <: unit -> {z: int | z = 3}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 2 || z = 3 || z = 4}"]