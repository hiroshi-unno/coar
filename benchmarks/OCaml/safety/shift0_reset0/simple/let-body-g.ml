external shift0 : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'a (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

let body () = shift0 (fun k -> k 0)
let main () = reset (fun () -> body ())

[@@@assert "typeof(main) <: unit -> {z: int | z = 0}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 1}"]
