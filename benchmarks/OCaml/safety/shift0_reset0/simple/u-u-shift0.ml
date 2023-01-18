external shift0 : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'a (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

let main () = (); (); shift0 (fun k -> k 0)
