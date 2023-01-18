external event_a : unit -> unit = "unknown"
external shift0 : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'd (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

[@@@rtype "event_a :: unit -> (unit & x. x=ev(a), y. false)"]

let rec repeat x = if x = 0 then () else (event_a (); repeat (x-1))

let main () = reset (fun () -> let x : int = shift0 (fun f -> f 3; f 5) in repeat x)

[@@@assert "typeof(main) <: unit -> (unit & x. x in ev(a) ev(a) ev(a) ev(a) ev(a) ev(a) ev(a) ev(a), y. false)"]
