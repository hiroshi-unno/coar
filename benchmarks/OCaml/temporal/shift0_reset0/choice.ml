external event_true : unit -> unit = "unknown"
external event_false : unit -> unit = "unknown"
external shift0 : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'd (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

[@@@rtype "event_true :: unit -> (unit & x. x=ev(t), y. false)"]
[@@@rtype "event_false :: unit -> (unit & x. x=ev(f), y. false)"]

let rec ( @ ) l1 l2 = match l1 with [] -> l2 | hd :: tl -> hd :: (tl @ l2)
let choice () =
  (shift0 (*: ((bool (*T*) -> bool list (*C1*)) -> bool list (*C2*)) -> bool (*T*)*))
    (fun k -> k true @ k false)

let main () =
  (reset (* : (unit -> bool list (*T*)) -> bool list (*C*)*))
    (fun () ->
       let x : bool = choice () in
       if x then event_true () else event_false ();
       let y : bool = choice () in
       if y then event_true () else event_false ();
       [ x && y ])

[@@@assert "typeof(main) <: unit -> (bool list & x. x in (ev(t) ev(t)) (ev(t) ev(f)) (ev(f) ev(t)) (ev(f) ev(f)), y. false)"]
