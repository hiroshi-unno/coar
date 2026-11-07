(* main calls a recursive function that never returns and raises an event at
   every step, so every run of main is infinite: the infinite-trace effect
   false does not hold.  A translation that lost the callee's fixpoint
   definition at the instance main uses would read that effect as false and
   accept the assertion. *)
external event_a : unit -> unit = "unknown"

[@@@rtype "event_a :: unit -> (unit & x. x=ev(a), y. false)"]

let rec loop (n : int) : int =
  event_a ();
  loop n

let main n = loop n

[@@@assert "typeof(main) <: int -> (int & x. true, y. false)"]
