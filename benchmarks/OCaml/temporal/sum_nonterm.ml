external event_a : unit -> unit = "unknown"
external event_b : unit -> unit = "unknown"
external event_c : unit -> unit = "unknown"
external event_d : unit -> unit = "unknown"

[@@@rtype "event_a :: unit -> (unit & x. x=ev(a), y. false)"]
[@@@rtype "event_b :: unit -> (unit & x. x=ev(b), y. false)"]
[@@@rtype "event_c :: unit -> (unit & x. x=ev(c), y. false)"]
[@@@rtype "event_d :: unit -> (unit & x. x=ev(d), y. false)"]

let rec sum n =
  if n = 0 then (event_c (); 0)
  else (event_b (); n + sum (n - 1))

let main n =
  event_a ();
  sum n;
  event_d ()

[@@@assert "typeof(main) <: int -> (unit & x. x in ev(a) ev(b)* ev(c) ev(d), y. y in ev(a) ev(b)!)"]
