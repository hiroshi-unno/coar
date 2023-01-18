external event_a : unit -> unit = "unknown"
external event_b : unit -> unit = "unknown"
external event_c : unit -> unit = "unknown"
external event_d : unit -> unit = "unknown"

[@@@rtype "event_a :: unit -> (unit & x. x=ev(a), y. false)"]
[@@@rtype "event_b :: unit -> (unit & x. x=ev(b), y. false)"]
[@@@rtype "event_c :: unit -> (unit & x. x=ev(c), y. false)"]
[@@@rtype "event_d :: unit -> (unit & x. x=ev(d), y. false)"]

let rec sum n =
  if n <= 0 then (event_b (); 0)
  else n + sum (n - 1)

let main n =
  event_a ();
  let res = sum n in
  event_c ();
  assert (n <= res);
  event_d ()

[@@@assert "typeof(main) <: int -> (unit & x. x=ev(a)++ev(b)++ev(c)++ev(d), y. false)"]
