external nondet_bool : unit -> bool = "unknown"
external event_ready : unit -> unit = "unknown"
external event_wait : unit -> unit = "unknown"
external event_send : unit -> unit = "unknown"
external shift0 : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'd (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

[@@@rtype "nondet_bool :: unit -> bool"]
[@@@rtype "event_ready :: unit -> (unit & x. x=ev(ready), y. false)"]
[@@@rtype "event_wait :: unit -> (unit & x. x=ev(wait), y. false)"]
[@@@rtype "event_send :: unit -> (unit & x. x=ev(send), y. false)"]

let rec wait ready =
  if ready ()
  then (event_ready ())
  else (event_wait (); wait ready)

let[@annot_MB "int -> (unit -> bool) -> (int -> (unit / s1 => s2)) -> (unit / s3 => s4)"] rec send x ready receiver =
  wait ready;
  event_send ();
  (receiver x : unit);
  send (x+1) ready receiver

let ready () = if nondet_bool () then true else false

let raise_ x = shift0 (fun _k -> x)

let main () = reset (fun () -> (send 0 ready raise_ : unit))

(* best *)
[@@@assert "typeof(main) <: unit -> (int & x. x in ev(wait)* ev(ready) ev(send),
                                           y. y in ev(wait)!)"]

(* second best *)
[@@@assert "typeof(main) <: unit -> (int & x. x in ev(wait)* ev(ready) ev(send),
                                           y. y in ev(wait)! | (ev(wait)* ev(ready) ev(send))!)"]
