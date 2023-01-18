external event_ready : unit -> unit = "unknown"
external event_wait : unit -> unit = "unknown"
external shift0 : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'd (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

[@@@rtype "event_ready :: unit -> (unit & x. x=ev(ready), y. false)"]
[@@@rtype "event_wait :: unit -> (unit & x. x=ev(wait), y. false)"]

let[@annot_MB "(unit -> (bool / s1 => s2)) -> (unit / s3 => s4)"] rec wait ready =
  if ready ()
  then (event_ready ())
  else (event_wait (); wait ready)

let rec ( @ ) l1 l2 = match l1 with [] -> l2 | hd :: tl -> hd :: (tl @ l2)
let choice () =
  (shift0 (*: ((bool (*T*) -> unit list (*C1*)) -> unit list (*C2*)) -> bool (*T*)*))
    (fun k -> k true @ k false)

let main () =
  (reset (*: (unit -> unit list (*T*)) -> unit list (*C*)*))
    (fun _ -> [wait choice])

(* best *)
[@@@assert "typeof(main) <: unit -> (unit list & x. false, y. y in (ev(ready) ev(wait))!)"]

(* second best *)
[@@@assert "typeof(main) <: unit -> (unit list & x. false, y. y in ev(wait)! | ev(ready) ev(wait)! | (ev(ready) ev(wait))!)"]

(* third best *)
[@@@assert "typeof(main) <: unit -> (unit list & x. false, y. y in ((ev(ready) ev(wait)) | ev(wait))!)"]

