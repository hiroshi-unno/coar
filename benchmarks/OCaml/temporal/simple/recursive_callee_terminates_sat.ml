(* main calls a recursive function that terminates, so no run of main is
   infinite: the infinite-trace effect false holds.  The callee's effect is a
   fixpoint definition over its own refinement predicates, and main's use of
   it is an instance of its generalised type. *)
external event_a : unit -> unit = "unknown"

[@@@rtype "event_a :: unit -> (unit & x. x=ev(a), y. false)"]

let rec count (n : int) : int = if n <= 0 then 0 else count (n - 1)

let main n =
  event_a ();
  count n

[@@@assert "typeof(main) <: int -> (int & x. true, y. false)"]
