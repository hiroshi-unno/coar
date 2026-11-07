(* A datatype whose parameter occurs only contravariantly ('a sink) instantiated with an arrow that performs: the function stored in the datatype is called with an effectful argument, so its parameter's effect must be impure.  Comparing the parameter covariantly typed it pure. *)
type[@boxed] 'a eff =
| Op : int eff
type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"
type 'a sink = Sink of ('a -> int)

let main () =
  try_with (fun () ->
    let s = Sink (fun k -> k ()) in
    match s with Sink g -> g (fun () -> perform Op)
  ) () { effc = fun (type a) (e: a eff) -> match e with
    | Op -> Some (fun (k: (a, _) continuation) -> continue k 1 + continue k 2) }
[@@@assert "typeof(main) <: unit -> {z: int | z = 3}"]
