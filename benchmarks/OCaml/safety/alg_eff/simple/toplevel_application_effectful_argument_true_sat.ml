(* A top-level application whose value is a function, used with an effectful argument in a later item. *)
type[@boxed] 'a eff =
| Op : unit eff
type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let identity f = f
let apply_one = identity (fun g -> g 1)
let main () = try_with (fun () -> apply_one (fun x -> perform Op; x)) () { effc = fun (type a) (e: a eff) -> match e with
    | Op -> Some (fun (k: (a, _) continuation) -> continue k ()) }
[@@@assert "typeof(main) <: unit -> {z: int | z = 1}"]
