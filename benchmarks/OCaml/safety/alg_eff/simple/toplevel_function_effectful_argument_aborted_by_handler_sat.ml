(* A top-level function applied, in a later item, to an argument that performs an operation; the handler discards the continuation and returns 42, so main returns 42. *)
type[@boxed] 'a eff =
| Op : unit eff
type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let apply_one g = g 1
let main () = try_with (fun () -> apply_one (fun x -> perform Op; x)) () { effc = fun (type a) (e: a eff) -> match e with
    | Op -> Some (fun (k: (a, _) continuation) -> 42) }
[@@@assert "typeof(main) <: unit -> {z: int | z = 42}"]
