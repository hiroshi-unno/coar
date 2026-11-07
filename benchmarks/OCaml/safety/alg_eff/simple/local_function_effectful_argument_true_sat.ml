(* As toplevel_function_effectful_argument_true_sat, with the function bound inside the item: the control that answers. *)
type[@boxed] 'a eff =
| Op : unit eff
type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let main () = try_with (fun () -> let apply_one g = g 1 in apply_one (fun x -> perform Op; x)) () { effc = fun (type a) (e: a eff) -> match e with
    | Op -> Some (fun (k: (a, _) continuation) -> continue k ()) }
[@@@assert "typeof(main) <: unit -> {z: int | z = 1}"]
