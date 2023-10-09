type 'a eff =
| E1 : int -> unit eff
| E2 : int -> int eff
external perform : 'a eff -> 'a = "unknown"

type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let main () =
  try_with (fun () -> perform (E2 10)) () {
    effc = fun (type a) (e: a eff) -> match e with
    | E1 _n -> Some (fun (k: (a, _) continuation) -> 1)
    | E2 n -> Some (fun (k: (a, _) continuation) -> n + continue k 2)
  }

[@@@assert "typeof(main) <: unit -> {z: int | z = 11}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 12}"]
