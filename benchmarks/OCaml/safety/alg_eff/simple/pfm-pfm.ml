type 'a eff =
| Op : int -> int eff
external perform : 'a eff -> 'a = "unknown"

type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let main () =
  try_with (fun () -> perform (Op 1) + perform (Op 2)) () {
    effc = fun (type a) (e: a eff) -> match e with
      | Op n -> Some (fun (k: (a, _) continuation) ->
          n + continue k 10
        )
  }

[@@@assert "typeof(main) <: unit -> {z: int | z = 23}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 12}"]