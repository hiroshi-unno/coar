type 'a eff =
| Op : int -> int eff
external perform : 'a eff -> 'a = "unknown"

type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let main () =
  try_with (fun () -> let x = perform (Op 0) in x) () {
    effc = fun (type a) (e: a eff) -> match e with
      | Op _n -> Some (fun (k: (a, _) continuation) ->
          continue k 1
        )
  }

[@@@assert "typeof(main) <: unit -> {z: int | z = 1}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 2}"]