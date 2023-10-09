type 'a eff =
| Op : int -> bool eff
external perform : 'a eff -> 'a = "unknown"

type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let main () =
  try_with (fun () -> if perform (Op 0) then 1 else 2) () {
    effc = fun (type a) (e: a eff) -> match e with
      | Op _n -> Some (fun (k: (a, _) continuation) ->
          continue k true
        )
  }

[@@@assert "typeof(main) <: unit -> {z: int | z = 1}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 2}"]