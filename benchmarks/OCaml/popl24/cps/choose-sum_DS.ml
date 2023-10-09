type[@boxed] 'a eff =
| Decide : bool(*ctxinfo*) * int(*ctxinfo*) -> bool eff

type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
type ('a,'b) handler = {
  retc: 'a -> 'b;
  exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option
}
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let main x y =
  try_with (fun () ->
    let a = if perform (Decide (true, 0)) then x else y in
    let b = if perform (Decide (false, a)) then x else y in
    a - b
  ) () {
    effc = fun (type a) (e: a eff) -> match e with
      | Decide _ -> Some (fun (k: (a, _) continuation) ->
          continue k true + continue k false
        )
  }

[@@@assert "typeof(main) <: int -> int -> {z: int | z = 0}"]
