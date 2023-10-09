type[@boxed] 'a eff =
| Op : int -> int eff

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

let simple () =
  try_with (fun () ->
    let y = perform (Op 3) in
    y * 2
  ) () {
    effc = fun (type a) (e: a eff) -> match e with
    | Op x -> Some (fun (k: (a, _) continuation) ->
        let a = x + 2 in continue k a
    )
  }

[@@@assert "typeof(simple) <: unit -> {z: int | z = 10}"]