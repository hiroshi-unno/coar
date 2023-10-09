type[@boxed] 'a eff =
| Op : unit eff
type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
type ('a,'b) handler = { retc: 'a -> 'b; exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option}
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"


let main () =
  try_with (fun () ->
    if false then 1 else (perform Op; 3)
  ) () {
    effc = fun (type a) (e: a eff) -> match e with
      | Op -> Some (fun (k: (a, _) continuation) ->
          2
        )
  }

[@@@assert "typeof(main) <: unit -> {z: int | z = 2}"]
