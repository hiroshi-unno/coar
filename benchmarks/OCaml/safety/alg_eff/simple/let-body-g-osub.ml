type 'a eff =
| Op1 : int -> int eff
| Op2 : int -> int eff
type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
type ('a,'b) handler = {
  retc: 'a -> 'b;
  exnc: exn -> 'b;
  effc: 'c. 'c eff -> (('c,'b) continuation -> 'b) option
}
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let body () = 0
let main () =
  try_with body () {
    effc = fun (type a) (e: a eff) -> match e with
      | Op1 _n -> Some (fun (k: (a, _) continuation) ->
          continue k 1
        )
      | Op2 _n -> Some (fun (k: (a, _) continuation) ->
          continue k 1
      )
  }
