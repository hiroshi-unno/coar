type[@boxed] 'a eff =
| Op : int eff
type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
type ('a,'b) handler = { retc: 'a -> 'b; exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option}
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"


let id x : int = x

let main () =
  try_with (fun () ->
    id (perform Op)
  ) () {
  effc = fun (type a) (e: a eff) -> match e with
    | Op -> Some (fun (k: (a, _) continuation) ->
        continue k 1 + continue k 2
      )
  }
[@@@assert "typeof(main) <: unit -> {z: int | z = 3}"]

let main2 () =
  try_with (fun () ->
    let arg = perform Op in id arg
  ) () {
  effc = fun (type a) (e: a eff) -> match e with
    | Op -> Some (fun (k: (a, _) continuation) ->
        continue k 1 + continue k 2
      )
  }
[@@@assert "typeof(main2) <: unit -> {z: int | z = 3}"]