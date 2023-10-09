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

let main () =
  let inner () = perform (Op1 1) in
  let outer () =
    try_with inner () {
      effc = fun (type zz) (e: zz eff) -> match e with
      | Op1 n -> Some (fun (k: (zz, _) continuation) ->
          10 + perform (Op2 2) + continue k n
        )
      | Op2 n -> Some (fun (k: (zz, _) continuation) ->
          -1
        )
    }
  in
  try_with outer () {
    effc = fun (type zz) (e: zz eff) -> match e with
    | Op1 n -> Some (fun (k: (zz, _) continuation) ->
        -1
      )
    | Op2 n -> Some (fun (k: (zz, _) continuation) ->
        20 + continue k n
      )
  }


[@@@assert "typeof(main) <: unit -> {z: int | z = 33}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 30}"]