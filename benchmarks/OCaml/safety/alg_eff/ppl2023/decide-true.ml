type[@boxed] 'a eff =
| Decide : bool eff

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

(* from https://github.com/matijapretnar/eff/blob/master/examples/choice.eff *)
(* handle
  let x = (if perform Decide then 10 else 20) in
  let y = (if perform Decide then 0 else 5) in
    x - y
with
| effect Decide k -> k true;; *)

let main () =
  try_with (fun () ->
    let x = (if perform Decide then 10 else 20) in
    let y = (if perform Decide then 0 else 5) in
    x - y
  ) () {
    effc = fun (type a) (e: a eff) -> match e with
      | Decide -> Some (fun (k: (a, _) continuation) ->
          continue k true
        )
  }

[@@@assert "typeof(main) <: unit -> {z: int | z = 10}"]