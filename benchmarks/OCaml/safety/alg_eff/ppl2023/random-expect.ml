type[@boxed] 'a eff =
| Pick : float -> bool eff

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


(* from https://github.com/matijapretnar/eff/blob/master/examples/random.eff *)
(* let expectation = handler
  | v -> v
  | effect (Pick p) k ->
    p *. (k true) +. (1.0 -. p) *. (k false)
;; *)

let main () =
  try_with (fun () ->
    if perform (Pick 0.25) then 2.0 else 1.0
  ) () {
    effc = fun (type a) (e: a eff) -> match e with
      | Pick p -> Some (fun (k: (a, _) continuation) ->
          p *. (continue k true) +. (1.0 -. p) *. (continue k false)
        )
  }

[@@@assert "typeof(main) <: unit -> {z: float | z = 1.25}"]