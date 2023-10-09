type[@boxed] 'a eff =
| Pick : int -> bool eff

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

let[@annot_MB "
  ctx -> (unit -> ({Pick: s1} |> int / s => s)) -> int
"] expectation _ctx body =
  try_with body () {
    effc = fun (type a) (e: a eff) -> match e with
      | Pick p -> Some (fun (k: (a, _) continuation) ->
          p * (continue k true) + (100 - p) * (continue k false)
        )
  }

let main p x y =
  expectation (p, x, y)(*dummy*) (fun () ->
    if perform (Pick p) then x else y
  )

[@@@assert "typeof(main) <: (p: int) -> (x: int) -> (y: int) -> {z: int | z = p * x + (100 - p) * y}"]

