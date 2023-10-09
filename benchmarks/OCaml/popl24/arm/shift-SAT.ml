type[@boxed] 'a eff =
| Shift : ((int -> int) -> int) -> int eff

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

(* from https://github.com/matijapretnar/eff/blob/master/examples/delimited.eff *)

let[@annot_MB "
  int -> (unit -> ({Shift: s} |> int / int => int)) -> int
"] rec reset_ (_ctx: int) body =
  try_with body () {
    effc = fun (type a) (e: a eff) -> match e with
      | Shift f -> Some (fun (k: (a, _) continuation) ->
          reset_ _ctx (fun () -> f (continue k))
        )
  }

let main n = reset_ n (fun () ->
  let s = perform (Shift (fun k -> k (k (k n)))) in s * 2 + 1
)
[@@@assert "typeof(main) <: (n:int) -> {z:int|z = 8 * n + 7}"]