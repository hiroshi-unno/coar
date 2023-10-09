type[@boxed] 'a eff =
| Call : int -> int eff

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

let max_ a b : int = if a >= b then a else b

(* from https://github.com/matijapretnar/eff/blob/master/examples/modulus.eff *)

let[@annot_MB "
((int -> ({Call: s1} |> int / s => s)) -> ({Call: s1} |> int / s => s)) -> (int -> int) -> int
"] mu f (sequence: int -> int) =
  match_with (fun () ->
    (f (fun x -> perform (Call x)): int)
  ) () {
    retc = (fun x -> (fun n -> n));
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Call n -> Some (fun (k: (a, _) continuation) ->
        fun (i: int) ->
          let j = max_ i n in
          continue k (sequence n) j
        )
  } 0

(**************)

let test _r(*ctx*) a b =
    let f a = 0 * a 10 in
    mu f a = mu f b
[@@@assert "typeof(test) <: (r:int)
  -> ((xa:int) -> {z:int| xa = 10 => z = r})
  -> ((xb:int) -> {z:int| xb = 10 => z = r})
  -> {z: bool | z = false}"]
(*unsat*)