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
(* let sequence_transformer sequence = handler
  | effect (Call n) k ->
    (fun i ->
       let j = max i n in
       k (sequence n) j)
  | x -> (fun n -> n)
  | finally g -> g 0
;; *)
(* let mu f a =
  with sequence_transformer a handle
  f (fun x -> perform (Call x))
;; *)
(* let f a = 0 * a 10 *)
(* mu f (fun i -> 30 + i * i) *)

let main () =
  let f a = 0 * a 10 in
  let sequence = (fun i -> 30 + i * i) in
  match_with (fun () ->
    f (fun x -> perform (Call x))
  ) () {
    retc = (fun x -> (fun n -> n));
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Call n -> Some (fun (k: (a, _) continuation) ->
        (fun i ->
           let j = max_ i n in
           continue k (sequence n) j)
        )
  } 0

[@@@assert "typeof(main) <: unit -> {z: int | z = 10}"]