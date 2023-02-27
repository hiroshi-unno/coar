type[@boxed] 'a eff =
| Get : int(*ctxinfo*) -> int eff
| Set : int -> unit eff

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

(* from https://github.com/ocaml-multicore/effects-examples/blob/master/state.ml *)


let main () =
  let body () =
    let n = perform (Get 0(*Dummy*)) in
    perform (Set 42);
    let m = perform (Get 1(*Dummy*)) in
    [n; m]
  in
  match_with body () {
    retc = (fun res -> (fun x -> (x, res)));
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Get _ctx -> Some (fun (k: (a, _) continuation) ->
          fun (x:int) -> continue k x x
        )
      | Set y -> Some (fun (k: (a, _) continuation) ->
          fun _x -> continue k () y
        )
  } 0

[@@@assert "typeof(main) <: unit -> {z: int | z = 42} * {z: int list | z = ::(0, ::(42, []))}"]