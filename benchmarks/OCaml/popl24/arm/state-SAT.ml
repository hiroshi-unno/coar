type[@boxed] 'a eff =
| Lookup : int(*ctx*) -> int eff
| Update : int(*ctx*) * int -> unit eff

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


(* from Andrej Bauer and Matija Pretnar. Programming with algebraic effects and handlers. 2015. *)

let[@annot_MB "
  int -> (unit -> ({Lookup: s1, Update: s2} |> int / s => s)) -> int
"] state x (main : unit -> int) =
  match_with main () {
    retc = (fun y -> (fun s -> y));
    exnc = raise;
    effc = fun (type b) (e : b eff) ->
      match e with
      | Lookup ctx -> Some (fun (k : (b, _) continuation) ->
          fun (s : int) -> (continue k s s)[@annot "{z: int | z = ctx + s}"])
      | Update (ctx2, s') -> Some (fun k ->
          fun (_s : int) -> (continue k () s')[@annot "{z: int | z = ctx2 + 1 + s'}"])
  } x


(*****************)

(* from https://github.com/daanx/effect-bench/blob/main/src/mstate.ml *)

let main init =
  state init (fun () ->
    let rec counter c =
      let i = perform (Lookup c(*dummy*)) in
      if i = 0 then c
      else (perform (Update (c(*dummy*), i - 1)); counter (c + 1))
    in
    counter 0
  )

[@@@assert "typeof(main) <: (init: {z: int | z >= 0}) -> {z: int | z = init}"]
