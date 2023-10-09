type 'a eff =
| Op : int -> int eff
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

let body () = if false then 0 else perform (Op 3)
(* let body () = perform (Op 3) *)

let main () = try_with body () {
  effc = fun (type a) (e: a eff) -> match e with
    | Op n -> Some (fun (k: (a, _) continuation) ->
        2 + continue k 10
      )
}

(* [@@@assert "typeof(main) <: unit -> {z: int | z = 10}"] *)
[@@@assert "typeof(main) <: unit -> {z: int | z = 12}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 10 || z = 12}"]
