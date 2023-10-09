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

let use_cont cont = 3 * cont 4

let main () =
  let body () = 2 + (perform (Op 0)) in
  try_with body () {
    effc = fun (type zz) (e: zz eff) -> match e with
    | Op _ -> Some (fun (k: (zz, _) continuation) ->
        use_cont (continue k)
      )
  }

[@@@assert "typeof(main) <: unit -> {z: int | z = 18}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 12}"] (* should be unsat *)