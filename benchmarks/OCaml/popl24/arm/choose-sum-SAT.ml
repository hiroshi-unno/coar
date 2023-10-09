type[@boxed] 'a eff =
| Decide : bool(*ctxinfo*) * int(*ctxinfo*) -> bool eff

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

let[@annot_MB "
  ctx -> ctx -> (unit -> ({Decide: s1} |> int / s => s)) -> int
"] choose_all _ctx1 _ctx2 (body: unit -> int) =
  match_with body () {
    retc = (fun x -> x);
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Decide _ -> Some (fun (k: (a, _) continuation) ->
          continue k true + continue k false
        )
  }


let main x y =
  choose_all x y(*dummy*) (fun () ->
    let a = if perform (Decide (false, 0)) then x else y in
    let b = if perform (Decide (true, a)) then x else y in
    a - b
  )

[@@@assert "typeof(main) <: int -> int -> {z: int | z = 0}"]
