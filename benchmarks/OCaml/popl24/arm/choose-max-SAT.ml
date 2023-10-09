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
  ctx -> ctx -> ctx -> ctx -> (unit -> ({Decide: s1} |> int / s => s)) -> int
"] choose_max _ctx1 _ctx2 _ctx3 _ctx4 (body: unit -> int) =
  try_with body () {
    effc = fun (type b) (e: b eff) -> match e with
      | Decide _ -> Some (fun (k: (b, _) continuation) ->
          let r1 = continue k true in
          let r2 = continue k false in
          if r1 >= r2 then r1 else r2
        )
  }

let main u v x y =
  choose_max u v x y(*dummy*) (fun () ->
    let a = if perform (Decide (false, 0)) then u else v in
    let b = if perform (Decide (true, a)) then x else y in
    a - b
  )

[@@@assert "typeof(main) <: (u:int) -> (v:{z:int|z >= u}) -> (x:int) -> (y:{z:int|z >= x}) -> {z: int | z = v - x}"]