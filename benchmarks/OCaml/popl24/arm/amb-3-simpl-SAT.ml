type[@boxed] 'a eff =
| Select : bool eff

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


(* from https://github.com/matijapretnar/eff/blob/master/examples/amb.eff *)

let[@annot_MB "
  ctx1 -> ctx2 -> (unit -> ({Select: s1} |> bool / s => s)) -> bool
"] amb _ctx1 _ctx2 (body: unit -> bool) =
  try_with body () {
  effc = fun (type a) (e: a eff) -> match e with
    | Select -> Some (fun (k: (a, _) continuation) ->
        if continue k true then true else continue k false
      )
}

(******************)

let amb_find e l =
  amb e l (fun () ->
    let rec select_from e l = match l with
    | [] -> false
    | x::xs -> if perform Select then x = e else select_from e xs
    in
    select_from e l
  )

let test e' e = amb_find e (e' :: e :: [])
[@@@assert "typeof(test) <: int -> int -> {z: bool | z = true}"]
