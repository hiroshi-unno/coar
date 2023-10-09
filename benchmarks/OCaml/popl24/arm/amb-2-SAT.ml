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


type 'a result = Failure | Success of 'a

(* from https://github.com/matijapretnar/eff/blob/master/examples/amb.eff *)

let[@annot_MB "
  ctx1 -> ctx2 -> (unit -> ({Select: s1} |> int result / s => s)) -> int result
"] amb _ctx1 _ctx2 (body: unit -> int result) =
  try_with body () {
  effc = fun (type a) (e: a eff) -> match e with
    | Select -> Some (fun (k: (a, _) continuation) ->
        match continue k true with
        | Success y -> Success y
        | Failure -> continue k false
      )
}

(******************)

let amb_find e l =
  amb e l (fun () ->
    let rec select_from l = match l with
    | [] -> None
    | x::xs -> if perform Select then Some x else select_from xs
    in
    match select_from l with
    | Some x -> if x = e then Success x else Failure
    | None -> Failure
  )

let test e l = amb_find e (e :: l) = Success e
[@@@assert "typeof(test) <: int -> int list -> {z: bool | z = true}"]
