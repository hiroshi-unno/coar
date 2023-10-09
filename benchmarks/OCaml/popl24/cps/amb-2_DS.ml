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

let test e l =
  let amb_find e l =
    try_with (fun () ->
      let rec select_from l = match l with
      | [] -> None
      | x::xs -> let b = perform Select in if b then Some x else select_from xs
      in
      let r = select_from l in
      match r with
      | Some x -> let b = x = e in if b then Success x else Failure
      | None -> Failure
    ) () {
    effc = fun (type a) (e: a eff) -> match e with
      | Select -> Some (fun (k: (a, _) continuation) ->
          let r = continue k true in
          match r with
          | Success y -> Success y
          | Failure -> continue k false
        )
  }
  in
  let r = amb_find e (e :: l) in
  r = Success e

[@@@assert "typeof(test) <:
  int -> int list ->
  {z: bool | z = true}"]