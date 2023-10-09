type[@boxed] 'a eff =
| Dummy
type exn =
| MyExn

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
external raise : exn -> 'a = "unknown"

(* from Andrej Bauer and Matija Pretnar. Programming with algebraic effects and handlers. 2015. *)

let[@annot_MB "
  ctx -> (unit -> ({MyExn: s} |> int / s2 => s2)) -> int option
"] optionize _ctx (body: unit -> int) =
  match_with body () {
    retc = (fun x -> Some x);
    exnc = (fun MyExn -> None);
    effc = fun (type a) (e: a eff) ->
      match e with
      | Dummy -> Some (fun (k : (a, _) continuation) ->
          None
        )
  }

let safe_div n m =
  optionize (n, m)(*dummy*) (fun () ->
      if m = 0 then raise MyExn else n / m
  )

[@@@assert "typeof(safe_div) <: int -> {z:int | z = 0} -> {z: int option | z <> None}"]
(*unsat*)