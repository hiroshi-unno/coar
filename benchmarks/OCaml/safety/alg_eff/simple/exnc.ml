type 'a eff =
  | Op
type exn =
  | MyExn of int
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

external raise : exn -> 'a = "unknown"

let raise_exn () = raise (MyExn 1)

[@@@assert "typeof(raise_exn) <: unit -> (
  {MyExn: int -> (float -> bool) -> bool} |> float / bool => bool
)"]

let main () =
  let body (): int = raise (MyExn 1) in
  match_with body () {
    retc = (fun x -> x);
    exnc = (fun (MyExn n) -> 10 + n);
    effc = fun (type zz) (e: zz eff) -> match e with
    | Op -> Some (fun (k: (zz, _) continuation) ->
        -1
      )
  }

[@@@assert "typeof(main) <: unit -> {z: int | z = 11}"]
(* [@@@assert "typeof(main) <: unit -> {z: int | z = 10}"] *)