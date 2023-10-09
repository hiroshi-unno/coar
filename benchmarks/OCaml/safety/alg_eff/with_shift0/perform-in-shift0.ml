external shift0 : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'a (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

type 'a eff =
| Op : int -> bool eff

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

let body () = shift0 (fun k -> k 4 + if perform (Op 1) then 2 else 3)
let main_reset (): int = reset (fun () -> 5 * body ())

let main () =
  try_with main_reset () {
    effc = fun (type a) (e: a eff) -> match e with
      | Op n -> Some (fun (k: (a, _) continuation) ->
          n + continue k true
        )
  }

[@@@assert "typeof(main) <: unit -> {z: int | z = 23}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 24}"] (* should be sat *) 
