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

let main_handle () =
  try_with (fun () -> if perform (Op 1) then 2 else 3) () {
    effc = fun (type a) (e: a eff) -> match e with
      | Op n -> Some (fun (k: (a, _) continuation) ->
          shift0 (fun k -> 4 * k n) + continue k true
        )
  }

let main () = reset (fun () -> main_handle ())

[@@@assert "typeof(main) <: unit -> {z: int | z = 12}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 16}"] (* should be unsat *)