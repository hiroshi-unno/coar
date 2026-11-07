(* The operation Ask is performed by a top-level item with no handler around it: OCaml ends the run with Effect.Unhandled, and RCaml reads the escaping operation as a failure. *)
type 'a eff = Ask : int eff
type exn = Neg of unit
type ('a, 'b) continuation = K
type ('a,'b) handler = {
  retc: 'a -> 'b;
  exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option
}
external perform : 'a eff -> 'a = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"
external raise : exn -> 'a = "unknown"

let v = perform Ask + 1
[@@@assert "typeof(v) <: int"]
