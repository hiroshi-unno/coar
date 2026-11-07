(* As toplevel_raise_unreachable_sat.ml, on -1: the exception Neg escapes the top level, which OCaml reports as an uncaught exception and RCaml as a failure, whatever the assertion says of the value. *)
type 'a eff = Exn_no_operation
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

let check n = if n < 0 then raise (Neg ()) else n
let r = check (-1)
[@@@assert "typeof(r) <: int"]
