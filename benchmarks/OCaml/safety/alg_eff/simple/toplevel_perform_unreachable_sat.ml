(* The top-level item performs Ask only on a branch it never takes: no operation escapes. *)
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

let ask_if b = if b then perform Ask else 0
let v = ask_if false + 1
[@@@assert "typeof(v) <: {r: int | r = 1}"]
