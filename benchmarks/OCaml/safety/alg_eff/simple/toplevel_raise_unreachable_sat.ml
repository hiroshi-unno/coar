(* The top-level item [r] calls a function that raises when its argument is negative, on 5: no exception escapes, and an exception that escaped the top level would be a failure, as in OCaml. *)
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
let r = check 5
[@@@assert "typeof(r) <: {v: int | v = 5}"]
