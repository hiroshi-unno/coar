(* An operation answered by an environment within a specification is written as a handler around the computation, not as a meaning of an escaping operation: ask_env returns a nonnegative integer, so v is at least 1.  The item is pure, and is read as it was before escaping operations were given a meaning. *)
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

external ask_env : unit -> int = "unknown"
[@@@rtype "ask_env :: unit -> {r: int | r >= 0}"]
let v =
  match_with (fun () -> perform Ask + 1) () {
    retc = (fun x -> x);
    exnc = (fun (Neg u) -> 0);
    effc = fun (type a) (e: a eff) -> match e with
      | Ask -> Some (fun (k : (a, _) continuation) -> continue k (ask_env ())) }
[@@@assert "typeof(v) <: {r: int | r >= 1}"]
