(* A top-level higher-order function applied, in a later item, to a function that may raise; the handler turns the exception into 0, so main returns a nonnegative result on a nonnegative input. *)
type 'a eff = Exn_no_operation
type exn = DivisionByZero of unit
type ('a, 'b) continuation = K
type ('a,'b) handler = {
  retc: 'a -> 'b;
  exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option
}
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external raise : exn -> 'a = "unknown"

let apply f x = f x
let div y = if y = 0 then raise (DivisionByZero ()) else y
let main n =
  match_with (fun () -> apply div n) () {
    retc = (fun x -> x);
    exnc = (fun (DivisionByZero u) -> 0);
    effc = fun (type a) (e: a eff) -> match e with Exn_no_operation -> Some (fun (k : (a, _) continuation) -> 0) }
[@@@assert "typeof(main) <: {v: int | v >= 0} -> {r: int | r >= 0}"]
