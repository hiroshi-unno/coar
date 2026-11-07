(* main returns n for n <> 0 and the handler's 0 for n = 0: every assertion holds. *)
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

(* No annotation on f: its effect is inferred.  The [else] branch is pure, so
   the answer types of f's computation must be equal; were they left
   unrelated, the normal return of f would never reach main's result. *)
let f n = if n = 0 then raise (DivisionByZero ()) else n

let main n =
  match_with (fun () -> f n) () {
    retc = (fun x -> x);
    exnc = (fun (DivisionByZero u) -> 0);
    effc = fun (type a) (e: a eff) -> match e with Exn_no_operation -> Some (fun (k : (a, _) continuation) -> 1) }

[@@@assert "typeof(main) <: {n:int | n = 3} -> {r:int | r = 3}"]
[@@@assert "typeof(main) <: {n:int | n = 0} -> {r:int | r = 0}"]
[@@@assert "typeof(main) <: (n:int) -> {r:int | r = n || r = 0}"]
