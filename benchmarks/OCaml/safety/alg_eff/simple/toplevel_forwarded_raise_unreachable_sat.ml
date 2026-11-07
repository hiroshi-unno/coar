(* A state handler answers Get with its state and forwards Raise by performing it again; on the state true the computation never raises, so no operation escapes the top level. *)
type 'a eff = Get : bool eff | Raise : 'a eff
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

let g b =
  match_with (fun () -> if perform Get then 1 else perform Raise) () {
    retc = (fun x -> fun (_s : bool) -> x);
    exnc = (fun (Neg u) -> fun (_s : bool) -> 0);
    effc = fun (type a) (e: a eff) -> match e with
      | Get -> Some (fun (k : (a, _) continuation) -> fun (s : bool) -> continue k s s)
      | Raise -> Some (fun (k : (a, _) continuation) -> let y = perform Raise in continue k y) } b
let main = g true
[@@@assert "typeof(main) <: {v: int | v = 1}"]
