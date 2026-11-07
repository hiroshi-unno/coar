(* fold_div of this corpus (benchmarks/OCaml/safety/tacas2015/fold_div.ml and fold_div-e.ml, in the directory
   named after Unno and Terauchi, Inferring Simple Solutions to Recursion-free Horn Clauses via Sampling, TACAS 2015,
   https://doi.org/10.1007/978-3-662-46681-0_10), with its exception desugared by hand into a handler: the
   top-level higher-order function fold_left is applied, in a later item, to div, which may raise, under a
   handler whose exception clause fails.
   A divisor make_list draws may be zero, so div can raise and the assertion in the handler is
   reachable. *)
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
external nondet_int : unit -> int = "unknown"
[@@@rtype "nondet_int::unit -> int"]

let rec fold_left f acc xs =
  match xs with
      [] -> acc
    | x::xs' -> fold_left f (f acc x) xs'

let rec randpos() =
 let n = nondet_int () in
  if n>=0 then n else randpos()

let rec make_list n =
  if n <= 0
  then []
  else randpos() :: make_list (n-1)

let div x y =
  if y=0 then raise (DivisionByZero ())
  else nondet_int ()

let main n m =
  match_with (fun () -> let xs = make_list n in fold_left div m xs) () {
    retc = (fun x -> x);
    exnc = (fun (DivisionByZero u) -> assert false; nondet_int ());
    effc = fun (type a) (e: a eff) -> match e with Exn_no_operation -> Some (fun (k : (a, _) continuation) -> nondet_int ()) }

[@@@assert "typeof(main) <: int -> int -> int"]
