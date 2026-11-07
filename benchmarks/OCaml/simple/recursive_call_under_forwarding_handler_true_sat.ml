(* The assertion holds: g reaches [perform Raise], its own handler forwards
   Raise by performing it again, and main's handler answers 0.

   g calls itself under its own handler, which forwards the operation, so
   the constraints bound the operation signature of g's handler clause from
   below by a signature that mentions it.  RCaml's effect type inference has
   only finite signatures and finds no typing: it refuses
   the program in words (it used to crash with an uncaught unification
   failure).  Reading Raise as answer-type polymorphic (performing it with
   perform_atp) does not help: a typing of g then gives Raise an
   answer-type-polymorphic entry, which only a clause that resumes its
   continuation in tail position can handle, and main's clause discards
   it; that variant is
   benchmarks/OCaml/safety/alg_eff/simple/atp_forwarding_caught_by_aborting_handler_true_sat.ml. *)
type 'a eff = Raise : 'a eff
[@@boxed]
type ('a, 'b) continuation = K
type ('a, 'b) handler = {
  retc : 'a -> 'b;
  exnc : exn -> 'b;
  effc : 'c. 'c eff -> (('c, 'b) continuation -> 'b) option;
}
external perform : 'a eff -> 'a = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let rec g (n : int) : unit =
  match_with
    (fun () -> if n > 0 then g (n - 1) else perform Raise)
    ()
    {
      retc = (fun () -> ());
      exnc = raise;
      effc =
        (fun (type b) (e : b eff) ->
          match e with
          | Raise -> Some (fun (k : (b, _) continuation) -> let y = perform Raise in continue k y));
    }

let main (n : int) =
  let r =
    match_with
      (fun () -> g n; 1)
      ()
      {
        retc = (fun x -> x);
        exnc = raise;
        effc =
          (fun (type b) (e : b eff) ->
            match e with Raise -> Some (fun (k : (b, _) continuation) -> 0));
      }
  in
  assert (r = 0)
