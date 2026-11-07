(* The assertion holds: g reaches [perform_atp Raise], its own handler
   forwards Raise by performing it again, and main's handler discards the
   continuation and answers 0.

   Every perform of Raise is perform_atp, so Raise is answer-type
   polymorphic, and every clause handling it must resume its continuation
   in tail position; main's clause does not.  No typing exists with
   answer-type-polymorphic operations either (a typing of g gives Raise an
   answer-type-polymorphic entry, which only a tail-resumptive clause can
   handle), so the program is refused, naming the operation and the
   clause.  The same program with perform is
   benchmarks/OCaml/simple/recursive_call_under_forwarding_handler_true_sat.ml. *)
type 'a eff = Raise : 'a eff
[@@boxed]
type ('a, 'b) continuation = K
type ('a, 'b) handler = {
  retc : 'a -> 'b;
  exnc : exn -> 'b;
  effc : 'c. 'c eff -> (('c, 'b) continuation -> 'b) option;
}
external perform_atp : 'a eff -> 'a = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let rec g (n : int) : unit =
  match_with
    (fun () -> if n > 0 then g (n - 1) else perform_atp Raise)
    ()
    {
      retc = (fun () -> ());
      exnc = raise;
      effc =
        (fun (type b) (e : b eff) ->
          match e with
          | Raise -> Some (fun (k : (b, _) continuation) -> let y = perform_atp Raise in continue k y));
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
