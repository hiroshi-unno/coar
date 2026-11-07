(* The state-passing shape of benchmarks/OCaml/oopsla25/state_*.ml with the
   escaping operation answered, g a top-level function: g reads a boolean
   state through Get under its own state-passing handler, calls itself
   while the state is true and otherwise performs Ask, which its handler
   forwards by performing Ask again and resuming with the answer.  main
   runs g false under a handler that answers Ask with 7.  Get and Set are
   answer-type modifying (perform); every perform of Ask is perform_atp, so
   Ask is answer-type polymorphic and its clauses are tail-resumptive.  The
   assertion holds.

   RCaml solves the effects of each top-level binding on its own, and for g
   alone it chooses the operation signature of g's handler, Get and Set
   included, as g's latent signature; main's handler, which handles only
   Ask, then cannot type the call, and the program is refused.  The same
   program with g local to main is atp_state_forwarding_sat.ml. *)
type 'a eff = Set : bool -> unit eff | Get : bool eff | Ask : int eff
[@@boxed]

type ('a, 'b) continuation = K

type ('a, 'b) handler = {
  retc : 'a -> 'b;
  exnc : exn -> 'b;
  effc : 'c. 'c eff -> (('c, 'b) continuation -> 'b) option;
}

external perform : 'a eff -> 'a = "unknown"
external perform_atp : 'a eff -> 'a = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let rec g (init : bool) : int =
  match_with
    (fun () ->
      let y = perform Get in
      if y then g y else perform_atp Ask)
    ()
    {
      retc = (fun x _s -> x);
      exnc = raise;
      effc =
        (fun (type b) (e : b eff) ->
          match e with
          | Set x ->
              Some
                (fun (k : (b, _) continuation) (_s : bool) -> continue k () x)
          | Get -> Some (fun k (s : bool) -> continue k s s)
          | Ask -> Some (fun k -> let y = perform_atp Ask in continue k y));
    }
    init

let main () =
  let r =
    match_with
      (fun () -> g false)
      ()
      {
        retc = (fun x -> x);
        exnc = raise;
        effc =
          (fun (type b) (e : b eff) ->
            match e with
            | Ask -> Some (fun (k : (b, _) continuation) -> continue k 7));
      }
  in
  assert (r = 7)

[@@@assert "typeof(main) <: unit -> unit"]
