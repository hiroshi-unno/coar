(* An answer-type-polymorphic operation forwarded through a recursion of
   handlers: g calls itself under its own handler, whose clause for Ask
   performs Ask again and resumes with the answer, and main answers Ask
   with 42 around g 3.  Every perform of Ask is perform_atp, so Ask is
   answer-type polymorphic and each clause for it is tail-resumptive; the
   assertion fails (r is 42). *)
type 'a eff = Ask : int eff
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

let rec g (n : int) : int =
  match_with
    (fun () -> if n > 0 then g (n - 1) else perform_atp Ask)
    ()
    {
      retc = (fun x -> x);
      exnc = raise;
      effc =
        (fun (type b) (e : b eff) ->
          match e with
          | Ask ->
              Some
                (fun (k : (b, _) continuation) ->
                  let r = perform_atp Ask in
                  continue k r));
    }

let main () =
  let r =
    match_with
      (fun () -> g 3)
      ()
      {
        retc = (fun x -> x);
        exnc = raise;
        effc =
          (fun (type b) (e : b eff) ->
            match e with
            | Ask -> Some (fun (k : (b, _) continuation) -> continue k 42));
      }
  in
  assert (r = 0)

[@@@assert "typeof(main) <: unit -> unit"]
