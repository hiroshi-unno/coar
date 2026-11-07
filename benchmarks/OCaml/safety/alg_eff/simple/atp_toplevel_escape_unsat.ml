(* benchmarks/OCaml/oopsla25/state_UNSAT.ml without its automaton: g false
   reaches perform_atp Raise, its own handler forwards Raise, and nothing
   handles it at the top level, so the run ends in Effect.Unhandled.  Raise
   is answer-type polymorphic (every perform of it is perform_atp), so the
   binding's control effect is pure while it still performs Raise; a check
   that read only the control effect would accept it.  It must not be
   answered sat. *)
type 'a eff = Set : bool -> unit eff | Get : bool eff | Raise : 'a eff
[@@boxed]

type ('a, 'b) continuation = K

type 'a effect_handler = {
  effc : 'b. 'b eff -> (('b, 'a) continuation -> 'a) option;
}

type ('a, 'b) handler = {
  retc : 'a -> 'b;
  exnc : exn -> 'b;
  effc : 'c. 'c eff -> (('c, 'b) continuation -> 'b) option;
}

external perform : 'a eff -> 'a = "unknown"
external perform_atp : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let rec g init =
  match_with
    (fun () ->
      let y = perform Get in
      if y then g y else perform_atp Raise)
    ()
    {
      retc = (fun () _s -> ());
      exnc = raise;
      effc =
        (fun (type b) (e : b eff) ->
          match e with
          | Set x ->
              Some
                (fun (k : (b, _) continuation) (_s : bool) -> continue k () x)
          | Get -> Some (fun k (s : bool) -> continue k s s)
          | Raise -> Some (fun k -> let y = perform_atp Raise in continue k y));
    }
    init

let main = g false
