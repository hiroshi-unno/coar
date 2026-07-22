type 'a eff = Label : int eff | Get : int eff | Set : int -> unit eff
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
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let[@annot_MB
     "\n\
     \  int -> (unit -> ({Label : s0, Get: s1, Set: s2} |> int / s => s)) -> int\n"] state
    x (main : unit -> int) =
  match_with main ()
    {
      retc = (fun y s -> y);
      exnc = raise;
      effc =
        (fun (type b) (e : b eff) ->
          match e with
          | Label ->
              Some
                (fun (k : (b, _) continuation) (s : int) ->
                  (*-1*)
                  (* zero shot *)
                  continue k 3 s
                  (* one shot *)
                  (*continue k 4 s; continue k 5 s*)
                  (* two shot *))
          | Get -> Some (fun k (s : int) -> continue k s s)
          | Set s' -> Some (fun k (_s : int) -> continue k () s'));
    }
    x

(*****************)

let main () =
  state 0 (fun () ->
      let ret = perform Label in
      let current = perform Get in
      let _ = perform (Set (current + 1)) in
      assert (current + 1 = 1);
      ret + 2)

[@@@assert "typeof(main) <: unit -> { x : int | x = 5 }"]
