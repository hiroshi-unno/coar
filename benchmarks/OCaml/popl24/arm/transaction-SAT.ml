type exn = MyExn

type[@boxed] 'a eff =
| Lookup : int eff
| Update : int -> unit eff

type ('a, 'b) continuation = K
type 'a effect_handler = { effc: 'b. 'b eff -> (('b,'a) continuation -> 'a) option }
type ('a,'b) handler = {
  retc: 'a -> 'b;
  exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option
}
external perform : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

external raise: exn -> 'a = "unknown"

(* from Andrej Bauer and Matija Pretnar. Programming with algebraic effects and handlers. 2015. *)

let[@annot_MB "
  int ref -> (unit -> ({Lookup: s1, Update: s2, MyExn: s3} |> unit / s => s)) -> unit
"] transaction r (main : unit -> unit) =
  match_with main () {
    retc = (fun x -> (fun s -> r := s; x));
    exnc = (fun MyExn -> (fun s -> ()));
    effc = fun (type b) (e : b eff) ->
      match e with
      | Lookup -> Some (fun (k : (b, _) continuation) ->
          fun (s : int) -> continue k s s)
      | Update s' -> Some (fun k ->
          fun (_s : int) -> continue k () s')
  } !r

(*******************)

let main b =
  let r = ref 0 in
  transaction r (fun () ->
    let (:=) (_r: int ref) i = perform (Update i) in
    let (!) (_r: int ref) = perform Lookup in

    r := 1;
    r := 2;
    if b then raise MyExn else ();
    let two = !r in
    r := 3;
    r := 40 + two
  );
  !r

[@@@assert "typeof(main) <: (b:bool) -> {z:int | z <> 2 && (z = 0 || z = 42)}"]
