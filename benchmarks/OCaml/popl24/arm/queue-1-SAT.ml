type[@boxed] 'a eff =
| Get_next : int(*ctx*) -> int option eff
| Add_to_queue : int -> unit eff

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

let rec ( @ ) l1 l2 = match l1 with [] -> l2 | hd :: tl -> hd :: (tl @ l2)

(* from https://github.com/matijapretnar/eff/blob/master/examples/threads.eff *)

[@@@rtype "[] :: {z:int list | _is_[](z)}"]
[@@@rtype ":: :: (x: int) -> (xs: int list) -> {z:int list | _is_::(z) && _get_::_0(z) = x && _get_::_1(z) = xs}"]
[@@@rtype "None :: {z: int option | _is_None(z)}"]
[@@@rtype "Some :: (x: int) -> {z: int option | _is_Some(z) && _get_Some_0(z) = x}"]

let[@annot_MB "
  int list ->
  (unit -> ({Get_next: s1, Add_to_queue: s2} |> int option / s => s)) ->
  int option
"] queue initial (body :unit -> int option) =
  match_with body () {
    retc = (fun x -> (fun _ -> x));
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Get_next _ctx -> Some (fun (k: (a, _) continuation) ->
          (fun queue -> match queue with
            | [] -> continue k None []
            | hd::tl -> continue k (Some hd) tl)
        )
      | Add_to_queue y -> Some (fun (k: (a, _) continuation) ->
          (fun queue -> continue k () (queue @ [y]))
        )
  } initial

(***************)

let main init =
  queue init (fun () ->
    perform (Add_to_queue 42);
    let _ = perform (Get_next 1(*dummy*)) in
    perform (Get_next 2(*dummy*))
  )

[@@@assert "typeof(main) <: {z:int list | z = []} -> {z: int option | z = None}"]
