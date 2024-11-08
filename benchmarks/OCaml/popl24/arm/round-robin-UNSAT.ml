type[@boxed] 'a eff =
| Yield : unit eff
| Spawn : (unit -> unit) -> unit eff

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

let push (x: unit -> unit) q = q := !q @ [x]
let pop_opt (q: (unit -> unit) list ref) =
  match !q with
  | [] -> None
  | x :: xs -> q := xs; Some x

(* from https://github.com/matijapretnar/eff/blob/master/examples/threads.eff *)

let[@annot_MB "
  (unit -> ({Yield: s1, Spawn: unit -> ({Yield: s1} |> unit / ss => ss) -> s2} |> unit / s => s)) -> unit
"] round_robin body =
  let q = ref [] in
  let enqueue t = push t q in
  let dequeue () =
    match pop_opt q with
    | None -> ()
    | Some t -> t ()
  in
  let rec rr_handler body =
    match_with body () {
      retc = (fun _ -> dequeue ());
      exnc = raise;
      effc = fun (type a) (e: a eff) -> match e with
        | Yield -> Some (fun (k: (a, _) continuation) ->
            enqueue (continue k); dequeue ()
          )
        | Spawn (t[@annot_MB "unit -> ({Yield: s1} |> unit / ss => ss)"]) -> Some (fun (k: (a, _) continuation) ->
            enqueue (continue k); rr_handler t
        )
    }
  in
  rr_handler body

let main init =
  let c = ref init in
  round_robin (fun () ->
    perform (Spawn (fun _ ->
      c := !c + 1; perform Yield; c := !c + 1; perform Yield;
    ));
    perform (Spawn (fun _ ->
      c := !c + 1; perform Yield; c := !c + 1; perform Yield;
    ))
  );
  !c

[@@@assert "typeof(main) <: (init: int) -> {z: int | z = init}"]
(*unsat*)