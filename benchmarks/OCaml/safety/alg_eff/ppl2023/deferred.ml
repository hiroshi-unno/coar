type[@boxed] 'a eff =
| Force : unit -> int eff

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

(* from Andrej Bauer and Matija Pretnar. Programming with algebraic effects and handlers. 2015. *)

type deferred = Value of int | Thunk of (unit -> int)

(* let lazy t =
  new lazy @ (Thunk t) with
    operation force () @ v ->
    (match v with
      | Value v -> (v, Value v)
      | Thunk t -> let v = t () in (v, Value v))
end *)
let[@annot_MB "
  (unit -> int) -> (unit -> ({Force: s} |> int / s2 => s2)) -> int
"] lazy_ t (body: unit -> int) =
  match_with body () {
    retc = (fun y -> (fun s -> y));
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Force _ -> Some (fun (k: (a, _) continuation) ->
          fun d ->
            match d with
            | Value v -> continue k v (Value v)
            | Thunk t -> let v = t () in continue k v (Value v)
        )
  } (Thunk t)

let main () =
  lazy_ (fun () -> 1 + 2 + 3) (fun () ->
    let res = perform (Force ()) in
    res
  )

[@@@assert "typeof(main) <: unit -> {z: int | z = 6}"]