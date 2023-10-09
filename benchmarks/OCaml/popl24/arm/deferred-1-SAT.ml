type[@boxed] 'a eff =
| Force : int eff

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

type deferred = Value of int | Thunk of int(*ctxinfo*) * (unit -> int)

[@@@rtype "Value :: (v: {z:int | p1(z)}) -> {z: deferred | z = Value(v)}"]
[@@@rtype "Thunk :: (c: {z:int | p3(z)}) -> (f:unit -> {z: int | p4(z, c)}) -> {z: deferred | z = Thunk(c, f)}"]

let[@annot_MB "
  int -> (unit -> int) -> (unit -> ({Force: s} |> int / s2 => s2)) -> int
"] lazy_ (ctx: int) t (body: unit -> int) =
  match_with body () {
    retc = (fun y -> (fun s -> y));
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Force -> Some (fun (k: (a, _) continuation) ->
          function
          | Value v -> continue k v (Value v)
          | Thunk (_, t) -> let v = t () in continue k v (Value v)
        )
  } (Thunk (ctx(*dummy*), t))

let test r(*ctx*) thunk =
  lazy_ r(*dummy*) thunk (fun () ->
    let res = perform Force in res
  )
[@@@assert "typeof(test) <: (r: int) -> (unit -> {z:int | z = r}) -> {z:int | z = r}"]
