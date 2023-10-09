type[@boxed] 'a eff =
| Yield : int -> int eff

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

(* from https://github.com/matijapretnar/eff/blob/master/examples/yield.eff *)

type 'a tree =
  | Leaf of 'a
  | Node of 'a tree * 'a tree

type iterator =
| Result of int tree
| Susp of int * (int -> iterator)

[@@@rtype "Result :: (t: {z: int | p0(z)} tree) -> {z: iterator | z = Result(t)}"]
[@@@rtype "Susp ::  (x: {z: int | p1(z)}) -> (f: ((y: {z: int | p2(z, x)}) -> {z: iterator | p3(z, x, y)})) -> {z: iterator | z = Susp(x, f)}"]


let[@annot_MB "
    (unit -> ({Yield: s1} |> int tree / s => s)) -> iterator
"] run body =
  match_with body () {
    retc = (fun x -> Result x);
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Yield (x: int) -> Some (fun (k: (a, _) continuation) ->
          Susp (x, continue k)
        )
  }

let rec depthWalk = function
| Node (l, r) ->
    let l' = depthWalk l in
    let r' = depthWalk r in
    Node (l', r')
| Leaf a ->
    let b = perform (Yield a) in
    Leaf b

let rec incr = function
  | Susp(x, k) -> incr (k (x + 1))
  | Result r -> r

let incr_tree t =
  let iter_tree =
    run (fun () ->
      depthWalk t
    )
  in
  incr iter_tree

[@@@assert "typeof(incr_tree) <: {z: int | z = 0} tree -> {z: int | z = 1} tree"]
