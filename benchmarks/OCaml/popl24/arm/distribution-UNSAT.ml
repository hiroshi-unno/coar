type[@boxed] 'a eff =
| Pick : int -> bool eff

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

let rec map f = function
| [] -> []
| x :: xs -> f x :: map f xs

let rec fold_right f l init =
  match l with
  | [] -> init
  | x :: xs -> f x (fold_right f xs init)

(* from https://github.com/matijapretnar/eff/blob/master/examples/random.eff *)

let combine p dist1 dist2 =
  let scale p dist = map (fun (x, q) -> (x, p * q / 100)) dist in
  let rec add ((x : int), p) = function
    | [] -> [(x, p)]
    | (y, q) :: dist ->
      if x = y then (x, p + q) :: dist else (y, q) :: add (x, p) dist
  in
  let dist1 = scale p dist1 in
  let dist2 = scale (100 - p) dist2 in
  fold_right add dist1 dist2

let[@annot_MB "
  (unit -> ({Pick: s1} |> int / s => s)) -> (int * int) list
"] distribution (body: unit -> int) =
  match_with body () {
    retc = (fun v -> [(v, 100)]);
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Pick p -> Some (fun (k: (a, _) continuation) ->
          combine p (continue k true) (continue k false)
        )
  }

(*******************)

let main p a b =
    distribution (fun () ->
      if perform (Pick p) then a else b
    )

[@@@assert "typeof(main) <: (p: {z:int | 0 <= z && z <= 100}) -> int -> int -> {z: int * int | z = Tuple(x, y) => 0 <= y && y <= 100} list"]
(*unsat*)