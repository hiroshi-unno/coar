type[@boxed] 'a eff =
| Select_int : int list -> int eff

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

type 'a result = Failure | Success of 'a

(* from https://github.com/matijapretnar/eff/blob/master/examples/select.eff *)

let[@annot_MB "
  ctx -> bool -> (unit -> ({Select_int: s1} |> bool / s => s)) -> int list result
"] selection_collector _ctx desired_outcome (body: unit -> bool) =
  match_with body () {
    retc = (fun outcome ->
      fun selected ->
        if outcome = desired_outcome then Success selected else Failure
    );
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Select_int choices -> Some (fun (k: (a, _) continuation) ->
        fun selected ->
            let rec try_choice = function
            | [] -> Failure
            | (y::ys : int list) ->
                (match (continue k y) (y::selected) with
                  | Success lst -> Success lst
                  | Failure -> try_choice ys)
            in try_choice choices
        )
  } []

let main x =
  selection_collector x(*dummy*) true (fun () ->
    let a = perform (Select_int [x; -x]) in
    a * a = x * x
  )

let test x =
  main x = Success [x]
[@@@assert "typeof(test) <: int -> {z: bool | z = false}"]
(*unsat*)