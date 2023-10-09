type[@boxed] 'a eff =
| Write : int -> unit eff

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

let[@annot_MB "
  (unit -> ({Write: s} |> unit / s3 => s3)) -> unit * int list
"] accumulate (body: unit -> unit) =
  match_with body () {
    retc = (fun v -> (v, []));
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Write x -> Some (fun (k: (a, _) continuation) ->
          let (v, xs) = continue k () in (v, x :: xs)
        )
  }

let write_all l =
  accumulate (fun () ->
    let rec go li = match li with
    | [] -> ()
    | s :: ss -> let _ = perform (Write s) in go ss
    in
    go l
  )

[@@@assert "typeof(write_all) <: {z:int list | z = []} -> {z: unit * int list | (z = Tuple(u, v) => v = [])}"]
