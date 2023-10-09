type[@boxed] 'a eff =
| Read : int eff

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

type result = Ok | Err

let read_n n l =
  let run =
  match_with (fun () ->
    let rec go m =
      if m <= 0 then Ok
      else let _ = perform Read in go (m - 1)
    in
    go n
  ) () {
    retc = (fun x -> fun _ -> x);
    exnc = raise;
    effc = fun (type a) (e: a eff) -> match e with
      | Read -> Some (fun (k: (a, _) continuation) ->
          fun lst ->
            match lst with
            | (s :: lst' : int list) -> let f = continue k s in f lst'
            | [] -> Err
        )
  }
  in
  run l

[@@@assert "typeof(read_n) <: {z: int | z = 1} -> {z: int list | z <> []} -> {z:result | z = Ok}"]
