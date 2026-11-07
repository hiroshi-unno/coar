(* A reader handler written with [Effect.Deep.match_with] and its
   [{ retc; exnc; effc }] record, with the final [| _ -> None] case that
   forwards every other operation, against the Effect module itself; it
   mirrors popl24/arm/io-read-1-SAT.ml, which declares the effect interface
   by hand.  [ctx] is the type of the ghost argument [_ctx]. *)

type _ Effect.t += Read : int Effect.t

(* from Andrej Bauer and Matija Pretnar. Programming with algebraic effects and handlers. 2015. *)

type result = Ok | Err

let[@annot_MB "
  ctx -> int list -> (unit -> ({Read: s} |> result / s3 => s3)) -> result
"] read_from_list _ctx lst (body: unit -> result) =
  Effect.Deep.match_with body () {
    retc = (fun x -> fun _ -> x);
    exnc = raise;
    effc = fun (type a) (e: a Effect.t) -> match e with
      | Read -> Some (fun (k: (a, _) Effect.Deep.continuation) ->
          function
          | (s :: lst' : int list) -> Effect.Deep.continue k s lst'
          | [] -> Err
        )
      | _ -> None
  } lst

let read_n n l =
  read_from_list n(*dummy*) l (fun () ->
    let rec go m =
      if m <= 0 then Ok
      else let _ = Effect.perform Read in go (m - 1)
    in
    go n
  )

[@@@assert "typeof(read_n) <: {z: int | z = 0} -> int list -> {z:result | z = Ok}"]
