(* A handler record's [effc] that lists a clause for every operation and ends
   with the catch-all case [| _ -> None], the case OCaml's own [Effect.t]
   needs for exhaustiveness and which here forwards nothing, since no other
   operation exists.  [Ask] is answered [true], so the handled body never
   performs [Bad] and nothing reaches the top level: sat.  The same handler
   without the catch-all case is translated and answers sat; a translation
   that reads the catch-all as an operation clause has no operation to give
   it and stops. *)

type 'a eff = Ask : bool eff | Bad : unit eff
[@@boxed]

type ('a, 'b) continuation = K

type 'a effect_handler = {
  effc : 'b. 'b eff -> (('b, 'a) continuation -> 'a) option;
}

type ('a, 'b) handler = {
  retc : 'a -> 'b;
  exnc : exn -> 'b;
  effc : 'c. 'c eff -> (('c, 'b) continuation -> 'b) option;
}

external perform : 'a eff -> 'a = "unknown"
external perform_atp : 'a eff -> 'a = "unknown"
external try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b = "unknown"
external match_with : ('a -> 'b) -> 'a -> ('b, 'c) handler -> 'c = "unknown"
external continue : ('a, 'b) continuation -> 'a -> 'b = "unknown"

let main =
  match_with (fun () -> if perform_atp Ask then () else perform_atp Bad) ()
    { retc = (fun x -> x); exnc = raise; effc = (fun (type b) (e : b eff) -> match e with
       | Ask -> Some (fun (k : (b, _) continuation) -> continue k true)
       | Bad -> Some (fun k -> let r = perform_atp Bad in continue k r)
       | _ -> None); }

[@@@check_toplevel "
%BEGINR
opAsk -> 2.
opBad -> 1.
fail -> 0.
unit -> 0.
tuple2 -> 2.
tuple3 -> 3.
tuple4 -> 4.
tt -> 0.
ff -> 0.
not -> 1.
and -> 2.
or -> 2.
imply -> 2.
iff -> 2.
xor -> 2.
if -> 3.
%ENDR

%BEGINATA
q0 opAsk -> (1,q0) /\\ (2,q0).
q0 opBad -> false.
q0 if -> (1,qT) /\\ (2,q0) \\/ (1,qF) /\\ (3,q0).
q0 unit -> true.
q0 tuple2 -> true.
q0 tuple3 -> true.
q0 tuple4 -> true.
q0 tt -> true.
q0 ff -> true.
q0 not -> true.
q0 and -> true.
q0 or -> true.
qV unit -> true.
qV tuple2 -> (1,qV) /\\ (2,qV).
qV tuple3 -> (1,qV) /\\ (2,qV) /\\ (3,qV).
qV tuple4 -> (1,qV) /\\ (2,qV) /\\ (3,qV) /\\ (4,qV).
qV tt -> true.
qV ff -> true.
qV not -> (1,qV).
qV and -> (1,qV) /\\ (2,qV).
qV or -> (1,qV) /\\ (2,qV).
qT tt -> true.
qT ff -> false.
qT not -> (1,qF).
qT and -> (1,qT) /\\ (2,qT).
qT or -> (1,qT) \\/ (2,qT).
qT imply -> (1,qF) \\/ (2,qT).
qT iff -> (1,qT) /\\ (2,qT) \\/ (1,qF) /\\ (2,qF).
qT xor -> (1,qT) /\\ (2,qF) \\/ (1,qF) /\\ (2,qT).
qT if -> (1,qT) /\\ (2,qT) \\/ (1,qF) /\\ (3,qT).
qF tt -> false.
qF ff -> true.
qF not -> (1,qT).
qF and -> (1,qF) \\/ (2,qF).
qF or -> (1,qF) /\\ (2,qF).
qF imply -> (1,qT) /\\ (2,qF).
qF iff -> (1,qT) /\\ (2,qF) \\/ (1,qF) /\\ (2,qT).
qF xor -> (1,qT) /\\ (2,qT) \\/ (1,qF) /\\ (2,qF).
qF if -> (1,qT) /\\ (2,qF) \\/ (1,qF) /\\ (3,qF).
%ENDATA
"]
