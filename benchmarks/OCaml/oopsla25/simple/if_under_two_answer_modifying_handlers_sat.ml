(* An [if] under two nested state handlers, each of whose clauses take the
   state as an extra argument, so the handled body's answer type is a function
   of the state at both levels.  The inner handler answers [Get1] with its
   state and forwards [Get2], which the outer handler answers with its own;
   both states start [true], so the body returns [true] and [Bad] is never
   performed: sat.  The outer handler's clause for [Get1] is never reached
   (the inner handler answers every [Get1]), and neither handler's clause for
   [Bad] is (the body never performs it); they are there because the
   translation requires a clause for every operation of the handled body's
   inferred signature. *)

type 'a eff = Get1 : bool eff | Get2 : bool eff | Bad : unit eff
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
  let r =
    match_with
      (fun () ->
        match_with
          (fun () -> if perform Get1 then perform Get2 else false)
          ()
          {
            retc = (fun x (_s : bool) -> x);
            exnc = raise;
            effc =
              (fun (type b) (e : b eff) ->
                match e with
                | Get1 -> Some (fun (k : (b, _) continuation) (s : bool) -> continue k s s)
                | Get2 -> Some (fun k (s : bool) -> let r = perform Get2 in continue k r s)
                | Bad -> Some (fun k (s : bool) -> let r = perform Bad in continue k r s));
          }
          true)
      ()
      {
        retc = (fun x (_s : bool) -> x);
        exnc = raise;
        effc =
          (fun (type b) (e : b eff) ->
            match e with
            | Get1 -> Some (fun (k : (b, _) continuation) (s : bool) -> let r = perform Get1 in continue k r s)
            | Get2 -> Some (fun k (s : bool) -> continue k s s)
            | Bad -> Some (fun k (s : bool) -> let r = perform Bad in continue k r s));
      }
      true
  in
  if r then () else perform Bad

[@@@check_toplevel "
%BEGINR
opGet1 -> 2.
opGet2 -> 2.
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
q0 opGet1 -> (1,q0) /\\ (2,q0).
q0 opGet2 -> (1,q0) /\\ (2,q0).
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
