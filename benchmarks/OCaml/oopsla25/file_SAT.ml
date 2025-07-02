type 'a eff =
  | Open : unit eff
  | EOF : bool eff
  | Read : unit eff
  | Close : unit eff
  | Raise : 'a eff
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

let rec f () =
  match_with
    (fun () ->
      let b = perform_atp EOF in
      if b then perform Raise else (perform_atp Read; f ()))
    ()
    {
      retc = (fun _ -> ());
      exnc = raise;
      effc =
        (fun (type b) (e : b eff) ->
          match e with
          | Open -> Some (fun (k : (b, _) continuation) -> let r = perform_atp Open in continue k r)
          | EOF -> Some (fun k -> let r = perform_atp EOF in continue k r)
          | Read -> Some (fun k -> let r = perform_atp Read in continue k r)
          | Close -> Some (fun k -> let r = perform_atp Close in continue k r)
          | Raise -> Some (fun k -> ()));
    }

let main = perform_atp Open; f (); perform_atp Close

[@@@check_toplevel "
%BEGINR
opOpen -> 1.
opEOF -> 2.
opRead -> 1.
opClose -> 1.
opRaise -> 1.
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
q0 opOpen -> (1,q1).
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
q1 opEOF -> (1,q1) /\\ (2,q2).
q1 opClose -> (1,q0).
q1 if -> (1,qT) /\\ (2,q1) \\/ (1,qF) /\\ (3,q1).
q1 unit -> true.
q1 tuple2 -> true.
q1 tuple3 -> true.
q1 tuple4 -> true.
q1 tt -> true.
q1 ff -> true.
q1 not -> true.
q1 and -> true.
q1 or -> true.
q2 opRead -> (1,q1).
q2 opEOF -> (1,q1) /\\ (2,q2).
q2 opClose -> (1,q0).
q2 if -> (1,qT) /\\ (2,q2) \\/ (1,qF) /\\ (3,q2).
q2 unit -> true.
q2 tuple2 -> true.
q2 tuple3 -> true.
q2 tuple4 -> true.
q2 tt -> true.
q2 ff -> true.
q2 not -> true.
q2 and -> true.
q2 or -> true.
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
