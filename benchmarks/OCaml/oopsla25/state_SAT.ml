type 'a eff = Set : bool -> unit eff | Get : bool eff | Raise : 'a eff
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

let rec g init =
  match_with
    (fun () ->
      let y = perform Get in
      if y then g y else perform_atp Raise)
    ()
    {
      retc = (fun () _s -> ());
      exnc = raise;
      effc =
        (fun (type b) (e : b eff) ->
          match e with
          | Set x ->
              Some
                (fun (k : (b, _) continuation) (_s : bool) -> continue k () x)
          | Get -> Some (fun k (s : bool) -> continue k s s)
          | Raise -> Some (fun k -> let y = perform_atp Raise in continue k y));
    }
    init

let main = g true

[@@@check_toplevel "
%BEGINR
opSet -> 2.
opGet -> 2.
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
q0 opSet -> (1,qV) /\\ (2,q0).
q0 opGet -> (1,q0) /\\ (2,q0).
q0 opRaise -> false.
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
