; The POPL 2024 ARM benchmark `io-read-1-SAT.ml` with its ghost parameter replaced by predicate
; polymorphism, encoded by universally quantified predicates.
;
;   read_from_list _ctx lst body = match_with body () {
;     retc = fun x -> fun _ -> x;
;     Read -> fun k -> function s :: lst' -> continue k s lst' | [] -> Err }  lst
;   let read_n n l = read_from_list n(*dummy*) l (fun () ->
;                      let rec go m = if m <= 0 then Ok else let _ = perform Read in go (m-1)
;                      in go n)
;
; The reader handler pops an element per `Read` and, on the empty list, **invents** the answer
; `Err` that the continuation never produced -- answer refinement modification again, as in
; `select`.  The operation's polymorphic type is
;   Read : forall X:(result,list). (unit) -> ((v:int) -> (l:list) -> {z | X(z,l)})
;                                          -> ((l:list) -> {z | X(z,l) \/ z = Err})
; and the ghost parameter of the evaluated file (`_ctx`, the read count `n`) is the first-order
; stand-in for `X`.  `result` is encoded as a Bool (`Ok` = true, `Err` = false).
;
; Rd(X, l, z): performing Read with the ambient answer refinement X at state l answers z.
; expected: sat
(set-logic DQHORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))

(declare-forall-fun X (Bool Lst) Bool)
(declare-dep-exists-fun Rd () ((Array Bool (Array Lst Bool)) Lst Bool) Bool)

; --- the handler, verified once for every X ---
; s :: lst' -- the continuation is resumed with s at state lst'
(assert (forall ((s Int) (l2 Lst) (z Bool)) (=> (X z l2) (Rd X (cons s l2) z))))
; [] -- the invented answer Err
(assert (Rd X nil false))
; NOTE (a modelling pitfall worth recording): there is *no* clause "Rd(X,l,z) => X(z,l)" here.
; Read moves the state from `s :: l'` to `l'`, so the answer refinement the handler's clause must
; meet is the **modified** one, not X at the outer state; demanding X(z, s::l') is simply the
; wrong obligation and makes the file `unsat` (measured while building it).  Rd *is* the modified
; refinement -- that is what answer refinement modification means -- and the clients check their
; goals against it.

; --- client 1: read one element from a non-empty list; the rest of `go` answers Ok, so
;     X := (z,l) |-> z, and the answer must be Ok ---
(assert (forall ((s Int) (l2 Lst) (z Bool))
  (=> (and (Rd (lambda ((b Bool)) (lambda ((l Lst)) b)) (cons s l2) z) (not z)) false)))
; --- client 2: a different instantiation, X := (z,l) |-> not z, reading from the empty list;
;     the answer is the invented Err.  One solution for Rd must serve both clients (one verification, several clients) ---
(assert (forall ((z Bool))
  (=> (and (Rd (lambda ((b Bool)) (lambda ((l Lst)) (not b))) nil z) z) false)))
(check-sat)
