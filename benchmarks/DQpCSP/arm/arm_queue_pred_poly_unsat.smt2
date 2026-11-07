; The POPL 2024 ARM benchmark `queue-1-SAT.ml` with its ghost parameters replaced by predicate
; polymorphism, encoded by universally quantified predicates.
;
;   queue initial body = match_with body () { retc = fun x -> fun _ -> x;
;     Get_next _ctx    -> fun k -> fun q -> (match q with [] -> continue k None []
;                                                       | hd::tl -> continue k (Some hd) tl);
;     Add_to_queue y   -> fun k -> fun q -> continue k () (q @ [y]) } initial
;   let main init = queue init (fun () -> perform (Add_to_queue 42);
;                                         let _ = perform (Get_next 1(*dummy*)) in
;                                         perform (Get_next 2(*dummy*)))
;   assert  main : {z: int list | z = []} -> {z: int option | z = None}
;
; **This file is the clearest illustration of what the ghost parameters are for.**  `Get_next`
; takes an argument it never uses, and the two calls pass `1` and `2`: the dummy is a *context
; label*, there so that the one operation can be given two different answer refinements at its
; two call sites.  That is exactly the role POPL 2024 § 3.2 gives predicate polymorphism —
; "calls to the same operation in different contexts [have] different control effects" — done by
; hand in a first-order way because the implementation cannot abstract the predicate itself.
;
; Here the label disappears: the two operations are verified once against a universal
; `X(z, v, q)` = "resuming with value `v` at queue `q` answers `z`", and each of the three calls
; of the client instantiates it with the answer refinement of *its* rest.  The `int option`
; results are abstracted to their `is_Some` bit, which is all the specification looks at.
; expected: unsat
(set-logic DQHORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))

(declare-forall-fun X (Bool Bool Lst) Bool)
(declare-dep-exists-fun GN () ((Array Bool (Array Bool (Array Lst Bool))) Lst Bool) Bool)
(declare-dep-exists-fun AQ () ((Array Bool (Array Bool (Array Lst Bool))) Int Lst Bool) Bool)

; --- the two operations, verified once for every X ---
; Get_next on an empty queue: continue k None []
(assert (forall ((z Bool)) (=> (X z false nil) (GN X nil z))))
; Get_next on hd :: tl: continue k (Some hd) tl
(assert (forall ((h Int) (t Lst) (z Bool)) (=> (X z true t) (GN X (cons h t) z))))
; Add_to_queue y: continue k () (q @ [y]) -- modelled at the empty queue, where q @ [y] = [y]
(assert (forall ((y Int) (z Bool)) (=> (X z false (cons y nil)) (AQ X y nil z))))

; --- client, three calls in three different contexts ---
; (1) the second Get_next (wrong): the queue is empty so the answer is None, but the
;     specification demands Some
(assert (forall ((z Bool))
  (=> (and (GN (lambda ((zz Bool)) (lambda ((v Bool)) (lambda ((q Lst)) (= zz v)))) nil z)
           (not z))
      false)))
; (2) the first Get_next, at the queue [42]: its rest is the second Get_next, which answers None
;     whenever it is reached with an empty queue
(assert (forall ((z Bool))
  (=> (and (GN (lambda ((zz Bool)) (lambda ((v Bool)) (lambda ((q Lst)) (=> (= q nil) (not zz)))))
               (cons 42 nil) z)
           z)
      false)))
; (3) the Add_to_queue: its rest is the two Get_nexts, which answer None from the queue [42]
(assert (forall ((z Bool))
  (=> (and (AQ (lambda ((zz Bool)) (lambda ((v Bool)) (lambda ((q Lst))
                (=> (= q (cons 42 nil)) (not zz)))))
               42 nil z)
           z)
      false)))
(check-sat)
