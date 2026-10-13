; The formula of fn_point_hole_uninstantiated_sat.smt2 with its universally quantified
; array instantiated at ONE candidate, which is the whole difference between a query no
; solver answers and one Z3 decides in well under a second.
;
; The candidate is the POINT HOLE
;
;   a := (lambda n. n /= i)
;
; -- the array that is false exactly at the index the formula reads, and nowhere else, so
; it trivially has no two consecutive falses.  It is the simplest candidate that can work
; and here it is the witness.
;
; Why instantiating is sound where it is used.  A universal may be instantiated at any
; value and the instance is implied by it, so an instance of a consequence is a
; consequence too: invalidating the instance refutes the original system just as well,
; with one quantified array fewer for the solver to invent.  The converse does not hold
; and is not used -- a VALID instance says nothing about the general statement.
;
; expected: sat (in well under a second, where the uninstantiated twin does not answer at
; 30 s).  Keep the two together: the pair is the measurement, not either file alone.
(set-logic ALL)
(declare-const m Int)
(declare-const b (Array Int Bool))
(declare-const c (Array Int Bool))
(assert (not
  (exists ((i Int))
    (let ((a (lambda ((n Int)) (not (= n i)))))
      (or (select a i)
          (not (select c m))
          (and (not (select b (+ m 1))) (not (select b m)))
          (and (not (select b (+ i 1))) (not (select b i)))
          (exists ((j Int)) (and (not (select b (+ j 1))) (not (select b j))))
          (exists ((k Int)) (and (not (select a (+ k 1))) (not (select a k)))))))))
(check-sat)
