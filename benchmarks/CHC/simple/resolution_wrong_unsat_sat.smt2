; A constrained Horn problem this tool answers `unsat` on, wrongly.
;
; The solution checker rejects the refutation: one derivation is reported as
;   "resolution example (...) does not follow from its clause instance and parents"
; so the answer rests on a resolution step that does not hold. Run it with a
; configuration that sets `check_solution` to see the report.
;
; Two other solvers answer `sat` on this file -- z3's Horn engine and hoice
; -- so the verdict is settled from outside as well as from inside, and
; needs no argument about where the file came from.
;
; Where it comes from, because that is the part worth keeping. It is a
; dependently quantified problem -- one whose quantified sort ranges over every
; non-empty type -- with that sort fixed at TWO elements and the result written
; out as an ordinary Horn problem. The source answers `sat` with all three of
; its constraints verified against the model, and a solution that works for
; every type works for a two-element one, so this instance is satisfiable and
; the `unsat` is wrong. The one-element instance of the same source answers
; `sat`, which is what a sound refutation route would also do here.
;
; It is kept as a plain Horn file because nothing about the defect needs the
; quantified-sort extension: the wrong answer is produced by the ordinary
; solving loop reading this file.
(set-logic HORN)
(declare-datatypes ((|#fin2_alpha| 0)) (((|#fin2_alpha_1|) (|#fin2_alpha_0|))))
(declare-fun I
             ((Array |#fin2_alpha| Bool) |#fin2_alpha| Int |#fin2_alpha|)
             Bool)

(assert (forall ((A (Array |#fin2_alpha| Bool)) (B |#fin2_alpha|))
  (I A B 0 B)))
(assert (forall ((A Int)
         (B (Array |#fin2_alpha| Bool))
         (C |#fin2_alpha|)
         (D |#fin2_alpha|)
         (E |#fin2_alpha|)
         (F Int)
         (G Int))
  (let ((a!1 (and (not (= false (select B D))) (not (= true (select B E)))))
           (a!2 (and (not (= false (select B E))) (not (= true (select B D))))))
       (=> (and (I B C G E)
                (= A (+ 1 G))
                (> 0 (- (- 1) F))
                (> 0 (- G F))
                (or a!1 a!2))
           (I B C A D)))
    ))
(assert (forall ((A (Array |#fin2_alpha| Bool))
         (B |#fin2_alpha|)
         (C |#fin2_alpha|)
         (D Int))
  (let ((a!1 (not (= 0 (+ (- 1) (mod D 2)))))
           (a!2 (or (not (= false (select A B))) (not (= true (select A C)))))
           (a!3 (or (not (= false (select A C))) (not (= true (select A B)))))
           (a!4 (or (not (= false (select A B))) (not (= false (select A C)))))
           (a!5 (or (not (= true (select A B))) (not (= true (select A C))))))
     (let ((a!6 (or (not (= 0 (mod D 2))) (and a!4 a!5))))
       (=> (and (I A B D C) (> 0 (- (- 1) D)) (or a!1 (and a!2 a!3)) a!6)
           false)))
    ))


(check-sat)
(exit)
