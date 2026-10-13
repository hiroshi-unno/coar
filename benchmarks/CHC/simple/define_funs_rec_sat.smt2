; define-funs-rec (here with non-recursive bodies: g calls f).  Every name is
; bound before any body is parsed.  g 0 = f 2 = 3, so P holds exactly at 3.  Expected: sat.
; Genuine recursion: define_fun_rec_sat.smt2 and define_funs_rec_mutual_sat.smt2.
(set-logic HORN)
(define-funs-rec ((f ((n Int)) Int) (g ((n Int)) Int)) ((+ n 1) (f (+ n 2))))
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x (g 0)) (P x))))
(assert (forall ((x Int)) (=> (and (P x) (not (= x 3))) false)))
(check-sat)
