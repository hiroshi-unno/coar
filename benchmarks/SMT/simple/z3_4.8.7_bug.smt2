; A reproducer for a Z3 4.8.7 defect, kept without a note of what the defect was.
;
; RE-MEASURED 2026-09-20 ON Z3 4.15.2 AND IT NO LONGER SHOWS ANYTHING. The file
; has no (get-model), so `sat` alone says nothing about a MODEL GENERATION
; defect, which the name suggests it was. Asked with :produce-models, the model
; asserted back into the problem as equations and re-checked, all eight values
; pinned: Z3 4.15.2 and cvc5 both answer `sat`, so the model is genuine.
;
; Nothing in the code or the documents mentions 4.8.7, and this file's only
; history entry is a directory rename, so no workaround was ever tied to it by
; name. It is kept because deleting a reproducer costs more than storing one,
; and because the method above is how the other version-tagged notes in this
; tree should be retired -- there are two more, about don't-care entries in a
; model, that name a version long past and have no reproducer at all.
;
(declare-fun |#tvar806| () Int)
(declare-fun |#tvar803| () Int)
(declare-fun |#tvar805| () Int)
(declare-fun |#tvar807| () Bool)
(declare-fun |#tvar853| () Int)
(declare-fun |#tvar850| () Int)
(declare-fun |#tvar852| () Int)
(declare-fun |#tvar854| () Bool)
(assert (let ((a!1 (not (= |#tvar806| (+ |#tvar852| (- 1)))))
      (a!2 (and (or (= |#tvar854| true) (= |#tvar807| true))
                (or (not (= |#tvar854| true)) (not (= |#tvar807| true)))))
      (a!3 (or (not (= |#tvar850| (+ |#tvar803| 1)))
               (> |#tvar803| 2147483647)
               (> 0 (+ |#tvar803| 2147483648))))
      (a!4 (and (not (= (- |#tvar852|) 0)) false))
      (a!7 (not (= (+ |#tvar852| (- |#tvar853|)) 0)))
      (a!10 (or (and (= |#tvar850| 0) false) (and (not (= |#tvar850| 0)) true)))
      (a!12 (and (not (= (- |#tvar805|) 0)) false))
      (a!15 (not (= (+ |#tvar805| (- |#tvar806|)) 0)))
      (a!18 (or (and (= |#tvar803| 0) false) (and (not (= |#tvar803| 0)) true))))
(let ((a!5 (or (and (= (- |#tvar852|) 0) true) a!4))
      (a!13 (or (and (= (- |#tvar805|) 0) true) a!12)))
(let ((a!6 (and (= (+ |#tvar852| (- |#tvar853|)) 0) a!5))
      (a!14 (and (= (+ |#tvar805| (- |#tvar806|)) 0) a!13)))
(let ((a!8 (or (and (= |#tvar854| true) false)
               (and (not (= |#tvar854| true)) (or a!6 (and a!7 false)))))
      (a!16 (or (and (= |#tvar807| true) false)
                (and (not (= |#tvar807| true)) (or a!14 (and a!15 false))))))
(let ((a!9 (or (and (= |#tvar850| 0) a!8) (and (not (= |#tvar850| 0)) false)))
      (a!17 (or (and (= |#tvar803| 0) a!16) (and (not (= |#tvar803| 0)) false))))
(let ((a!11 (or (and (<= |#tvar852| 0) a!9) (and (not (<= |#tvar852| 0)) a!10)))
      (a!19 (or (and (<= |#tvar805| 0) a!17) (and (not (<= |#tvar805| 0)) a!18))))
(let ((a!20 (or (and (<= |#tvar806| 15) a!19)
                (and (not (<= |#tvar806| 15)) false))))
(let ((a!21 (or (= 0 |#tvar852|)
                a!1
                a!2
                (and (not (= |#tvar854| true)) a!3)
                (not (= |#tvar852| |#tvar853|))
                (and (<= |#tvar853| 15) a!11)
                (and (not (<= |#tvar853| 15)) false)
                (not a!20))))
  (not a!21))))))))))
(check-sat)
