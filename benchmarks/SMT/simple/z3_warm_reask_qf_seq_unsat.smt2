(set-logic ALL)
(declare-sort |#svar_a1| 0)
(declare-fun |#tvar35531| () Int)
(declare-fun |#tvar35533| () (Seq |#svar_a1|))
(declare-fun |#tvar35532| () (Seq |#svar_a1|))
(declare-fun |#tvar35534| () (Seq |#svar_a1|))
(declare-fun |#tvar35537| () (Seq |#svar_a1|))
(declare-fun |#tvar35535| () Int)
(declare-fun |#tvar35536| () (Seq |#svar_a1|))
(declare-fun |#tvar35538| () (Seq |#svar_a1|))
(assert (let ((a!1 (seq.++ |#tvar35538|
                   |#tvar35537|
                   (seq.extract |#tvar35536|
                                0
                                (- |#tvar35535| (seq.len |#tvar35537|)))))
      (a!3 (<= 0
               (- (- (+ (- 1) |#tvar35535|) (seq.len |#tvar35536|))
                  (seq.len |#tvar35537|))))
      (a!4 (not (<= 0 (+ (- (- 1) |#tvar35535|) (seq.len |#tvar35537|)))))
      (a!5 (= (seq.++ |#tvar35534| (seq.extract |#tvar35533| 0 |#tvar35531|))
              (seq.++ |#tvar35534|
                      (seq.extract (seq.++ |#tvar35533| |#tvar35532|)
                                   0
                                   |#tvar35531|))))
      (a!6 (not (<= 0 (- (+ (- 1) |#tvar35531|) (seq.len |#tvar35533|))))))
(let ((a!2 (= (seq.++ |#tvar35538|
                      (seq.extract (seq.++ |#tvar35537| |#tvar35536|)
                                   0
                                   |#tvar35535|))
              a!1))
      (a!7 (and (not a!5) a!6 (not (<= 0 (- (- 1) |#tvar35531|))))))
  (or (and (not a!2) (not a!3) a!4) a!7))))
(check-sat)
