(declare-fun |#tvar5| () Int)
(declare-fun |#tvar6| () Int)
(declare-fun |#tvar7| () Int)
(declare-fun |#tvar8| () Int)
(declare-fun |#tvar9| () Int)
(declare-fun |#tvar10| () Int)
(declare-fun |#tvar11| () Int)
(declare-fun |#tvar12| () Int)
(assert (let ((a!1 (or (< |#tvar9| 4)
               (not (= |#tvar5| (+ |#tvar9| 1)))
               (not (= |#tvar6| (+ |#tvar10| 3)))
               (not (= |#tvar7| (+ |#tvar11| 10)))
               (not (= |#tvar8| (+ |#tvar12| 10)))))
      (a!2 (or (not (= |#tvar5| (+ |#tvar9| 1)))
               (not (= |#tvar6| (+ |#tvar10| 2)))
               (not (= |#tvar7| |#tvar11|))
               (not (= |#tvar8| |#tvar12|))))
      (a!3 (or (<= |#tvar12| |#tvar10|)
               (< |#tvar9| |#tvar11|)
               (not (= |#tvar5| (- |#tvar9|)))
               (not (= |#tvar6| (- |#tvar10|)))
               (not (= |#tvar7| |#tvar11|))
               (not (= |#tvar8| |#tvar12|))))
      (a!4 (and (= |#tvar5| 0)
                (= |#tvar6| 0)
                (= |#tvar7| 0)
                (= |#tvar8| 0)
                (>= (+ 1
                       (* (- 26) |#tvar5|)
                       (* (- 13) |#tvar6|)
                       (* 3 |#tvar7|)
                       (* 68 |#tvar8|))
                    0)))
      (a!5 (and (not (= |#tvar6| 0))
                (>= (+ |#tvar6| (- |#tvar8|)) 0)
                (>= (+ (* 3 |#tvar5|) (- |#tvar6|)) 0)
                (>= (+ (- 1)
                       (* (- 153) |#tvar5|)
                       (* 86 |#tvar6|)
                       (* 717 |#tvar7|)
                       (* (- 735) |#tvar8|))
                    0)
                (>= (+ (- 2)
                       (* 36 |#tvar5|)
                       (* (- 17) |#tvar6|)
                       (* (- 212) |#tvar7|)
                       (* 213 |#tvar8|))
                    0)))
      (a!6 (or (not (= |#tvar9| 0))
               (not (= |#tvar10| 0))
               (not (= |#tvar11| 0))
               (not (= |#tvar12| 0))
               (< (+ 1
                     (* (- 26) |#tvar9|)
                     (* (- 13) |#tvar10|)
                     (* 3 |#tvar11|)
                     (* 68 |#tvar12|))
                  0)))
      (a!7 (or (= |#tvar10| 0)
               (< (+ |#tvar10| (- |#tvar12|)) 0)
               (< (+ (* 3 |#tvar9|) (- |#tvar10|)) 0)
               (< (+ (- 1)
                     (* (- 153) |#tvar9|)
                     (* 86 |#tvar10|)
                     (* 717 |#tvar11|)
                     (* (- 735) |#tvar12|))
                  0)
               (< (+ (- 2)
                     (* 36 |#tvar9|)
                     (* (- 17) |#tvar10|)
                     (* (- 212) |#tvar11|)
                     (* 213 |#tvar12|))
                  0))))
  (not (or (and a!1 a!2 a!3) a!4 a!5 (and a!6 a!7)))))
(check-sat)
(get-model)