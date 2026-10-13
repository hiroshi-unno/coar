; Function-definition bodies must match their declared result sort.
(set-logic ALL)
(define-fun r () Real (/ 1 2))
(assert (= r 0.5))
(check-sat)
