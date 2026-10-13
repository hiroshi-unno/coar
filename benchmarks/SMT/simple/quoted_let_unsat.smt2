(set-logic ALL)
(assert (let ((|3| 4)) (= |3| 3)))
(check-sat)
