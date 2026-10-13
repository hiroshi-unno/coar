; A constructor qualification fixes its result datatype instance.
(set-logic ALL)
(declare-datatypes ((E 1)) ((par (T) ((nil) (cons (head T) (tail (E T)))))))
(declare-const x (E Bool))
(assert (= x (cons true (as nil (E Bool))))) (assert (not (head x)))
(check-sat)
