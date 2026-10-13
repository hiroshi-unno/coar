; Constructor testers retain independent instances and explicit signature constraints.
(set-logic ALL)
(declare-datatype E (par (T) ((a) (b))))
(declare-const x (E Bool))
(declare-const y (E Int))
(assert ((_ is a) x))
(assert ((_ is b) y))
(assert ((_ is b) x))
(check-sat)
