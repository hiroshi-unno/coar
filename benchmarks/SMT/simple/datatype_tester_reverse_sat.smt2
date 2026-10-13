; Constructor testers retain independent instances and explicit signature constraints.
(set-logic ALL)
(declare-datatype E (par (T) ((a) (b))))
(declare-const x (E Bool))
(declare-const y (E Int))
(assert ((_ is b) y))
(assert ((_ is a) x))
(check-sat)
