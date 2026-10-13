; Well-foundedness on Bool excludes both loops and the two-state cycle.
(set-logic HORN)
(declare-wfp P (Bool Bool) Bool)
(define-fun-rec f ((x Bool)) Bool x)
(assert (P false true))
(check-sat)
