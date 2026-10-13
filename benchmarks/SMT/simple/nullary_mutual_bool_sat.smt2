; Nullary Boolean references in recursive definitions retain their function rank.
(set-logic ALL)
(define-funs-rec ((q () Bool) (p () Bool)) ((not p) true))
(assert (and p (not q)))
(check-sat)
