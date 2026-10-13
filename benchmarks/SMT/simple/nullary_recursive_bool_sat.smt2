; Nullary Boolean references in recursive definitions retain their function rank.
(set-logic ALL)
(define-fun-rec p () Bool (or true p))
(assert p)
(check-sat)
