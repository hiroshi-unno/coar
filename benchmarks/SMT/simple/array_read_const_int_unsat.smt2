(set-logic ALL)
(assert (distinct (select ((as const (Array Int Int)) 3) 0) 3))
(check-sat)
