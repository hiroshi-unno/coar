; Game G3 of Beyene, Chaudhuri, Popeea, Rybalchenko, "A constraint-based approach to solving games on
; infinite graphs", POPL 2014, pp. 221-233, https://doi.org/10.1145/2535838.2535860
; (Table 1; Section 5.2), the dual side: Cinderella's safety objective in G3's game, where Adam =
; Cinderella moves first and Eve = Stepmother.  The paper reports that Stepmother wins F overflow, so
; Cinderella has no strategy for G not overflow and this system is unsatisfiable.
; Cinderella-Stepmother game, Section 2 of the paper: five buckets b1..b5 on a circle, all empty
; initially.  stepmother(v,v') = (b1'+..+b5' = b1+..+b5+1 /\ bi' >= bi): she pours one unit, split as she
; likes.  cinderella(v,v') = some i with bi' = 0 /\ b(i+1 mod 5)' = 0, the other buckets unchanged.
; overflow(v) = some bi > c.  The game is turn-based with Adam moving first (Section 3.1), Eve's
; deadlock losing and Adam's deadlock leaving no play; the game does not stop at an overflow.
; Bucket contents are reals (the paper's capacities 1.4 and its strategy's 0.8, 0.1 are not integers).
; Here: capacity c = 1.4.  I(v): Cinderella to move, J(v): Stepmother to move; I(v) -> safe(v) and
; some Cinderella move lands in J; every pour from J is safe and lands in I.  Exact for the same reason
; as RULE SAFE over arbitrary relations (the winning region is the greatest solution).
; Expected verdict from the paper's Table 1 (Stepmother wins at c = 1.4; Section 2: she wins for every c < 1.5).
; expected: unsat
(set-logic HORN)
(declare-fun I (Real Real Real Real Real) Bool)
(declare-fun J (Real Real Real Real Real) Bool)
(assert (I 0.0 0.0 0.0 0.0 0.0))
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real)) (=> (and (I b1 b2 b3 b4 b5) (or (> b1 1.4) (> b2 1.4) (> b3 1.4) (> b4 1.4) (> b5 1.4))) false)))
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real)) (=> (I b1 b2 b3 b4 b5) (exists ((b1p Real) (b2p Real) (b3p Real) (b4p Real) (b5p Real)) (and (or (and (= b1p 0.0) (= b2p 0.0) (= b3p b3) (= b4p b4) (= b5p b5)) (and (= b1p b1) (= b2p 0.0) (= b3p 0.0) (= b4p b4) (= b5p b5)) (and (= b1p b1) (= b2p b2) (= b3p 0.0) (= b4p 0.0) (= b5p b5)) (and (= b1p b1) (= b2p b2) (= b3p b3) (= b4p 0.0) (= b5p 0.0)) (and (= b1p 0.0) (= b2p b2) (= b3p b3) (= b4p b4) (= b5p 0.0))) (J b1p b2p b3p b4p b5p))))))
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real) (b1p Real) (b2p Real) (b3p Real) (b4p Real) (b5p Real)) (=> (and (J b1 b2 b3 b4 b5) (and (>= b1p b1) (>= b2p b2) (>= b3p b3) (>= b4p b4) (>= b5p b5) (= (+ b1p b2p b3p b4p b5p) (+ b1 b2 b3 b4 b5 1.0))) (or (> b1p 1.4) (> b2p 1.4) (> b3p 1.4) (> b4p 1.4) (> b5p 1.4))) false)))
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real) (b1p Real) (b2p Real) (b3p Real) (b4p Real) (b5p Real)) (=> (and (J b1 b2 b3 b4 b5) (and (>= b1p b1) (>= b2p b2) (>= b3p b3) (>= b4p b4) (>= b5p b5) (= (+ b1p b2p b3p b4p b5p) (+ b1 b2 b3 b4 b5 1.0)))) (I b1p b2p b3p b4p b5p))))
(check-sat)
