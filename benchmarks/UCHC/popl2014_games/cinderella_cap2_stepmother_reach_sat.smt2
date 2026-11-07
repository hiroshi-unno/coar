; Game G2 of Beyene, Chaudhuri, Popeea, Rybalchenko, "A constraint-based approach to solving games on
; infinite graphs", POPL 2014, pp. 221-233, https://doi.org/10.1145/2535838.2535860
; (Table 1), the dual side: the same game as the ECHC file of the same name, read as Stepmother's
; reachability objective F overflow.
; Cinderella-Stepmother game, Section 2 of the paper: five buckets b1..b5 on a circle, all empty
; initially.  stepmother(v,v') = (b1'+..+b5' = b1+..+b5+1 /\ bi' >= bi): she pours one unit, split as she
; likes.  cinderella(v,v') = some i with bi' = 0 /\ b(i+1 mod 5)' = 0, the other buckets unchanged.
; overflow(v) = some bi > c.  The game is turn-based with Adam moving first (Section 3.1), Eve's
; deadlock losing and Adam's deadlock leaving no play; the game does not stop at an overflow.
; Bucket contents are reals (the paper's capacities 1.4 and its strategy's 0.8, 0.1 are not integers).
; Here: capacity c = 2.0, Stepmother moves first.  W(v) holds at the positions where Stepmother is to
; move and can force an overflow, A(v) at those where Cinderella is to move; the clauses are the
; attractor's, so the least solution of the definite clauses is Stepmother's winning region, and the
; goal clause W(init) -> false is satisfiable iff Stepmother cannot win from init, i.e. (the game being
; determined) iff Cinderella wins G not overflow.  Cinderella's reply is universally quantified in A's
; premise (her five moves; expanding them would give a non-linear clause without the quantifier).
; Expected verdict from the paper's Table 1 (Cinderella wins at c = 2).  The paper's Section 5.1 also says
; "for values c <= 2 there are no strategies for the player Cinderella", which contradicts its own
; Table 1 row G2; the threshold c = 2 (Cinderella wins at 2, loses below) is the cited Hurkens et al.
; result (unverified here: the paper's reference [28] was not read).
; expected: sat
(set-logic HORN)
(declare-fun W (Real Real Real Real Real) Bool)
(declare-fun A (Real Real Real Real Real) Bool)
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real)) (=> (or (> b1 2.0) (> b2 2.0) (> b3 2.0) (> b4 2.0) (> b5 2.0)) (W b1 b2 b3 b4 b5))))
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real) (b1p Real) (b2p Real) (b3p Real) (b4p Real) (b5p Real)) (=> (and (and (>= b1p b1) (>= b2p b2) (>= b3p b3) (>= b4p b4) (>= b5p b5) (= (+ b1p b2p b3p b4p b5p) (+ b1 b2 b3 b4 b5 1.0))) (or (> b1p 2.0) (> b2p 2.0) (> b3p 2.0) (> b4p 2.0) (> b5p 2.0))) (W b1 b2 b3 b4 b5))))
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real) (b1p Real) (b2p Real) (b3p Real) (b4p Real) (b5p Real)) (=> (and (and (>= b1p b1) (>= b2p b2) (>= b3p b3) (>= b4p b4) (>= b5p b5) (= (+ b1p b2p b3p b4p b5p) (+ b1 b2 b3 b4 b5 1.0))) (A b1p b2p b3p b4p b5p)) (W b1 b2 b3 b4 b5))))
(assert (forall ((b1p Real) (b2p Real) (b3p Real) (b4p Real) (b5p Real)) (=> (forall ((b1q Real) (b2q Real) (b3q Real) (b4q Real) (b5q Real)) (=> (or (and (= b1q 0.0) (= b2q 0.0) (= b3q b3p) (= b4q b4p) (= b5q b5p)) (and (= b1q b1p) (= b2q 0.0) (= b3q 0.0) (= b4q b4p) (= b5q b5p)) (and (= b1q b1p) (= b2q b2p) (= b3q 0.0) (= b4q 0.0) (= b5q b5p)) (and (= b1q b1p) (= b2q b2p) (= b3q b3p) (= b4q 0.0) (= b5q 0.0)) (and (= b1q 0.0) (= b2q b2p) (= b3q b3p) (= b4q b4p) (= b5q 0.0))) (W b1q b2q b3q b4q b5q))) (A b1p b2p b3p b4p b5p))))
(assert (=> (W 0.0 0.0 0.0 0.0 0.0) false))
(check-sat)
