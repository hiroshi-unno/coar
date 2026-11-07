; Game G1 of Beyene, Chaudhuri, Popeea, Rybalchenko, "A constraint-based approach to solving games on
; infinite graphs", POPL 2014, pp. 221-233, https://doi.org/10.1145/2535838.2535860
; (Table 1), as the paper defines it, not as the authors' ConSynth input does (that input fixes
; Cinderella's moves by a template with parameters, so it asks a narrower question).
; Cinderella-Stepmother game, Section 2 of the paper: five buckets b1..b5 on a circle, all empty
; initially.  stepmother(v,v') = (b1'+..+b5' = b1+..+b5+1 /\ bi' >= bi): she pours one unit, split as she
; likes.  cinderella(v,v') = some i with bi' = 0 /\ b(i+1 mod 5)' = 0, the other buckets unchanged.
; overflow(v) = some bi > c.  The game is turn-based with Adam moving first (Section 3.1), Eve's
; deadlock losing and Adam's deadlock leaving no play; the game does not stop at an overflow.
; Bucket contents are reals (the paper's capacities 1.4 and its strategy's 0.8, 0.1 are not integers).
; Here: capacity c = 3.0, Adam = Stepmother, Eve = Cinderella, objective G not overflow.  The clauses
; are RULE SAFE (Figure 1) with inv an unknown over arbitrary relations: S1 init -> inv,
; S2 inv(v) /\ stepmother(v,v') -> safe(v') /\ exists v''. cinderella(v',v'') /\ inv(v''), S3 inv -> safe.
; Satisfiable over arbitrary relations iff Cinderella wins (the winning region, a greatest fixpoint, is a
; solution, and any solution is a set from which she can stay in it), so this is exact, not the rule's
; relative completeness.  S2's safe(v') is written as a separate goal clause.
; Expected verdict from the paper's Table 1 (Cinderella wins, c >= 3 by the round-robin strategy of Section 2).
; expected: sat
(set-logic HORN)
(declare-fun Inv (Real Real Real Real Real) Bool)
; S1
(assert (Inv 0.0 0.0 0.0 0.0 0.0))
; S3
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real)) (=> (and (Inv b1 b2 b3 b4 b5) (or (> b1 3.0) (> b2 3.0) (> b3 3.0) (> b4 3.0) (> b5 3.0))) false)))
; S2, the conjunct safe(v')
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real) (b1p Real) (b2p Real) (b3p Real) (b4p Real) (b5p Real)) (=> (and (Inv b1 b2 b3 b4 b5) (and (>= b1p b1) (>= b2p b2) (>= b3p b3) (>= b4p b4) (>= b5p b5) (= (+ b1p b2p b3p b4p b5p) (+ b1 b2 b3 b4 b5 1.0))) (or (> b1p 3.0) (> b2p 3.0) (> b3p 3.0) (> b4p 3.0) (> b5p 3.0))) false)))
; S2, the existential conjunct: Cinderella's reply
(assert (forall ((b1 Real) (b2 Real) (b3 Real) (b4 Real) (b5 Real) (b1p Real) (b2p Real) (b3p Real) (b4p Real) (b5p Real)) (=> (and (Inv b1 b2 b3 b4 b5) (and (>= b1p b1) (>= b2p b2) (>= b3p b3) (>= b4p b4) (>= b5p b5) (= (+ b1p b2p b3p b4p b5p) (+ b1 b2 b3 b4 b5 1.0))))
  (exists ((b1q Real) (b2q Real) (b3q Real) (b4q Real) (b5q Real)) (and (or (and (= b1q 0.0) (= b2q 0.0) (= b3q b3p) (= b4q b4p) (= b5q b5p)) (and (= b1q b1p) (= b2q 0.0) (= b3q 0.0) (= b4q b4p) (= b5q b5p)) (and (= b1q b1p) (= b2q b2p) (= b3q 0.0) (= b4q 0.0) (= b5q b5p)) (and (= b1q b1p) (= b2q b2p) (= b3q b3p) (= b4q 0.0) (= b5q 0.0)) (and (= b1q 0.0) (= b2q b2p) (= b3q b3p) (= b4q b4p) (= b5q 0.0))) (Inv b1q b2q b3q b4q b5q))))))
(check-sat)
