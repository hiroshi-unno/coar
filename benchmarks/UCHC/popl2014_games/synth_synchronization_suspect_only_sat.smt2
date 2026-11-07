; Game G9 (Synth-Synchronization) of Beyene, Chaudhuri, Popeea, Rybalchenko, "A constraint-based approach to solving games on
; infinite graphs", POPL 2014, pp. 221-233, https://doi.org/10.1145/2535838.2535860
; (Table 1; Section 6.3, the program of Figure 1 of Vechev, Yahav, Yorsh, POPL 2010, as the paper
; restates it).  v = (x, y1, y2, z, pc1, pc2, pc3), init = (x = 0 /\ z = 0 /\ all pc = l1); thread 1 does
; x := x + z twice, thread 2 z := z + 1 twice, thread 3 y1 := f(x) (f(1) = 3, f(2) = 6, else 5), then
; y2 := x, then passes l3 only if y1 != y2; error = (pc3 = l3 /\ y1 = y2).  The controller fixes, once
; at the start, the auxiliary variables c11, c21, c31, c32 (cij = l: thread i flows from lj to l, a
; single step or an atomic section), the paper's mid(w, t) with init(w) -> exists t. mid(w, t).
; Modelling choices: (1) the paper shows only thread 1's instrumentation and says the others are
; "instrumented similarly"; threads 2 and 3 are instrumented here as in the authors' ConSynth input
; (thread 2: l1 -> l3 does z := z + 2; thread 3: l1 -> l3 does both assignments, l1 -> l4 and l2 -> l4
; also take the l3 test, which blocks when it fails); the cost variable of that input is dropped.
; (2) The interleaving is the environment's (the paper's literal eve = next would let the controller
; schedule and win trivially).  With the c's left to the environment the assertion fails; many choices
; win, among them the paper's (c11, c21, c31, c32) = (3, 3, 4, 3) (explicit-state check).
; Dual side: Bad is the environment's attractor to error (least solution); the controller's initial choice
; of the c's is universally quantified in the premise of BadInit.  BadInit -> false is satisfiable iff the
; controller has a winning choice.
; expected: sat
(set-logic HORN)
(declare-fun Bad (Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun BadInit () Bool)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (= pc3 3) (= y1 y2)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T1 l1 -> l2
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc1 1) (= c11 2)) (Bad (+ x z) y1 y2 z 2 pc2 pc3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T1 l1 -> l3 atomic
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc1 1) (= c11 3)) (Bad (+ x (* 2 z)) y1 y2 z 3 pc2 pc3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T1 l2 -> l3
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (= pc1 2) (Bad (+ x z) y1 y2 z 3 pc2 pc3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T2 l1 -> l2
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc2 1) (= c21 2)) (Bad x y1 y2 (+ z 1) pc1 2 pc3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T2 l1 -> l3 atomic
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc2 1) (= c21 3)) (Bad x y1 y2 (+ z 2) pc1 3 pc3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T2 l2 -> l3
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (= pc2 2) (Bad x y1 y2 (+ z 1) pc1 3 pc3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l1 -> l2 (y1 := 3)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 1) (= c31 2) (= x 1)) (Bad x 3 y2 z pc1 pc2 2 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l1 -> l3 atomic (y1 := 3)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 1) (= c31 3) (= x 1)) (Bad x 3 x z pc1 pc2 3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l1 -> l4 atomic (y1 := 3)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 1) (= c31 4) (= x 1) (distinct 3 x)) (Bad x 3 x z pc1 pc2 4 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l1 -> l2 (y1 := 6)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 1) (= c31 2) (= x 2)) (Bad x 6 y2 z pc1 pc2 2 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l1 -> l3 atomic (y1 := 6)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 1) (= c31 3) (= x 2)) (Bad x 6 x z pc1 pc2 3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l1 -> l4 atomic (y1 := 6)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 1) (= c31 4) (= x 2) (distinct 6 x)) (Bad x 6 x z pc1 pc2 4 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l1 -> l2 (y1 := 5)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 1) (= c31 2) (or (<= x 0) (>= x 3))) (Bad x 5 y2 z pc1 pc2 2 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l1 -> l3 atomic (y1 := 5)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 1) (= c31 3) (or (<= x 0) (>= x 3))) (Bad x 5 x z pc1 pc2 3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l1 -> l4 atomic (y1 := 5)
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 1) (= c31 4) (or (<= x 0) (>= x 3)) (distinct 5 x)) (Bad x 5 x z pc1 pc2 4 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l2 -> l3
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 2) (= c32 3)) (Bad x y1 x z pc1 pc2 3 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l2 -> l4 atomic
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 2) (= c32 4) (distinct y1 x)) (Bad x y1 x z pc1 pc2 4 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
; T3 l3 -> l4
(assert (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= pc3 3) (distinct y1 y2)) (Bad x y1 y2 z pc1 pc2 4 c11 c21 c31 c32)) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))))
(assert (=> (forall ((x Int) (y1 Int) (y2 Int) (z Int) (pc1 Int) (pc2 Int) (pc3 Int) (c11 Int) (c21 Int) (c31 Int) (c32 Int)) (=> (and (and (= x 0) (= z 0) (= pc1 1) (= pc2 1) (= pc3 1)) (and (<= 2 c11) (<= c11 3) (<= 2 c21) (<= c21 3) (<= 2 c31) (<= c31 4) (<= 3 c32) (<= c32 4))) (Bad x y1 y2 z pc1 pc2 pc3 c11 c21 c31 c32))) BadInit))
(assert (=> BadInit false))
(check-sat)
