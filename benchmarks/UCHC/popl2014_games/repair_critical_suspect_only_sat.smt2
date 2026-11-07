; Game G7 (Repair-Critical, safety) of Beyene, Chaudhuri, Popeea, Rybalchenko, "A constraint-based approach to solving games on
; infinite graphs", POPL 2014, pp. 221-233, https://doi.org/10.1145/2535838.2535860
; (Table 1; Section 6.2, the CRITICAL SECTION program of Figure 5 of Jobstmann, Griesmayer, Bloem,
; CAV 2005, as the paper restates it).  v = (f1a, f1b, t1b, f2a, f2b, t2b, pc1, pc2), Booleans as 0/1,
; init all flags 0 and both threads at l1; next = next1 /\ pc2' = pc2 \/ next2 /\ pc1' = pc1 with next1,
; next2 transcribed from Section 6.2 (one clause per disjunct); thread 1's l2 assigns t1b a
; nondeterministic value in {0,1} (the faulty statement); objective phi1 = G((pc1 = l4 -> pc2 != l4) /\
; (pc1 = l8 -> pc2 != l7)), so error = (pc1 = 4 /\ pc2 = 4) \/ (pc1 = 8 /\ pc2 = 7).
; Transcribed as printed, including both of thread 1's l5 disjuncts carrying t1b = 1 (so thread 1 blocks
; at l5 when t1b = 0; the authors' ConSynth input and GenSys's restatement print the same); reading the
; second one as t1b = 0 does not change the verdict (explicit-state check of both readings).
; Modelling choice (the reading the authors' ConSynth input takes, where the deterministic transitions are
; universally quantified and only the l2 assignment is existential): the environment chooses the
; interleaving and every other transition; the controller chooses the value in {0,1} that thread 1's l2
; assigns to t1b.  The paper's repair t1b := 1 is winning; with the value left to the environment the
; program violates mutual exclusion (explicit-state check).
; Dual side: Bad is the environment's attractor to error (least solution); the controller's choice at
; thread 1's l2 is universally quantified in the premise.
; expected: sat
(set-logic HORN)
(declare-fun Bad (Int Int Int Int Int Int Int Int) Bool)
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (or (and (= pc1 4) (= pc2 4)) (and (= pc1 8) (= pc2 7))) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l1
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc1 1) (Bad 1 f1b t1b f2a f2b t2b 2 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l2 (suspect turn1B := ND): every value the controller may choose for t1b leads to Bad
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc1 2) (forall ((t1b_c Int)) (=> (and (<= 0 t1b_c) (<= t1b_c 1)) (Bad f1a f1b t1b_c f2a f2b t2b 3 pc2)))) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l3 wait
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc1 3) (= f1b 1) (= t1b 1)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l3 go
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc1 3) (or (= f1b 0) (= t1b 0))) (Bad f1a f1b t1b f2a f2b t2b 4 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l4
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc1 4) (Bad 0 f1b t1b f2a f2b t2b 5 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l5 -> l6
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc1 5) (= t1b 1)) (Bad f1a f1b t1b 1 f2b t2b 6 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l5 -> l9 (guard t1b = 1 as printed)
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc1 5) (= t1b 1)) (Bad f1a f1b t1b f2a f2b t2b 9 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l6
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc1 6) (Bad f1a f1b t1b f2a f2b 1 7 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l7 wait
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc1 7) (= f2b 1) (= t2b 1)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l7 go
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc1 7) (or (= f2b 0) (= t2b 0))) (Bad f1a f1b t1b f2a f2b t2b 8 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l8
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc1 8) (Bad f1a f1b t1b 0 f2b t2b 9 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; A l9
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc1 9) (Bad f1a f1b t1b f2a f2b t2b 1 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l1
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc2 1) (Bad f1a 1 t1b f2a f2b t2b pc1 2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l2
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc2 2) (Bad f1a f1b 0 f2a f2b t2b pc1 3)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l3 wait
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc2 3) (= f1a 1) (= t1b 0)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l3 go
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc2 3) (or (= f1a 0) (= t1b 1))) (Bad f1a f1b t1b f2a f2b t2b pc1 4)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l4
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc2 4) (Bad f1a f1b t1b f2a 1 t2b pc1 5)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l5
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc2 5) (Bad f1a f1b t1b f2a f2b 0 pc1 6)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l6 wait
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc2 6) (= f2a 1) (= t2b 0)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l6 go
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= pc2 6) (or (= f2a 0) (= t2b 1))) (Bad f1a f1b t1b f2a f2b t2b pc1 7)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l7
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc2 7) (Bad f1a f1b t1b f2a 0 t2b pc1 8)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l8
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc2 8) (Bad f1a 0 t1b f2a f2b t2b pc1 9)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
; B l9
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= pc2 9) (Bad f1a f1b t1b f2a f2b t2b pc1 1)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2))))
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (and (= f1a 0) (= f1b 0) (= t1b 0) (= f2a 0) (= f2b 0) (= t2b 0) (= pc1 1) (= pc2 1)) (Bad f1a f1b t1b f2a f2b t2b pc1 pc2)) false)))
(check-sat)
