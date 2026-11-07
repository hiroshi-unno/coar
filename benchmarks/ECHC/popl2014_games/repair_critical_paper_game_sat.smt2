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
; This file is the game exactly as Section 6.2 defines it: adam = skip, eve = next, so the program player
; also chooses the interleaving and wins trivially; the paper's template t1b'' = ?1 restricts the strategy,
; not the game.  RULE SAFE with adam = skip.
; expected: sat
(set-logic HORN)
(declare-fun Inv (Int Int Int Int Int Int Int Int) Bool)
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (= f1a 0) (= f1b 0) (= t1b 0) (= f2a 0) (= f2b 0) (= t2b 0) (= pc1 1) (= pc2 1)) (Inv f1a f1b t1b f2a f2b t2b pc1 pc2))))
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (and (Inv f1a f1b t1b f2a f2b t2b pc1 pc2) (or (and (= pc1 4) (= pc2 4)) (and (= pc1 8) (= pc2 7)))) false)))
(assert (forall ((f1a Int) (f1b Int) (t1b Int) (f2a Int) (f2b Int) (t2b Int) (pc1 Int) (pc2 Int)) (=> (Inv f1a f1b t1b f2a f2b t2b pc1 pc2) (exists ((f1a_n Int) (f1b_n Int) (t1b_n Int) (f2a_n Int) (f2b_n Int) (t2b_n Int) (pc1_n Int) (pc2_n Int)) (and (or
    (and (= pc1 1) (= f1a_n 1) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n 2) (= pc2_n pc2))
    (and (= pc1 2) (= f1a_n f1a) (= f1b_n f1b) (and (<= 0 t1b_n) (<= t1b_n 1)) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n 3) (= pc2_n pc2))
    (and (and (= pc1 3) (= f1b 1) (= t1b 1)) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n pc2))
    (and (and (= pc1 3) (or (= f1b 0) (= t1b 0))) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n 4) (= pc2_n pc2))
    (and (= pc1 4) (= f1a_n 0) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n 5) (= pc2_n pc2))
    (and (and (= pc1 5) (= t1b 1)) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n 1) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n 6) (= pc2_n pc2))
    (and (and (= pc1 5) (= t1b 1)) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n 9) (= pc2_n pc2))
    (and (= pc1 6) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n 1) (= pc1_n 7) (= pc2_n pc2))
    (and (and (= pc1 7) (= f2b 1) (= t2b 1)) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n pc2))
    (and (and (= pc1 7) (or (= f2b 0) (= t2b 0))) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n 8) (= pc2_n pc2))
    (and (= pc1 8) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n 0) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n 9) (= pc2_n pc2))
    (and (= pc1 9) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n 1) (= pc2_n pc2))
    (and (= pc2 1) (= f1a_n f1a) (= f1b_n 1) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n 2))
    (and (= pc2 2) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n 0) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n 3))
    (and (and (= pc2 3) (= f1a 1) (= t1b 0)) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n pc2))
    (and (and (= pc2 3) (or (= f1a 0) (= t1b 1))) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n 4))
    (and (= pc2 4) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n 1) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n 5))
    (and (= pc2 5) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n 0) (= pc1_n pc1) (= pc2_n 6))
    (and (and (= pc2 6) (= f2a 1) (= t2b 0)) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n pc2))
    (and (and (= pc2 6) (or (= f2a 0) (= t2b 1))) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n 7))
    (and (= pc2 7) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n 0) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n 8))
    (and (= pc2 8) (= f1a_n f1a) (= f1b_n 0) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n 9))
    (and (= pc2 9) (= f1a_n f1a) (= f1b_n f1b) (= t1b_n t1b) (= f2a_n f2a) (= f2b_n f2b) (= t2b_n t2b) (= pc1_n pc1) (= pc2_n 1)))
  (Inv f1a_n f1b_n t1b_n f2a_n f2b_n t2b_n pc1_n pc2_n))))))
(check-sat)
