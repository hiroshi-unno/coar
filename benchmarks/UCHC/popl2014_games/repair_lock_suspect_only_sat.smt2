; Game G6 (Repair-Lock) of Beyene, Chaudhuri, Popeea, Rybalchenko, "A constraint-based approach to solving games on
; infinite graphs", POPL 2014, pp. 221-233, https://doi.org/10.1145/2535838.2535860
; (Table 1; Section 6.1, the program of Figure 3 of Jobstmann, Griesmayer, Bloem, CAV 2005, as the
; paper restates it).  v = (l, gl, pc), init = (gl = 0 /\ l = 0 /\ pc = l0), the seven transitions
; rho1..rho7 of Section 6.1 (rho3 and rho7 leave gl unconstrained: they are the suspect statements),
; error = (pc = l2 /\ l = 1 \/ pc = l5 /\ l = 0), objective G not error.  Locations l_k are written k.
; Modelling choice (the program-repair reading of Jobstmann et al., not the paper's literal eve = next):
; the environment resolves the program's own nondeterminism (the branch at l0) and the controller chooses
; only the value the suspect statements assign to gl (any integer; rho3 and rho7 are its moves).  One
; step = the environment picks an enabled transition, the controller then picks the suspect value; an
; environment with no enabled transition ends the play (no infinite play, so the controller wins, as in
; the paper's semantics).  The paper's repair (gl := 1 at l2, gl := 0 at l6) is a winning strategy;
; with the suspect values left to the environment the program is unsafe (explicit-state check).
; Dual side: Bad(v) is the environment's attractor to error (least solution); at a suspect transition the
; controller's choice is universally quantified in the premise.  The goal Bad(init) -> false is
; satisfiable iff the controller wins.
; expected: sat
(set-logic HORN)
(declare-fun Bad (Int Int Int) Bool)
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (or (and (= pc 2) (= l 1)) (and (= pc 5) (= l 0))) (Bad l gl pc))))
; rho1
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (= pc 0) (Bad l gl 2)) (Bad l gl pc))))
; rho2
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (= pc 0) (Bad l gl 4)) (Bad l gl pc))))
; rho3: every value the controller may choose for gl leads to Bad
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (and (= pc 2) (<= l 0)) (forall ((gl_c Int)) (=> true (Bad 1 gl_c 4)))) (Bad l gl pc))))
; rho4
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (and (= pc 4) (distinct gl 0)) (Bad l gl 5)) (Bad l gl pc))))
; rho5
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (and (= pc 4) (= gl 0)) (Bad l gl 6)) (Bad l gl pc))))
; rho6
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (and (= pc 5) (>= l 1)) (Bad 0 gl 6)) (Bad l gl pc))))
; rho7: every value the controller may choose for gl leads to Bad
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (= pc 6) (forall ((gl_c Int)) (=> true (Bad l gl_c 0)))) (Bad l gl pc))))
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (and (= gl 0) (= l 0) (= pc 0)) (Bad l gl pc)) false)))
(check-sat)
