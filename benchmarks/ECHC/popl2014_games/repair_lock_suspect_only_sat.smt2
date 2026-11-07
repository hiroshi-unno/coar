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
; Clauses: inv is the controller's winning region (greatest solution).
; expected: sat (Table 1; explicit-state game solving agrees)
(set-logic HORN)
(declare-fun Inv (Int Int Int) Bool)
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (= gl 0) (= l 0) (= pc 0)) (Inv l gl pc))))
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (Inv l gl pc) (or (and (= pc 2) (= l 1)) (and (= pc 5) (= l 0)))) false)))
; rho1
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (Inv l gl pc) (= pc 0)) (Inv l gl 2))))
; rho2
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (Inv l gl pc) (= pc 0)) (Inv l gl 4))))
; rho3: the controller chooses gl
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (Inv l gl pc) (and (= pc 2) (<= l 0))) (exists ((gl_c Int)) (and true (Inv 1 gl_c 4))))))
; rho4
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (Inv l gl pc) (and (= pc 4) (distinct gl 0))) (Inv l gl 5))))
; rho5
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (Inv l gl pc) (and (= pc 4) (= gl 0))) (Inv l gl 6))))
; rho6
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (Inv l gl pc) (and (= pc 5) (>= l 1))) (Inv 0 gl 6))))
; rho7: the controller chooses gl
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (Inv l gl pc) (= pc 6)) (exists ((gl_c Int)) (and true (Inv l gl_c 0))))))
(check-sat)
