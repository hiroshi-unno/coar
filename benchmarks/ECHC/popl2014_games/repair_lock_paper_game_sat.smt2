; Game G6 (Repair-Lock) of Beyene, Chaudhuri, Popeea, Rybalchenko, "A constraint-based approach to solving games on
; infinite graphs", POPL 2014, pp. 221-233, https://doi.org/10.1145/2535838.2535860
; (Table 1; Section 6.1, the program of Figure 3 of Jobstmann, Griesmayer, Bloem, CAV 2005, as the
; paper restates it).  v = (l, gl, pc), init = (gl = 0 /\ l = 0 /\ pc = l0), the seven transitions
; rho1..rho7 of Section 6.1 (rho3 and rho7 leave gl unconstrained: they are the suspect statements),
; error = (pc = l2 /\ l = 1 \/ pc = l5 /\ l = 0), objective G not error.  Locations l_k are written k.
; This file is the game exactly as Section 6.1 defines it: eve = next, adam = skip, so the program player
; resolves ALL of next's nondeterminism (which branch at l0, and gl at rho3, rho7), not only the suspect
; values; the paper's template then restricts the strategy to constant gl at rho3, rho7, which is not
; part of the game.  With that much control the program wins trivially (always take rho2, set gl = 0).
; RULE SAFE with adam = skip: inv -> safe, and inv(v) -> exists v''. next(v,v'') /\ inv(v'').
; expected: sat (by hand: the program player takes rho2 and rho5 forever)
(set-logic HORN)
(declare-fun Inv (Int Int Int) Bool)
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (= gl 0) (= l 0) (= pc 0)) (Inv l gl pc))))
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (and (Inv l gl pc) (or (and (= pc 2) (= l 1)) (and (= pc 5) (= l 0)))) false)))
(assert (forall ((l Int) (gl Int) (pc Int)) (=> (Inv l gl pc) (exists ((l_n Int) (gl_n Int) (pc_n Int)) (and (or
    (and (= pc 0) (= l_n l) (= gl_n gl) (= pc_n 2))
    (and (= pc 0) (= l_n l) (= gl_n gl) (= pc_n 4))
    (and (and (= pc 2) (<= l 0)) (= l_n 1) true (= pc_n 4))
    (and (and (= pc 4) (distinct gl 0)) (= l_n l) (= gl_n gl) (= pc_n 5))
    (and (and (= pc 4) (= gl 0)) (= l_n l) (= gl_n gl) (= pc_n 6))
    (and (and (= pc 5) (>= l 1)) (= l_n 0) (= gl_n gl) (= pc_n 6))
    (and (= pc 6) (= l_n l) true (= pc_n 0)))
  (Inv l_n gl_n pc_n))))))
(check-sat)
