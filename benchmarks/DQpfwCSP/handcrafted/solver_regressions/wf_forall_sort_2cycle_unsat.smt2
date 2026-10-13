; A well-foundedness predicate whose arguments live in a universally quantified sort.
;
; Why it exists.  The labeler's cycle learning keeps only ground atoms (PApp), and an example over a
; forall-sort arrives guarded (PPApp: "cond => WF(...)"), so cycle learning has never once seen such
; an example -- a capability gap, not a bug.  Nothing in the corpus
; combined the two, so nothing exercised it, and nothing could measure a change to the labeling that
; claims to close it.  This file is that input, and it is deliberately the smallest one.
;
; NOTE ON SCOPE.  This is *not* a (D)QpCSP problem, and it is not an ordinary pfwCSP either: it is
; the Q extension of *pfwCSP*, which is its own class and the reason this directory exists.  The
; distinction is the predicate kinds.  (D)QpCSP and its Horn fragments quantify over sorts,
; functions and dependency sets while every unknown stays an ordinary predicate; pfwCSP adds kinds
; -- well-foundedness, functionality, non-emptiness and the rest -- whose solutions must satisfy a
; semantic condition of their own.  A file with both, as this one has (a well-foundedness predicate
; whose arguments live in a universally quantified sort), belongs to neither of the other two
; corpora: benchmarks/pfwnCSP holds the kinds without the quantification, benchmarks/DQpCSP the
; quantification without the kinds.
;
; The problem.  WF must be a well-founded relation on pairs drawn from the sort a.  The clause
; offers it a swap: from any two distinct x and y it demands the step (x,y) -> (y,x).  That step
; composed with itself returns to where it started, so no well-founded relation contains it, and
; the demand is unconditional on the sort (a forall-sort is every non-empty type, and every type
; with two elements supplies a distinct x and y).  The integer twin of this shape is
; wf_int_2cycle_unsat.smt2 next to this file; the only difference here is that the elements come
; from a sort the problem quantifies over rather than from Int, which is exactly what turns the
; derived examples from ground into guarded ones.
;
; What it showed on its first use (2026-09-14).  The integer twin accumulates two positive examples,
; WF(0,1,1,0) and WF(1,0,0,1), because validation returns a different pair of concrete values each
; round, and a swap 2-cycle needs two steps; it refutes at unsat,1.  This file accumulates one,
; [$1 != $2] WF($1,$2,$2,$1), because every counterexample collapses to the same parametric example,
; and raising the labeler's pex_instances to 3 does not produce the swapped instance either.  One
; step cannot close a 2-cycle whatever the cycle learners are given.  So the gap this file was
; written for is not that the learners cannot see a forall-sort example -- it is that a forall-sort
; problem yields one parametric example where a ground one yields many instances.
;
; expected: unsat (no configuration answers it today; that is the point of the file).
(set-logic QHORN)

(declare-forall-sort a)

(declare-wfp WF (a a a a) Bool)

(assert (forall ((x a) (y a))
  (=> (distinct x y) (WF x y y x))))

(check-sat)
