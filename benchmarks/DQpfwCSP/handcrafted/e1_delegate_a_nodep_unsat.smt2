; E1-A  expected: unsat   (test T1: widening the dependency set makes it sat, see b_)
;
; Abstract model: OS sandbox with a privileged broker (Chromium-style broker process).
;   ValidS h : handle h is valid inside the sandbox's namespace     (abstract: Ok1)
;   ValidK h : handle h is accepted by the privileged kernel API    (abstract: Ok2)
; Both are platform-dependent and unknown at design time, hence universally quantified.
; Contract Phi (abstraction of a "hot spare" guarantee documented by the platform):
;   of any two consecutive handle numbers at least one is kernel-valid.
; The unimplemented component Sbx: sandboxed component. It receives a sandbox-valid handle i and must hand
;   a kernel-valid handle y to the broker. It can only reference the sandbox API (ValidS);
;   it has no way to ask the kernel whether a handle is valid.
; System spec S: the handle passed on is kernel-valid.
;
; Why unsat: Sbx(i) is nonempty, pick y in it; the adversary chooses ValidK := Z \ {y},
; which satisfies Phi, so S fails.
(set-logic DQHORN)
(declare-forall-fun ValidS (Int) Bool)
(declare-forall-fun ValidK (Int) Bool)
(define-fun Phi () Bool (forall ((h Int)) (or (ValidK h) (ValidK (+ h 1)))))
(declare-dep-exists-fun Sbx (ValidS) (Int Int) Bool)
; totality: every reachable input has some output
(assert (forall ((i Int)) (=> (and Phi (ValidS i)) (exists ((y Int)) (Sbx i y)))))
; safety: S
(assert (forall ((i Int) (y Int)) (=> (and Phi (ValidS i) (Sbx i y)) (ValidK y))))
