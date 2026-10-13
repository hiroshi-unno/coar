; The twin of predeclared_list_builtin_unsat.smt2, and the direction that is easy to break while
; fixing the other: this file declares a List of its own, with the constructors nil and cons
; and the selectors hd and tl, which are not the built-in's insert/head/tail.  A predeclared
; built-in must lose to the file's own declaration, and the two sets of constructor names must
; not mix -- reading cons here as the built-in's insert would be a silent misreading of the
; input rather than a parse failure.
(set-logic HORN)
(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (hd T) (tl (List T)))))))
(declare-fun P ((List Int)) Bool)
(assert (P nil))
(assert (forall ((l (List Int))) (=> (P l) (not (= l nil)))))
(check-sat)
