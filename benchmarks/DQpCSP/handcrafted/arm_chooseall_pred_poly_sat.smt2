; The POPL 2024 ARM benchmark `choose-all-SAT.ml` with its ghost parameters replaced by predicate
; polymorphism, encoded by universally quantified predicates.  The last member of the "combining" family: the
; handler **appends** the two branch answers instead of taking their max or sum.
;
;   choose_all _ctx1 _ctx2 body = match_with body () { retc = fun x -> [x];
;     Decide _ -> fun k -> continue k true @ continue k false }
;   let main x y = choose_all x y(*dummy*) (fun () ->
;     let a = if perform (Decide (false,0)) then x else y in
;     let b = if perform (Decide (true,a))  then x else y in a - b)
;   let test x y = main x y = [0; x - y; y - x; 0]
;
; As in `choose-max` the abstracted predicate is indexed by the resumed value, `X(l, b)` = "the
; branch resumed with `b` answers the list `l`".  The clause is written at the two-element case
; the program produces, so that no list-append relation is needed: appending `[p; q]` to `l2`
; is `p :: q :: l2`.  (A general append would have to be an *exact* relation, and an unknown
; constrained by Horn clauses is only a lower bound -- worth recording as the reason this file is
; specialised rather than general.)
;
; Two clients, the program's two `Decide` calls in their two contexts.  expected: sat
(set-logic DQHORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))

(declare-forall-fun X (Lst Bool) Bool)
(declare-dep-exists-fun Dec () ((Array Lst (Array Bool Bool)) Lst) Bool)

; --- the handler, verified once for every X: the answer is the concatenation of the branches
(assert (forall ((p Int) (q Int) (l2 Lst))
  (=> (and (X (cons p (cons q nil)) true) (X l2 false))
      (Dec X (cons p (cons q l2))))))

; --- client 1, the inner call in the context of the local `a`: the branches answer [a-x] and
;     [a-y]... written at the shape the outer call consumes, [a-x; a-y] ---
(assert (forall ((a Int) (x Int) (y Int) (l Lst))
  (=> (and (Dec (lambda ((m Lst)) (lambda ((b Bool))
              (or (and b (= m (cons (- a x) (cons (- a y) nil))))
                  (and (not b) (= m nil))))) l)
           (not (= l (cons (- a x) (cons (- a y) nil)))))
      false)))
; --- client 2, the outer call: the true branch answers [0; x-y] and the false branch [y-x; 0],
;     so the program's answer is [0; x-y; y-x; 0] -- the specification of `test` ---
(assert (forall ((x Int) (y Int) (l Lst))
  (=> (and (Dec (lambda ((m Lst)) (lambda ((b Bool))
              (or (and b (= m (cons 0 (cons (- x y) nil))))
                  (and (not b) (= m (cons (- y x) (cons 0 nil))))))) l)
           (not (= l (cons 0 (cons (- x y) (cons (- y x) (cons 0 nil)))))))
      false)))
(check-sat)
