; expected: sat
;
; Every operator whose SMT-LIB declaration carries an arity annotation, applied
; to more than two arguments, with each conjunct chosen so that the WRONG rule
; gives the wrong answer or no parse at all:
;
;   xor   :left-assoc  -- three arguments at all; the helper behind it was binary
;   =>    :right-assoc -- (=> false true false) is true right-associated, false
;                         left-associated
;   = < > <= >=  :chainable -- adjacent pairs conjoined, so (= 1 1 2) is false
;                              and (< 1 3 2) is false although 1 < 3
;   - / div      :left-assoc, and each also has a one-argument form of its own,
;                so (- 9 3 2) is 4 and not 8
;   + * bvand bvor bvxor bvadd bvmul concat re.++   :left-assoc
;
; z3 and cvc5 agree on every one. They were answered with `<op> is not bound`,
; or an assertion failure for xor. This file is the reproducer that the reader's
; operator table is checked against: an operator declared n-ary and applied
; nowhere here fails that check rather than going untested.
(set-logic ALL)
(assert (and (xor true false false)
             (not (=> true true false))
             (=> false true false)
             (= 1 1 1)
             (not (= 1 1 2))
             (< 1 2 3)
             (not (< 1 3 2))
             (> 3 2 1)
             (not (> 3 1 2))
             (<= 1 1 2)
             (not (<= 1 2 1))
             (>= 2 1 1)
             (not (>= 1 2 1))
             (= (- 9 3 2) 4)
             (= (/ 12.0 2.0 3.0) 2.0)
             (= (div 12 2 3) 2)
             (= (+ 1 2 3) 6)
             (= (* 2 3 4) 24)
             (= (bvand #xff #x0f #x03) #x03)
             (= (bvor #x01 #x02 #x04) #x07)
             (= (bvxor #x0f #x0f #x0f) #x0f)
             (= (bvadd #x01 #x02 #x04) #x07)
             (= (bvmul #x02 #x03 #x04) #x18)
             (= (concat #x1 #x2 #x3) #x123)
             (str.in_re "abc" (re.++ (str.to_re "a")
                                     (str.to_re "b")
                                     (str.to_re "c")))))
(check-sat)
