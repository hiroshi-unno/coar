(set-logic QF_LIA)
(set-option :produce-models true)
;  c11 c12|c13 c14
;  c21 c22|c23 c24
;  -------+-------
;  c31 c32|c33 c34
;  c41 c42|c43 c44
(declare-fun c11 () Int)
(declare-fun c12 () Int)
(declare-fun c13 () Int)
(declare-fun c14 () Int)
(declare-fun c21 () Int)
(declare-fun c22 () Int)
(declare-fun c23 () Int)
(declare-fun c24 () Int)
(declare-fun c31 () Int)
(declare-fun c32 () Int)
(declare-fun c33 () Int)
(declare-fun c34 () Int)
(declare-fun c41 () Int)
(declare-fun c42 () Int)
(declare-fun c43 () Int)
(declare-fun c44 () Int)

; each cell contains 1, 2, 3, or 4
(assert (and (<= 1 c11) (<= c11 4)))
(assert (and (<= 1 c12) (<= c12 4)))
(assert (and (<= 1 c13) (<= c13 4)))
(assert (and (<= 1 c14) (<= c14 4)))
(assert (and (<= 1 c21) (<= c21 4)))
(assert (and (<= 1 c22) (<= c22 4)))
(assert (and (<= 1 c23) (<= c23 4)))
(assert (and (<= 1 c24) (<= c24 4)))
(assert (and (<= 1 c31) (<= c31 4)))
(assert (and (<= 1 c32) (<= c32 4)))
(assert (and (<= 1 c33) (<= c33 4)))
(assert (and (<= 1 c34) (<= c34 4)))
(assert (and (<= 1 c41) (<= c41 4)))
(assert (and (<= 1 c42) (<= c42 4)))
(assert (and (<= 1 c43) (<= c43 4)))
(assert (and (<= 1 c44) (<= c44 4)))

; the 1st column contains no duplicate numbers
(assert (distinct c11 c12 c13 c14))
; the 2nd column contains no duplicate numbers
(assert (distinct c21 c22 c23 c24))
; the 3rd column contains no duplicate numbers
(assert (distinct c31 c32 c33 c34))
; the 4th column contains no duplicate numbers
(assert (distinct c41 c42 c43 c44))
; the 1st row contains no duplicate numbers
(assert (distinct c11 c21 c31 c41))
; the 2nd row contains no duplicate numbers
(assert (distinct c12 c22 c32 c42))
; the 3rd row contains no duplicate numbers
(assert (distinct c13 c23 c33 c43))
; the 4th row contains no duplicate numbers
(assert (distinct c14 c24 c34 c44))
; the 1st block contains no duplicate numbers
(assert (distinct c11 c12 c21 c22))
; the 2nd block contains no duplicate numbers
(assert (distinct c13 c14 c23 c24))
; the 3rd block contains no duplicate numbers
(assert (distinct c31 c32 c41 c42))
; the 4th block contains no duplicate numbers
(assert (distinct c33 c34 c43 c44))

; input:
; . .|. 4
; . .|1 2
; ---+----
; . .|4 3
; 4 3|2 1
(assert (= c14 4))
(assert (= c23 1))
(assert (= c24 2))
(assert (= c33 4))
(assert (= c34 3))
(assert (= c41 4))
(assert (= c42 3))
(assert (= c43 2))
(assert (= c44 1))

;(assert (not (and (= c11 1) (= c12 2) (= c13 3) (= c21 3) (= c22 4) (= c31 2) (= c32 1))))
;(assert (not (and (= c11 2) (= c12 1) (= c13 3) (= c21 3) (= c22 4) (= c31 1) (= c32 2))))

(check-sat)
(get-model)
