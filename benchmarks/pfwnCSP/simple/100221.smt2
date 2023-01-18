; 19 clauses (0 existential), 13 predicate variables (2 functional)
; (* 10022-SAT: range basic *)
; 
; type list = Nil of int | Cons of int * list
; type list2d = Nil2d of int | Cons2d of list * list2d
; type tree = Leaf of int | Node of int * tree * tree
; 
; let rec range n =
;   if n = 0 then Nil(0)
;   else          Cons(n, range (n - 1))
; 
; let rec main n =
;   if n >= 0 then
;     match (range n) with
;     | Nil(x) -> assert (n = 0)
;     | Cons(x) -> 0 (*assert (n > 0)*)
;   else
;     0
(set-logic HORN)
(declare-fun pI0 (Int) Bool)
(declare-fun fAM1 (Int Int) Bool)
(declare-fnp fAM0 (Int Int) Bool)
(declare-fun pI3 (Int Int) Bool)
(declare-fun pI1 (Int Int) Bool)
(declare-fun pxAR0_1 (Int Int) Bool)
(declare-fnp pxAR0_0 (Int Int) Bool)
(declare-fun pI4 (Int Int) Bool)
(declare-fun pI2 (Int Int) Bool)
(declare-fun fAM2 (Int Int Int Int) Bool)
(declare-fun pI5 (Int Int) Bool)
(declare-fun pxAR0_2 (Int Int) Bool)
(declare-fun pI6 (Int Int) Bool)
; range₀ n₀: (μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
; ∀{|⊤}(xP₁:{_|pI₀(_)})→(μlist₁(xPs₂)❰Nil: {_|pI₁(xPs₂,_)}, Cons: ∃{xAR0₂|pxAR0₀(xPs₂,xAR0₂)}.(xl₂:{_|pI₂(xPs₂,_)})×list₁(xAR0₂)❱)[xAM0₂|fAM₀(xP₁,xAM0₂)] <: ∀{|⊤}(_₋:{_|n₀=_})→(μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
(assert (forall ((n0 Int) (stru0 Int))
  (=> (and (>= n0 0)
           (= n0 stru0))
      (pI0 stru0))))
; range₀ n₀: (μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
; ∀{|⊤}(xP₁:{_|pI₀(_)})→(μlist₁(xPs₂)❰Nil: {_|pI₁(xPs₂,_)}, Cons: ∃{xAR0₂|pxAR0₀(xPs₂,xAR0₂)}.(xl₂:{_|pI₂(xPs₂,_)})×list₁(xAR0₂)❱)[xAM0₂|fAM₀(xP₁,xAM0₂)] <: ∀{|⊤}(_₋:{_|n₀=_})→(μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
(assert (forall ((n0 Int) (yxAM0_0 Int) (yxP0 Int))
  (=> (and (= n0 yxP0)
           (>= n0 0)
           (fAM0 yxP0 yxAM0_0))
      (fAM1 n0 yxAM0_0))))
; range₀ n₀: (μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
; ∀{|⊤}(xP₁:{_|pI₀(_)})→(μlist₁(xPs₂)❰Nil: {_|pI₁(xPs₂,_)}, Cons: ∃{xAR0₂|pxAR0₀(xPs₂,xAR0₂)}.(xl₂:{_|pI₂(xPs₂,_)})×list₁(xAR0₂)❱)[xAM0₂|fAM₀(xP₁,xAM0₂)] <: ∀{|⊤}(_₋:{_|n₀=_})→(μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
(assert (forall ((sxI0 Int) (yxAM0_0 Int))
  (=> (pI1 yxAM0_0 sxI0)
      (pI3 yxAM0_0 sxI0))))
; range₀ n₀: (μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
; ∀{|⊤}(xP₁:{_|pI₀(_)})→(μlist₁(xPs₂)❰Nil: {_|pI₁(xPs₂,_)}, Cons: ∃{xAR0₂|pxAR0₀(xPs₂,xAR0₂)}.(xl₂:{_|pI₂(xPs₂,_)})×list₁(xAR0₂)❱)[xAM0₂|fAM₀(xP₁,xAM0₂)] <: ∀{|⊤}(_₋:{_|n₀=_})→(μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
(assert (forall ((yxAM0_0 Int) (yxAR0_0 Int))
  (=> (pxAR0_0 yxAM0_0 yxAR0_0)
      (pxAR0_1 yxAM0_0 yxAR0_0))))
; range₀ n₀: (μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
; ∀{|⊤}(xP₁:{_|pI₀(_)})→(μlist₁(xPs₂)❰Nil: {_|pI₁(xPs₂,_)}, Cons: ∃{xAR0₂|pxAR0₀(xPs₂,xAR0₂)}.(xl₂:{_|pI₂(xPs₂,_)})×list₁(xAR0₂)❱)[xAM0₂|fAM₀(xP₁,xAM0₂)] <: ∀{|⊤}(_₋:{_|n₀=_})→(μlist₂(xPs₁)❰Nil: {_|pI₃(xPs₁,_)}, Cons: ∃{xAR0₁|pxAR0₁(xPs₁,xAR0₁)}.(xl₁:{_|pI₄(xPs₁,_)})×list₂(xAR0₁)❱)[xAM0₁|fAM₁(n₀,xAM0₁)]
(assert (forall ((sxI1 Int) (yxAM0_0 Int) (yxAR0_0 Int))
  (=> (and (pxAR0_0 yxAM0_0 yxAR0_0)
           (pI2 yxAM0_0 sxI1))
      (pI4 yxAM0_0 sxI1))))
; assert (n₀=0): int⊤
(assert (forall ((n0 Int) (x1 Int) (xAM0_1 Int))
  (=> (and (pI3 xAM0_1 x1)
           (>= n0 0)
           (fAM1 n0 xAM0_1))
      (= n0 0))))
; Nil(zero₂): (μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)[xAM0₀|fAM₀(n₁,xAM0₀)]
; {_|zero₂=_} <: {_|pI₁(xAM0₀,_)}
(assert (forall ((xAM0_0 Int))
  (=> (and (pI0 0)
           (fAM0 0 xAM0_0))
      (pI1 xAM0_0 0))))
; range₀ minus₀: (μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
; ∀{|⊤}(xP₂:{_|pI₀(_)})→(μlist₁(xPs₄)❰Nil: {_|pI₁(xPs₄,_)}, Cons: ∃{xAR0₅|pxAR0₀(xPs₄,xAR0₅)}.(xl₄:{_|pI₂(xPs₄,_)})×list₁(xAR0₅)❱)[xAM0₄|fAM₀(xP₂,xAM0₄)] <: ∀{|⊤}(_₋:{_|minus₀=_})→(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
(assert (forall ((minus0 Int) (n1 Int) (sminus0 Int))
  (=> (and (= minus0 (- n1 1))
           (pI0 n1)
           (not (= n1 0))
           (= minus0 sminus0))
      (pI0 sminus0))))
; range₀ minus₀: (μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
; ∀{|⊤}(xP₂:{_|pI₀(_)})→(μlist₁(xPs₄)❰Nil: {_|pI₁(xPs₄,_)}, Cons: ∃{xAR0₅|pxAR0₀(xPs₄,xAR0₅)}.(xl₄:{_|pI₂(xPs₄,_)})×list₁(xAR0₅)❱)[xAM0₄|fAM₀(xP₂,xAM0₄)] <: ∀{|⊤}(_₋:{_|minus₀=_})→(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
(assert (forall ((minus0 Int) (n1 Int) (yxAM0_1 Int) (yxP1 Int))
  (=> (and (= minus0 yxP1)
           (= minus0 (- n1 1))
           (pI0 n1)
           (not (= n1 0))
           (fAM0 yxP1 yxAM0_1))
      (fAM2 minus0 n1 1 yxAM0_1))))
; range₀ minus₀: (μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
; ∀{|⊤}(xP₂:{_|pI₀(_)})→(μlist₁(xPs₄)❰Nil: {_|pI₁(xPs₄,_)}, Cons: ∃{xAR0₅|pxAR0₀(xPs₄,xAR0₅)}.(xl₄:{_|pI₂(xPs₄,_)})×list₁(xAR0₅)❱)[xAM0₄|fAM₀(xP₂,xAM0₄)] <: ∀{|⊤}(_₋:{_|minus₀=_})→(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
(assert (forall ((sxI2 Int) (yxAM0_1 Int))
  (=> (pI1 yxAM0_1 sxI2)
      (pI5 yxAM0_1 sxI2))))
; range₀ minus₀: (μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
; ∀{|⊤}(xP₂:{_|pI₀(_)})→(μlist₁(xPs₄)❰Nil: {_|pI₁(xPs₄,_)}, Cons: ∃{xAR0₅|pxAR0₀(xPs₄,xAR0₅)}.(xl₄:{_|pI₂(xPs₄,_)})×list₁(xAR0₅)❱)[xAM0₄|fAM₀(xP₂,xAM0₄)] <: ∀{|⊤}(_₋:{_|minus₀=_})→(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
(assert (forall ((yxAM0_1 Int) (yxAR0_1 Int))
  (=> (pxAR0_0 yxAM0_1 yxAR0_1)
      (pxAR0_2 yxAM0_1 yxAR0_1))))
; range₀ minus₀: (μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
; ∀{|⊤}(xP₂:{_|pI₀(_)})→(μlist₁(xPs₄)❰Nil: {_|pI₁(xPs₄,_)}, Cons: ∃{xAR0₅|pxAR0₀(xPs₄,xAR0₅)}.(xl₄:{_|pI₂(xPs₄,_)})×list₁(xAR0₅)❱)[xAM0₄|fAM₀(xP₂,xAM0₄)] <: ∀{|⊤}(_₋:{_|minus₀=_})→(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₁,one₀,xAM0₃)]
(assert (forall ((sxI3 Int) (yxAM0_1 Int) (yxAR0_1 Int))
  (=> (and (pxAR0_0 yxAM0_1 yxAR0_1)
           (pI2 yxAM0_1 sxI3))
      (pI6 yxAM0_1 sxI3))))
; Cons(pair₀): (μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)[xAM0₀|fAM₀(n₁,xAM0₀)]
; (n₂:{_|pair₀.L=_})×(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₂,one₀,xAM0₃)] <: (xl₀:{_|pI₂(xAM0₀,_)})×(μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)(xAR0₆)
(assert (forall ((minus0 Int) (n1 Int) (pair0_L Int) (sxI4 Int) (xAM0_0 Int) (xAR0_6 Int))
  (=> (and (= minus0 (- n1 1))
           (pI0 n1)
           (= n1 pair0_L)
           (= pair0_L sxI4)
           (pxAR0_0 xAM0_0 xAR0_6)
           (not (= n1 0))
           (fAM0 n1 xAM0_0))
      (pI2 xAM0_0 sxI4))))
; Cons(pair₀): (μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)[xAM0₀|fAM₀(n₁,xAM0₀)]
; (n₂:{_|pair₀.L=_})×(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₂,one₀,xAM0₃)] <: (xl₀:{_|pI₂(xAM0₀,_)})×(μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)(xAR0₆)
(assert (forall ((minus0 Int) (n1 Int) (pair0_L Int) (xAM0_0 Int) (xAR0_6 Int) (yn0 Int) (yxAM0_2 Int))
  (=> (and (= pair0_L yn0)
           (= minus0 (- n1 1))
           (pI0 n1)
           (= n1 pair0_L)
           (fAM2 minus0 yn0 1 yxAM0_2)
           (pxAR0_0 xAM0_0 xAR0_6)
           (not (= n1 0))
           (fAM0 n1 xAM0_0))
      (= xAR0_6 yxAM0_2))))
; Cons(pair₀): (μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)[xAM0₀|fAM₀(n₁,xAM0₀)]
; (n₂:{_|pair₀.L=_})×(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₂,one₀,xAM0₃)] <: (xl₀:{_|pI₂(xAM0₀,_)})×(μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)(xAR0₆)
(assert (forall ((sxI5 Int) (yxAM0_2 Int))
  (=> (pI5 yxAM0_2 sxI5)
      (pI1 yxAM0_2 sxI5))))
; Cons(pair₀): (μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)[xAM0₀|fAM₀(n₁,xAM0₀)]
; (n₂:{_|pair₀.L=_})×(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₂,one₀,xAM0₃)] <: (xl₀:{_|pI₂(xAM0₀,_)})×(μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)(xAR0₆)
(assert (forall ((yxAM0_2 Int) (yxAR0_2 Int))
  (=> (pxAR0_2 yxAM0_2 yxAR0_2)
      (pxAR0_0 yxAM0_2 yxAR0_2))))
; Cons(pair₀): (μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)[xAM0₀|fAM₀(n₁,xAM0₀)]
; (n₂:{_|pair₀.L=_})×(μlist₃(xPs₃)❰Nil: {_|pI₅(xPs₃,_)}, Cons: ∃{xAR0₄|pxAR0₂(xPs₃,xAR0₄)}.(xl₃:{_|pI₆(xPs₃,_)})×list₃(xAR0₄)❱)[xAM0₃|fAM₂(minus₀,n₂,one₀,xAM0₃)] <: (xl₀:{_|pI₂(xAM0₀,_)})×(μlist₁(xPs₀)❰Nil: {_|pI₁(xPs₀,_)}, Cons: ∃{xAR0₀|pxAR0₀(xPs₀,xAR0₀)}.(xl₀:{_|pI₂(xPs₀,_)})×list₁(xAR0₀)❱)(xAR0₆)
(assert (forall ((sxI6 Int) (yxAM0_2 Int) (yxAR0_2 Int))
  (=> (and (pxAR0_2 yxAM0_2 yxAR0_2)
           (pI6 yxAM0_2 sxI6))
      (pI2 yxAM0_2 sxI6))))
