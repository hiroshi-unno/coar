; BUGGY twin of recon_ins_sorted_sat.smt2: the [i <= hd] branch returns
; hd :: i :: tl, so inserting 3 into [5] gives [5; 3], which is not sorted.
; Otherwise as there: the verification conditions of
; Champion, Chiba, Kobayashi and Sato, "ICE-Based Refinement Type Discovery for
; Higher-Order Functional Programs" (JAR 2020), section 5.1, for
;   let rec ins i lst = match lst with [] -> [i]
;     | hd :: tl -> if i <= hd then i :: lst else hd :: ins i tl
;   let rec sorted = function [] | [_] -> true
;     | h1 :: h2 :: tl -> if h1 > h2 then false else sorted (h2 :: tl)
;   let main i lst = if sorted lst then assert (sorted (ins i lst))
; [rho_sorted] and [rho_ins] are the refinement unknowns of the two functions.
; The goal is refuted at i = 3, lst = [5].  Expected: unsat.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((cons (head Int) (tail Lst)) (nil))))
(declare-fun rho_sorted (Lst Bool) Bool)
(declare-fun rho_ins (Int Lst Lst) Bool)
(assert (forall ((i Int) (lst Lst) (r Lst))
  (=> (and (rho_sorted lst true) (rho_ins i lst r) (rho_sorted r false)) false)))
(assert (forall ((i Int) (lst Lst))
  (=> (= lst nil) (rho_ins i lst (cons i nil)))))
(assert (forall ((i Int) (hd Int) (tl Lst))
  (=> (<= i hd) (rho_ins i (cons hd tl) (cons hd (cons i tl))))))
(assert (forall ((i Int) (hd Int) (tl Lst) (r Lst))
  (=> (and (> i hd) (rho_ins i tl r)) (rho_ins i (cons hd tl) (cons hd r)))))
(assert (forall ((lst Lst)) (=> (= lst nil) (rho_sorted lst true))))
(assert (forall ((hd Int) (tl Lst)) (=> (= tl nil) (rho_sorted (cons hd tl) true))))
(assert (forall ((hd1 Int) (hd2 Int) (tl Lst))
  (=> (> hd1 hd2) (rho_sorted (cons hd1 (cons hd2 tl)) false))))
(assert (forall ((hd1 Int) (hd2 Int) (tl Lst) (res Bool))
  (=> (and (<= hd1 hd2) (rho_sorted (cons hd2 tl) res))
      (rho_sorted (cons hd1 (cons hd2 tl)) res))))
(check-sat)
