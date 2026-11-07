(set-info :smt-lib-version 2.6)
(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 11756 For more info see: No further information available.
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun ts9uscore1 () Real)
(declare-fun stuscore2dollarskuscore15 () Real)
(declare-fun xuscore2dollarskuscore7 () Real)
(declare-fun yuscore2dollarskuscore15 () Real)
(declare-fun t9uscore0dollarskuscore1 () Real)
(assert (not (exists ((ts9uscore1 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts9uscore1) (<= ts9uscore1 t9uscore0dollarskuscore1)) (<= (+ ts9uscore1 xuscore2dollarskuscore7) 2)) (>= t9uscore0dollarskuscore1 0)) (< xuscore2dollarskuscore7 2)) (= stuscore2dollarskuscore15 1)) (>= yuscore2dollarskuscore15 1)) (<= yuscore2dollarskuscore15 12)) (<= yuscore2dollarskuscore15 (+ 10 xuscore2dollarskuscore7))) (or (= stuscore2dollarskuscore15 3) (<= (+ t9uscore0dollarskuscore1 yuscore2dollarskuscore15) 12))))))
(check-sat)
(exit)
