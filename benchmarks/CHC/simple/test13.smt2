(set-logic HORN)
(declare-fun X0 () Bool)
(declare-fun X1 () Bool)
(declare-fun X2 () Bool)
(declare-fun X3 () Bool)
(declare-fun X4 () Bool)
(declare-fun X5 () Bool)
(declare-fun X6 () Bool)
(declare-fun X7 () Bool)
(declare-fun X8 () Bool)
(declare-fun X9 () Bool)
(declare-fun X10 () Bool)
(declare-fun X11 () Bool)
(declare-fun X12 () Bool)
(declare-fun X13 () Bool)
(declare-fun X14 () Bool)
(declare-fun X15 () Bool)
(declare-fun X51 () Bool)
(declare-fun X52 () Bool)
(declare-fun X53 () Bool)
(declare-fun X54 () Bool)
(declare-fun X65 () Bool)
(declare-fun X66 () Bool)
(declare-fun X67 () Bool)
(declare-fun X68 () Bool)
(declare-fun X69 () Bool)
(declare-fun X70 () Bool)
(declare-fun X71 () Bool)
(declare-fun X72 () Bool)
(declare-fun X73 () Bool)
(declare-fun X74 () Bool)
(declare-fun X75 () Bool)
(declare-fun X76 () Bool)
(declare-fun X77 () Bool)
(declare-fun X78 () Bool)
(declare-fun X79 () Bool)
(declare-fun X80 () Bool)
(declare-fun X81 () Bool)
(declare-fun X82 () Bool)
(declare-fun X83 () Bool)
(declare-fun X84 () Bool)
(declare-fun X85 () Bool)
(declare-fun X86 () Bool)
(declare-fun X87 () Bool)
(declare-fun X88 () Bool)
(declare-fun X89 () Bool)
(assert (=> true X0))
(assert (=> X8 X89))
(assert (=> (and X8 X15) X7))
(assert (=> (and X8 X14) X6))
(assert (=> (and (and X8 X14) X5) X13))
(assert (=> (and (and (and X8 X14) X5) X12) X4))
(assert (=> (and X8 X11) X3))
(assert (=> (and (and X8 X11) X2) X10))
(assert (=> (and (and (and X8 X11) X2) X9) X1))
(assert (=> X89 X14))
(assert (=> (and X89 X13) X87))
(assert (=> (and (and X89 X13) X88) X12))
(assert (=> X87 X82))
(assert (=> (and X87 X83) X88))
(assert (=> (and X87 X84) X11))
(assert (=> (and (and X87 X84) X10) X85))
(assert (=> (and (and (and X87 X84) X10) X86) X9))
(assert (=> X82 X8))
(assert (=> (and X82 X7) X83))
(assert (=> (and X82 X6) X84))
(assert (=> (and (and X82 X6) X85) X5))
(assert (=> (and (and (and X82 X6) X85) X4) X86))
(assert (=> (and X82 X3) X14))
(assert (=> (and (and X82 X3) X13) X2))
(assert (=> (and (and (and X82 X3) X13) X1) X12))
(assert (=> X81 X11))
(assert (=> (and X81 X10) X79))
(assert (=> (and (and X81 X10) X80) X9))
(assert (=> X79 X74))
(assert (=> (and X79 X75) X80))
(assert (=> (and X79 X76) X11))
(assert (=> (and (and X79 X76) X10) X77))
(assert (=> (and (and (and X79 X76) X10) X78) X9))
(assert (=> X74 X8))
(assert (=> (and X74 X7) X75))
(assert (=> (and X74 X6) X76))
(assert (=> (and (and X74 X6) X77) X5))
(assert (=> (and (and (and X74 X6) X77) X4) X78))
(assert (=> (and X74 X3) X14))
(assert (=> (and (and X74 X3) X13) X2))
(assert (=> (and (and (and X74 X3) X13) X1) X12))
(assert (=> X0 X73))
(assert (=> X73 X71))
(assert (=> false false))
(assert (=> X71 X66))
(assert (=> (and X71 X67) X72))
(assert (=> (and X71 X68) false))
(assert (=> (and (and X71 X68) X52) X69))
(assert (=> (and (and (and X71 X68) X52) X70) X51))
(assert (=> X66 X8))
(assert (=> (and X66 X7) X67))
(assert (=> (and X66 X6) X68))
(assert (=> (and (and X66 X6) X69) X5))
(assert (=> (and (and (and X66 X6) X69) X4) X70))
(assert (=> (and X66 X3) X65))
(assert (=> (and (and X66 X3) X54) X2))
(assert (=> (and (and (and X66 X3) X54) X1) X53))
(assert (=> X65 X54))
(assert (=> false false))
(check-sat)
