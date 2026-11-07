; unknown.  Z3 5.1.0 runs this question past the budget it states, (set-option :timeout 5000), and past an
; :rlimit in its place, growing to 2 GB and more inside the sequence theory (smt::theory_seq, in
; add_solution).  The overrun depends on the random seed and is not stable across runs: on 2026-10-22
; seeds 1 and 7 were killed at 90 s and ten other seeds answered at about 5 s; on 2026-10-28 seed 7
; was killed at 40 s while seeds 1 and 3 answered `unknown` at 5-6 s.  A library that honours the
; budget answers `unknown` at about 5 s at every seed (Z3Prover/z3 issue #11271; Z3 5.3.1 still
; overruns at seed 3).  A validation question of a constraint problem over generic sequences, as PCSat
; asked it, with seed 7 set below.  The reason PCSat asks such questions in a forked copy killed by
; the wall clock (fork_unreturnable_queries and its siblings).
(set-option :smt.random_seed 7)
(set-option :sat.random_seed 7)
(set-option :timeout 5000)
(set-logic ALL)
(declare-sort |#svar_a15| 0)
(declare-datatypes ((|#dt_2864617461747970652041315f5475706c653c5365713c6131353e2d496e743e29| 0)) (((tuple<Seq<a15>-Int> (tuple_proj<Seq<a15>-Int>.0 (Seq |#svar_a15|)) (tuple_proj<Seq<a15>-Int>.1 Int)))))
(declare-fun x12 () (Seq |#svar_a15|))
(declare-fun x0
             ()
             |#dt_2864617461747970652041315f5475706c653c5365713c6131353e2d496e743e29|)
(declare-fun x8 () (Seq |#svar_a15|))
(declare-fun x6 () |#svar_a15|)
(declare-fun x22 () Int)
(declare-fun x16 () Int)
(declare-fun x3 () (Array Int Bool))
(declare-fun x2 () (Seq |#svar_a15|))
(declare-fun x21 () Int)
(declare-fun x5 () (Array |#svar_a15| Int))
(declare-fun x13 () Int)
(declare-fun x20 () Int)
(declare-fun x19 () Int)
(declare-fun x18 () Int)
(declare-fun x17 () Int)
(declare-fun x4 () (Array |#svar_a15| (Array Int Bool)))
(declare-fun x7 () (Seq |#svar_a15|))
(declare-fun x15 () Int)
(declare-fun x24 () Int)
(declare-fun x1 () (Seq |#svar_a15|))
(declare-fun x11 () Int)
(declare-fun x14 () Int)
(declare-fun x9 () Int)
(declare-fun x10 () Int)
(declare-fun x23 () Int)
(declare-fun x25 () Int)
(declare-fun x26 () Int)
(assert (let ((a!1 (= 0 (- (+ (seq.len x1) (seq.len x2)) (seq.len x8))))
      (a!2 (= 0 (- (+ (seq.len x1) (seq.len x2)) (seq.len x12))))
      (a!3 (> 0 (- (+ (- 1) x9) (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!4 (> 0 (- (+ (- 1) x15) (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!5 (> 0 (- (+ (- 1) x14) (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!6 (> 0 (- (+ (- 1) x13) (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!7 (> 0 (- (+ (- 1) x11) (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!8 (> 0 (- (- 1) (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!9 (= 0 (+ (- (seq.len x8) x9) (tuple_proj<Seq<a15>-Int>.1 x0))))
      (a!10 (= 0 (+ (- (seq.len x8) x11) (tuple_proj<Seq<a15>-Int>.1 x0))))
      (a!11 (= 0 (+ (- (seq.len x12) x14) (tuple_proj<Seq<a15>-Int>.1 x0))))
      (a!12 (not (= false (select (select x4 x6) x23))))
      (a!13 (not (= false (select (select x4 x6) x10))))
      (a!14 (forall ((|#tvar24594| |#svar_a15|))
              (let ((a!1 (not (= false
                                 (select (select x4 |#tvar24594|)
                                         (select x5 |#tvar24594|)))))
                    (a!2 (forall ((|#tvar24595| Int))
                           (let ((a!1 (not (= true
                                              (select (select x4 |#tvar24594|)
                                                      |#tvar24595|)))))
                             (or (= 0 (- |#tvar24595| (select x5 |#tvar24594|)))
                                 a!1)))))
                (and (> 0 (- (- 1) (select x5 |#tvar24594|))) a!1 a!2))))
      (a!15 (forall ((|#tvar24592| Int))
              (let ((a!1 (+ (- x13 (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))
                            (select x5 (seq.nth x2 |#tvar24592|)))))
                (or (> 0 (+ (- (- 1) |#tvar24592|) (seq.len x2)))
                    (> 0 a!1)
                    (< |#tvar24592| 0)))))
      (a!16 (forall ((|#tvar24591| Int) (|#tvar24590| Int))
              (let ((a!1 (- (select x5
                                    (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0)
                                             |#tvar24591|))
                            (select x5
                                    (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0)
                                             |#tvar24590|))))
                    (a!2 (> 0
                            (+ (- (- 1) |#tvar24590|)
                               (seq.len (tuple_proj<Seq<a15>-Int>.0 x0))))))
                (or (> 0 (- (+ (- 1) |#tvar24590|) |#tvar24591|))
                    (not (= 0 a!1))
                    a!2
                    (< |#tvar24591| 0)))))
      (a!17 (forall ((|#tvar24589| Int) (|#tvar24588| Int))
              (let ((a!1 (> 0
                            (- |#tvar24588|
                               (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
                    (a!2 (> 0
                            (+ (- (- 1) |#tvar24589|)
                               (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
                    (a!3 (select (select x4
                                         (seq.nth (tuple_proj<Seq<a15>-Int>.0
                                                    x0)
                                                  |#tvar24589|))
                                 |#tvar24588|)))
                (or a!1 a!2 (not (= true a!3)) (< |#tvar24589| 0)))))
      (a!18 (forall ((|#tvar24587| Int))
              (let ((a!1 (> 0
                            (- (seq.len (tuple_proj<Seq<a15>-Int>.0 x0))
                               |#tvar24587|))))
                (or a!1
                    (not (= false (select x3 |#tvar24587|)))
                    (< |#tvar24587| 0)))))
      (a!19 (forall ((|#tvar24600| Int))
              (let ((a!1 (= (seq.nth x12 |#tvar24600|)
                            (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0)
                                     (+ (tuple_proj<Seq<a15>-Int>.1 x0)
                                        |#tvar24600|)))))
                (or a!1
                    (> 0 (+ (- (- 1) |#tvar24600|) (seq.len x12)))
                    (< |#tvar24600| 0)))))
      (a!20 (and (>= (seq.len (tuple_proj<Seq<a15>-Int>.0 x0))
                     (+ (tuple_proj<Seq<a15>-Int>.1 x0) (seq.len x12)))
                 (<= 0 (tuple_proj<Seq<a15>-Int>.1 x0))))
      (a!21 (forall ((|#tvar24593| Int))
              (let ((a!1 (= (seq.nth x8 |#tvar24593|)
                            (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0)
                                     (+ (tuple_proj<Seq<a15>-Int>.1 x0)
                                        |#tvar24593|)))))
                (or a!1
                    (> 0 (+ (- (- 1) |#tvar24593|) (seq.len x8)))
                    (< |#tvar24593| 0)))))
      (a!22 (and (>= (seq.len (tuple_proj<Seq<a15>-Int>.0 x0))
                     (+ (tuple_proj<Seq<a15>-Int>.1 x0) (seq.len x8)))
                 (<= 0 (tuple_proj<Seq<a15>-Int>.1 x0))))
      (a!23 (+ (seq.len x2) (seq.len (seq.++ x1 (seq.unit x6)))))
      (a!25 (> 0 (- (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)) x15)))
      (a!26 (> 0 (- (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)) x13)))
      (a!27 (not (= 0 (- (seq.len x2) x24))))
      (a!28 (- (seq.len (seq.++ x12 (seq.unit x6))) x15))
      (a!30 (> 0 (- x17 (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!31 (> 0 (+ (- (- 1) x18) (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!32 (select (select x4 (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0) x17))
                    x18))
      (a!33 (- (select x5 (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0) x19))
               (select x5 (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0) x20))))
      (a!34 (> 0 (- x20 (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!35 (- (+ (- (- 1) x13) (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))
               (select x5 (seq.nth x2 x21))))
      (a!37 (> 0 (- (+ (- 1) x16) (seq.len (tuple_proj<Seq<a15>-Int>.0 x0)))))
      (a!39 (and (<= (seq.len x12) x22) (< x22 (+ (seq.len x12) 1))))
      (a!43 (- x22 (seq.len (seq.++ x12 (seq.unit x6)))))
      (a!45 (or (< (seq.len (tuple_proj<Seq<a15>-Int>.0 x0))
                   (+ (tuple_proj<Seq<a15>-Int>.1 x0) (seq.len x8)))
                (> 0 (tuple_proj<Seq<a15>-Int>.1 x0))
                (= x8
                   (seq.extract (tuple_proj<Seq<a15>-Int>.0 x0)
                                (tuple_proj<Seq<a15>-Int>.1 x0)
                                (seq.len x8)))))
      (a!46 (or (< (seq.len (tuple_proj<Seq<a15>-Int>.0 x0))
                   (+ (tuple_proj<Seq<a15>-Int>.1 x0) (seq.len x12)))
                (> 0 (tuple_proj<Seq<a15>-Int>.1 x0))
                (= x12
                   (seq.extract (tuple_proj<Seq<a15>-Int>.0 x0)
                                (tuple_proj<Seq<a15>-Int>.1 x0)
                                (seq.len x12))))))
(let ((a!24 (- a!23 (seq.len (seq.++ x12 (seq.unit x6)))))
      (a!29 (not (= 0 (+ a!28 (tuple_proj<Seq<a15>-Int>.1 x0)))))
      (a!36 (and (> 0 a!35) (> 0 (- (- 1) x21)) (> 0 (- x21 (seq.len x2)))))
      (a!38 (and a!37 (> 0 (- (- 1) x16)) (not (= true (select x3 x16)))))
      (a!40 (ite a!39 x6 (seq.nth (seq.++ x12 (seq.unit x6)) x22))))
(let ((a!41 (ite (and (<= 0 x22) (< x22 (seq.len x12))) (seq.nth x12 x22) a!40)))
(let ((a!42 (= a!41
               (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0)
                        (+ (tuple_proj<Seq<a15>-Int>.1 x0) x22)))))
(let ((a!44 (or (not (= 0 a!24))
                a!25
                a!26
                (> 0 (- (seq.len x7) x15))
                a!27
                (> 0 (- x15 (tuple_proj<Seq<a15>-Int>.1 x0)))
                a!29
                (not (= 0 (tuple_proj<Seq<a15>-Int>.1 x0)))
                (not (= x7 (tuple_proj<Seq<a15>-Int>.0 x0)))
                (and (> 0 (- (- 1) x17)) a!30 a!31 (not (= false a!32)))
                (and (= 0 a!33) (> 0 (- (- 1) x19)) a!34 (> 0 (- x19 x20)))
                a!36
                a!38
                (and (not a!42) (> 0 (- (- 1) x22)) (> 0 a!43)))))
  (and (= (seq.++ x12 (seq.unit x6)) (seq.++ x8 (seq.unit x6)))
       a!1
       a!2
       (= 0 (- (+ 1 x9) x15))
       (= 0 (- (+ 1 x14) x15))
       (= 0 (- (+ 1 x11) x15))
       a!3
       (> 0 (- (+ (- 1) x9) x15))
       a!4
       (> 0 (- (+ (- 1) x15) (seq.len x7)))
       a!5
       (> 0 (- (+ (- 1) x14) x15))
       a!6
       a!7
       (> 0 (- (+ (- 1) x11) x15))
       (= 0 (- (seq.len x2) x26))
       (= 0 (- (seq.len x2) x25))
       a!8
       (> 0 (- (- 1) x23))
       (> 0 (- (- 1) x13))
       (> 0 (- (- 1) x10))
       (> 0 (- x23 x13))
       (> 0 (- x10 x13))
       a!9
       a!10
       a!11
       (> 0 (+ (- (- 1) x9) (tuple_proj<Seq<a15>-Int>.1 x0)))
       (> 0 (+ (- (- 1) x14) (tuple_proj<Seq<a15>-Int>.1 x0)))
       (> 0 (+ (- (- 1) x11) (tuple_proj<Seq<a15>-Int>.1 x0)))
       (= 0 (tuple_proj<Seq<a15>-Int>.1 x0))
       a!12
       a!13
       (= x7 (tuple_proj<Seq<a15>-Int>.0 x0))
       (= x6 (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0) x9))
       (= x6 (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0) x14))
       (= x6 (seq.nth (tuple_proj<Seq<a15>-Int>.0 x0) x11))
       a!14
       a!15
       a!16
       a!17
       a!18
       (or a!19 a!20)
       (or a!21 a!22)
       a!44
       a!45
       a!46)))))))
(check-sat)
