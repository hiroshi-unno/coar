;; Provenance.  A hand-reduced z3 reproducer of the validity query PCSat asks on the Thrust `skip_step`
;; query (a Rust program's verification condition emitted by the Thrust frontend with THRUST_OUTPUT_DIR and
;; a stub solver), received from the Thrust developers on 2026-09-27 as a 6302-byte query (sha256
;; cdac4b1e88d184a5c08f1a58dde441544fb6117c292800282dda5f75dc246311).  It is a quantified SMT query over
;; uninterpreted sorts, datatypes, sequences (a z3/cvc5 extension, not an SMT-LIB theory) and arrays, with no
;; predicate unknown, so it moved here from the constraint-problem corpus on 2026-09-27.  Changes from the
;; original: these comment lines, and a final (check-sat), which the original lacked.  No verdict is known:
;; z3 timed out at 14.8 s on the original, so the name carries none.
(declare-sort |#svar_a1| 0)
(declare-datatypes ((A5_std.option.Option<a1> 0)) (((std.option.Option.Some<a1> (_getstd.option.Option.Some.0<a1> |#svar_a1|)) (std.option.Option.None<a1>))))
(declare-sort |#svar_a0| 0)
(declare-datatypes ((A3_Mut<a0> 0)) (((mut<a0> (mut_current<a0> |#svar_a0|) (mut_final<a0> |#svar_a0|)))))
(declare-datatypes ((A1_Tuple<a0-Int> 0)) (((tuple<a0-Int> (tuple_proj<a0-Int>.0 |#svar_a0|) (tuple_proj<a0-Int>.1 Int)))))
(declare-datatypes ((A2_Mut<Tuple<a0-Int>> 0)) (((mut<Tuple<a0-Int>> (mut_current<Tuple<a0-Int>> A1_Tuple<a0-Int>) (mut_final<Tuple<a0-Int>> A1_Tuple<a0-Int>)))))
(declare-fun x5 () A5_std.option.Option<a1>)
(declare-fun x3 () |#svar_a0|)
(declare-fun x0 () (Seq |#svar_a0|))
(declare-fun x7 () (Array A3_Mut<a0> Bool))
(declare-fun x6 () |#svar_a1|)
(declare-fun x9
             ()
             (Array |#svar_a0| (Array |#svar_a1| (Array |#svar_a0| Bool))))
(declare-fun x4 () A2_Mut<Tuple<a0-Int>>)
(declare-fun x1 () Int)
(declare-fun x8 () (Array |#svar_a0| Bool))
(declare-fun x2 () (Seq |#svar_a0|))
(assert (let ((a!1 (not (= (seq.nth x0 0)
                   (tuple_proj<a0-Int>.0 (mut_current<Tuple<a0-Int>> x4)))))
      (a!2 (= (seq.nth x2 (- (seq.len x2) 1)) (seq.nth x0 (- (seq.len x0) 1))))
      (a!3 (not (= (seq.nth x2 0)
                   (tuple_proj<a0-Int>.0 (mut_current<Tuple<a0-Int>> x4)))))
      (a!4 (<= 0
               (- (+ (- 1) x1)
                  (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> x4)))))
      (a!5 (= 0
              (+ (- (- 1 x1) (seq.len x0))
                 (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> x4)))))
      (a!6 (= 0
              (+ (- (- 1 x1) (seq.len x2))
                 (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> x4)))))
      (a!7 (select x8 (seq.nth x0 (- (seq.len x0) 1))))
      (a!8 (select x8 (seq.nth x2 (- (seq.len x2) 1))))
      (a!9 (= true
              (ite (= x5 std.option.Option.None<a1>)
                   true
                   (not ((_ is std.option.Option.Some<a1>) x5)))))
      (a!10 (forall ((|#tvar1204| Int))
              (let ((a!1 (not (<= 0 (+ (- (- 2) |#tvar1204|) (seq.len x0))))))
                (or a!1
                    (not (>= |#tvar1204| 0))
                    (exists ((|#tvar1205| |#svar_a1|))
                      (let ((a!1 (select (select (select x9
                                                         (seq.nth x0
                                                                  |#tvar1204|))
                                                 |#tvar1205|)
                                         (seq.nth x0 (+ |#tvar1204| 1)))))
                        (not (= false a!1))))))))
      (a!11 (forall ((|#tvar1203| |#svar_a1|))
              (let ((a!1 (select x9 (seq.nth x0 (- (seq.len x0) 1)))))
              (let ((a!2 (not (= false (select (select a!1 |#tvar1203|) x3)))))
                (or a!2 (not (= x5 (std.option.Option.Some<a1> |#tvar1203|))))))))
      (a!12 (forall ((|#tvar1201| Int))
              (let ((a!1 (not (<= 0 (+ (- (- 2) |#tvar1201|) (seq.len x2))))))
                (or a!1
                    (not (>= |#tvar1201| 0))
                    (exists ((|#tvar1202| |#svar_a1|))
                      (let ((a!1 (select (select (select x9
                                                         (seq.nth x2
                                                                  |#tvar1201|))
                                                 |#tvar1202|)
                                         (seq.nth x2 (+ |#tvar1201| 1)))))
                        (not (= false a!1))))))))
      (a!13 (<= 0
                (+ (- 1 x1)
                   (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> x4)))))
      (a!15 (not (not (= x5 (std.option.Option.Some<a1> x6)))))
      (a!17 (mut<a0> (seq.nth x0 (- (seq.len x0) 1)) x3)))
(let ((a!14 (or (not a!13)
                (not (<= 0 (+ (- 1) x1)))
                (not (= true (select x8 x3)))
                (forall ((|#tvar1209| (Seq |#svar_a0|)))
                  (let ((a!1 (not (= (seq.nth |#tvar1209| 0)
                                     (tuple_proj<a0-Int>.0
                                       (mut_current<Tuple<a0-Int>> x4)))))
                        (a!2 (= 0
                                (+ (- (- 2 x1) (seq.len |#tvar1209|))
                                   (tuple_proj<a0-Int>.1
                                     (mut_current<Tuple<a0-Int>> x4)))))
                        (a!3 (= x3
                                (seq.nth |#tvar1209|
                                         (- (seq.len |#tvar1209|) 1))))
                        (a!4 (exists ((|#tvar1210| Int))
                               (let ((a!1 (not (<= 0
                                                   (- (+ 1 |#tvar1210|)
                                                      (seq.len |#tvar1209|))))))
                                 (and a!1
                                      (not (<= 0 (- (- 1) |#tvar1210|)))
                                      (forall ((|#tvar1211| |#svar_a1|))
                                        (let ((a!1 (select (select (select x9
                                                                           (seq.nth |#tvar1209|
                                                                                    |#tvar1210|))
                                                                   |#tvar1211|)
                                                           (seq.nth |#tvar1209|
                                                                    (+ |#tvar1210|
                                                                       1)))))
                                          (not (= true a!1)))))))))
                    (or a!1 (not a!2) (not a!3) a!4)))))
      (a!16 (or a!15 (not (not (= x5 std.option.Option.None<a1>)))))
      (a!18 (or (not (= false (select x7 a!17)))
                (not (= x5 std.option.Option.None<a1>)))))
  (and (not a!1)
       (not (not a!2))
       (not a!3)
       (not a!4)
       (not (<= 0 (- (- 1) x1)))
       (not (not a!5))
       (not (not a!6))
       (not (= false a!7))
       (not (= false a!8))
       (not (= false (select x8 x3)))
       (not a!9)
       (not (= x1 0))
       a!10
       a!11
       a!12
       a!14
       a!16
       a!18))))

(check-sat)
