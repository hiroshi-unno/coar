(push)
(declare-sort |#svar_a142| 0)
(declare-sort |#svar_a141| 0)
(declare-sort |#svar_a140| 0)
(declare-fun x2 () (Seq |#svar_a142|))
(declare-fun x9 () |#svar_a142|)
(declare-fun x8 () |#svar_a141|)
(declare-fun x1 () |#svar_a141|)
(declare-fun x7
             ()
             (Array |#svar_a141|
                    (Array (Seq |#svar_a142|) (Array |#svar_a141| Bool))))
(declare-fun x0 () |#svar_a140|)
(declare-fun x6 () (Array |#svar_a140| (Array |#svar_a142| Bool)))
(declare-fun x10 () |#svar_a141|)
(declare-fun x5 () (Array |#svar_a140| (Array |#svar_a142| (Array Bool Bool))))
(declare-fun x4 () (Array |#svar_a141| Bool))
(declare-fun x3 () |#svar_a141|)
(assert (let ((a!1 (= false (select (select (select x5 x0) x9) false)))
      (a!2 (= false
              (select (select (select x7 x3) (as seq.empty (Seq |#svar_a142|)))
                      x10)))
      (a!3 (= false
              (select (select (select x7 x3) (as seq.empty (Seq |#svar_a142|)))
                      x1)))
      (a!4 (forall ((|#tvar3149| (Seq |#svar_a142|)))
             (forall ((|#tvar3150| |#svar_a142|))
               (forall ((|#tvar3151| |#svar_a141|))
                 (let ((a!1 (not (= false (select (select x6 x0) |#tvar3150|))))
                       (a!2 (select (select (select x7 x8)
                                            (seq.++ |#tvar3149|
                                                    (seq.unit |#tvar3150|)))
                                    |#tvar3151|)))
                   (or a!1 (not (= true a!2))))))))
      (a!5 (forall ((|#tvar3146| (Seq |#svar_a142|)))
             (forall ((|#tvar3147| |#svar_a141|))
               (let ((a!1 (not (<= 0 (+ (- 1) (seq.len |#tvar3146|)))))
                     (a!2 (select (select x5 x0)
                                  (seq.nth |#tvar3146|
                                           (- (seq.len |#tvar3146|) 1))))
                     (a!3 (= true
                             (select (select (select x7 x3) |#tvar3146|)
                                     |#tvar3147|)))
                     (a!4 (exists ((|#tvar3148| Int))
                            (let ((a!1 (not (<= 0
                                                (- (+ 1 |#tvar3148|)
                                                   (seq.len |#tvar3146|)))))
                                  (a!2 (= true
                                          (select (select (select x5 x0)
                                                          (seq.nth |#tvar3146|
                                                                   |#tvar3148|))
                                                  true))))
                              (and a!1
                                   (not (<= 0 (- (- 1) |#tvar3148|)))
                                   (not a!2))))))
                 (or a!1 (not (= true (select a!2 false))) (not a!3) a!4)))))
      (a!6 (forall ((|#tvar3141| |#svar_a141|))
             (forall ((|#tvar3142| (Seq |#svar_a142|)))
               (forall ((|#tvar3143| |#svar_a141|))
                 (forall ((|#tvar3144| (Seq |#svar_a142|)))
                   (forall ((|#tvar3145| |#svar_a141|))
                     (let ((a!1 (= false
                                   (select (select (select x7 |#tvar3141|)
                                                   (seq.++ |#tvar3142|
                                                           |#tvar3144|))
                                           |#tvar3145|)))
                           (a!2 (= true
                                   (select (select (select x7 |#tvar3143|)
                                                   |#tvar3144|)
                                           |#tvar3145|)))
                           (a!3 (= true
                                   (select (select (select x7 |#tvar3141|)
                                                   |#tvar3142|)
                                           |#tvar3143|))))
                       (or (not a!1) (not a!2) (not a!3)))))))))
      (a!7 (forall ((|#tvar3140| |#svar_a141|))
             (let ((a!1 (= false
                           (select (select (select x7 |#tvar3140|)
                                           (as seq.empty (Seq |#svar_a142|)))
                                   |#tvar3140|))))
               (or (not a!1) (not (= true (select x4 |#tvar3140|)))))))
      (a!8 (forall ((|#tvar3137| (Seq |#svar_a142|)))
             (forall ((|#tvar3138| |#svar_a142|))
               (forall ((|#tvar3139| |#svar_a141|))
                 (let ((a!1 (not (= false (select (select x6 x0) |#tvar3138|))))
                       (a!2 (select (select (select x7 x10)
                                            (seq.++ |#tvar3137|
                                                    (seq.unit |#tvar3138|)))
                                    |#tvar3139|)))
                   (or a!1 (not (= true a!2))))))))
      (a!9 (forall ((|#tvar3136| Int))
             (let ((a!1 (not (<= 0
                                 (+ (- (- 1) |#tvar3136|)
                                    (seq.len (as seq.empty (Seq |#svar_a142|)))))))
                   (a!2 (= false
                           (select (select (select x5 x0)
                                           (seq.nth (as seq.empty
                                                        (Seq |#svar_a142|))
                                                    |#tvar3136|))
                                   true))))
               (or a!1 (not a!2) (not (>= |#tvar3136| 0))))))
      (a!10 (forall ((|#tvar3135| |#svar_a142|))
              (let ((a!1 (= false
                            (select (select (select x7 x10)
                                            (seq.unit |#tvar3135|))
                                    x8))))
                (or (not a!1) (not (= x9 |#tvar3135|))))))
      (a!11 (forall ((|#tvar3123| (Seq |#svar_a142|)))
              (forall ((|#tvar3124| |#svar_a142|))
                (forall ((|#tvar3125| |#svar_a141|))
                  (let ((a!1 (not (= false (select (select x6 x0) |#tvar3124|))))
                        (a!2 (select (select (select x7 x1)
                                             (seq.++ |#tvar3123|
                                                     (seq.unit |#tvar3124|)))
                                     |#tvar3125|)))
                    (or a!1 (not (= true a!2))))))))
      (a!12 (forall ((|#tvar3121| |#svar_a142|))
              (let ((a!1 (= false
                            (select (select (select x7 x1)
                                            (seq.unit |#tvar3121|))
                                    x8))))
                (or (not a!1) (not (= x9 |#tvar3121|)))))))
  (and (not a!1)
       (not a!2)
       (not a!3)
       (not (= false (select x4 x10)))
       (not (= false (select x4 x8)))
       (not (= false (select x4 x1)))
       a!4
       a!5
       a!6
       a!7
       a!8
       a!9
       a!10
       a!11
       a!12
       (= x2 (as seq.empty (Seq |#svar_a142|))))))

;; assumptions

(check-sat)
