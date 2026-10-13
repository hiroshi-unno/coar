; An integer transition system in the TermCOMP ITS format (read with -p pltsterm): locations are
; constants of the uninterpreted sort Loc declared with declare-const, so the reader must take them
; as ordinary constants rather than unknowns to solve for (it used to refuse every such file with
; "synthesis of a function of the sort Loc is not supported").  The loop counts x down to 0, so the
; system terminates: expected answer YES.
(declare-sort Loc 0)
(declare-const l_init Loc)
(declare-const l_loop Loc)
(assert (distinct l_init l_loop))

(define-fun cfg_init ( (pc Loc) (src Loc) (rel Bool) ) Bool
  (and (= pc src) rel))

(define-fun cfg_trans2 ( (pc Loc) (src Loc)
                         (pc1 Loc) (dst Loc)
                         (rel Bool) ) Bool
  (and (= pc src) (= pc1 dst) rel))

(define-fun init_main ( (pc Loc) (x Int) ) Bool
  (cfg_init pc l_init true))

(define-fun next_main (
                 (pc Loc) (x Int)
                 (pc1 Loc) (xP Int)
             ) Bool
  (or
    (cfg_trans2 pc l_init pc1 l_loop true)
    (cfg_trans2 pc l_loop pc1 l_loop (and (> x 0) (= xP (- x 1))))
  )
)
