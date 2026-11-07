; An integer transition system in the TermCOMP ITS format (read with -p pltsterm / -p pltsnterm)
; whose transition relation is false: no state has a successor, so every run stops in its initial
; state and the system terminates: expected answer YES for pltsterm and NO for pltsnterm.  The
; reader used to take the false disjunct for a cfg_trans2 application and failed on it.
(declare-sort Loc 0)
(declare-const l0 Loc)

(define-fun cfg_init ( (pc Loc) (src Loc) (rel Bool) ) Bool
  (and (= pc src) rel))

(define-fun cfg_trans2 ( (pc Loc) (src Loc)
                         (pc1 Loc) (dst Loc)
                         (rel Bool) ) Bool
  (and (= pc src) (= pc1 dst) rel))

(define-fun init_main ( (pc Loc) (x Int) ) Bool
  (cfg_init pc l0 true))

(define-fun next_main (
                 (pc Loc) (x Int)
                 (pc1 Loc) (xP Int)
             ) Bool
  false
)
