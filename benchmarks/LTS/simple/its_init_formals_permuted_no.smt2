; An integer transition system in the TermCOMP ITS format (read with -p pltsterm / -p pltsnterm)
; whose init_main lists the variables in a different order from next_main.  The two lists
; correspond by position, so init_main's y is next_main's x and conversely; the initial relation
; is true, so every pair of values is an initial state.  From any state with x > y the loop at
; l1 runs forever, so the system does not terminate: expected answer NO for pltsterm and YES for
; pltsnterm.  Copying the initial values with one assignment after another gave x the value of y
; before y was read, so every initial state had x = y and the system was proved terminating.
(declare-sort Loc 0)
(declare-const l0 Loc)
(declare-const l1 Loc)
(assert (distinct l0 l1))

(define-fun cfg_init ( (pc Loc) (src Loc) (rel Bool) ) Bool
  (and (= pc src) rel))

(define-fun cfg_trans2 ( (pc Loc) (src Loc)
                         (pc1 Loc) (dst Loc)
                         (rel Bool) ) Bool
  (and (= pc src) (= pc1 dst) rel))

(define-fun init_main ( (pc Loc) (y Int) (x Int) ) Bool
  (cfg_init pc l0 true))

(define-fun next_main (
                 (pc Loc) (x Int) (y Int)
                 (pc1 Loc) (xP Int) (yP Int)
             ) Bool
  (or
    (cfg_trans2 pc l0 pc1 l1 (and (= xP x) (= yP y)))
    (cfg_trans2 pc l1 pc1 l1 (and (> x y) (= xP x) (= yP y)))
  )
)
