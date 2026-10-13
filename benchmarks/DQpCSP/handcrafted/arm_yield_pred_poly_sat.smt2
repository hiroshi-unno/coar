; The POPL 2024 ARM benchmark `yield-SAT.ml`, whose ghost information sits in **constructor-level**
; abstracted predicates, as QCHC, encoded by universally quantified predicates.
;
;   type iterator = Result of int tree | Susp of int * (int -> iterator)
;   [@@@rtype "Result :: (t: {z: int | p0(z)} tree) -> {z: iterator | z = Result(t)}"]
;   [@@@rtype "Susp :: (x: {z: int | p1(z)}) ->
;                      (f: ((y: {z: int | p2(z, x)}) -> {z: iterator | p3(z, x, y)})) -> ..."]
;   run body = match_with body () { retc = fun x -> Result x;
;                                   Yield x -> fun k -> Susp (x, continue k) }
;   let rec depthWalk = function Node (l,r) -> ... | Leaf a -> let b = perform (Yield a) in Leaf b
;   let rec incr = function Susp (x, k) -> incr (k (x + 1)) | Result r -> r
;   assert  incr_tree : {z: int | z = 0} tree -> {z: int | z = 1} tree
;
; This is the first ARM program in the corpus whose abstraction is **not a single predicate**:
; the annotations name four (`p0` … `p3`), and two of them are indexed by the yielded value `x`.
; They are the coroutine protocol between the producer (`run` + `depthWalk`, which yields `x`
; with `p1(x)` and resumes with a value satisfying `p2(·, x)`) and the consumer (`incr`, which
; supplies `x + 1` and must discharge `p2(x+1, x)`).  In the evaluated file those predicates are
; written out by hand as `[@@@rtype]` annotations, which is the constructor-level form of the
; ghost parameter; here they are two universal symbols and the unknown is a Henkin function of
; both.
;
; One leaf is modelled: the tree recursion adds nothing to the abstraction (`Node` just walks).
; A genuinely *dependency*-quantified instance would need two components observing different
; abstracted predicates -- the `queue-1`/`queue-2` files, whose handlers pass a continuation
; between two clients, are where to look for that.  expected: sat
(set-logic DQHORN)

(declare-forall-fun P1 (Int) Bool)        ; p1: what the producer yields
(declare-forall-fun P2 (Int Int) Bool)    ; p2(y, x): what the consumer may resume with, given x
(declare-dep-exists-fun Iter () ((Array Int Bool) (Array Int (Array Int Bool)) Int Int Int) Bool)

; --- the producer, verified once for every (P1, P2): a leaf yields its value x and becomes the
;     value y it is resumed with ---
(assert (forall ((x Int) (y Int)) (=> (and (P1 x) (P2 y x)) (Iter P1 P2 x y y))))

; --- client 1: `incr` on a tree of zeros -- P1 := (x |-> x = 0), P2 := (y,x) |-> y = x + 1;
;     the leaves of the result must be 1 ---
(assert (forall ((x Int) (y Int) (r Int))
  (=> (and (Iter (lambda ((a Int)) (= a 0)) (lambda ((b Int)) (lambda ((a Int)) (= b (+ a 1))))
                 x y r)
           (not (= r 1)))
      false)))
; --- client 2: a different instantiation of the same, once-verified producer -- non-negative
;     leaves resumed with something strictly larger; the result's leaves are positive (one verification, several clients) ---
(assert (forall ((x Int) (y Int) (r Int))
  (=> (and (Iter (lambda ((a Int)) (>= a 0)) (lambda ((b Int)) (lambda ((a Int)) (> b a)))
                 x y r)
           (<= r 0))
      false)))
(check-sat)
