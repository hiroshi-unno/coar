; The POPL 2024 ARM benchmark `bfs-simpl-SAT.ml` with its ghost parameter replaced by predicate
; polymorphism, encoded by universally quantified predicates.
;
;   bfs _ctx body = let q = ref [] in
;     let run_next () = match pop_opt q with None -> Failure | Some (k,x) -> k x in
;     match_with body () {
;       retc = (fun x -> match x with Success x -> Success x | Failure -> run_next ());
;       Select -> fun k -> push (continue k, true) q; push (continue k, false) q; run_next () }
;   let sqrt a = bfs a (fun () -> let cand = if perform Select then a else -a in
;                                 if cand * cand = a * a then Success cand else Failure)
;
; Breadth-first search: the handler stores the *continuations themselves* in a queue and runs
; them one by one, so the abstracted predicate has to describe what a queued continuation
; answers when resumed — `X(ok, v, b)` = "resuming with `b` answers `Success v`, or `Failure`
; when `ok` is false".  The queue's discipline changes the order in which branches are tried but
; not the set of answers, so the two clauses below are the whole content: a branch that succeeds
; is returned, and if both fail the answer is `Failure`.
;
; The ghost parameter `_ctx` passed the client's `a` into the handler; here the handler is
; verified once and the two clients instantiate.  expected: sat
(set-logic DQHORN)

(declare-forall-fun X (Bool Int Bool) Bool)
(declare-dep-exists-fun Bfs () ((Array Bool (Array Int (Array Bool Bool))) Bool Int) Bool)

; --- the handler, verified once for every X ---
; a queued branch answered Success v: that is the answer
(assert (forall ((v Int) (b Bool)) (=> (X true v b) (Bfs X true v))))
; both branches answered Failure and the queue is exhausted: Failure
(assert (forall ((v1 Int) (v2 Int))
  (=> (and (X false v1 true) (X false v2 false)) (Bfs X false 0))))

; --- client 1: `sqrt a` -- both candidates satisfy cand * cand = a * a, so both branches answer
;     Success; the answer is a Success whose value squares to a * a ---
(assert (forall ((a Int) (ok Bool) (v Int))
  (=> (and (Bfs (lambda ((o Bool)) (lambda ((w Int)) (lambda ((b Bool))
              (and o (or (and b (= w a)) (and (not b) (= w (- 0 a))))))))
                ok v)
           (not (and ok (= (* v v) (* a a)))))
      false)))
; --- client 2: a body that never succeeds -- a different instantiation of the same handler;
;     the answer must be Failure (one verification, several clients) ---
(assert (forall ((ok Bool) (v Int))
  (=> (and (Bfs (lambda ((o Bool)) (lambda ((w Int)) (lambda ((b Bool)) (not o)))) ok v) ok)
      false)))
(check-sat)
