; The POPL 2024 ARM benchmark `select-SAT.ml` in its ghost-free form (`select-simpl-noctx-SAT.ml`),
; as QCHC (predicate polymorphism encoded by universally quantified predicates).
;
;   selection_collector ... {
;     Select_int choices -> fun k -> fun selected ->
;       let rec try_choice = function
;         | [] -> Failure
;         | y::ys -> (match (continue k y) (y::selected) with
;                     | Success lst -> Success lst | Failure -> try_choice ys)
;       in try_choice choices }
;   let main x = selection_collector true (fun () ->
;                  let a = perform (Select_int [x; -x]) in a * a = x * x)
;   let test x = main x = Success [x]
;   assert  test : int -> {z: bool | z = true}
;
; This handler both backtracks (angelic choice over `choices`) and threads the accumulator
; `selected`, and its base case *invents* an answer (`Failure`) that the continuation never
; produced -- the answer refinement is genuinely modified, which is what ARM is named after.
; The abstracted predicate is the continuation's success condition: `X(y)` says that running the
; body at the choice `y` succeeds.  The handler is verified once for every `X`; the client
; instantiates it -- here at `true`, since `a * a = x * x` holds for both choices.
;
; Try(X, choices, ok, h): running try_choice on `choices` answers `Success (h :: selected)` when
; `ok`, and `Failure` otherwise; `h` is the choice that succeeded.  RCaml times out on this
; program with *and* without the ghost parameters (600 s, 2026-09-06), so unlike the other three
; ARM programs this one carries no measured comparison -- it is here for coverage of the
; backtracking-with-accumulator shape.  expected: sat
(set-logic DQHORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))

(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun Try () ((Array Int Bool) Lst Bool Int) Bool)

; --- the handler, verified once for every X ---
; try_choice [] = Failure -- the invented answer
(assert (forall ((h Int)) (Try X nil false h)))
; y succeeds: the continuation answers Success, and try_choice returns it with y accumulated
(assert (forall ((y Int) (ys Lst)) (=> (X y) (Try X (cons y ys) true y))))
; y fails: try the rest
(assert (forall ((y Int) (ys Lst) (ok Bool) (h Int))
  (=> (and (not (X y)) (Try X ys ok h)) (Try X (cons y ys) ok h))))

; --- the client: the body `a * a = x * x` succeeds for every choice, so X := (a |-> true);
;     choices = [x; -x], and the answer must be Success [x] ---
(assert (forall ((x Int) (ok Bool) (h Int))
  (=> (and (Try (lambda ((a Int)) true) (cons x (cons (- 0 x) nil)) ok h)
           (not (and ok (= h x))))
      false)))
; --- client 2: a body that succeeds only on positive choices, X := (a |-> a > 0); whichever of
;     [x; -x] is chosen, a successful answer is positive.  The same solution for Try must serve
;     both clients -- one verification, several clients ---
(assert (forall ((x Int) (ok Bool) (h Int))
  (=> (and (Try (lambda ((a Int)) (> a 0)) (cons x (cons (- 0 x) nil)) ok h) ok (<= h 0))
      false)))
(check-sat)
