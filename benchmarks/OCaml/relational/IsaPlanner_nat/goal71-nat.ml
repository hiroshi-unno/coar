type nat = Z | S of nat
let rec plus m n =
  match m with
  | Z -> n
  | S m' -> S (plus m' n)
let rec minus n m =
  match n with
  | Z -> Z
  | S n' ->
    match m with
    | Z -> n
    | S m' -> minus n' m'
let rec less x y =
  match y with
  | Z -> false
  | S y' ->
    match x with
    | Z -> true
    | S x' -> less x' y'
let leq x y =
  x = y || less x y


type list = Nil | Cons of nat * list

let main m n =
  if leq m n then
    assert(leq m (S n))
  else ()

(*** Assume leq m n = true always holds ***)

(*** Proof by structural induction on m ***)
(*
[Case m = Z]
      leq Z (S n)
   -> Z = (S n) || less Z (S n)
   -> false     || less Z (S n)
   -> false     || true
   -> true

[Assume the claim for m = i and prove it for m = (S i)]
Induction Hypothesis : leq i (S n) = true
Prove : leq (S i) (S n) = true
      leq (S i) (S n)
   -> (S i) = (S n) || less (S i) (S n)
   -> (S i) = (S n) || less i n
   -> ?  ((S i) = (S n) ... leq m i may be assumed, but simple induction or unfolding cannot
                             show this to be true, so it cannot be decided.
          less i n      ... the functions differ, so induction does not apply and it cannot be decided.)
*)


(**** Proof by structural induction on n ***)
(*
[Case n = Z]
      leq m (S Z)
   -> m = (S Z) || less m (S Z)
   -> false     || less m (S Z)
      (case m = Z)
      -> false     || less Z (S Z)
      -> false     || true
      -> true
      (case m = S m')
      -> false     || less (S m') (S Z)
      -> false     || false
      -> false

[Assume the claim for m = i and prove it for m = (S i)]
Induction Hypothesis : leq i (S n) = true
Prove : leq (S i) (S n) = true
      leq m (S (S i))
   -> m = (S (S i)) || less m (S (S i))
   -> ?  (undecidable for the same reason as in the induction on m.)
*)
