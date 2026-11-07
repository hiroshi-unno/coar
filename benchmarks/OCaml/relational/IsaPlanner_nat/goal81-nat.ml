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


let main m n k =
  assert(minus (minus (S m) n) (S k) = minus (minus m n) k)

(* Proof by structural induction
[Case m = Z]
  LHS = minus (minus (S Z) n) (S k)
    (case n = Z)
      -> minus (minus (S Z) Z) (S k)
      -> minus Z (S k)
      -> Z
    (case n = S n')
      -> minus (minus (S Z) (S n')) (S k)
      -> minus Z (S k))
      -> Z

  RHS = minus (minus Z n) k)
      -> minus Z k
      -> Z

[Assume the claim for m = i and prove it for m = (S i)]
Γ =   [(minus (minus (S i) n) (S k)     = minus (minus i n) k)]
Prove : minus (minus (S (S i)) n) (S k) = minus (minus (S i) n) k

(case n = Z)
  LHS = minus (minus (S (S i)) Z) (S k)
      -> minus (S (S i)) (S k)
      -> minus (S i) k
  RHS = minus (minus (S i) Z) k
      -> minus (S i) k

(case n = S n')
  LHS = minus (minus (S (S i)) (S n')) (S k)
      -> minus (minus (S i) n') (S k)
      -> minus (minus i n') k   (<- Applied)
  RHS = minus (minus (S i) (S n')) k
      -> minus (minus i n') k
*)
