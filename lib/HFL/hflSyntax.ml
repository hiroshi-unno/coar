(* The abstract syntax of HFL(Z) and of its hierarchical equation systems
   (HES), with lambda-HFL as the internal form.

   lambda-HFL (Kura, arXiv:2301.09997, as reviewed by Kura and Unno, "Automated
   Verification of Higher-Order Probabilistic Programs via a Dependent
   Refinement Type System", ICFP 2024, Section 2.1, Fig. 2) is a simply typed
   lambda-calculus whose function types all end in [Prop], parameterised by a
   set of base types and a set of basic operators.  This module is its Boolean
   instance over integer arithmetic: [Prop] is the two truth values, the
   connectives, the integer comparisons and the quantifiers over [int] are
   basic operators ([forall_int (fun x -> phi)] in lambda-HFL, written as a
   binder [Forall] here because no other operator binds), and a fixed point is
   a recursive equation of the system.  The quantitative instances (the
   expectation modes) share the term language and are represented only as
   OCaml programs (no text syntax of this module covers them).

   What the HES forms of the existing tools add to lambda-HFL, and how it is
   represented:
   - an HES [X1 x1 =a1 phi1; ...; Xn xn =an phin] is a group of mutually
     recursive equations, each with its own fixpoint kind [a_i]; lambda-HFL has
     one unary [fix] whose kind is the model's order, so a group with one kind
     is the simultaneous fixed point of the group (equal to the tools' nesting
     by Bekic's lemma) and a group with two kinds is alternation, which is
     outside one lambda-HFL model and is refused by the solvers;
   - the main formula is the first equation (the tools' convention); the
     integer variables free in it are parameters of that equation, and the
     file is valid when the main equation holds for all of their values
     ([closure] records which parameters came from free variables, so that a
     tool's form is printed back with them free);
   - curried application is lambda-HFL's sugar for uncurried products.

   Invariants of every value built by the readers of this library:
   - formulas are negation-free: there is no negation constructor, and a
     negation in the input is pushed to the atoms on reading (a negated
     predicate-variable application is refused);
   - integer [/] and [%] truncate towards zero (OCaml's [/] and [mod]), the
     rounding the readers choose for every dialect;
   - after [HflTyping.infer] every [Abs] and every equation parameter carries
     its simple type and no type is [TVar]. *)

open Core

(** the fixpoint kind of an equation: greatest ([Nu]) or least ([Mu]) *)
type fix = Nu | Mu [@@deriving equal, compare]

(** simple types: [eta ::= rho | int], [rho ::= Prop | eta -> rho] *)
type sty = TProp | TInt | TArrow of sty * sty
[@@deriving equal, compare]

(** integer operations; [Div] and [Mod] truncate towards zero *)
type aop = Add | Sub | Mul | Div | Mod [@@deriving equal, compare]

(** integer comparisons *)
type pred = Eq | Neq | Le | Ge | Lt | Gt [@@deriving equal, compare]

type t =
  | Var of string  (** an integer variable, a bound variable or an equation *)
  | Int of int
  | Bool of bool  (** [true]/[false] at type [Prop] *)
  | Op of aop * t * t  (** integer arithmetic *)
  | Neg of t  (** integer negation *)
  | Pred of pred * t * t  (** an integer comparison, at type [Prop] *)
  | And of t * t
  | Or of t * t
  | Forall of string * t  (** over [int] *)
  | Exists of string * t  (** over [int] *)
  | Abs of string * sty option * t
      (** [None] only before type inference *)
  | App of t * t
[@@deriving equal, compare]

type eqn = {
  name : string;  (** starts with an upper-case letter *)
  params : (string * sty option) list;
  fix : fix;
  body : t;
}
[@@deriving equal, compare]

(** the dialects whose concrete syntax is read and printed *)
type dialect =
  | Rethfl  (** ReTHFL, github.com/hopv/rethfl *)
  | Hflmc2  (** hflmc2 = PaHFL, github.com/Hogeyama/hflmc2 *)
  | Muhfl  (** MuHFL, github.com/kamocyc/muapprox *)
  | Coar  (** the union of the three, with ASCII spellings *)
[@@deriving equal, compare]

type hes = {
  eqns : eqn list;  (** the first is the main formula *)
  closure : string list;
      (** parameters of the main equation that were free integer variables of
          the main formula in the input *)
  env_ignored : bool;  (** the input had a [%ENV] section, which is ignored *)
}
[@@deriving equal, compare]

let dialect_of_string s =
  match String.lowercase s with
  | "rethfl" -> Some Rethfl
  | "hflmc2" | "pahfl" -> Some Hflmc2
  | "muhfl" | "muapprox" -> Some Muhfl
  | "coar" | "union" -> Some Coar
  | _ -> None

let string_of_dialect = function
  | Rethfl -> "rethfl"
  | Hflmc2 -> "hflmc2"
  | Muhfl -> "muhfl"
  | Coar -> "coar"

let string_of_fix = function Nu -> "nu" | Mu -> "mu"

let rec string_of_sty = function
  | TProp -> "prop"
  | TInt -> "int"
  | TArrow (((TArrow _) as a), b) ->
      "(" ^ string_of_sty a ^ ") -> " ^ string_of_sty b
  | TArrow (a, b) -> string_of_sty a ^ " -> " ^ string_of_sty b

let negate_pred = function
  | Eq -> Neq
  | Neq -> Eq
  | Le -> Gt
  | Gt -> Le
  | Ge -> Lt
  | Lt -> Ge

(** [args_ret_of_sty ty] splits [ty] into its argument types and [TProp] *)
let rec args_of_sty = function
  | TArrow (a, b) -> a :: args_of_sty b
  | TProp | TInt -> []

let rec sty_of_args args ret =
  match args with [] -> ret | a :: rest -> TArrow (a, sty_of_args rest ret)

(** the order of a type: [order(Prop) = order(int) = 0],
    [order(eta -> rho) = max (order(eta) + 1) (order(rho))]; a first-order
    predicate [int -> ... -> Prop] has order 1 *)
let rec order_of_sty = function
  | TProp | TInt -> 0
  | TArrow (a, b) -> Int.max (order_of_sty a + 1) (order_of_sty b)

let sty_of_eqn e =
  sty_of_args
    (List.map e.params ~f:(fun (_, ty) -> Option.value ty ~default:TInt))
    TProp

(** the order of an HES: the largest order of its equations' types *)
let order hes =
  List.fold hes.eqns ~init:0 ~f:(fun acc e ->
      Int.max acc (order_of_sty (sty_of_eqn e)))

let rec has_abs = function
  | Abs _ -> true
  | Var _ | Int _ | Bool _ -> false
  | Neg a | Forall (_, a) | Exists (_, a) -> has_abs a
  | Op (_, a, b) | Pred (_, a, b) | And (a, b) | Or (a, b) | App (a, b) ->
      has_abs a || has_abs b

(** every equation takes only integer arguments and no body contains a
    lambda: the HES is a muCLP *)
let is_order1 hes =
  List.for_all hes.eqns ~f:(fun e ->
      List.for_all e.params ~f:(fun (_, ty) ->
          match ty with Some TInt -> true | _ -> false)
      && not (has_abs e.body))

let fix_kinds hes =
  List.dedup_and_sort ~compare:compare_fix
  @@ List.map hes.eqns ~f:(fun e -> e.fix)

(** an HES with both kinds of equations is alternating (conservatively: two
    groups of different kinds that do not depend on each other count too) *)
let is_alternating hes = List.length (fix_kinds hes) > 1

(** the De Morgan dual: [psi] is valid iff [dual psi] is not valid.  Swaps the
    connectives, the quantifiers, the constants, the comparisons and the
    fixpoint kinds; variables, applications and abstractions are kept, which
    is the dual because predicate variables occur only positively.
    [dual (dual e) = e]. *)
let rec dual = function
  | (Var _ | Int _ | Op _ | Neg _) as t -> t
  | Bool b -> Bool (not b)
  | Pred (p, a, b) -> Pred (negate_pred p, a, b)
  | And (a, b) -> Or (dual a, dual b)
  | Or (a, b) -> And (dual a, dual b)
  | Forall (x, a) -> Exists (x, dual a)
  | Exists (x, a) -> Forall (x, dual a)
  | Abs (x, ty, a) -> Abs (x, ty, dual a)
  | App (a, b) -> App (dual a, dual_arg b)

(* An argument of integer sort is not a formula and is kept as it is; a
   formula argument is dualised.  Syntactically the two are told apart by
   their head: arithmetic is built from [Int], [Op], [Neg] and variables, and a
   variable argument is kept either way. *)
and dual_arg = function
  | (Var _ | Int _ | Op _ | Neg _) as t -> t
  | t -> dual t

let dual_fix = function Nu -> Mu | Mu -> Nu

let dual_hes hes =
  {
    hes with
    eqns =
      List.map hes.eqns ~f:(fun e ->
          { e with fix = dual_fix e.fix; body = dual e.body });
  }

(** [Exists] occurs in a body of kind [Nu], or [Forall] in a body of kind [Mu]:
    the quantifier that is not Scott-continuous in that kind's order
    (over an infinite domain), for which no sound typing rule is known *)
let discontinuous_quantifier hes =
  let rec has_exists = function
    | Exists _ -> true
    | Var _ | Int _ | Bool _ -> false
    | Neg a | Forall (_, a) | Abs (_, _, a) -> has_exists a
    | Op (_, a, b) | Pred (_, a, b) | And (a, b) | Or (a, b) | App (a, b) ->
        has_exists a || has_exists b
  in
  let rec has_forall = function
    | Forall _ -> true
    | Var _ | Int _ | Bool _ -> false
    | Neg a | Exists (_, a) | Abs (_, _, a) -> has_forall a
    | Op (_, a, b) | Pred (_, a, b) | And (a, b) | Or (a, b) | App (a, b) ->
        has_forall a || has_forall b
  in
  List.find_map hes.eqns ~f:(fun e ->
      match e.fix with
      | Nu when has_exists e.body -> Some (e.name, "exists", Nu)
      | Mu when has_forall e.body -> Some (e.name, "forall", Mu)
      | _ -> None)

let rec free_vars bound = function
  | Var x -> if Set.mem bound x then [] else [ x ]
  | Int _ | Bool _ -> []
  | Neg a -> free_vars bound a
  | Op (_, a, b) | Pred (_, a, b) | And (a, b) | Or (a, b) | App (a, b) ->
      free_vars bound a @ free_vars bound b
  | Forall (x, a) | Exists (x, a) | Abs (x, _, a) ->
      free_vars (Set.add bound x) a

(** [beta t] is the beta-normal form of [t] (the calculus is simply typed, so
    it exists); substitution renames a binder that would capture *)
let rec beta t =
  match t with
  | Var _ | Int _ | Bool _ -> t
  | Neg a -> Neg (beta a)
  | Op (o, a, b) -> Op (o, beta a, beta b)
  | Pred (p, a, b) -> Pred (p, beta a, beta b)
  | And (a, b) -> And (beta a, beta b)
  | Or (a, b) -> Or (beta a, beta b)
  | Forall (x, a) -> Forall (x, beta a)
  | Exists (x, a) -> Exists (x, beta a)
  | Abs (x, ty, a) -> Abs (x, ty, beta a)
  | App (a, b) -> (
      match beta a with
      | Abs (x, _, body) -> beta (subst x (beta b) body)
      | a' -> App (a', beta b))

and subst x s t =
  let fvs = lazy (String.Set.of_list (free_vars String.Set.empty s)) in
  let rec go t =
    match t with
    | Var y -> if String.equal x y then s else t
    | Int _ | Bool _ -> t
    | Neg a -> Neg (go a)
    | Op (o, a, b) -> Op (o, go a, go b)
    | Pred (p, a, b) -> Pred (p, go a, go b)
    | And (a, b) -> And (go a, go b)
    | Or (a, b) -> Or (go a, go b)
    | App (a, b) -> App (go a, go b)
    | Forall (y, a) -> binder (fun y a -> Forall (y, a)) y a
    | Exists (y, a) -> binder (fun y a -> Exists (y, a)) y a
    | Abs (y, ty, a) -> binder (fun y a -> Abs (y, ty, a)) y a
  and binder mk y a =
    if String.equal x y then mk y a
    else if Set.mem (Lazy.force fvs) y then
      let y' = fresh_name y in
      mk y' (go (subst y (Var y') a))
    else mk y (go a)
  in
  go t

and fresh_name =
  let cnt = ref 0 in
  fun base ->
    incr cnt;
    sprintf "%s_%d" base !cnt

(** [apps h args] is [h a1 ... an]; [unapps t] is its inverse *)
let apps h args = List.fold args ~init:h ~f:(fun f a -> App (f, a))

let rec unapps = function
  | App (f, a) ->
      let h, args = unapps f in
      (h, args @ [ a ])
  | t -> (t, [])

(** alpha-equivalence of two HES: equal after renaming every bound variable
    (equation parameters, lambda and quantifier binders) to a canonical name
    in binding order; equation names and free variables are compared as
    they are *)
let alpha_normalize hes =
  let cnt = ref 0 in
  let fresh () =
    incr cnt;
    sprintf "_a%d" !cnt
  in
  let rec go env = function
    | Var x -> Var (Option.value (Map.find env x) ~default:x)
    | (Int _ | Bool _) as t -> t
    | Neg a -> Neg (go env a)
    | Op (o, a, b) -> Op (o, go env a, go env b)
    | Pred (p, a, b) -> Pred (p, go env a, go env b)
    | And (a, b) -> And (go env a, go env b)
    | Or (a, b) -> Or (go env a, go env b)
    | App (a, b) -> App (go env a, go env b)
    | Forall (x, a) ->
        let y = fresh () in
        Forall (y, go (Map.set env ~key:x ~data:y) a)
    | Exists (x, a) ->
        let y = fresh () in
        Exists (y, go (Map.set env ~key:x ~data:y) a)
    | Abs (x, ty, a) ->
        let y = fresh () in
        Abs (y, ty, go (Map.set env ~key:x ~data:y) a)
  in
  let main_closure = ref [] in
  let eqns =
    List.mapi hes.eqns ~f:(fun i e ->
        let env, params =
          List.fold_map e.params ~init:String.Map.empty ~f:(fun env (x, ty) ->
              let y = fresh () in
              if i = 0 && List.mem hes.closure x ~equal:String.equal then
                main_closure := y :: !main_closure;
              (Map.set env ~key:x ~data:y, (y, ty)))
        in
        { e with params; body = go env e.body })
  in
  { hes with eqns; closure = List.rev !main_closure }

let alpha_equal h1 h2 =
  equal_hes
    { (alpha_normalize h1) with env_ignored = false }
    { (alpha_normalize h2) with env_ignored = false }
