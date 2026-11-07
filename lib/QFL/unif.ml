(* The integral binder of QFL: [unif r. F] denotes the Lebesgue integral of
   [F] over [r] in [0, 1], the expected value of [F] for [r] drawn uniformly
   from [0, 1] (an integral against a transition kernel, Kura, Unno and
   Tsukada, "Supermartingales for Unique Fixed Points", PLDI 2026, Appendix F).
   Values are in [0, inf], as everywhere in QFL.

   Representation: [unif r. F] is the application of the function symbol
   [FVar "unif"] to the array lambda [ALambda ((r, real), real) F], so that the
   binding of [r] is the lambda's, and every traversal that already respects an
   array lambda (capture-avoiding substitution, function substitution, free
   variables, the lifting of conditionals) respects the integral too.  [r] is
   renamed apart when the term is built, which is what the type inference of a
   lambda assumes.  ["unif"] is a keyword of the reader, so no function of a
   problem can carry that name.

   Nothing downstream of the bound checker knows the symbol: [integrate]
   replaces every integral by its closed form, and refuses when it cannot
   compute one exactly (the cases are listed at [integrate]). *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

let name = Ident.Tvar "unif"
let lambda_sort = T_array.SArray (T_real.SReal, T_real.SReal)

(* [mk x body] is [unif x. body], with [x] renamed apart from every variable *)
let mk x body =
  let x' =
    Ident.mk_fresh_tvar_avoiding
      ~prefix:("unif_" ^ Ident.name_of_tvar x ^ "_")
      ~taken:(fun v -> Set.mem (Term.tvs_of body) v)
      ()
  in
  let body =
    Term.subst (Map.Poly.singleton x (Term.mk_var x' T_real.SReal)) body
  in
  Term.mk_fvar_app name [ lambda_sort ] T_real.SReal
    [ T_array.mk_lambda (x', T_real.SReal) T_real.SReal body ]

(* [let_unif t] is [Some (r, F)] when [t] is [unif r. F] *)
let let_unif = function
  | Term.FunApp
      ( FVar (Ident.Tvar "unif", _, _),
        [ FunApp (T_array.ALambda ((r, _), _), [ body ], _) ],
        _ ) ->
      Some (r, body)
  | _ -> None

let is_unif t = Option.is_some (let_unif t)

let str_of r body =
  sprintf "unif %s. %s" (Ident.name_of_tvar r) (Term.str_of body)

(** {2 Exact integration} *)

(* A polynomial in the integration variable: coefficient [i] is the
   coefficient of [r^i], a term free of [r]. *)
let padd p q =
  let rec go p q =
    match (p, q) with
    | [], q -> q
    | p, [] -> p
    | a :: p, b :: q -> T_real.mk_radd a b :: go p q
  in
  go p q

let pscale c = List.map ~f:(T_real.mk_rmul c)

let pmul p q =
  List.foldi p ~init:[] ~f:(fun i acc a ->
      padd acc (List.init i ~f:(fun _ -> T_real.rzero ()) @ pscale a q))

(* a piecewise polynomial: a tree of conditionals over polynomials in [r] *)
type pw = Poly of Term.t list | Ite of Formula.t * pw * pw

let rec lift2 f a b =
  match (a, b) with
  | Poly p, Poly q -> Poly (f p q)
  | Ite (c, a1, a2), b -> Ite (c, lift2 f a1 b, lift2 f a2 b)
  | a, Ite (c, b1, b2) -> Ite (c, lift2 f a b1, lift2 f a b2)

let rec lift1 f = function
  | Poly p -> Poly (f p)
  | Ite (c, a, b) -> Ite (c, lift1 f a, lift1 f b)

let mentions r t = Set.mem (Term.tvs_of t) r

let refuse_integrand r body fmt =
  Printf.ksprintf
    (fun why ->
      Common.Refusal.refuse
        "the integral %s is not computed exactly: %s (the bound checker \
         integrates a piecewise polynomial in the integration variable whose \
         pieces are separated by guards linear in it with constant \
         coefficients)"
        (str_of r body) why)
    fmt

(* [to_pw r body t]: [t] as a piecewise polynomial in [r]; refuses when [t] is
   not one (a function applied to a term mentioning [r], a division by such a
   term, ...) *)
let rec to_pw r body t =
  if not (mentions r t) then Poly [ t ]
  else
    match t with
    | Term.Var (x, _, _) when Ident.tvar_equal x r ->
        Poly [ T_real.rzero (); T_real.rone () ]
    | FunApp ((T_real.RAdd | T_num.NAdd _), [ a; b ], _) ->
        lift2 padd (to_pw r body a) (to_pw r body b)
    | FunApp ((T_real.RSub | T_num.NSub _), [ a; b ], _) ->
        lift2 padd (to_pw r body a)
          (lift1 (pscale (T_real.mk_real Q.minus_one)) (to_pw r body b))
    | FunApp ((T_real.RNeg | T_num.NNeg _), [ a ], _) ->
        lift1 (pscale (T_real.mk_real Q.minus_one)) (to_pw r body a)
    | FunApp ((T_real.RMul | T_num.NMul _), [ a; b ], _) ->
        lift2 pmul (to_pw r body a) (to_pw r body b)
    | FunApp (T_real.RDiv, [ a; b ], _) when not (mentions r b) ->
        lift1 (pscale (T_real.mk_rdiv (T_real.rone ()) b)) (to_pw r body a)
    | FunApp (T_bool.IfThenElse, [ c; a; b ], _) ->
        Ite (Formula.of_bool_term c, to_pw r body a, to_pw r body b)
    | FunApp (FVar (Ident.Tvar (("min" | "max") as m), _, _), [ a; b ], _) ->
        (* exact: [min a b] is [if a <= b then a else b] *)
        let c = if String.equal m "min" then Formula.leq a b else Formula.geq a b in
        Ite (c, to_pw r body a, to_pw r body b)
    | _ ->
        refuse_integrand r body "%s is not a polynomial in %s"
          (Term.str_of t) (Ident.name_of_tvar r)

let constant_of t =
  match Evaluator.simplify_term t with
  | t when T_real.is_real t -> Some (T_real.let_real t)
  | t when T_int.is_int t -> Some (Q.of_bigint (T_int.let_int t))
  | _ -> None

(* [linear r body d] is [(alpha, beta)] with [d = alpha + beta * r], [alpha] a
   term free of [r] and [beta] a rational constant; refuses otherwise *)
let linear r body guard d =
  match to_pw r body d with
  | Poly (alpha :: beta :: higher) -> (
      if
        not
          (List.for_all higher ~f:(fun c ->
               Option.exists (constant_of c) ~f:(Q.equal Q.zero)))
      then
        refuse_integrand r body "the guard %s is not linear in %s"
          (Formula.str_of guard) (Ident.name_of_tvar r);
      match constant_of beta with
      | Some beta -> (alpha, beta)
      | None ->
          refuse_integrand r body
            "the coefficient %s of %s in the guard %s is not a constant (a \
             template condition with unknown coefficients evaluated at a \
             point that depends on %s; the bound checker's templates take \
             the body's own guards when a problem has an integral, but a \
             template with conditions of its own, such as the Pareto cache's \
             (pareto_cache = Cache_after), meets this)"
            (Term.str_of beta) (Ident.name_of_tvar r) (Formula.str_of guard)
            (Ident.name_of_tvar r))
  | Poly [ alpha ] -> (alpha, Q.zero)
  | Poly [] -> (T_real.rzero (), Q.zero)
  | Ite _ ->
      refuse_integrand r body "the guard %s has a conditional term in it"
        (Formula.str_of guard)

let rec power t = function
  | 0 -> T_real.rone ()
  | k -> T_real.mk_rmul t (power t (k - 1))

(* [antiderivative p lo hi] is the integral of [p] over [lo, hi] *)
let antiderivative p lo hi =
  List.foldi p ~init:(T_real.rzero ()) ~f:(fun k acc c ->
      let n = k + 1 in
      T_real.mk_radd acc
        (T_real.mk_rmul c
           (T_real.mk_rmul
              (T_real.mk_real Q.(one / of_int n))
              (T_real.mk_rsub (power hi n) (power lo n)))))

(* [integ r body pw lo hi] is the integral of [pw] over [lo, hi], assuming
   [lo <= hi].  A guard free of [r] stays a guard of the result.  A guard
   [alpha + beta * r >= 0] with a constant [beta <> 0] splits the interval at
   [s = -alpha / beta]: below and above [s] each side is one branch, and
   [s] is clamped to [lo, hi] by the three cases [s <= lo], [hi <= s] and
   [lo < s < hi].  Whether the guard is strict, and an equation guard as a
   whole, changes the integrand only at the single point [s], a set of
   measure zero, so neither affects the integral. *)
let rec integ r body pw lo hi =
  match pw with
  | Poly p -> antiderivative p lo hi
  | Ite (c, a, b) when not (Set.mem (Formula.tvs_of c) r) ->
      T_bool.mk_if_then_else (T_bool.of_formula c) (integ r body a lo hi)
        (integ r body b lo hi)
  | Ite (c, a, b) -> (
      match c with
      | Formula.UnaryOp (Formula.Not, c, _) -> integ r body (Ite (c, b, a)) lo hi
      | Formula.BinaryOp (Formula.And, c1, c2, _) ->
          integ r body (Ite (c1, Ite (c2, a, b), b)) lo hi
      | Formula.BinaryOp (Formula.Or, c1, c2, _) ->
          integ r body (Ite (c1, a, Ite (c2, a, b))) lo hi
      | Formula.BinaryOp (Formula.Imply, c1, c2, _) ->
          integ r body (Ite (c1, Ite (c2, a, b), a)) lo hi
      | Formula.Atom (Atom.True _, _) -> integ r body a lo hi
      | Formula.Atom (Atom.False _, _) -> integ r body b lo hi
      | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) -> (
          let shape =
            match psym with
            | T_real.(RGeq | RGt) | T_num.(NGeq _ | NGt _) ->
                `Nonneg (T_real.mk_rsub t1 t2)
            | T_real.(RLeq | RLt) | T_num.(NLeq _ | NLt _) ->
                `Nonneg (T_real.mk_rsub t2 t1)
            | T_bool.Eq -> `Point (T_real.mk_rsub t1 t2)
            | T_bool.Neq -> `Copoint (T_real.mk_rsub t1 t2)
            | _ ->
                refuse_integrand r body "the guard %s is not a comparison"
                  (Formula.str_of c)
          in
          let d = match shape with `Nonneg d | `Point d | `Copoint d -> d in
          let alpha, beta = linear r body c d in
          if Q.equal beta Q.zero then
            (* the guard does not depend on [r] after all *)
            let c' =
              match shape with
              | `Nonneg _ -> Formula.geq alpha (T_real.rzero ())
              | `Point _ -> Formula.eq alpha (T_real.rzero ())
              | `Copoint _ -> Formula.neq alpha (T_real.rzero ())
            in
            integ r body (Ite (c', a, b)) lo hi
          else
            match shape with
            | `Point _ -> integ r body b lo hi
            | `Copoint _ -> integ r body a lo hi
            | `Nonneg _ ->
                (* the breakpoint [-alpha / beta], written as a product with
                   the rational [-1 / beta]: PolyQEnt's reader takes a
                   division only between two numerals, and refused every
                   constraint carrying [(/ (- 2 x) 3)] *)
                let s =
                  T_real.mk_rmul (T_real.mk_real Q.(neg (inv beta))) alpha
                in
                (* [above] holds on [s, inf), [below] on (-inf, s] *)
                let above, below = if Q.(beta > zero) then (a, b) else (b, a) in
                T_bool.mk_if_then_else
                  (T_bool.of_formula @@ Formula.leq s lo)
                  (integ r body above lo hi)
                  (T_bool.mk_if_then_else
                     (T_bool.of_formula @@ Formula.leq hi s)
                     (integ r body below lo hi)
                     (T_real.mk_radd (integ r body below lo s)
                        (integ r body above s hi))))
      | _ ->
          refuse_integrand r body "the guard %s is not a Boolean combination \
                                   of comparisons"
            (Formula.str_of c))

(* [integral r body] is the closed form of [unif r. body], [body] free of
   integrals *)
let integral r body =
  Evaluator.simplify_term
  @@ integ r body (to_pw r body body) (T_real.rzero ()) (T_real.rone ())

(* [integrate t] replaces every integral of [t], innermost first, by its
   closed form.  Exact, and so sound in either direction of a bound, when each
   integrand, once the integrals inside it are replaced, is built from terms
   free of the integration variable [r], [r] itself, [+], [-], [*], division
   by a term free of [r], [min], [max] and conditionals whose guards are
   Boolean combinations of comparisons [e1 op e2] with [e1 - e2] linear in [r]
   with a constant coefficient.  Anything else is refused: in particular an
   unknown function applied to an argument that mentions [r] (an integral is
   integrated only after the unknowns are replaced by templates), and a guard
   whose coefficient of [r] is a template parameter. *)
let integrate =
  Term.map_term true ~f:(fun t ->
      match let_unif t with Some (r, body) -> integral r body | None -> t)

let integrate_formula = Formula.map_term ~f:integrate

(** {2 Detection} *)

let rec term_mentions t =
  match t with
  | Term.Var _ -> false
  | FunApp (_, _, _) when is_unif t -> true
  | FunApp (T_bool.Formula phi, [], _) -> formula_mentions phi
  | FunApp (_, ts, _) -> List.exists ts ~f:term_mentions
  | LetTerm (_, _, t1, t2, _) -> term_mentions t1 || term_mentions t2

and formula_mentions phi =
  let found = ref false in
  ignore
    (Formula.map_term phi ~f:(fun t ->
         if is_unif t then found := true;
         t));
  !found

(* [rewrite_min_max ~unknowns t]: inside every integrand of [t], [min a b] and
   [max a b] become conditionals.  Needed because the bound checker splits a
   [min] or [max] into one constraint per argument, which is sound for a [min]
   at the top of a body and not under an integral (the integral of a minimum
   is at most the minimum of the integrals).  A [min] or [max] under an
   integral whose arguments apply an unknown is refused: its conditional
   compares two unknowns, which no template guard can express. *)
let rewrite_min_max ~unknowns t =
  let applies_unknown t =
    Set.exists (Term.tvs_of t) ~f:(Set.mem unknowns)
    || Set.exists (Term.fvar_apps_of t) ~f:(function
         | Term.FunApp (FVar (f, _, _), _, _) -> Set.mem unknowns f
         | _ -> false)
  in
  let rec under = function
    | Term.FunApp (FVar (Ident.Tvar (("min" | "max") as m), _, _), [ a; b ], _)
      as t ->
        if applies_unknown t then
          Common.Refusal.refuse
            "%s applies an unknown under an integral (unif): the bound \
             checker cannot split it there, since the integral of a %s is \
             not the %s of the integrals"
            (Term.str_of t) m m;
        let a = under a and b = under b in
        T_bool.mk_if_then_else
          (T_bool.of_formula
             (if String.equal m "min" then Formula.leq a b else Formula.geq a b))
          a b
    | Term.FunApp (sym, ts, info) -> Term.mk_fsym_app ~info sym (List.map ts ~f:under)
    | t -> t
  in
  let rec outside t =
    match let_unif t with
    | Some (_, body) -> (
        match t with
        | Term.FunApp (sym, [ FunApp (lam, [ _ ], linfo) ], info) ->
            Term.mk_fsym_app ~info sym
              [ Term.mk_fsym_app ~info:linfo lam [ under body ] ]
        | _ -> t)
    | None -> (
        match t with
        | Term.FunApp (sym, ts, info) ->
            Term.mk_fsym_app ~info sym (List.map ts ~f:outside)
        | t -> t)
  in
  outside t
