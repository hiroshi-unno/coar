(* Solving a constraint over unknown coefficients: the second half of every
   template method, whose first half (a template with coefficient variables,
   its conditions turned into constraints on those variables by [Farkas])
   leaves a quantifier-free formula whose free variables are all unknowns.

   [solve] asks Z3 for an assignment, optionally first under restrictions
   that bias it towards simple answers, and returns an assignment only after
   Z3 has confirmed that the constraint with the assignment substituted is
   valid -- so a wrong model, a model of a restricted question read back
   wrongly, or a default given to an unknown the model left out cannot
   reach the caller.  The restrictions (each tried before the unrestricted
   question, each dropped when it makes the question unsatisfiable or
   undecided):
   - [prefer_zero]: the listed unknowns set to 0 (fewer atoms in the
     answer);
   - [small]: every unknown in [-i, i] for [i] = 1, 2, ... up to the bound,
     stated as bounds or as a disjunction of the values;
   - [Min_abs]: after the unrestricted question is answered, the sum of the
     unknowns' absolute values is lowered by asking for an assignment whose
     sum is at least one smaller, until that is unsatisfiable or undecided.
     Z3's optimiser would state the same objective in one question, but its
     interface here takes no budget and was seen not to return on a
     four-unknown integer system; each question of the descent is an
     ordinary satisfiability question under the caller's budget. If this
     unrestricted descent rules out another unit improvement (by unsat or
     the objective's non-negativity), its integer result has the least sum;
     a real result is within one of the infimum. An undecided step retains
     only a checked feasible assignment, with no optimality guarantee.
     Successful prefer-zero or small searches return before this descent and
     carry no optimality guarantee.
   The restrictions change which assignment is found, never whether one is:
   [No_solution] is said only of the unrestricted question.

   The coefficient solver of the template-based Horn constraint solving of
   Unno and Terauchi, "Inferring simple solutions to recursion-free Horn
   clauses via sampling" (TACAS 2015), whose small-coefficient preference is
   what the restrictions above provide; that paper's GLPK and GSL back ends
   are not here. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type mode = Z3 | Min_abs [@@deriving yojson]

(* How the [small] restriction states [|c| <= i]: as two bounds, or as the
   disjunction [c = -i \/ ... \/ c = i] (integers only; a real unknown always
   takes the bounds). *)
type small_by = Bounds | Values [@@deriving yojson]

type outcome =
  | Solved of (Ident.tvar * Term.t) list
      (** a value for every unknown, checked: the constraint with these values
          substituted is valid *)
  | No_solution  (** Z3 proved the unrestricted constraint unsatisfiable *)
  | Unknown of string  (** no checked assignment, and no proof of none *)

let zero_of sort =
  if Term.is_real_sort sort then T_real.rzero () else T_int.zero ()

let of_int sort i =
  if Term.is_real_sort sort then T_real.mk_real (Q.of_int i)
  else T_int.mk_int (Z.of_int i)

(* [assignment unknowns model]: a value for every unknown, the model's when
   it gives one, else 0 (an unknown the model leaves out is unconstrained by
   it, and the check below decides whether 0 is right).  The model is read
   by name and sort: an entry of the same name at another sort, left in a
   pooled solver context by an earlier query, says nothing about the unknown. *)
let assignment unknowns model =
  List.map unknowns ~f:(fun (v, s) ->
      ( v,
        match model_find model (v, s) with
        | Some t -> snd (remove_dontcare_elem ((v, s), t))
        | None -> zero_of s ))

(* [checked ~id phi sol]: [Some sol] when [phi] with [sol] substituted is
   valid by Z3, [None] otherwise (invalid or undecided). *)
let checked ~timeout ~id phi sol =
  let closed = Formula.subst (Map.Poly.of_alist_exn sol) phi in
  if Z3Smt.Z3interface.is_valid ~timeout ~id (get_fenv ()) closed then Some sol
  else None

(* One question: [`Sat sol] with [sol] checked, [`Unsat], or [`Unknown]. *)
let ask ~timeout ~id unknowns phi =
  match Z3Smt.Z3interface.check_sat ~timeout ~id (get_fenv ()) [ phi ] with
  | `Sat model -> (
      match checked ~timeout ~id phi (assignment unknowns model) with
      | Some sol -> `Sat sol
      | None -> `Unknown "the model failed the validity check")
  | `Unsat -> `Unsat
  | _ -> `Unknown "the solver did not decide"

(* The sum of the absolute values of the unknowns, as a term (real when an
   unknown is real) and as the rational value it takes under [sol]. *)
let abs_sum unknowns =
  let real = List.exists unknowns ~f:(fun (_, s) -> Term.is_real_sort s) in
  let term =
    let parts =
      List.map unknowns ~f:(fun (v, s) ->
          let x = Term.mk_var v s in
          if Term.is_real_sort s then T_real.mk_rabs x
          else if real then T_irb.mk_int_to_real (T_int.mk_abs x)
          else T_int.mk_abs x)
    in
    if real then T_real.mk_rsum (T_real.rzero ()) parts
    else T_int.mk_sum (T_int.zero ()) parts
  in
  let value sol =
    List.fold sol ~init:Q.zero ~f:(fun acc (_, t) ->
        Q.(acc + abs (Value.cast_real_of (Evaluator.eval_term t))))
  in
  (real, term, value)

(* [descend ~timeout ~id unknowns phi sol]: [Min_abs]'s descent from the
   checked assignment [sol]; every assignment it returns was checked. *)
let descend ~timeout ~id unknowns phi sol =
  let real, term, value = abs_sum unknowns in
  let rec go sol =
    let bound = Q.(value sol - one) in
    if Q.lt bound Q.zero then sol
    else
      let limit =
        if real then T_real.mk_real bound else T_int.mk_int (Q.to_bigint bound)
      in
      match
        ask ~timeout ~id unknowns
          (Formula.and_of [ phi; Formula.leq term limit ])
      with
      | `Sat sol' -> go sol'
      | `Unsat | `Unknown _ -> sol
  in
  go sol

(* [solve ?mode ?prefer_zero ?small ?small_by ?timeout ~id unknowns phi].
   Pre: [phi] quantifier-free, its free variables among [unknowns] (integer
   or real); [timeout] in milliseconds, per question.
   Post: [Solved sol] assigns every unknown and [phi[sol]] was checked valid;
   [No_solution] only when the unrestricted question was answered unsat;
   [Unknown] otherwise. *)
let solve ?(mode = Z3) ?(prefer_zero = []) ?(small = 0) ?(small_by = Bounds)
    ?timeout ~id unknowns phi =
  if Formula.is_true phi then
    Solved (List.map unknowns ~f:(fun (v, s) -> (v, zero_of s)))
  else if Formula.is_false phi then No_solution
  else
    let restricted extra =
      match ask ~timeout ~id unknowns (Formula.and_of (phi :: extra)) with
      | `Sat sol -> Some sol
      | `Unsat | `Unknown _ -> None
    in
    let masked () =
      let zs =
        List.filter unknowns ~f:(fun (v, _) ->
            List.mem prefer_zero v ~equal:Ident.tvar_equal)
      in
      if List.is_empty zs then None
      else
        restricted
          (List.map zs ~f:(fun (v, s) ->
               Formula.eq (Term.mk_var v s) (zero_of s)))
    in
    let bounded i =
      restricted
        (List.map unknowns ~f:(fun (v, s) ->
             let x = Term.mk_var v s in
             match small_by with
             | Values when not (Term.is_real_sort s) ->
                 Formula.or_of
                   (List.init
                      ((2 * i) + 1)
                      ~f:(fun k -> Formula.eq x (of_int s (k - i))))
             | Bounds | Values ->
                 Formula.and_of
                   [ Formula.leq (of_int s (-i)) x; Formula.leq x (of_int s i) ]))
    in
    let rec small_first i =
      if i > small then None
      else
        match bounded i with Some sol -> Some sol | None -> small_first (i + 1)
    in
    match masked () with
    | Some sol -> Solved sol
    | None -> (
        match small_first 1 with
        | Some sol -> Solved sol
        | None -> (
            match ask ~timeout ~id unknowns phi with
            | `Sat sol -> (
                match mode with
                | Z3 -> Solved sol
                | Min_abs -> Solved (descend ~timeout ~id unknowns phi sol))
            | `Unsat -> No_solution
            | `Unknown r -> Unknown r))
