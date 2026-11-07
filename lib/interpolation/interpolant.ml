(* Binary interpolation over the theories the tree's solvers handle: given
   [phi1] and [phi2] with [phi1 => phi2] valid (equivalently [phi1 /\ not
   phi2] unsatisfiable), a formula [I] over the shared arguments [args] with
   [phi1 => I] and [I => phi2] valid.

   An interpolant is asked of an ordered list of leaf procedures, each tried
   in turn; a leaf that declines passes the query to the next, and a leaf
   that answers -- with an interpolant, or with the fact that none exists --
   ends the list.  The leaves:

   - [Spacer_chc]: the query as the two Horn clauses [phi1 => I(args)] and
     [I(args) => phi2] over one unknown [I], handed to a CHC solver the caller
     supplies; a solution is an interpolant once Z3 has confirmed it (a
     solution failing the check declines), [unsat] means none exists, and
     an unknown or a timeout declines.  The solver is an argument, so this
     library depends on no particular CHC engine.
   - [Qe_weakest]: [forall v. phi2], [v] the variables only [phi2] mentions,
     with the quantifier eliminated -- the weakest interpolant over the shared
     vocabulary.
   - [Qe_strongest]: [exists v. phi1], [v] the variables only [phi1]
     mentions, eliminated -- the strongest.
   - [Farkas_lra]: [phi1] and [not phi2] in disjunctive normal form over
     linear comparisons; for every pair of a cube [A_i] of the first and
     [B_j] of the second, one Motzkin certificate that [A_i /\ B_j] has no
     rational solution, and its [A_i] part as the interpolant [I_ij]
     (McMillan, "An interpolating theorem prover", TCS 345(1), 2005); the
     answer is [OR_i AND_j I_ij].  Sound over integer columns too (a
     rational certificate refutes the integer points as well), and declines
     when some pair has a rational solution.
   - [Farkas_lia]: [Farkas_lra] over integer columns only, each row first
     rounded to an equivalent row over the integers (a strict row made
     non-strict, the coefficients divided by their gcd and the bound rounded
     down).  It declines when a pair is still rationally feasible after the
     rounding: an integer-only infeasibility such as [z = 2 x] against
     [z = 2 y + 1] has no linear interpolant at all (every interpolant is
     "z is even"), and answering it needs divisibility atoms and an integer
     proof system (cutting planes), which this leaf does not have.
     Both Farkas leaves first rewrite [phi1] and [phi2] into an equivalent
     Boolean skeleton ([skeleton]): every [ite] term is case-split into the
     propositional structure, so each cube fixes the conditions it took,
     and Boolean variables stay as literals of the cubes.  A pair of cubes
     with complementary literals on a shared Boolean variable is answered by
     that literal; any other pair by the certificate of its rows, since
     after the rewriting no Boolean variable occurs inside a comparison.
     They decline on a quantifier or [let], a non-linear atom, an atom of
     another theory, a mixture of integer and real columns, a skeleton
     larger than a fixed number of atom occurrences or more cube pairs than
     a fixed number (shape bounds, never a clock), and a conflict found only
     on a Boolean variable outside the shared arguments; and their answer is
     checked by Z3 ([phi1 => I] and [I => phi2] valid) before it is
     returned, since the affine reading of an atom is by evaluation and a
     certificate is checked against the rows, not against the formulas.

   - [Mbp_cover n]: an enumeration of model-based projections ([MbpProject])
     of [phi1] onto [args]: each round takes a model of [phi1] outside the
     cubes found so far, projects [phi1] at it, weakens the cube by dropping
     each literal whose removal keeps it inconsistent with [not phi2], and adds
     it, until [phi1] is covered; the disjunction is then checked to imply
     [phi2], since [phi2] may share with [phi1] a variable outside [args].  It
     declines when more than [n] cubes are needed, a cube keeps a variable
     outside [args], a satisfiability check is undecided or the final check
     fails; it never answers that no interpolant exists.  The projection is
     the caller's [project] when given (MuCyc passes its configured one), else
     [MbpProject.get_mbp_with] with the choices MuCyc's configuration ships
     ([All_paths], [Inline_lets], unchecked); on word-level circuits whose
     transition shares subterms through let-bindings the inlining one can
     make every round too slow for the leaf to answer.  Unlike [Spacer_chc] it never asks the CHC
     solver to generalise over [phi1] as a whole, which on a word-level
     circuit can spend the whole budget blocking one cube.

   - [Bitwuzla_bv o]: the query asked of an external Bitwuzla ([./bitwuzla]
     in the working directory) through its [get-interpolant] command, which
     reads a Craig interpolant off the resolution proof of the bit-blasted
     problem.  Only for queries whose arguments and variables are all
     bit-vectors or Booleans; it declines on any other sort, when the
     executable is absent, when it answers nothing usable (timeout, an
     interpolant larger than [o.max_size] bytes, one outside [args]), and
     when Z3 does not confirm [phi1 => I] and [I => phi2]: the answer is read
     back through the SMT-LIB reader, so the check guards the round trip as
     well as the solver.  It answers that no interpolant exists when Bitwuzla
     finds [phi1 /\ not phi2] satisfiable.

   An answer can then be passed through post-processing steps, in order;
   each returns an interpolant of the same query whenever it is given one:

   - [Word_regroup o]: an interpolant obtained through bit-blasting may keep,
     in one clause, a group of literals on single bits of one register (e.g.
     [v[30:0] <> 0] spelled as 31 one-bit disjuncts) where a relation between
     two registers of the same sort separates the same two sides.  Each such
     group is replaced by nothing or by an equality or disequality of two
     arguments when the replacement is still implied by [phi1] and still
     implies [phi2] together with the other clauses (see [word_regroup]).

   A projection leaf declines when a quantifier survives elimination (as on
   bit-vectors), since returning that formula as an interpolant would be
   unsound: it mentions no variable outside the vocabulary but is not
   quantifier-free, which a caller substituting it into a clause does not
   expect. *)

open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open Linarith

(* How [Bitwuzla_bv] asks.  [timeout] is in seconds; [max_size] bounds the
   printed interpolant in bytes; [subst], [pudlak], [lift] and [simp] are
   Bitwuzla's own interpolation options (see [Bitwuzla.Interpolant]), each
   given its usual value by default. *)
type bitwuzla_options = {
  timeout : int option; [@default None]
  max_size : int option; [@default None]
  subst : bool; [@default false]
  pudlak : bool; [@default false]
  lift : bool; [@default true]
  simp : bool; [@default true]
}
[@@deriving yojson]

(* How [Word_regroup] asks.  At most [max_queries] satisfiability queries
   per interpolant, each with a budget of [timeout] milliseconds. *)
type regroup_options = { max_queries : int; timeout : int }
[@@deriving yojson]

type post = Word_regroup of regroup_options [@@deriving yojson]

type leaf =
  | Spacer_chc
  | Qe_strongest
  | Qe_weakest
  | Farkas_lra
  | Farkas_lia
  | Mbp_cover of int
  | Bitwuzla_bv of bitwuzla_options
[@@deriving yojson]

(* How the blocking loop weakens the numerals of a cube's inequalities.
   [Weaken_numerals] replaces the numeral of each integer or real inequality
   by a weaker one among the numerals of the query and their negations while
   the query's left side still excludes the result, as Spacer's bound
   expansion does; with the loop's [sum_bounds], a pair of bounds whose sum
   alone is not excluded is also tried as the sum next to one of the two, so
   that a constant read off one model can then be expanded away.  The weakest
   excluded numeral is found by bisection over the candidates, about log2 of
   their number in checks.  Its [strict] also tries the strict form of each
   real inequality: after [t + c' >= 0] fails, [t + c' > 0], which lies
   between it and the next numeral, so a literal made non-strict earlier (by
   summing) can still reach a strict bound such as [t + 1 > 0], which no
   numeral reaches non-strictly over the reals.  Integer bounds are left
   alone ([t + c' > 0] is [t + c' - 1 >= 0] there); [strict] doubles the
   candidates, so one more bisection step per literal. *)
type bound_expansion =
  | Keep_numerals
  | Weaken_numerals of { strict : bool [@default false] }
[@@deriving yojson]

(* The payload of [Spacer_blocking]: the blocking loop learns at most
   [max_rounds] lemmas in one call; the other fields choose how a cube is
   generalised and when the loop is tried. *)
type blocking = {
  max_rounds : int; [@default 100]
  (* in the loop, after dropping literals from a cube, replace two
     of its integer or real bounds by their sum while the query's left side
     still excludes the result, so that numerals read off one model cancel
     (two bounds [x <= k] and [k - 3 <= y] give [x <= y + 3] for any [k]).
     Each accepted step costs one check per pair tried; [false] keeps the
     cube as dropped *)
  sum_bounds : bool; [@default false]
  (* in the loop, after the summing step, whether to replace the numeral
     of each integer or real inequality of a cube by a weaker one
     ([Weaken_numerals]) or to keep the cube as summed ([Keep_numerals]) *)
  expand_bounds : bound_expansion; [@default Keep_numerals]
  (* the loop's entry test: [true] does not count an integer
     division or remainder by a non-zero integer literal as a term whose value
     a model of the theory leaves open (its value is fixed by the dividend's
     in every standard model); [false] counts every integer division and
     remainder, so a query mentioning one goes to the leaves *)
  rem_numeral : bool; [@default false]
  (* [true] adds to the loop's lemmas from the start the bounds that [phi1]
     implies among those a top-level conjunct of one of its top-level
     disjuncts states over arguments only: a bound on one argument (an
     equality giving both of its bounds), so an interpolant may keep a bound
     of [phi1] over an argument no literal of [phi2] mentions, as Spacer's
     Farkas interpolants do, and a relation over several arguments (an
     equality between arguments giving its two halves), which Spacer's
     interpolants also keep from [phi1].  It then drops from the
     interpolant each of those it does not need to imply [phi2], recognising
     one also when it normalises to the given form (the loop may return
     [-x >= 0] as [0 <= -x]).  The checks of those bounds and of the
     dropping share one domain-local Z3 context per step ([phi1], resp. the
     negated [phi2], asserted once and each question in a scope; Z3 may
     then answer differently, never unsoundly), and with several disjuncts
     the bounds are checked a round at a time (one check whether [phi1]
     holds with the negation of one of the bounds still unrefuted, every
     bound false in the model dropped).  [true] also lets the loop answer
     a cube true in a model of an earlier satisfiable cube check of the
     call as satisfiable without asking Z3.  [false] builds the lemmas from
     the cubes of [~phi2] only *)
  phi1_bounds : bool; [@default false]
}
[@@deriving yojson]

(* How one binary query is searched for an interpolant.  [Leaves]: the leaves
   in order.  [Spacer_blocking b]: Spacer's blocking loop with plain unsat
   cores ([SpacerBlocking.interpolate]) first; it declines a query with a
   function-sorted variable or a term whose value the theory leaves open, and
   one the loop does not finish, and a declined query goes to the leaves. *)
type search = Leaves | Spacer_blocking of blocking [@@deriving yojson]

(* What one query of the leaf list comes back with.  [Interpolant i]: [i] is
   the answer of the first leaf that gave one.  [No_interpolant]: a leaf
   proved that none exists (the CHC solver answered [unsat]).  [Declined]:
   every leaf declined. *)
type outcome = Interpolant of Formula.t | No_interpolant | Declined

let is_projection = function
  | Spacer_chc | Farkas_lra | Farkas_lia | Mbp_cover _ | Bitwuzla_bv _ -> false
  | Qe_strongest | Qe_weakest -> true

(* A short name of [leaf] for traces and timing lines. *)
let leaf_name = function
  | Spacer_chc -> "spacer_chc"
  | Qe_strongest -> "qe_strongest"
  | Qe_weakest -> "qe_weakest"
  | Farkas_lra -> "farkas_lra"
  | Farkas_lia -> "farkas_lia"
  | Mbp_cover n -> Printf.sprintf "mbp_cover_%d" n
  | Bitwuzla_bv _ -> "bitwuzla_bv"

(* The projection leaves.  [qelim] is the caller's quantifier elimination;
   its result is simplified here and accepted only when it is
   quantifier-free and mentions only the requested arguments. *)
let projection ~qelim ~strongest args phi1 phi2 =
  let quantified =
    if strongest then
      let env =
        Set.diff (Formula.term_sort_env_of phi1) (Formula.term_sort_env_of phi2)
      in
      Formula.mk_exists_if_bounded (Set.to_list env) phi1
    else
      let env =
        Set.diff (Formula.term_sort_env_of phi2) (Formula.term_sort_env_of phi1)
      in
      Formula.mk_forall_if_bounded (Set.to_list env) phi2
  in
  let res = Evaluator.simplify @@ qelim quantified in
  if
    Formula.is_quantifier_free res
    && Set.is_subset (Formula.term_sort_env_of res) ~of_:(Set.Poly.of_list args)
  then Interpolant res
  else Declined

(* The CHC leaf.  [solve_chc ~bpvs chcs] is the caller's CHC solver.  An
   answer other than a solution, [unsat], unknown or a timeout is the solver
   failing rather than answering, and is raised.
   Post: [Interpolant i] has its free variables among [args], and Z3 has
   proved [phi1 => i] and [i => phi2] valid; a solution failing either is
   declined.  The solver's word is not taken for it: Z3's Spacer can answer
   a definition holding a free constant of its own (e.g. [aux!3_0] when a
   side has a non-linear product, [y = x * x] against [y < 0]), which the
   answer reader closes universally into a formula that is no solution
   ([forall aux. y - aux * aux > -1], false for every [y]); handed on as an
   interpolant it was stronger than [phi1] and hid reachable states.  A
   quantified solution (Spacer's answers over arrays) is accepted when Z3
   proves it within [quantified_check_ms], since a quantified validity
   question can fail to return; a quantifier-free one is checked unbounded,
   like the Farkas leaves' answers. *)
let quantified_check_ms = 5000

let spacer_chc ~solve_chc args phi1 phi2 =
  let taken =
    Set.Poly.union_list
      [
        Formula.names_spelled_in phi1;
        Formula.names_spelled_in phi2;
        Set.Poly.of_list (List.map args ~f:fst);
        Map.key_set (get_fenv ());
      ]
  in
  let rec choose index =
    let name =
      if index = 0 then "interp" else "interp_" ^ Int.to_string index
    in
    if Set.mem taken (Ident.Tvar name) then choose (index + 1) else name
  in
  let name = choose 0 in
  let pvapp = Formula.mk_atom @@ Atom.pvar_app_of_senv (Ident.Pvar name) args in
  let chcs =
    let params =
      PCSP.Params.make
      @@ Map.Poly.singleton (Ident.Tvar name)
      @@ Logic.Sort.mk_fun
      @@ List.map args ~f:(snd >> Logic.ExtTerm.of_old_sort)
      @ [ Logic.BoolTerm.SBool ]
    in
    let senv = Map.Poly.of_alist_exn args in
    let senv1 =
      Map.force_merge senv @@ Map.of_set_exn @@ Formula.term_sort_env_of phi1
    in
    let senv2 =
      Map.force_merge senv @@ Map.of_set_exn @@ Formula.term_sort_env_of phi2
    in
    PCSP.Problem.of_old_formulas ~params
    @@ Set.Poly.of_list
         [
           (senv1, Formula.mk_imply phi1 pvapp);
           (senv2, Formula.mk_imply pvapp phi2);
         ]
  in
  let bpvs = Set.Poly.singleton (Ident.Tvar name) in
  match solve_chc ~bpvs chcs with
  | Result.Ok (PCSP.Problem.Sat sol, _) ->
      let psub = Map.of_set_exn @@ snd @@ CandSolOld.of_subst sol in
      let interp = Evaluator.simplify @@ Formula.subst_preds psub pvapp in
      let timeout =
        if Formula.is_quantifier_free interp then None
        else Some quantified_check_ms
      in
      let valid phi =
        Z3Smt.Z3interface.is_valid ~timeout ~id:None (get_fenv ()) phi
      in
      let checked =
        try
          Set.is_subset
            (Formula.term_sort_env_of interp)
            ~of_:(Set.Poly.of_list args)
          && valid (Formula.mk_imply phi1 interp)
          && valid (Formula.mk_imply interp phi2)
        with exn_ when not (Common.Timer.is_async exn_) -> false
      in
      if checked then Interpolant interp else Declined
  | Result.Ok (PCSP.Problem.Unsat _, _) -> No_interpolant
  (* a timeout is an unknown: no interpolant came back, so the next leaf is
     asked *)
  | Result.Ok ((PCSP.Problem.Unknown | PCSP.Problem.Timeout), _) -> Declined
  (* phi1 and phi2 should be quantifier-free *)
  | Result.Ok (sol, _) ->
      failwith
      @@ sprintf "[FrameSearch.interpolate] unexpected answer: %s"
           (PCSP.Problem.str_of_solution sol)
  | Result.Error err -> Or_error.ok_exn (Result.Error err)

(* [literal_dnf ~pos phi]: [phi] (when [pos]) or its negation as a list of
   cubes, each a list of comparison atoms ([<=], [<], [>=], [>], [=]);
   [None] when [phi] has a connective other than not, and, or and
   implication, or an atom other than [true], [false] and a binary
   comparison.  A negated or positive disequality becomes the two cubes
   [t1 < t2] and [t1 > t2].
   Post: the disjunction of the cubes' conjunctions is equivalent to [phi]
   (to [not phi] when [not pos]).  Exponential in the alternation of and and
   or; the leaves that call it are asked binary queries of clause size. *)
let rec literal_dnf ~pos phi =
  let open Formula in
  let product c1 c2 =
    List.concat_map c1 ~f:(fun l1 -> List.map c2 ~f:(fun l2 -> l1 @ l2))
  in
  let both f phi1 phi2 =
    match (literal_dnf ~pos phi1, literal_dnf ~pos phi2) with
    | Some c1, Some c2 -> Some (f c1 c2)
    | _ -> None
  in
  match phi with
  | _ when Formula.is_true phi -> Some (if pos then [ [] ] else [])
  | _ when Formula.is_false phi -> Some (if pos then [] else [ [] ])
  | Atom (Atom.App (Predicate.Psym sym, [ t1; t2 ], _), _) ->
      let eq_ = Stdlib.( = ) sym T_bool.Eq
      and neq = Stdlib.( = ) sym T_bool.Neq in
      if (eq_ && not pos) || (neq && pos) then
        Some [ [ lt t1 t2 ]; [ gt t1 t2 ] ]
      else if eq_ || neq then Some [ [ eq t1 t2 ] ]
      else if pos then Some [ [ phi ] ]
      else Some [ [ Formula.negate phi ] ]
  | UnaryOp (Not, phi1, _) -> literal_dnf ~pos:(not pos) phi1
  | BinaryOp (And, phi1, phi2, _) ->
      both (if pos then product else ( @ )) phi1 phi2
  | BinaryOp (Or, phi1, phi2, _) ->
      both (if pos then ( @ ) else product) phi1 phi2
  | BinaryOp (Imply, phi1, phi2, _) ->
      literal_dnf ~pos (mk_or (mk_neg phi1) phi2)
  | _ -> None

(* [affine_formula zs (coeffs, bound, strict)]: [coeffs . z <= bound] (or
   [<]) as a formula over the columns [zs], scaled to integer entries by a
   positive factor; a comparison with no non-zero coefficient is folded to
   [true] or [false].  All columns are of [sort] (integer or real). *)
let affine_formula ~sort zs (coeffs, bound, strict) =
  let l =
    List.fold (bound :: coeffs) ~init:Z.one ~f:(fun l q -> Z.lcm l (Q.den q))
  in
  let int_of q = Q.num Q.(q * of_bigint l) in
  let ks = List.map coeffs ~f:int_of and b = int_of bound in
  let num =
    if Term.is_real_sort sort then Farkas.Num.real_num else Farkas.Num.int_num
  in
  let terms =
    List.filter_map (List.zip_exn ks zs) ~f:(fun (k, (v, s)) ->
        if Z.equal k Z.zero then None else Some (num.mul k (Term.mk_var v s)))
  in
  if List.is_empty terms then
    if if strict then Z.lt Z.zero b else Z.leq Z.zero b then Formula.mk_true ()
    else Formula.mk_false ()
  else (if strict then Formula.lt else Formula.leq) (num.sum terms) (num.of_z b)

(* The Boolean skeleton of a quantifier-free formula, which lets the Farkas
   leaves take [ite] terms and Boolean variables.

   [skeleton ~unnegated ~max_atoms phi]: a formula equivalent to [phi] whose
   atoms are only [true], [false], a Boolean variable read as an atom
   ([b = true]), and applications of a built-in predicate symbol to terms
   containing no [ite]; obtained by
   - the case split of an [ite] term inside such an application:
       A[ite(c, t, e)]  <=>  (c /\ A[t]) \/ (not c /\ A[e]),
     leftmost-outermost first, [c] itself put in skeleton form;
   - an equation or disequation between Boolean terms as the equivalence
     (or its negation) of their formulas, an embedded formula as itself, a
     Boolean [ite] as its two guarded cases;
   - implication, equivalence and exclusive or as and, or and not.
   [None] when [phi] has a binder, a [let], a predicate variable, a term
   [let], or when the result would hold more than [max_atoms] atom
   occurrences.  That bound is the shape test that keeps the case split
   finite in practice: each split doubles the application it splits, so an
   application with [k] [ite] subterms becomes up to [2^k] copies; the count
   is taken as the result is built, never against a clock.
   [unnegated] (a test's mutant only) guards the else-branch of every case
   split by [c] instead of [not c].
   Post (without [unnegated]): [Some psi] is equivalent to [phi] under
   every assignment (each rewrite is a propositional equivalence or the case
   split), and [fv psi] is a subset of [fv phi]; no Boolean variable occurs
   in [psi] inside a comparison, so Boolean and numeric variables meet only
   through the propositional structure. *)
let skeleton ?(unnegated = false) ~max_atoms phi =
  let exception Outside in
  let count = ref 0 in
  let emit phi =
    incr count;
    if !count > max_atoms then raise Outside else phi
  in
  let case c a b =
    Formula.mk_or (Formula.mk_and c a)
      (Formula.mk_and (if unnegated then c else Formula.mk_neg c) b)
  in
  (* the leftmost-outermost [ite] among [ts], with [ts] rebuilt with its
     then- and its else-branch in its place; embedded formulas are not
     entered (an [ite] there is the formula's own, met when it is read as a
     condition) *)
  let rec lift_list :
      'a. (Term.t list -> 'a) -> Term.t list -> (Term.t * 'a * 'a) option =
   fun rebuild ts ->
    let rec go pre = function
      | [] -> None
      | t :: rest -> (
          match lift t with
          | Some (c, a, b) ->
              Some
                ( c,
                  rebuild (List.rev_append pre (a :: rest)),
                  rebuild (List.rev_append pre (b :: rest)) )
          | None -> go (t :: pre) rest)
    in
    go [] ts
  and lift t =
    match t with
    | Term.Var _ -> None
    | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) -> Some (c, a, b)
    | Term.FunApp (T_bool.Formula _, _, _) -> None
    | Term.FunApp (sym, ts, info) ->
        lift_list (fun ts -> Term.mk_fsym_app ~info sym ts) ts
    | Term.LetTerm _ -> raise Outside
  in
  let rec formula phi =
    match phi with
    | Formula.Atom (atom, _) -> atom_ atom
    | Formula.UnaryOp (Not, p, _) -> Formula.mk_neg (formula p)
    | Formula.BinaryOp (And, p, q, _) -> Formula.mk_and (formula p) (formula q)
    | Formula.BinaryOp (Or, p, q, _) -> Formula.mk_or (formula p) (formula q)
    | Formula.BinaryOp (Imply, p, q, _) ->
        Formula.mk_or (Formula.mk_neg (formula p)) (formula q)
    | Formula.BinaryOp (Iff, p, q, _) -> iff (formula p) (formula q)
    | Formula.BinaryOp (Xor, p, q, _) ->
        Formula.mk_neg (iff (formula p) (formula q))
    | Formula.Bind _ | Formula.LetRec _ | Formula.LetFormula _ -> raise Outside
  and iff p q =
    Formula.mk_or (Formula.mk_and p q)
      (Formula.mk_and (Formula.mk_neg p) (Formula.mk_neg q))
  and bool_term t =
    match t with
    | Term.Var (b, s, _) when Term.is_bool_sort s ->
        emit (Formula.of_bool_var b)
    | Term.FunApp (T_bool.Formula p, [], _) -> formula p
    | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) ->
        case (bool_term c) (bool_term a) (bool_term b)
    | _ -> raise Outside
  and atom_ atom =
    match atom with
    | Atom.True _ | Atom.False _ -> Formula.mk_atom atom
    | Atom.App (Predicate.Psym sym, [ t1; t2 ], _)
      when (Stdlib.( = ) sym T_bool.Eq || Stdlib.( = ) sym T_bool.Neq)
           && Term.is_bool_sort (Term.sort_of t1) ->
        let eqv =
          if T_bool.is_true t2 then bool_term t1
          else if T_bool.is_false t2 then Formula.mk_neg (bool_term t1)
          else if T_bool.is_true t1 then bool_term t2
          else if T_bool.is_false t1 then Formula.mk_neg (bool_term t2)
          else iff (bool_term t1) (bool_term t2)
        in
        if Stdlib.( = ) sym T_bool.Eq then eqv else Formula.mk_neg eqv
    | Atom.App (Predicate.Psym sym, ts, info) -> (
        match lift_list (fun ts -> Atom.mk_psym_app ~info sym ts) ts with
        | None -> emit (Formula.mk_atom atom)
        | Some (c, a, b) -> case (bool_term c) (atom_ a) (atom_ b))
    | _ -> raise Outside
  in
  try Some (formula phi) with Outside -> None

(* A literal of a cube of a skeleton: a comparison, or a Boolean variable
   with its polarity. *)
type lit = Cmp of Formula.t | Bvar of Ident.tvar * bool

(* [bool_lit phi]: [Some (b, true)] when [phi] is the atom [b = true] (or
   [true = b]) of a Boolean variable [b], [Some (b, false)] for [b = false]
   or a disequation with [true]; [None] otherwise. *)
let bool_lit phi =
  match phi with
  | Formula.Atom (Atom.App (Predicate.Psym sym, [ t1; t2 ], _), _)
    when Stdlib.( = ) sym T_bool.Eq || Stdlib.( = ) sym T_bool.Neq -> (
      let pol v = if Stdlib.( = ) sym T_bool.Eq then v else not v in
      match (t1, t2) with
      | Term.Var (b, s, _), c when Term.is_bool_sort s && T_bool.is_true c ->
          Some (b, pol true)
      | Term.Var (b, s, _), c when Term.is_bool_sort s && T_bool.is_false c ->
          Some (b, pol false)
      | c, Term.Var (b, s, _) when Term.is_bool_sort s && T_bool.is_true c ->
          Some (b, pol true)
      | c, Term.Var (b, s, _) when Term.is_bool_sort s && T_bool.is_false c ->
          Some (b, pol false)
      | _ -> None)
  | _ -> None

(* [skeleton_cube_count ~cap ~pos psi]: the number of cubes
   [skeleton_dnf ~pos psi] returns, or [cap + 1] when it exceeds [cap];
   computed without building them. *)
let rec skeleton_cube_count ~cap ~pos psi =
  let sat n = min n (cap + 1) in
  let both f p q =
    sat (f (skeleton_cube_count ~cap ~pos p) (skeleton_cube_count ~cap ~pos q))
  in
  match psi with
  | _ when Formula.is_true psi -> if pos then 1 else 0
  | _ when Formula.is_false psi -> if pos then 0 else 1
  | Formula.Atom (Atom.App (Predicate.Psym sym, [ _; _ ], _), _)
    when Option.is_none (bool_lit psi) ->
      let eq_ = Stdlib.( = ) sym T_bool.Eq
      and neq = Stdlib.( = ) sym T_bool.Neq in
      if (eq_ && not pos) || (neq && pos) then 2 else 1
  | Formula.Atom _ -> 1
  | Formula.UnaryOp (Not, p, _) -> skeleton_cube_count ~cap ~pos:(not pos) p
  | Formula.BinaryOp (And, p, q, _) -> both (if pos then ( * ) else ( + )) p q
  | Formula.BinaryOp (Or, p, q, _) -> both (if pos then ( + ) else ( * )) p q
  | _ -> cap + 1

(* [skeleton_dnf ~pos psi]: [psi] (when [pos]) or its negation, for [psi] a
   [skeleton]'s output, as a list of cubes of literals; a numeric
   disequation (positive or negated equation) becomes the two cubes [<] and
   [>].  [None] on an atom that is neither a Boolean-variable literal nor a
   binary comparison.
   Post: the disjunction of the cubes is equivalent to [psi] (to [not psi]
   when [not pos]); the number of cubes is [skeleton_cube_count]'s. *)
let rec skeleton_dnf ~pos psi =
  let product c1 c2 =
    List.concat_map c1 ~f:(fun l1 -> List.map c2 ~f:(fun l2 -> l1 @ l2))
  in
  let both f p q =
    match (skeleton_dnf ~pos p, skeleton_dnf ~pos q) with
    | Some c1, Some c2 -> Some (f c1 c2)
    | _ -> None
  in
  match psi with
  | _ when Formula.is_true psi -> Some (if pos then [ [] ] else [])
  | _ when Formula.is_false psi -> Some (if pos then [] else [ [] ])
  | Formula.Atom _ when Option.is_some (bool_lit psi) ->
      let b, v = Option.value_exn (bool_lit psi) in
      Some [ [ Bvar (b, if pos then v else not v) ] ]
  | Formula.Atom (Atom.App (Predicate.Psym sym, [ t1; t2 ], _), _) ->
      let eq_ = Stdlib.( = ) sym T_bool.Eq
      and neq = Stdlib.( = ) sym T_bool.Neq in
      if (eq_ && not pos) || (neq && pos) then
        Some [ [ Cmp (Formula.lt t1 t2) ]; [ Cmp (Formula.gt t1 t2) ] ]
      else if eq_ || neq then Some [ [ Cmp (Formula.eq t1 t2) ] ]
      else if pos then Some [ [ Cmp psi ] ]
      else Some [ [ Cmp (Formula.negate psi) ] ]
  | Formula.UnaryOp (Not, p, _) -> skeleton_dnf ~pos:(not pos) p
  | Formula.BinaryOp (And, p, q, _) -> both (if pos then product else ( @ )) p q
  | Formula.BinaryOp (Or, p, q, _) -> both (if pos then ( @ ) else product) p q
  | _ -> None

(* Test mutants of the Farkas leaves' candidate construction; only a
   property test passes anything but [No_mutant]. *)
type mutant =
  | No_mutant
  | Conflict_polarity
      (** a Boolean conflict answered with the B side's literal *)
  | Ite_unnegated  (** case splits guarding the else-branch by the condition *)

(* [farkas_candidate ~integer args phi1 phi2]: the Farkas leaves' answer
   before its check (see the header), or the reason for declining.
   Construction: [phi1] and [not phi2] are put in [skeleton] form and then
   in disjunctive normal form; a cube is a conjunction of rows (its
   comparisons) and of Boolean literals, and a cube whose literals contain
   [b] and [not b] is dropped (it is unsatisfiable).  For each pair of a
   cube [A_i] of [phi1] and [B_j] of [not phi2]:
   - if [A_i] holds a literal [l] and [B_j] its complement, with [l]'s
     variable in [args], [I_ij := l];
   - otherwise [I_ij] is the Farkas interpolant of the two cubes' rows
     (declining when they are rationally feasible after the rounding of
     [integer], or when the interpolant has a non-zero coefficient outside
     [args]).
   The answer is [OR_i AND_j I_ij].
   Why the literals may be set aside when no complement meets: no Boolean
   variable occurs inside a comparison of a skeleton, so a cube's literals
   and rows share no variable; a consistent set of literals is satisfiable
   on its own, and a pair of cubes is then unsatisfiable exactly when its
   rows are.
   Shape bound: declines when [phi1] or [phi2]'s skeleton exceeds
   [max_atoms] atom occurrences or the number of cube pairs exceeds
   [max_pairs] (both counted before any cube or row is built).  Each pair
   is one linear program to Z3, tens of milliseconds on MuCyc's queries, so
   the default of 256 pairs keeps a query to seconds; at 4096 a single query
   took close to three minutes.
   Pre: none; any formula is accepted and the unsupported ones declined.
   Post: [Ok i] has its free variables in [args] and, under [No_mutant],
   [phi1 => i] and [i /\ not phi2] unsatisfiable hold of the rows read
   (each [I_ij] by construction); the formulas themselves are checked by
   [farkas_leaf], since the affine reading of an atom is by evaluation. *)
let farkas_candidate ?(mutant = No_mutant) ?(max_atoms = 4096)
    ?(max_pairs = 256) ~integer args phi1 phi2 =
  let exception Decline of string in
  let decline s = raise (Decline s) in
  try
    if not (Formula.is_quantifier_free phi1 && Formula.is_quantifier_free phi2)
    then decline "quantified";
    let unnegated = Stdlib.( = ) mutant Ite_unnegated in
    let skel phi =
      match skeleton ~unnegated ~max_atoms phi with
      | Some psi -> psi
      | None -> decline "skeleton: unsupported form or more than max_atoms"
    in
    let psi1 = skel phi1 and psi2 = skel phi2 in
    let zs =
      Set.to_list
        (Set.filter
           (Set.union
              (Formula.term_sort_env_of psi1)
              (Formula.term_sort_env_of psi2))
           ~f:(fun (_, s) -> not (Term.is_bool_sort s)))
    in
    let sort =
      match zs with
      | [] -> T_real.SReal
      | (_, s) :: _ ->
          if
            (Term.is_int_sort s || Term.is_real_sort s)
            && List.for_all zs ~f:(fun (_, s') -> Stdlib.( = ) s s')
          then s
          else decline "columns not all integer or all real"
    in
    if integer && not (Term.is_int_sort sort) then decline "not integer";
    (* The pair bound applies to every query, counted on the skeletons
       without building a cube: a query whose two sides are plain linear
       formulas has as many cubes as one with [ite] terms, and a least
       solution of a few thousand nodes handed in as one side (a recursion-
       free system's lower bound) has a disjunctive normal form that does not
       fit in memory. *)
    let na = skeleton_cube_count ~cap:max_pairs ~pos:true psi1
    and nb = skeleton_cube_count ~cap:max_pairs ~pos:false psi2 in
    if na > max_pairs || nb > max_pairs || na * nb > max_pairs then
      decline "more than max_pairs cube pairs";
    let cubes ~pos psi =
      match skeleton_dnf ~pos psi with
      | None -> decline "an atom outside comparisons and Boolean literals"
      | Some cs ->
          List.filter_map cs ~f:(fun lits ->
              let cmps =
                List.filter_map lits ~f:(function
                  | Cmp c -> Some c
                  | Bvar _ -> None)
              and bools =
                List.dedup_and_sort ~compare:Stdlib.compare
                  (List.filter_map lits ~f:(function
                    | Bvar (b, v) -> Some (b, v)
                    | Cmp _ -> None))
              in
              if
                List.exists bools ~f:(fun (b, v) ->
                    List.mem bools (b, not v) ~equal:Stdlib.( = ))
              then None
              else
                match Rows.cube_rows_over zs (Formula.and_of cmps) with
                | None -> decline "a comparison that is not linear"
                | Some rows ->
                    Some
                      ( (if integer then
                           List.map rows ~f:(Rows.tighten_integer zs)
                         else rows),
                        bools ))
    in
    (* a case split often yields the same cube twice; duplicates add pairs,
       each one linear program, and no answer *)
    let dedup = List.dedup_and_sort ~compare:Stdlib.compare in
    let a_cubes = dedup (cubes ~pos:true psi1)
    and b_cubes = dedup (cubes ~pos:false psi2) in
    let shared = Set.Poly.of_list (List.map args ~f:fst) in
    let lit_formula (b, v) =
      if v then Formula.of_bool_var b else Formula.of_neg_bool_var b
    in
    let pair (a_rows, a_bools) (b_rows, b_bools) =
      match
        List.find a_bools ~f:(fun (b, v) ->
            Set.mem shared b && List.mem b_bools (b, not v) ~equal:Stdlib.( = ))
      with
      | Some (b, v) ->
          lit_formula
            (if Stdlib.( = ) mutant Conflict_polarity then (b, not v) else (b, v))
      | None -> (
          match Farkas.refute (a_rows @ b_rows) with
          | Farkas.Refuted lambda ->
              let ((coeffs, _, _) as row) =
                Farkas.interpolant_row a_rows b_rows lambda
              in
              if
                List.exists2_exn coeffs zs ~f:(fun k (v, _) ->
                    (not (Q.equal k Q.zero)) && not (Set.mem shared v))
              then decline "Farkas interpolant outside args"
              else affine_formula ~sort zs row
          | Farkas.Feasible ->
              if
                List.exists a_bools ~f:(fun (b, v) ->
                    List.mem b_bools (b, not v) ~equal:Stdlib.( = ))
              then decline "Boolean conflict outside args"
              else decline "a cube pair rationally feasible"
          | Farkas.Undecided _ -> decline "LP undecided")
    in
    Ok
      (Evaluator.simplify
         (Formula.or_of
            (List.map a_cubes ~f:(fun a ->
                 Formula.and_of
                   (List.dedup_and_sort ~compare:Stdlib.compare
                      (List.map b_cubes ~f:(pair a)))))))
  with Decline reason -> Error reason

(* [farkas_leaf_why ~integer args phi1 phi2]: [farkas_candidate]'s answer
   once Z3 has proved [phi1 => I] and [I => phi2] valid, or the reason it
   declined ("check" when the proof failed). *)
let farkas_leaf_why ?max_atoms ?max_pairs ~integer args phi1 phi2 =
  match farkas_candidate ?max_atoms ?max_pairs ~integer args phi1 phi2 with
  | Error _ as e -> e
  | Ok interp ->
      let valid phi = Z3Smt.Z3interface.is_valid ~id:None (get_fenv ()) phi in
      if
        valid (Formula.mk_imply phi1 interp)
        && valid (Formula.mk_imply interp phi2)
      then Ok interp
      else Error "check"

(* The Farkas leaves (see the header).  [integer] selects [Farkas_lia]. *)
let farkas_leaf ~integer args phi1 phi2 =
  match farkas_leaf_why ~integer args phi1 phi2 with
  | Ok i -> Interpolant i
  | Error _ -> Declined

(* [model_of senv model]: a satisfiability model as a substitution over
   [senv], a don't-care or missing variable given a dummy value of its sort.
   An entry whose name [senv] holds at another sort is dropped first: a pooled
   solver context reports names left by earlier queries, and such an entry
   says nothing about the variable of [senv]. *)
let model_of senv model =
  let model =
    List.dedup_and_sort ~compare:(fun (x, _) (y, _) -> Ident.tvar_compare x y)
    @@ remove_dontcare
    @@ model_restrict ~target:senv model
  in
  Set.fold senv ~init:(Map.Poly.of_alist_exn model) ~f:(fun model (x, sort) ->
      if Map.Poly.mem model x then model
      else Map.Poly.add_exn model ~key:x ~data:(Term.mk_dummy sort))

(* The MBP cover leaf (see the header).  Each cube is satisfied by its model
   and implies the existential closure of [phi1] over the variables outside
   [args] (the projection's contract), and the weakening keeps [cube => phi2];
   so on exit [phi1 => acc], and [acc => phi2] is checked rather than assumed.
   Each round strictly enlarges the covered set (the new cube holds at a
   model outside it), and [max_cubes] bounds the rounds. *)
let mbp_cover ?project ~max_cubes args phi1 phi2 =
  let project =
    match project with
    | Some project -> project
    | None ->
        fun model eliminated phi ->
          MbpProject.get_mbp_with ~conditionals:MbpProject.All_paths
            ~lets:MbpProject.Inline_lets ~check_validity:false
            ~print:(fun _ -> ())
            model eliminated phi
  in
  let exception Decline in
  let argset = Set.Poly.of_list @@ List.map args ~f:fst in
  let senv = Formula.term_sort_env_of phi1 in
  let eliminated = Set.filter senv ~f:(fst >> Set.mem argset >> not) in
  let check phis =
    Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ()) phis
  in
  let not_phi2 = Formula.negate phi2 in
  (* The projection alone gives the strongest interpolant, whose cubes on a
     circuit are close to single states and whose enumeration does not end;
     a dropped literal keeps [cube => phi2] and only enlarges the cube. *)
  let generalize cube =
    let rec drop kept = function
      | [] -> List.rev kept
      | l :: rest -> (
          match check (not_phi2 :: List.rev_append kept rest) with
          | `Unsat -> drop kept rest
          | _ -> drop (l :: kept) rest)
    in
    let lits = Formula.conjuncts_list_of cube in
    if List.length lits <= 1 then cube else Formula.and_of @@ drop [] lits
  in
  let rec loop n acc =
    match check [ phi1; Formula.negate @@ Formula.or_of acc ] with
    | `Unsat -> (
        let interp = Evaluator.simplify @@ Formula.or_of acc in
        match check [ interp; not_phi2 ] with
        | `Unsat -> Interpolant interp
        | _ -> raise Decline)
    | `Sat model when n < max_cubes ->
        let cube = project (model_of senv model) eliminated phi1 in
        if Set.for_all (Formula.tvs_of cube) ~f:(Set.mem argset) then
          loop (n + 1) (generalize cube :: acc)
        else raise Decline
    | _ -> raise Decline
  in
  (* a failing projection rule or an exception of Z3 declines too, so that
     the next leaf is asked; a timeout still propagates *)
  try loop 0 [] with
  | Decline -> Declined
  | exn_ when not (Common.Timer.is_async exn_) -> Declined

let bit_vector_only args phi1 phi2 =
  let ok = function T_bv.SBV _ | T_bool.SBool -> true | _ -> false in
  List.for_all args ~f:(snd >> ok)
  && Set.for_all (Formula.term_sort_env_of phi1) ~f:(snd >> ok)
  && Set.for_all (Formula.term_sort_env_of phi2) ~f:(snd >> ok)

(* The Bitwuzla leaf.  Bitwuzla's [sat] is taken as the absence of an
   interpolant: on quantifier-free bit-vectors satisfiability is decided and
   needs no interpretation of anything left open. *)
let bitwuzla_bv (o : bitwuzla_options) args phi1 phi2 =
  if not (bit_vector_only args phi1 phi2) then Declined
  else
    match
      Bitwuzla.Interpolant.interpolate
        ~opts:
          { subst = o.subst; pudlak = o.pudlak; lift = o.lift; simp = o.simp }
        ?timeout:o.timeout ?max_size:o.max_size args phi1 phi2
    with
    | Bitwuzla.Interpolant.NoInterpolant -> No_interpolant
    | Bitwuzla.Interpolant.Unavailable _ -> Declined
    | Bitwuzla.Interpolant.Interpolant interp -> (
        let valid phi = Z3Smt.Z3interface.is_valid ~id:None (get_fenv ()) phi in
        try
          if
            valid (Formula.mk_imply phi1 interp)
            && valid (Formula.mk_imply interp phi2)
          then Interpolant interp
          else Declined
        with exn_ when not (Common.Timer.is_async exn_) -> Declined)

(* The [Word_regroup] step.  For each clause [c] of [interp] and each
   argument [v] some literal of [c] extracts bits from, the group [G_v] of
   those literals is replaced first by nothing, then by [u = w] and last by
   [u <> w] for each pair of arguments [u], [w] of [v]'s sort (pairs with
   [v], and pairs occurring in the rest of [c], first); the first candidate
   accepted replaces the group.  The disequality generalises a group stating
   [v <> k] for a constant [k] when the clause pairs it with [u <> k]:
   [v <> u \/ u <> k] contains [v <> k \/ u <> k].

   Contract.  Let [interp = c /\ rest] be an interpolant of [phi1] and
   [phi2].  A candidate [c'] for [c] is accepted only when [phi1 /\ not c']
   and [rest /\ c' /\ not phi2] are both answered [Unsat]; [phi1] implies
   [rest], so [rest /\ c'] is again an interpolant, and it mentions no
   variable outside [args] since [c'] adds only arguments.  A timeout or
   unknown rejects the candidate.  The result is in general neither stronger
   nor weaker than [interp].  An interpolant with a quantifier is returned
   unchanged, since its clauses are not literals over the arguments. *)
let word_regroup (o : regroup_options) args phi1 phi2 interp =
  let queries = ref 0 and replaced = ref 0 in
  let unsat phis =
    if !queries >= o.max_queries then false
    else (
      incr queries;
      match
        Z3Smt.Z3interface.check_sat ~timeout:(Some o.timeout) ~id:None
          (FunEnv.mk_empty ()) phis
      with
      | `Unsat -> true
      | _ -> false)
  in
  let extracted lit =
    let vs = ref [] in
    Formula.iter_term lit ~f:(function
      | Term.FunApp (T_bv.BVEXTRACT _, [ Term.Var (x, s, _) ], _)
        when not (List.mem !vs (x, s) ~equal:Stdlib.( = )) ->
          vs := (x, s) :: !vs
      | _ -> ());
    !vs
  in
  let replace_group rest lits (v, s) =
    let group, others =
      List.partition_tf lits ~f:(fun l ->
          List.mem (extracted l) (v, s) ~equal:Stdlib.( = ))
    in
    if List.is_empty group then lits
    else
      let fvs = Formula.fvs_of @@ Formula.or_of others in
      let us =
        List.filter_map args ~f:(fun (u, s') ->
            if Stdlib.(s' = s) then Some u else None)
      in
      let rank (u, w) =
        (if Ident.tvar_equal u v || Ident.tvar_equal w v then 0 else 2)
        + if Set.mem fvs u && Set.mem fvs w then 0 else 1
      in
      let pairs =
        List.stable_sort ~compare:(fun p q -> Int.compare (rank p) (rank q))
        @@ List.concat_mapi us ~f:(fun i u ->
            List.filter_mapi us ~f:(fun j w ->
                if i < j then Some (u, w) else None))
      in
      let candidates =
        (if List.is_empty others then [] else [ others ])
        @ List.concat_map pairs ~f:(fun (u, w) ->
            List.map [ Formula.eq; Formula.neq ] ~f:(fun rel ->
                others @ [ rel (Term.mk_var u s) (Term.mk_var w s) ]))
      in
      match
        List.find candidates ~f:(fun lits' ->
            let c' = Formula.or_of lits' in
            unsat [ phi1; Formula.negate c' ]
            && unsat (rest @ [ c'; Formula.negate phi2 ]))
      with
      | Some lits' ->
          incr replaced;
          lits'
      | None -> lits
  in
  let rec go done_ = function
    | [] -> List.rev done_
    | c :: todo ->
        let lits = Formula.disjuncts_list_of c in
        let vars =
          List.dedup_and_sort ~compare:Stdlib.compare
          @@ List.concat_map lits ~f:extracted
        in
        let lits' =
          List.fold vars ~init:lits ~f:(fun lits var ->
              replace_group (List.rev_append done_ todo) lits var)
        in
        go (Formula.or_of lits' :: done_) todo
  in
  if not (Formula.is_quantifier_free interp) then interp
  else
    try
      let clauses = go [] @@ Formula.conjuncts_list_of interp in
      if !replaced = 0 then interp else Formula.and_of clauses
    with exn_ when not (Common.Timer.is_async exn_) -> interp

(* [binary ~leaves ~solve_chc ~qelim args phi1 phi2]: the leaves of [leaves]
   asked in order until one does not decline.
   Pre: [phi1] and [phi2] quantifier-free; [args] the shared arguments, the
   interpolant's only free variables.
   Post: [Interpolant i] is the first answer a leaf gave, a projection
   leaf's quantifier-free; [i] is not checked here for the CHC and
   projection leaves (a CHC solver's solution and an exact projection are
   interpolants by their own contracts), was checked by Z3 for the Farkas
   leaves, and for [Mbp_cover] holds by construction on the antecedent side
   and was checked by Z3 on the consequent side, and for [Bitwuzla_bv] was
   checked by Z3 on both.  [project] (when given) is the projection the
   [Mbp_cover] leaf runs at each model; its contract (a cube true at the
   model that implies the existential closure of [phi1] over the eliminated
   variables) is what the leaf's antecedent side rests on.
   [No_interpolant] only when a leaf found that none exists; [Declined] when
   every leaf declined, including on an empty list.
   The steps of [post] (none by default) are then applied in order to an
   [Interpolant]; each keeps it an interpolant (Z3-checked per change).
   With [search] [Spacer_blocking b] (default [Leaves]), the blocking loop
   is asked first, keeping no state between calls, with [project] (when
   given) the model-based projection of its non-bit-vector cubes: its
   [Interpolant i] holds in every model of the theory and its
   [No_interpolant] is a refutation read off a model (see
   [SpacerBlocking.blocking_interpolant]); the steps of [post] are applied
   to the leaves' answers only, and a query the loop declines or does not
   finish goes to the leaves as above.  With [session] and [at] (used only
   by [Spacer_blocking], and only when both are given) the loop keeps state
   between calls and takes its options from [session], see
   [SpacerBlocking.interpolate]; [binary] only passes them through.  [print]
   (silent by default) receives the loop's trace.  [observe] (nothing by
   default) is called with [`Blocking stats] when the loop answered, and
   otherwise with [`Leaves] just before the leaves are asked and then with
   [`Leaf l] when leaf [l] answered (gave an [Interpolant] or
   [No_interpolant]; not called when every leaf declined). *)
let binary ?(search = Leaves) ?session ?at ?project ?(print = fun _ -> ())
    ?(observe = fun _ -> ()) ~leaves ?(post = []) ~solve_chc ~qelim args phi1
    phi2 =
  let blocking =
    match search with
    | Leaves -> None
    | Spacer_blocking b -> (
        match
          SpacerBlocking.interpolate ?session ?at ?project ~print
            ~max_rounds:b.max_rounds ~sum_bounds:b.sum_bounds
            ~expand_bounds:
              (match b.expand_bounds with
              | Keep_numerals -> false
              | Weaken_numerals _ -> true)
            ~expand_strict:
              (match b.expand_bounds with
              | Keep_numerals -> false
              | Weaken_numerals { strict } -> strict)
            ~rem_numeral:b.rem_numeral ~phi1_bounds:b.phi1_bounds args phi1
            phi2
        with
        | `Ran (`Answer (Some i), s) ->
            observe (`Blocking s);
            Some (Interpolant i)
        | `Ran (`Answer None, s) ->
            observe (`Blocking s);
            Some No_interpolant
        | `Ran (`Fallback, _) | `Declined -> None)
  in
  match blocking with
  | Some outcome -> outcome
  | None ->
  observe `Leaves;
  let post_process = function
    | Interpolant i ->
        Interpolant
          (List.fold post ~init:i ~f:(fun i -> function
             | Word_regroup o -> word_regroup o args phi1 phi2 i))
    | (No_interpolant | Declined) as outcome -> outcome
  in
  post_process
  @@ List.fold_until leaves ~init:()
    ~f:(fun () leaf ->
      let outcome =
        match leaf with
        | Spacer_chc -> spacer_chc ~solve_chc args phi1 phi2
        | Qe_strongest -> projection ~qelim ~strongest:true args phi1 phi2
        | Qe_weakest -> projection ~qelim ~strongest:false args phi1 phi2
        | Farkas_lra -> farkas_leaf ~integer:false args phi1 phi2
        | Farkas_lia -> farkas_leaf ~integer:true args phi1 phi2
        | Mbp_cover max_cubes -> mbp_cover ?project ~max_cubes args phi1 phi2
        | Bitwuzla_bv o -> bitwuzla_bv o args phi1 phi2
      in
      match outcome with
      | Declined -> Continue ()
      | Interpolant _ | No_interpolant ->
          observe (`Leaf leaf);
          Stop outcome)
    ~finish:(fun () -> Declined)
