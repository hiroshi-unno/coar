(* Function reconstruction, totality and lemmas for recursive functions.

   SOURCE.  Champion, Chiba, Kobayashi and Sato, "ICE-Based Refinement Type
   Discovery for Higher-Order Functional Programs", Journal of Automated
   Reasoning 64(7), 2020, section 5.2 ("function reconstruction") and the
   remark on invariant discovery after it.  The source omits the totality
   check and says its implementation is unsound for that reason; it is made
   here and every step below that it guards refuses when it is not proved.

   RECONSTRUCTION ([reconstruct]).  An ordinary Bool-valued unknown [rho] of
   arity k + 1 is ELIGIBLE when every clause mentioning it either has it as
   its only head atom and mentions no other unknown (a DEFINING clause), or
   has it in the body only and no other unknown in the head (a NEGATIVE
   clause).  A nullary unknown whose every body occurrence is alone in its
   clause (a goal marker, [body => ff] and [ff => false]) is not counted as
   another unknown.  The unknown must not occur in a clause's pure part.

   Each defining clause [C /\ rho(s_1, w_1) /\ .. => rho(u_1 .. u_k, t)] is
   NORMALISED over fresh formals [x_1 .. x_k]: the equations [x_i = u_i] and
   the equations of each cube of [C]'s disjunctive normal form are solved for
   the clause's variables -- a variable equal to a term over what is already
   known is replaced by it, an equation [T = c(e_1 .. e_n)] with [T] known
   becomes the tester [is-c(T)] and the equations [sel_i(T) = e_i], an integer
   equation with one unknown variable of coefficient one is solved for it.
   The [w_j] must be distinct variables (the results [y_j] of the recursive
   calls) and count as known.  A variable left unsolved, a guard that
   mentions a [y_j], or calls whose arguments depend on each other cyclically
   refuse the predicate.  The normalised clause is equivalent to the original
   one in every model: each step is the one-point rule or the identity
   [x = c(z) <=> is-c(x) /\ z = sel(x)], valid in the term algebra.

   The guards [g_1 .. g_n] must be proved MUTUALLY EXCLUSIVE (validity), or,
   for two branches with no recursive call, their results proved equal where
   both guards hold, and the function
     f(x) = ite(g_1, e_1, ite(g_2, e_2, .. e_n)),
     e_i = t_i with each y_j replaced by f(args_j) in call order,
   must be proved TOTAL ([total]).  Guards proved EXHAUSTIVE make [f] the
   function the clauses define; otherwise the clauses define a partial
   function, which is completed by a default value (an integer, real or
   Boolean result only; any other is refused) and is vocabulary only.  Then
   [f] is added to the function environment and its applications to the
   qualifier vocabulary; [rho] stays an unknown.

   RESULT GUARDS ([~result_guards:true]).  A guard conjunct that mentions a
   [y_j] -- a refinement guard on a call's value ([n >= 0] in
   [len(t, n) /\ n >= 0 => len(c :: t, n + 1)]), or a case split on a Boolean
   call ([mem(e, t, b) /\ b = false /\ e = c => mem(e, c :: t, true)]) -- is
   otherwise refused.  With the switch it stays in the branch's guard, after
   the conjuncts over the formals alone (the guard's CALL-FREE part), and the
   body tests it with [y_j] replaced by the call: [f(x) = ite(g_1[f(a)/y],
   e_1[f(a)/y], ..)].  The checks become:
     - exclusivity and exhaustiveness are asked of the guards with each
       call's value written as an application of a symbol no environment
       defines; valid for every interpretation of the symbol, they hold for
       [f];
     - each call's arguments must decrease under its branch's call-free part.
       A call a guard evaluates sits to the right of that part in a
       short-circuit conjunction, so only its value where the call-free part
       holds matters, and so the body's value at [x] depends on [f] at
       smaller arguments only: the defining equation has exactly one
       solution, by well-founded induction as in WHY TOTALITY.
   With exclusive and exhaustive guards the function's graph is again the
   least solution of the defining clauses: by induction on the measure the
   premises' values are [f]'s, so the one branch whose guard holds at them is
   the one [f] takes, and conversely.  A refinement guard is not exhaustive
   for an arbitrary symbol (nothing says [f(t) >= 0]), so such a predicate
   gets the default-completed function, which equals the defined one
   wherever the refinement holds of [f] (for [len], everywhere) and is
   vocabulary only in either case.

   COMPOSITIONS ([~compositions:true]).  A defining clause of [rho] that
   applies another unknown [q] ([nmax] in a defining clause of [height]) is
   otherwise refused, and so is [q] itself, being applied in the body of a
   clause whose head is [rho].  With the switch:
     - a clause with [q] in the body and another unknown in the head is a
       negative clause of [q]: it does not constrain [q]'s least solution,
       which its own defining clauses fix alone;
     - once [q] has been reconstructed as [g] with exhaustive guards, an atom
       [q(a, w)] in a defining clause of [rho] is read as the equation
       [w = g(a)] and [rho] is normalised as before.  [q]'s least solution
       is the graph of [g] (exhaustive guards, totality), so read against it
       [rho]'s defining clauses define the function so obtained;
     - the unknowns refused in a pass are tried again while a pass
       reconstructs something, so a definition is read after the ones it
       applies (dependency order).
   Every function so obtained passes the checks of the plain case (exclusive
   guards, a decreasing measure for its own calls, every function it applies
   proved total), so it is a total function and sound vocabulary whatever
   the solution of [q].  Its graph is [rho]'s least solution only where [q]
   takes its least solution, so an unknown whose eligibility needed either
   relaxation is never put in its unknown's place.

   WHY TOTALITY.  A [define-fun-rec] is read by the solver as the equation
   [forall x. f(x) = body]; for a non-terminating "definition" that equation
   may have many solutions or none, and an inconsistent one makes every query
   that declares it valid -- a candidate mentioning it would then be accepted
   whatever it says.  For a total function the equation has exactly one
   solution in each model, and it is the least solution of the defining
   clauses (well-founded induction on the arguments: exactly one guard holds
   and the premises' calls are smaller).

   REPLACEMENT ([replace]: optional).  With the totality proof and
   exhaustive guards, every
   occurrence [rho(a, b)] outside the defining clauses is replaced by
   [b = f(a)] and the defining clauses dropped; [rho] leaves the signature
   with the definition [lambda x y. y = f(x)].  Equisatisfiable: [rho] occurs
   elsewhere only as a premise, so those clauses are antitone in it and the
   least solution -- the graph of [f] -- is the best choice, and the graph
   satisfies every defining clause by the definition.

   TOTALITY ([total]).  The recursive calls of a body are collected with the
   condition under which each one's value can matter (the conditions of the
   enclosing [ite]s, and the left operand of an enclosing [and], [or] or
   [=>], read short-circuit); a call under any other binder refuses.  A
   lexicographic measure of one or two components is searched, a component
   being the size of a datatype argument (decreasing only to a proper
   subterm: a selector chain under its testers, after the eta rule
   [c(sel_1(T) .. sel_n(T)) = T]) or [max(e, 0)] for an integer argument, its
   negation, the difference of two integer arguments, or a sequence's length.
   For every call, the call's condition must make the measure decrease, as a
   validity question.  Each function the body applies other than [f] itself
   must already have been proved total: a validity question that declares a
   non-terminating definition proves nothing.

   LEMMAS ([lemmas]).  For a total function, candidates from the signature --
   an integer result [>= 0] and compared with each integer argument and each
   sequence argument's length; a sequence result's length compared with each
   sequence argument's; for a Boolean result, implications with each tester
   of each datatype argument -- are filtered to a jointly inductive set: each
   call's value is replaced by a fresh variable [r] assumed to satisfy the
   current set under the call's condition, and each candidate is kept when it
   then holds of the body, until nothing more is dropped.  Sound by
   well-founded induction on the measure [total] found.  The kept set is
   recorded as the function's property, [forall x. inv(x, f(x))] together
   with the instances at the body's recursive calls, which every query that
   reaches the function conjoins at each application it contains.

   Every validity question here has a resource limit and a kill budget; an
   undecided question counts as not proved, which refuses (or drops) and so
   never adds anything unproved. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* ---------------------------------------------------------------------- *)
(* Solver questions                                                        *)

let rlimit = 4_000_000
let kill_ms = 5000

(* The number of validity questions asked; read by a property check. *)
let questions = Atomic.make 0

(* Whether a question that binds a sequence (or another sort Z3 has no
   complete quantifier support for) under a quantifier is refused rather than
   asked; set from the configuration before each pass.  Such a question can run
   until the kill budget while Z3's resource counter advances far below the
   limit -- on a Thrust iterator input six lemma questions whose function body
   nests a sequence existential under universals each ran the full 5 s kill
   having spent 0.5-0.75 M of the 4 M units, and none was decided -- so the
   limit does not bound it.  The shape is [Z3interface.may_not_return], the
   test the validator's and the zero-unknown ladder's questions already refuse
   by.  Not exact: a refused question counts as not proved, which only drops a
   candidate (a lemma, or a reconstruction the question would have shown), never
   adds one, so the pass stays sound and can lose what Z3 would have proved.
   [false] (the default): every question is asked. *)
let refuse_seq_quantified = Atomic.make false

(* [true] when [phi] has the shape [refuse_seq_quantified] refuses.  Tested
   only when the refusal is on or the phase account is (where it is reported
   as the answer-neutral event [recon-seq-quantified-question], so a default
   run's report shows where the refusal would act); otherwise [false]
   without looking at [phi]. *)
let seq_quantified phi =
  if
    (Atomic.get refuse_seq_quantified || !Common.PhaseTime.on)
    && Z3Smt.Z3interface.may_not_return phi
  then (
    Common.PhaseTime.event "recon-seq-quantified-question";
    true)
  else false

let z3_valid ~(fenv : FunEnv.t) phi =
  if seq_quantified phi && Atomic.get refuse_seq_quantified then (
    Common.PhaseTime.event "recon-seq-quantified-refused";
    false)
  else
    match
      Z3Smt.Z3interface.with_rlimit ~label:"recon" (Some rlimit) @@ fun () ->
      Z3Smt.Z3interface.check_valid ~timeout:(Some kill_ms) ~fresh_solver:true
        ~id:None
        (Z3Smt.Z3interface.fenv_reached_by fenv phi)
        phi
    with
    | `Valid -> true
    | _ -> false
    | exception exn when not (Common.Timer.is_async exn) -> false

(* The oracle every question goes through.  A property check replaces it by
   one that lies, to show that a check fails when the oracle is wrong. *)
let oracle : (fenv:FunEnv.t -> Formula.t -> bool) ref = ref z3_valid

let valid ~fenv phi =
  Atomic.incr questions;
  !oracle ~fenv phi

(* ---------------------------------------------------------------------- *)
(* Small term utilities                                                    *)

exception Refuse of string

let refuse fmt = Printf.ksprintf (fun s -> raise (Refuse s)) fmt
let tvs_mem t x = Set.mem (Term.tvs_of t) x

let is_var_named x = function
  | Term.Var (y, _, _) -> Ident.tvar_equal x y
  | _ -> false

let formula_of_bool_term t =
  if T_bool.is_formula t then T_bool.let_formula t else Formula.of_bool_term t

let sdt_of_sort = function
  | T_dt.SDT dt when not (Datatype.is_codt dt) -> Some dt
  | _ -> None

(* ---------------------------------------------------------------------- *)
(* Recursive calls of a body, with the condition under which each matters  *)

type call = {
  r : Ident.tvar;  (** stands for the call's value in [abstracted] *)
  path : Formula.t;
  args : Term.t list;  (** inner calls replaced by their [r]s *)
  orig_args : Term.t list;  (** as written in the body *)
}

(* The calls of [f] in [body] and [body] with each call replaced by its [r].
   Raises [Refuse] when a call sits where its condition cannot be read (under
   a binder, a [let], or inside a formula's quantifier). *)
let calls_of_body ~f ~(sret : Sort.t) body =
  let calls = ref [] in
  let mentions_f_term t =
    Set.exists (Term.fvar_apps_of t) ~f:(function
      | Term.FunApp (FVar (g, _, _), _, _) -> Ident.tvar_equal g f
      | _ -> false)
  in
  let mentions_f_fml phi =
    Set.exists (Formula.fvar_apps_of phi) ~f:(function
      | Term.FunApp (FVar (g, _, _), _, _) -> Ident.tvar_equal g f
      | _ -> false)
  in
  let rec walk path t =
    match t with
    | Term.Var _ -> t
    | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], info) ->
        let c' = walk path c in
        let cphi = formula_of_bool_term c' in
        Term.mk_fsym_app ~info T_bool.IfThenElse
          [
            c';
            walk (Formula.and_of [ path; cphi ]) a;
            walk (Formula.and_of [ path; Formula.mk_neg cphi ]) b;
          ]
    | Term.FunApp (FVar (g, _, _), args, _) when Ident.tvar_equal g f ->
        let args' = List.map args ~f:(walk path) in
        let r = Ident.mk_fresh_tvar () in
        calls := { r; path; args = args'; orig_args = args } :: !calls;
        Term.mk_var r sret
    | Term.FunApp (T_bool.Formula phi, [], info) ->
        T_bool.of_formula ~info (walk_fml path phi)
    | Term.FunApp (sym, args, info) ->
        Term.mk_fsym_app ~info sym (List.map args ~f:(walk path))
    | _ ->
        if mentions_f_term t then refuse "a recursive call under a binder"
        else t
  and walk_fml path phi =
    match phi with
    | Formula.Atom (Atom.App (pred, args, ai), info) ->
        Formula.mk_atom ~info
          (Atom.mk_app ~info:ai pred (List.map args ~f:(walk path)))
    | Formula.Atom _ -> phi
    | Formula.UnaryOp (Formula.Not, p, info) ->
        Formula.mk_neg ~info (walk_fml path p)
    | Formula.BinaryOp (Formula.And, a, b, info) ->
        let a' = walk_fml path a in
        Formula.mk_and ~info a' (walk_fml (Formula.and_of [ path; a' ]) b)
    | Formula.BinaryOp (Formula.Or, a, b, info) ->
        let a' = walk_fml path a in
        Formula.mk_or ~info a'
          (walk_fml (Formula.and_of [ path; Formula.mk_neg a' ]) b)
    | Formula.BinaryOp (Formula.Imply, a, b, info) ->
        let a' = walk_fml path a in
        Formula.mk_imply ~info a' (walk_fml (Formula.and_of [ path; a' ]) b)
    | Formula.BinaryOp (op, a, b, info) ->
        Formula.mk_binop ~info op (walk_fml path a) (walk_fml path b)
    | _ ->
        if mentions_f_fml phi then refuse "a recursive call under a binder"
        else phi
  in
  let abstracted = walk (Formula.mk_true ()) body in
  (List.rev !calls, abstracted)

(* the functions of [fenv] that [t] applies *)
let applied_functions (fenv : FunEnv.t) t =
  Set.Poly.filter_map (Term.fvar_apps_of t) ~f:(function
    | Term.FunApp (FVar (g, _, _), _, _) when Map.Poly.mem fenv g -> Some g
    | _ -> None)

(* ---------------------------------------------------------------------- *)
(* Totality                                                                *)

type component =
  | Struct of int  (** the size of the datatype argument at this position *)
  | Nat of Term.t  (** [max(e, 0)] for an integer term over the formals *)

let str_of_component = function
  | Struct i -> sprintf "size(#%d)" i
  | Nat e -> sprintf "nat(%s)" (Term.str_of e)

let components (formals : sort_env_list) =
  let vars = List.mapi formals ~f:(fun i (x, s) -> (i, Term.mk_var x s, s)) in
  let structs =
    List.filter_map vars ~f:(fun (i, _, s) ->
        (* the subterm order is well-founded on finite trees only: every
           datatype the argument's values can contain must be inductive *)
        if SubtermOrder.inductive_closure_sort s then Some (Struct i) else None)
  in
  let ints =
    List.filter_map vars ~f:(fun (_, v, s) ->
        if Term.is_int_sort s then Some v else None)
  in
  let lens =
    List.filter_map vars ~f:(fun (_, v, s) ->
        if T_seq.is_sseq s then
          Some (Nat (T_seq.mk_len (T_seq.elem_sort_of s) v))
        else None)
  in
  let diffs =
    List.concat_map ints ~f:(fun a ->
        List.filter_map ints ~f:(fun b ->
            if Stdlib.( = ) a b then None else Some (Nat (T_int.mk_sub b a))))
  in
  structs @ lens
  @ List.concat_map ints ~f:(fun v -> [ Nat v; Nat (T_int.mk_neg v) ])
  @ diffs

let nat t =
  T_bool.ifte
    (Formula.mk_atom (T_int.mk_geq t (T_int.zero ())))
    t (T_int.zero ())

(* [strict] and [non-strict] decrease of one component from the formals to
   [args], as formulas *)
let decrease (formals : sort_env_list) args comp =
  match comp with
  | Struct i ->
      let x, s = List.nth_exn formals i in
      let a = List.nth_exn args i in
      let strict = SubtermOrder.strict_decrease x a in
      (strict, Formula.or_of [ Formula.eq a (Term.mk_var x s); strict ])
  | Nat e ->
      let sub =
        Map.Poly.of_alist_exn
        @@ List.map2_exn formals args ~f:(fun (x, _) a -> (x, a))
      in
      let before = nat e and after = nat (Term.subst sub e) in
      ( Formula.mk_atom (T_int.mk_lt after before),
        Formula.mk_atom (T_int.mk_leq after before) )

let lex_decrease formals args = function
  | [ c ] -> fst (decrease formals args c)
  | [ c1; c2 ] ->
      let s1, n1 = decrease formals args c1 in
      let s2, _ = decrease formals args c2 in
      Formula.or_of [ s1; Formula.and_of [ n1; s2 ] ]
  | _ -> assert false

let max_orders = 48

(* A lexicographic measure under which every call decreases, if one is
   found; [Some []] when there is no call. *)
let find_measure ~fenv (formals : sort_env_list)
    (calls : (Formula.t * Term.t list) list) =
  if List.is_empty calls then Some []
  else
    let comps = components formals in
    let singles = List.map comps ~f:(fun c -> [ c ]) in
    let pairs =
      List.concat_map comps ~f:(fun a ->
          List.filter_map comps ~f:(fun b ->
              if Stdlib.( = ) a b then None else Some [ a; b ]))
    in
    List.find
      (List.take (singles @ pairs) max_orders)
      ~f:(fun order ->
        List.for_all calls ~f:(fun (path, args) ->
            valid ~fenv
              (Formula.mk_imply path (lex_decrease formals args order))))

(* ---------------------------------------------------------------------- *)
(* Eligibility and normalisation                                           *)

type branch = {
  guard : Formula.t;
      (** over the formals only, unless [~result_guards:true]: then also over
          the [y]s, its conjuncts over the formals alone first *)
  call_free : Formula.t;
      (** the conjuncts of [guard] over the formals alone; [guard] itself
          (physically) when it mentions no [y] *)
  calls : (Ident.tvar * Term.t list) list;
      (** [y_j] and its arguments, each mentioning only earlier [y]s *)
  result : Term.t;  (** over the formals and the [y]s *)
}

let pvar_of_atom = function
  | Atom.App (Predicate.Var (p, _), _, _) -> Some p
  | _ -> None

let args_of_atom = function Atom.App (_, args, _) -> args | _ -> []
let atom_pvars ps ns = Set.Poly.filter_map (Set.union ps ns) ~f:pvar_of_atom

(* nullary unknowns whose every body occurrence is alone in its clause *)
let goal_markers (clauses : ClauseOld.t list) senv =
  let nullary =
    Map.Poly.filter_keys senv ~f:(fun _ -> true)
    |> Map.Poly.filter ~f:(fun s -> List.is_empty (Logic.Sort.args_of s))
    |> Map.key_set
    |> Set.Poly.map ~f:Ident.tvar_to_pvar
  in
  Set.filter nullary ~f:(fun g ->
      List.for_all clauses ~f:(fun (_, ps, ns, _) ->
          if
            Set.exists ns ~f:(fun a ->
                Option.equal Ident.pvar_equal (pvar_of_atom a) (Some g))
          then Set.is_empty ps && Set.length ns = 1
          else true))

type role = Defining | Negative | Unrelated

(* the role of one clause for [rho]; raises [Refuse] when it makes [rho]
   ineligible.  With [~compose:true] (COMPOSITIONS at the top): an unknown of
   [known] is not another unknown in a clause with [rho] in the head, and a
   clause with [rho] in the body and another unknown in the head is a
   negative clause *)
let role_of ?(compose = false) ?(known = Set.Poly.empty) ~markers rho
    ((_, ps, ns, phi) : ClauseOld.t) =
  let is_rho a = Option.equal Ident.pvar_equal (pvar_of_atom a) (Some rho) in
  let in_head = Set.exists ps ~f:is_rho and in_body = Set.exists ns ~f:is_rho in
  if Set.mem (Formula.pvs_of phi) rho then refuse "occurs in a pure part"
  else if not (in_head || in_body) then Unrelated
  else
    let others =
      Set.filter (atom_pvars ps ns) ~f:(fun p ->
          (not (Ident.pvar_equal p rho)) && not (Set.mem markers p))
    in
    if in_head then
      let others =
        if compose then Set.filter others ~f:(fun p -> not (Set.mem known p))
        else others
      in
      if Set.length ps = 1 && Set.is_empty others then Defining
      else refuse "a clause with it in the head mentions another unknown"
    else
      let pos_others =
        Set.filter (Set.Poly.filter_map ps ~f:pvar_of_atom) ~f:(fun p ->
            not (Set.mem markers p))
      in
      if Set.is_empty pos_others || compose then Negative
      else refuse "a clause with it in the body has another unknown in the head"

(* the disjunctive normal form of a negation-normal formula, as cubes of
   literals, at most [cap] of them *)
let dnf ~cap phi =
  let rec go phi =
    match phi with
    | Formula.BinaryOp (Formula.Or, a, b, _) -> go a @ go b
    | Formula.BinaryOp (Formula.And, a, b, _) ->
        let ca = go a and cb = go b in
        if List.length ca * List.length cb > cap then refuse "too many cubes"
        else List.concat_map ca ~f:(fun x -> List.map cb ~f:(fun y -> x @ y))
    | phi when Formula.is_true phi -> [ [] ]
    | phi when Formula.is_false phi -> []
    | phi -> [ [ phi ] ]
  in
  let cubes = go phi in
  if List.length cubes > cap then refuse "too many cubes" else cubes

(* a Boolean literal read as an equation where it is one *)
let equation_of_literal lit =
  let bool_const t = T_bool.is_true t || T_bool.is_false t in
  let flip t =
    if T_bool.is_true t then T_bool.mk_false () else T_bool.mk_true ()
  in
  match lit with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _) ->
      Some (a, b)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _),
        _ )
    when bool_const b ->
      Some (a, flip b)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _),
        _ )
    when bool_const a ->
      Some (flip a, b)
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ a; b ], _), _)
    when bool_const b ->
      Some (a, flip b)
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ a; b ], _), _)
    when bool_const a ->
      Some (flip a, b)
  | _ -> None

(* The branches of one defining clause over [formals] (one per cube of its
   guard), or [Refuse]. *)
let normalise ?(result_guards = false) ~formals
    ((uni_senv, ps, ns, phi) : ClauseOld.t) =
  let head = Set.choose_exn ps in
  let hargs = args_of_atom head in
  let us, t = (List.drop_last_exn hargs, List.last_exn hargs) in
  let old_sort x =
    match Map.Poly.find uni_senv x with
    | Some s -> Logic.ExtTerm.to_old_sort s
    | None -> refuse "a variable without a sort"
  in
  let formal_set = Set.Poly.of_list (List.map formals ~f:fst) in
  let body_calls =
    List.map (Set.to_list ns) ~f:(fun a ->
        let args = args_of_atom a in
        match List.last_exn args with
        | Term.Var (y, _, _) -> (y, List.drop_last_exn args)
        | _ -> refuse "a recursive call's result is not a variable")
  in
  let ys = List.map body_calls ~f:fst in
  if List.contains_dup ys ~compare:Ident.tvar_compare then
    refuse "two calls share a result variable";
  if
    List.exists ys ~f:(fun y ->
        List.exists us ~f:(fun u -> tvs_mem u y) || Set.mem formal_set y)
  then refuse "a call's result occurs in the head's arguments";
  let ys_set = Set.Poly.of_list ys in
  let known0 = Set.union formal_set ys_set in
  let known_params = formals @ List.map ys ~f:(fun y -> (y, old_sort y)) in
  let cubes = dnf ~cap:16 (Formula.nnf_of (Formula.negate phi)) in
  List.filter_map cubes ~f:(fun cube ->
      let defs = ref Map.Poly.empty in
      let testers = ref [] in
      let contradiction = ref false in
      let apply t = Term.subst !defs t in
      let resolved t =
        Evaluator.known_function_body_is_closed known_params (apply t)
      in
      let unknown_var = function
        | Term.Var (z, _, _)
          when (not (Set.mem known0 z)) && not (Map.Poly.mem !defs z) ->
            Some z
        | _ -> None
      in
      let define z e =
        let e = apply e in
        defs := Map.Poly.map !defs ~f:(Term.subst (Map.Poly.singleton z e));
        defs := Map.Poly.set !defs ~key:z ~data:e
      in
      let eqs, rest =
        List.partition_map cube ~f:(fun lit ->
            match equation_of_literal lit with
            | Some (a, b) -> First (a, b)
            | None -> Second lit)
      in
      let pending =
        ref
          (List.map2_exn formals us ~f:(fun (x, s) u -> (Term.mk_var x s, u))
          @ eqs)
      in
      let step (a, b) =
        let a = apply a and b = apply b in
        let cons_app = function
          | Term.FunApp (T_dt.DTCons (c, _, dt), args, _) -> Some (c, dt, args)
          | _ -> None
        in
        let solve_one () =
          (* an integer or real equation with one unknown variable *)
          let unknowns =
            Set.filter
              (Set.union (Term.tvs_of a) (Term.tvs_of b))
              ~f:(fun v -> not (Set.mem known0 v || Map.Poly.mem !defs v))
          in
          match Set.to_list unknowns with
          | [ z ] -> (
              let occurs t = tvs_mem t z in
              match
                Evaluator.isolate_target ~is_target:(is_var_named z) ~occurs a b
              with
              | Some e when resolved e -> `Define (z, e)
              | _ -> `Keep)
          | _ -> `Keep
        in
        match (unknown_var a, unknown_var b) with
        | Some z, _ when resolved b && not (tvs_mem b z) -> `Define (z, b)
        | _, Some z when resolved a && not (tvs_mem a z) -> `Define (z, a)
        | _ -> (
            match (cons_app a, cons_app b) with
            | Some (c1, _, args1), Some (c2, _, args2) ->
                if String.equal c1 c2 then `Split ([], List.zip_exn args1 args2)
                else `Contradiction
            | Some (c, dt, args), None when resolved b ->
                `Split
                  ( [ T_dt.mk_is_cons dt c b ],
                    List.mapi args ~f:(fun i e ->
                        (T_dt.mk_sel_by_cons dt c i b, e)) )
            | None, Some (c, dt, args) when resolved a ->
                `Split
                  ( [ T_dt.mk_is_cons dt c a ],
                    List.mapi args ~f:(fun i e ->
                        (T_dt.mk_sel_by_cons dt c i a, e)) )
            | _ -> solve_one ())
      in
      let rec loop () =
        let progress = ref false in
        let next = ref [] in
        List.iter !pending ~f:(fun eq ->
            if not !contradiction then
              match step eq with
              | `Define (z, e) ->
                  progress := true;
                  define z e
              | `Split (ts, eqs) ->
                  progress := true;
                  testers := !testers @ ts;
                  next := !next @ eqs
              | `Contradiction -> contradiction := true
              | `Keep -> next := !next @ [ eq ]);
        pending := !next;
        if !progress && not !contradiction then loop ()
      in
      loop ();
      if !contradiction then None
      else
        let close t =
          let t = apply t in
          if resolved t then t else refuse "a variable could not be eliminated"
        in
        let close_fml phi =
          let phi = Formula.subst !defs phi in
          if Evaluator.known_function_body_is_closed known_params (T_bool.of_formula phi)
          then phi else refuse "a variable could not be eliminated"
        in
        let guard =
          Formula.and_of
            (List.map !testers ~f:(fun a -> close_fml (Formula.mk_atom a))
            @ List.map !pending ~f:(fun (a, b) ->
                Formula.eq (close a) (close b))
            @ List.map rest ~f:close_fml)
        in
        let over_formals phi =
          Evaluator.known_function_body_is_closed formals (T_bool.of_formula phi)
        in
        let guard, call_free =
          if over_formals guard then (guard, guard)
          else if not result_guards then
            refuse "a guard mentions a recursive call's result"
          else
            (* [~result_guards:true]: a conjunct over a call's result stays
               in the guard, after the call-free conjuncts, so that a call it
               evaluates is reached only where the call-free part holds;
               every conjunct is closed over the formals and the [y]s
               ([close_fml] above) *)
            let free, dep =
              List.partition_tf (Formula.conjuncts_list_of guard)
                ~f:over_formals
            in
            let call_free = Formula.and_of free in
            (Formula.and_of (free @ dep), call_free)
        in
        let calls =
          List.map body_calls ~f:(fun (y, args) -> (y, List.map args ~f:close))
        in
        (* order the calls so that each mentions only earlier results *)
        let rec order placed acc = function
          | [] -> List.rev acc
          | remaining ->
              let ready, waiting =
                List.partition_tf remaining ~f:(fun (_, args) ->
                    List.for_all args ~f:(fun a ->
                        Evaluator.known_function_body_is_closed
                          (formals @ List.filter known_params ~f:(fun (v, _) -> Set.mem placed v)) a))
              in
              if List.is_empty ready then
                refuse "calls depend on each other cyclically"
              else
                order
                  (Set.union placed (Set.Poly.of_list (List.map ready ~f:fst)))
                  (List.rev_append ready acc)
                  waiting
        in
        Some
          { guard; call_free; calls = order Set.Poly.empty [] calls;
            result = close t })

(* ---------------------------------------------------------------------- *)
(* The registry and the result of the pass                                 *)

type reconstructed = {
  pvar : Ident.pvar;
  fname : Ident.tvar;
  formals : sort_env_list;
  sret : Sort.t;
  body : Term.t;
  branches : branch list;
  exhaustive : bool;
      (** the defining clauses' guards cover every argument; otherwise the last
          branch is a default value and the function is vocabulary only *)
}

type outcome = {
  problem : PCSP.Problem.t;
  reconstructed : reconstructed list;
  refused : (Ident.pvar * string) list;
  replaced : Ident.pvar list;
  lemmas : (Ident.tvar * Formula.t list) list;
}

(* each call's result variable [y_j] of [b] mapped to the call [fname(args_j)],
   earlier results in its arguments replaced first *)
let call_subst ~fname ~sargs ~sret b =
  List.fold b.calls ~init:Map.Poly.empty ~f:(fun sub (y, args) ->
      let call =
        Term.mk_fvar_app fname sargs sret (List.map args ~f:(Term.subst sub))
      in
      Map.Poly.set sub ~key:y ~data:call)

(* [b]'s guard with each call's result replaced by the call; the guard
   itself when it mentions no result *)
let guard_with_calls ~fname ~sargs ~sret b =
  if phys_equal b.guard b.call_free then b.guard
  else Formula.subst (call_subst ~fname ~sargs ~sret b) b.guard

let build_body ~fname ~formals ~sret branches =
  let sargs = List.map formals ~f:snd in
  let branch_term b = Term.subst (call_subst ~fname ~sargs ~sret b) b.result in
  match List.rev branches with
  | [] -> refuse "no branch"
  | last :: rest ->
      List.fold rest ~init:(branch_term last) ~f:(fun acc b ->
          T_bool.ifte
            (guard_with_calls ~fname ~sargs ~sret b)
            (branch_term b) acc)

(* the problem's clauses in their old form *)
let clauses_of pcsp =
  let senv = PCSP.Problem.senv_of pcsp in
  let cls =
    match PCSP.Problem.clauses_of_opt pcsp with
    | Some cls -> cls
    | None -> ClauseSet.of_formulas senv (PCSP.Problem.formulas_of pcsp)
  in
  Set.to_list @@ ClauseSet.to_old_clause_set senv cls

(* The problem's clauses as the names of the unknowns they apply: one pair
   (names of the positive atoms, names of the negative atoms) per clause of
   [clauses_of pcsp], as a set, computed without the clauses.
   Contract: exactly the image of [clauses_of pcsp] under the map
   [(_, ps, ns, _) |-> (pvars ps, pvars ns)], each name set in canonical
   shape ([Set.canon]: a [Set.Poly] of sets orders by tree shape, so equal
   pairs of differently built sets would be two members), raising where
   computing the clauses would raise.  A problem held as formulas goes through
   [BoolTerm.cnf_pvar_names_of], the image of the clausal form
   [ClauseSet.of_formulas] builds; a problem held as clauses is read
   directly.  The conversion to the old form preserves the image: an atom
   whose head the signature declares becomes an application of the
   predicate variable of the same name, and an atom whose head it does not
   declare becomes no predicate-variable atom at all, which is why such
   heads are left out here.
   [clause_name_ids_of pcsp] is [(names, pairs)]: the same set with each
   unknown named by its index in [names] (the unknowns met, each once) and
   each name set the strictly increasing list of its indices, [pairs] its
   members without repetition; [clause_names_of] is that set read back. *)
let clause_name_ids_of pcsp =
  let senv = PCSP.Problem.senv_of pcsp in
  (* the names met, interned in the order first met *)
  let ids = Hashtbl.Poly.create () in
  let names = ref [||] and n = ref 0 in
  let id_of x =
    match Hashtbl.Poly.find ids x with
    | Some i -> i
    | None ->
        let i = !n in
        incr n;
        if i = Array.length !names then (
          let a = Array.create ~len:(Int.max 16 (2 * i)) x in
          Array.blit ~src:!names ~src_pos:0 ~dst:a ~dst_pos:0 ~len:i;
          names := a);
        !names.(i) <- x;
        Hashtbl.Poly.set ids ~key:x ~data:i;
        i
  in
  let pairs =
    match PCSP.Problem.clauses_of_opt pcsp with
    | Some cls ->
        let ids_of atoms =
          List.dedup_and_sort ~compare:Int.compare
          @@ Set.fold atoms ~init:[] ~f:(fun acc a ->
              let rec head = function
                | Logic.Var (x, _) -> Some x
                | Logic.App (t, _, _) -> head t
                | _ -> None
              in
              match head a with
              | Some x when Map.Poly.mem senv x -> id_of x :: acc
              | _ -> acc)
        in
        Set.Poly.map cls ~f:(fun (_, ps, ns, _) -> (ids_of ps, ids_of ns))
    | None ->
        Logic.BoolTerm.with_shared_nnf_cnf @@ fun () ->
        Set.concat_map (PCSP.Problem.formulas_of pcsp)
          ~f:(fun (uni_senv, phi) ->
            Logic.BoolTerm.cnf_pvar_name_ids_of id_of senv uni_senv phi)
  in
  (Array.sub !names ~pos:0 ~len:!n, Set.to_list pairs)

(* [clause_name_facts_of pcsp] is [(names, facts)]: [names] as in
   [clause_name_ids_of pcsp] (the unknowns met, each named by its index) and
   [facts] the [Logic.cnf_name_facts] of that function's set of pairs.
   Contract: [names] holds the same unknowns (in the order this walk meets
   them, which only relabels them) and [facts] is the facts of the same set
   under these labels, computed
   without the set: a problem held as formulas through
   [BoolTerm.cnf_pvar_name_facts_of] (the facts of the image
   [BoolTerm.cnf_pvar_name_ids_of] gives, by the same walker), a problem
   held as clauses as the union over its clauses of the product of their
   atoms' facts (a clause is the pairwise union of its one-atom clauses);
   raises where [clause_name_ids_of] raises.  Why: on the dual of a
   termination problem whose formulas nest disjunctions, the set of pairs
   held hundreds of thousands of distinct pairs, hundreds of megabytes,
   and its walk did not finish in the run's time while every byte of it
   stayed live, so the dual side of a primal-dual run spent its whole run
   here and the process grew until a memory cap ended it; the facts are
   polynomial in the number of unknowns. *)
let clause_name_facts_of pcsp =
  let senv = PCSP.Problem.senv_of pcsp in
  let ids = Hashtbl.Poly.create () in
  let names = ref [||] and n = ref 0 in
  let id_of x =
    match Hashtbl.Poly.find ids x with
    | Some i -> i
    | None ->
        let i = !n in
        incr n;
        if i = Array.length !names then (
          let a = Array.create ~len:(Int.max 16 (2 * i)) x in
          Array.blit ~src:!names ~src_pos:0 ~dst:a ~dst_pos:0 ~len:i;
          names := a);
        !names.(i) <- x;
        Hashtbl.Poly.set ids ~key:x ~data:i;
        i
  in
  let facts =
    match PCSP.Problem.clauses_of_opt pcsp with
    | Some cls ->
        let ids_of atoms =
          List.dedup_and_sort ~compare:Int.compare
          @@ Set.fold atoms ~init:[] ~f:(fun acc a ->
              let rec head = function
                | Logic.Var (x, _) -> Some x
                | Logic.App (t, _, _) -> head t
                | _ -> None
              in
              match head a with
              | Some x when Map.Poly.mem senv x -> id_of x :: acc
              | _ -> acc)
        in
        Set.fold cls ~init:Logic.BoolTerm.cnf_name_facts_empty
          ~f:(fun acc (_, ps, ns, _) ->
            let ps = ids_of ps in
            let ns = ids_of ns in
            let clause =
              List.fold ns
                ~init:
                  (List.fold ps ~init:Logic.BoolTerm.cnf_name_facts_unit
                     ~f:(fun f a ->
                       Logic.BoolTerm.cnf_name_facts_product f
                         (Logic.BoolTerm.cnf_name_facts_pos a)))
                ~f:(fun f g ->
                  Logic.BoolTerm.cnf_name_facts_product f
                    (Logic.BoolTerm.cnf_name_facts_neg g))
            in
            Logic.BoolTerm.cnf_name_facts_union acc clause)
    | None ->
        Logic.BoolTerm.with_shared_nnf_cnf @@ fun () ->
        Set.fold (PCSP.Problem.formulas_of pcsp)
          ~init:Logic.BoolTerm.cnf_name_facts_empty
          ~f:(fun acc (uni_senv, phi) ->
            Logic.BoolTerm.cnf_name_facts_union acc
              (Logic.BoolTerm.cnf_pvar_name_facts_of id_of senv uni_senv phi))
  in
  (Array.sub !names ~pos:0 ~len:!n, facts)

let clause_names_of pcsp =
  let names, pairs = clause_name_ids_of pcsp in
  let to_p l =
    Set.canon
      (Set.Poly.of_list
         (List.map l ~f:(fun i -> Ident.tvar_to_pvar names.(i))))
  in
  Set.Poly.of_list (List.map pairs ~f:(fun (ps, ns) -> (to_p ps, to_p ns)))

(* [COAR_RECON_PRECHECK_OFF] set: the pass always builds the clause form, as
   before the pre-check; [COAR_RECON_PRECHECK_CROSSCHECK] set: where the
   pre-check refuses every candidate the pass still runs in full and says on
   stderr whether the full pass reconstructed nothing, as the pre-check
   claims *)
let precheck_off = Option.is_some (Sys.getenv "COAR_RECON_PRECHECK_OFF")

let precheck_crosscheck =
  Option.is_some (Sys.getenv "COAR_RECON_PRECHECK_CROSSCHECK")

(* [precheck_by_image ~compose pcsp] (the reference [precheck] is tested
   against; nothing else calls it) is [Some refusals] when every candidate of the
   pass is refused by a test that needs only the sort environment and the
   names form [clause_names_of], and [None] otherwise.  [refusals] gives each
   candidate with the reason found, in the signature's order.

   Contract: [Some _] only when the full pass (the clause form, [goal_markers]
   on it, [try_reconstruct] on every candidate, compositions included)
   reconstructs nothing.  The candidates here are the ordinary Bool-valued
   unknowns minus [markers'], a superset of the goal markers (below), so a
   full-pass candidate missing here is a nullary goal-marker suspect, which
   the full pass refuses by arity.  Each test implies a refusal by
   [try_reconstruct] in the full pass, whatever the order of the clauses:
     - arity below two: the same sort fact [try_reconstruct] tests first;
     - a names pair [(P, N)] with [rho] in [P] and an unknown of [P] or [N]
       other than [rho] outside [markers']: the clause it is the image of has
       [rho] in its head and that unknown among its atoms, and that unknown is
       no goal marker, so [role_of] refuses it (head with another unknown),
       or earlier for a pure-part occurrence.  With compositions an unknown
       already reconstructed would not count, but the first round starts with
       none reconstructed, and a later round runs only after a round has
       reconstructed something;
     - without compositions, a pair with [rho] in [N] but not in [P] and an
       unknown of [P] outside [markers']: the clause has [rho] in the body
       only and that unknown in its head, refused by [role_of].
   [role_of] maps every clause before any is read, so one refusing clause
   refuses the candidate.  Why [markers'] contains every goal marker: a goal
   marker is a nullary unknown such that every clause with it in the body
   has no head atom and exactly one body atom; the image of such a clause has
   an empty [P] and [N] equal to the marker's name alone, which is the test
   [markers'] makes on every pair.  The converse can fail only for a clause
   with two body atoms of the same nullary unknown, so [markers'] may hold
   more names, which only makes the tests above refuse less.

   Why: the clause form of a problem handed over as formulas can multiply
   into tens of thousands of clauses (a dual termination problem gave 29,973
   in 14 s) only for every candidate to be refused by one of these tests; the
   names form has at most one pair per distinct pair of name sets. *)
let precheck_by_image ~compose pcsp =
  let senv = PCSP.Problem.senv_of pcsp in
  (* the names form with each unknown named by an int ([clause_name_ids_of]):
     the tests below read only which unknowns each pair holds, so they give
     on it what they give on [clause_names_of]'s sets *)
  let names, pairs = clause_name_ids_of pcsp in
  let id_of = Hashtbl.Poly.create () in
  Array.iteri names ~f:(fun i x -> Hashtbl.Poly.set id_of ~key:x ~data:i);
  let nullary x =
    match Map.Poly.find senv x with
    | Some s -> List.is_empty (Logic.Sort.args_of s)
    | None -> false
  in
  (* [is_marker.(i)]: the unknown [names.(i)] is in [markers']; an unknown of
     the signature met in no pair is in [markers'] iff it is nullary *)
  let is_marker =
    Array.map names ~f:(fun g -> nullary g) |> fun a ->
    List.iter pairs ~f:(fun (ps, ns) ->
        if not (List.is_empty ps && List.length ns = 1) then
          List.iter ns ~f:(fun g -> a.(g) <- false));
    a
  in
  let in_markers v =
    match Hashtbl.Poly.find id_of v with
    | Some i -> is_marker.(i)
    | None -> nullary v
  in
  let candidates =
    Map.Poly.keys senv
    |> List.filter ~f:(fun v ->
        PCSP.Problem.is_bool_valued_ord_pred pcsp v && not (in_markers v))
  in
  let refusal v =
    let arity = List.length (Logic.Sort.args_of (Map.Poly.find_exn senv v)) in
    if arity < 2 then Some "arity below two"
    else
      match Hashtbl.Poly.find id_of v with
      | None ->
          (* [v] is in no pair, so no test below can fire *)
          None
      | Some rho ->
          let mem l = List.mem l rho ~equal:Int.equal in
          let counted p = p <> rho && not is_marker.(p) in
          if
            List.exists pairs ~f:(fun (ps, ns) ->
                mem ps
                && (List.exists ps ~f:counted || List.exists ns ~f:counted))
          then Some "a clause with it in the head mentions another unknown"
          else if
            (not compose)
            && List.exists pairs ~f:(fun (ps, ns) ->
                mem ns && (not (mem ps))
                && List.exists ps ~f:(fun p -> not is_marker.(p)))
          then Some "a clause with it in the body has another unknown in the head"
          else None
  in
  let rec all acc = function
    | [] -> Some (List.rev acc)
    | v :: vs -> (
        match refusal v with
        | Some why -> all ((Ident.tvar_to_pvar v, why) :: acc) vs
        | None -> None)
  in
  all [] candidates

(* [precheck ~compose pcsp]: [precheck_by_image ~compose pcsp], each test
   read off the facts of the names form ([clause_name_facts_of]) in place of
   its pairs.  Contract: the same result, raising where it raises.  Why the
   same: with [S] the set of pairs,
   - an unknown met is in [markers'] iff it is nullary and no pair holds it
     in its [N] other than [({}, {g})], that is iff it is nullary and not in
     [accompanied];
   - the first refusal asks for a pair with [rho] in [P] and some
     [x <> rho] outside [markers'] in [P + N]: an [x] of [pos_with rho];
   - the second asks for a pair with [rho] in [N], not in [P], and some [p]
     outside [markers'] in [P]: a [p] of [neg_only_with_pos rho] (which
     never holds [rho]);
   and the candidates, their order and the arity test do not read [S].
   Why: see [clause_name_facts_of]. *)
let precheck ~compose pcsp =
  let senv = PCSP.Problem.senv_of pcsp in
  let names, facts = clause_name_facts_of pcsp in
  let id_of = Hashtbl.Poly.create () in
  Array.iteri names ~f:(fun i x -> Hashtbl.Poly.set id_of ~key:x ~data:i);
  let nullary x =
    match Map.Poly.find senv x with
    | Some s -> List.is_empty (Logic.Sort.args_of s)
    | None -> false
  in
  let is_marker =
    Array.mapi names ~f:(fun i g ->
        nullary g && not (Set.mem facts.Logic.accompanied i))
  in
  let in_markers v =
    match Hashtbl.Poly.find id_of v with
    | Some i -> is_marker.(i)
    | None -> nullary v
  in
  let candidates =
    Map.Poly.keys senv
    |> List.filter ~f:(fun v ->
        PCSP.Problem.is_bool_valued_ord_pred pcsp v && not (in_markers v))
  in
  let related m rho =
    match Map.find m rho with
    | Some xs -> Set.exists xs ~f:(fun x -> not is_marker.(x))
    | None -> false
  in
  let refusal v =
    let arity = List.length (Logic.Sort.args_of (Map.Poly.find_exn senv v)) in
    if arity < 2 then Some "arity below two"
    else
      match Hashtbl.Poly.find id_of v with
      | None -> None
      | Some rho ->
          if related facts.Logic.pos_with rho then
            Some "a clause with it in the head mentions another unknown"
          else if (not compose) && related facts.Logic.neg_only_with_pos rho
          then Some "a clause with it in the body has another unknown in the head"
          else None
  in
  let rec all acc = function
    | [] -> Some (List.rev acc)
    | v :: vs -> (
        match refusal v with
        | Some why -> all ((Ident.tvar_to_pvar v, why) :: acc) vs
        | None -> None)
  in
  all [] candidates

(* Every function [f]'s body applies other than [f] itself, transitively. *)
let reached_others (fenv : FunEnv.t) f body =
  let rec close seen = function
    | [] -> seen
    | g :: rest when Set.mem seen g -> close seen rest
    | g :: rest -> (
        let seen = Set.add seen g in
        match Map.Poly.find fenv g with
        | Some (_, _, b, _, _) ->
            close seen (Set.to_list (applied_functions fenv b) @ rest)
        | None -> close seen rest)
  in
  Set.remove
    (close Set.Poly.empty (Set.to_list (applied_functions fenv body)))
    f

(* Whether [f] (in [fenv]) is total, given the set [total] of functions
   already proved total; [Error] with the reason otherwise. *)
let check_total ~(fenv : FunEnv.t) ~total f =
  match Map.Poly.find fenv f with
  | None -> Error "not a defined function"
  | Some (formals, sret, body, _, _) -> (
      let others = reached_others fenv f body in
      if Set.mem others f then Error "mutual recursion"
      else if not (Set.is_subset others ~of_:total) then
        Error "applies a function not proved total"
      else
        match calls_of_body ~f ~sret body with
        | exception Refuse why -> Error why
        | calls, _ -> (
            match
              find_measure ~fenv formals
                (List.map calls ~f:(fun c -> (c.path, c.args)))
            with
            | Some _ -> Ok ()
            | None -> Error "no decreasing measure proved"))

(* The input's recursive functions proved total, each after every other
   function its body applies. *)
let total_functions (fenv : FunEnv.t) =
  let rec fix total pending =
    let total', pending' =
      List.fold pending ~init:(total, []) ~f:(fun (total, acc) f ->
          let _, _, body, _, _ = Map.Poly.find_exn fenv f in
          let others = reached_others fenv f body in
          if Set.mem others f then (total, acc)
          else if Set.is_subset others ~of_:total then
            match check_total ~fenv ~total f with
            | Ok () -> (Set.add total f, acc)
            | Error _ -> (total, acc)
          else (total, f :: acc))
    in
    if Set.length total' > Set.length total then fix total' pending' else total'
  in
  fix Set.Poly.empty
    (Map.Poly.keys (Map.Poly.filter fenv ~f:(fun (_, _, _, r, _) -> r)))

(* ---------------------------------------------------------------------- *)
(* Lemmas                                                                  *)

(* candidate invariants over the formals and [v], the function's value *)
let lemma_candidates (formals : sort_env_list) (sret : Sort.t) v =
  let vars = List.map formals ~f:(fun (x, s) -> (Term.mk_var x s, s)) in
  if Term.is_int_sort sret then
    Formula.mk_atom (T_int.mk_geq v (T_int.zero ()))
    :: List.concat_map vars ~f:(fun (x, s) ->
        if Term.is_int_sort s then
          [
            Formula.mk_atom (T_int.mk_leq v x);
            Formula.mk_atom (T_int.mk_geq v x);
          ]
        else if T_seq.is_sseq s then
          let l = T_seq.mk_len (T_seq.elem_sort_of s) x in
          [
            Formula.mk_atom (T_int.mk_leq v l);
            Formula.mk_atom (T_int.mk_geq v l);
          ]
        else [])
  else if T_seq.is_sseq sret then
    let lv = T_seq.mk_len (T_seq.elem_sort_of sret) v in
    List.concat_map vars ~f:(fun (x, s) ->
        if T_seq.is_sseq s then
          let l = T_seq.mk_len (T_seq.elem_sort_of s) x in
          [
            Formula.mk_atom (T_int.mk_leq lv l);
            Formula.mk_atom (T_int.mk_geq lv l);
          ]
        else [])
  else if Term.is_bool_sort sret then
    let b = Formula.of_bool_term v in
    List.concat_map vars ~f:(fun (x, s) ->
        match sdt_of_sort s with
        | None -> []
        | Some dt ->
            List.concat_map (Datatype.conses_of dt) ~f:(fun cons ->
                let is_c =
                  Formula.mk_atom
                  @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) x
                in
                [
                  Formula.mk_imply is_c b;
                  Formula.mk_imply is_c (Formula.mk_neg b);
                ]))
  else []

(* The candidate invariant over [formals] and [v] (the value of [f] at the
   formals) that a user lemma [forall ys. phi] states about [f], or [Error]
   with the reason it is not one.  It is one when every application of [f] in
   [phi] is the same application [f(y_1' .. y_n')] to distinct variables that
   are exactly [ys] (in any order, at the formals' sorts), every other
   function [phi] applies is in [total] (a validity question that declares a
   function not proved total proves nothing), and [phi] has no free variable
   but [ys]; the invariant is [phi] with that application replaced by [v] and
   each [y_i'] by the [i]-th formal.  Not a source of soundness: whatever
   formula this returns is proved by induction before it is used, and an
   unproved one is dropped. *)
let user_candidate ~(fenv : FunEnv.t) ~total f (formals : sort_env_list) v
    ((ys, phi) : sort_env_list * Formula.t) =
  let ( let* ) = Result.( >>= ) in
  let apps = Set.to_list (Formula.fvar_apps_of phi) in
  let is_f = function
    | Term.FunApp (FVar (g, _, _), _, _) -> Ident.tvar_equal g f
    | _ -> false
  in
  let* args =
    match List.filter apps ~f:is_f with
    | [] -> Error "does not apply the function"
    | Term.FunApp (_, args, _) :: rest ->
        let vars_of args =
          List.map args ~f:(function Term.Var (y, _, _) -> Some y | _ -> None)
        in
        let names = vars_of args in
        if
          List.for_all rest ~f:(function
            | Term.FunApp (_, args', _) ->
                Stdlib.(vars_of args' = names) && List.for_all names ~f:Option.is_some
            | _ -> false)
          && List.for_all names ~f:Option.is_some
        then Ok args
        else Error "applies the function to anything but its own variables"
    | _ -> Error "unexpected application"
  in
  let names = List.filter_map args ~f:(function Term.Var (y, _, _) -> Some y | _ -> None) in
  let* () =
    if
      List.length names = List.length formals
      && List.length names = List.length ys
      && (not (List.contains_dup names ~compare:Ident.tvar_compare))
      && List.for_all names ~f:(fun y ->
          List.exists ys ~f:(fun (y', _) -> Ident.tvar_equal y y'))
      && List.for_all2_exn args formals ~f:(fun a (_, s) ->
          Stdlib.(Term.sort_of a = s))
    then Ok ()
    else Error "its variables are not the function's arguments"
  in
  let* () =
    if
      List.for_all apps ~f:(function
        | Term.FunApp (FVar (g, _, _), _, _) ->
            Ident.tvar_equal g f || Set.mem total g
        | _ -> true)
    then Ok ()
    else Error "applies a function not proved total"
  in
  let* () =
    let free =
      Set.filter (Formula.tvs_of phi) ~f:(fun x ->
          (not (Ident.tvar_equal x f)) && not (Map.Poly.mem fenv x))
    in
    if Set.for_all free ~f:(fun x -> List.mem names x ~equal:Ident.tvar_equal)
    then Ok ()
    else Error "mentions a variable it does not bind"
  in
  let replaced =
    Formula.map_term phi ~f:(fun t -> if is_f t then v else t)
  in
  Ok
    (Formula.subst
       (Map.Poly.of_alist_exn
          (List.map2_exn names formals ~f:(fun y (x, s) -> (y, Term.mk_var x s))))
       replaced)

(* The user lemmas of [get_user_lemmas] that are candidate invariants of
   [f] (see [user_candidate]), each with its source; the others are
   reported through [print] and ignored. *)
let user_candidates ?(print = fun (_ : string lazy_t) -> ()) ~fenv ~total f
    formals v =
  List.filter_map (get_user_lemmas ()) ~f:(fun ((ys, phi) as lemma) ->
      let mentions_f =
        Set.exists (Formula.fvar_apps_of phi) ~f:(function
          | Term.FunApp (FVar (g, _, _), _, _) -> Ident.tvar_equal g f
          | _ -> false)
      in
      if not mentions_f then None
      else
        match user_candidate ~fenv ~total f formals v lemma with
        | Ok inv -> Some (Formula.mk_forall ys phi, inv)
        | Error why ->
            print
              (lazy
                (sprintf "[recon] user lemma %s ignored for %s: %s"
                   (Formula.str_of (Formula.mk_forall ys phi))
                   (Ident.name_of_tvar f) why));
            None)

(* The largest jointly inductive subset of the candidates of a total [f]:
   the built-in candidates when [builtin], and [user]'s candidates (each
   paired with the lemma it came from) given the value variable.  A user
   candidate that is not kept is reported through [print]; one that is kept
   is in the result like any other. *)
let prove_lemmas ?(print = fun (_ : string lazy_t) -> ()) ?(builtin = true)
    ?(user = fun _ -> []) ~(fenv : FunEnv.t) f =
  let formals, sret, body, _, _ = Map.Poly.find_exn fenv f in
  match calls_of_body ~f ~sret body with
  | exception Refuse _ -> []
  | calls, abstracted ->
      let v = Ident.mk_fresh_tvar () in
      let vterm = Term.mk_var v sret in
      let user = user vterm in
      let cands =
        List.map user ~f:snd
        @ (if builtin then lemma_candidates formals sret vterm else [])
        |> List.fold ~init:[] ~f:(fun acc c ->
               if
                 List.exists acc ~f:(fun c' ->
                     try Stdlib.(c = c') with Invalid_argument _ -> false)
               then acc
               else c :: acc)
        |> List.rev
      in
      let inst inv args value =
        Formula.subst
          (Map.Poly.of_alist_exn
             ((v, value)
             :: List.map2_exn formals args ~f:(fun (x, _) a -> (x, a))))
          inv
      in
      let self_args = List.map formals ~f:(fun (x, s) -> Term.mk_var x s) in
      (* the body without [f]: the questions must not declare it *)
      let fenv' = Map.Poly.remove fenv f in
      let rec fix cur =
        let hyp =
          Formula.and_of
          @@ List.map calls ~f:(fun c ->
              Formula.mk_imply c.path
                (Formula.and_of
                   (List.map cur ~f:(fun inv ->
                        inst inv c.args (Term.mk_var c.r sret)))))
        in
        let kept =
          List.filter cur ~f:(fun inv ->
              valid ~fenv:fenv'
                (Formula.mk_imply hyp (inst inv self_args abstracted)))
        in
        if List.length kept = List.length cur then cur else fix kept
      in
      let kept = if List.is_empty cands then [] else fix cands in
      List.iter user ~f:(fun (src, inv) ->
          let proved =
            List.exists kept ~f:(fun k ->
                try Stdlib.(k = inv) with Invalid_argument _ -> false)
          in
          print
            (lazy
              (sprintf "[recon] user lemma %s %s for %s" (Formula.str_of src)
                 (if proved then "proved" else "not proved (ignored)")
                 (Ident.name_of_tvar f))));
      if List.is_empty kept then []
      else
        let sargs = List.map formals ~f:snd in
        let at args =
          List.map kept ~f:(fun inv ->
              inst inv args (Term.mk_fvar_app f sargs sret args))
        in
        at self_args @ List.concat_map calls ~f:(fun c -> at c.orig_args)

(* [prop] (the existing property of [f], [forall formals. phi] or [true])
   with [extra] conjoined, as one universal over [formals] *)
let extend_property formals prop extra =
  let old =
    if Formula.is_bind prop then
      let _, env, phi, _ = Formula.let_bind prop in
      if List.length env = List.length formals then
        Formula.subst
          (Map.Poly.of_alist_exn
             (List.map2_exn env formals ~f:(fun (y, _) (x, s) ->
                  (y, Term.mk_var x s))))
          phi
      else Formula.mk_true ()
    else Formula.mk_true ()
  in
  (* a lemma already among the property's conjuncts is not added again, so a
     second pass over a property an earlier pass extended returns it as it
     is, rather than conjoining the same lemmas once more at every pass *)
  let present = Formula.conjuncts_list_of old in
  let extra =
    List.filter extra ~f:(fun e ->
        not
          (List.exists present ~f:(fun c ->
               try Poly.equal c e with Invalid_argument _ -> false)))
  in
  if List.is_empty extra && Formula.is_bind prop then prop
  else Formula.mk_forall formals (Formula.and_of (old :: extra))

(* ---------------------------------------------------------------------- *)
(* The pass                                                                *)

(* Names the template and the Houdini pre-pass read their vocabulary from,
   and the vocabulary limit; set once, by the solver, before solving. *)
let qual_limit = Atomic.make 0

(* [COAR_RECON_TRACE] set: the pass says on stderr what it reconstructed,
   refused (and why) and proved, whatever the solver's tracing *)
let trace = Option.is_some (Sys.getenv "COAR_RECON_TRACE")

(* the passes this process has run, over every solver instance (MuVal's
   primal and dual included); read only by the solver's census exit
   [COAR_RECON_EXIT] *)
let census_passes = Atomic.make 0

(* this pass's own counters for [reconstruct ~names_apart:true]: the
   replay scopes and the function names drawn under it *)
let scope_count = Atomic.make 0
let fname_count = Atomic.make 0

(* [cl] with every body atom [q(a, w)] of a reconstruction [r] in [known]
   read as the equation [w = g(a)], [g] being [r]'s function; the other
   atoms stay.  Used on [rho]'s defining clauses only (COMPOSITIONS at the
   top), where [known] holds exhaustive reconstructions only, whose
   unknowns' least solutions are the graphs of their functions *)
let inline_known (known : reconstructed list)
    ((uni_senv, ps, ns, phi) : ClauseOld.t) : ClauseOld.t =
  if List.is_empty known then (uni_senv, ps, ns, phi)
  else
    let find p = List.find known ~f:(fun r -> Ident.pvar_equal r.pvar p) in
    let ns', extra =
      Set.fold ns ~init:([], []) ~f:(fun (keep, extra) a ->
          match Option.bind (pvar_of_atom a) ~f:find with
          | Some r ->
              let args = args_of_atom a in
              let app =
                Term.mk_fvar_app r.fname
                  (List.map r.formals ~f:snd)
                  r.sret (List.drop_last_exn args)
              in
              ( keep,
                Formula.mk_neg (Formula.eq (List.last_exn args) app) :: extra )
          | None -> (a :: keep, extra))
    in
    if List.is_empty extra then (uni_senv, ps, ns, phi)
    else (uni_senv, ps, Set.Poly.of_list ns', Formula.or_of (phi :: extra))

let try_reconstruct ?(result_guards = false) ?(compose = false)
    ?(known = []) ~fenv ~total pcsp (clauses : ClauseOld.t list) ~markers rho
    =
  let tv = Ident.pvar_to_tvar rho in
  let sort = Map.Poly.find_exn (PCSP.Problem.senv_of pcsp) tv in
  let sorts = List.map (Logic.Sort.args_of sort) ~f:Logic.ExtTerm.to_old_sort in
  if List.length sorts < 2 then refuse "arity below two";
  let known =
    if compose then
      List.filter known ~f:(fun r ->
          r.exhaustive && not (Ident.pvar_equal r.pvar rho))
    else []
  in
  let known_pvars = Set.Poly.of_list (List.map known ~f:(fun r -> r.pvar)) in
  let roles =
    List.map clauses ~f:(fun c ->
        (role_of ~compose ~known:known_pvars ~markers rho c, c))
  in
  let defining =
    List.filter_map roles ~f:(function
      | Defining, c -> Some (inline_known known c)
      | _ -> None)
  in
  if List.is_empty defining then refuse "no defining clause";
  let formals =
    List.map (List.drop_last_exn sorts) ~f:(fun s ->
        (Ident.mk_fresh_tvar (), s))
  in
  let sret = List.last_exn sorts in
  let branches =
    List.concat_map defining ~f:(normalise ~result_guards ~formals)
  in
  if List.is_empty branches then refuse "no satisfiable defining clause";
  (* a guard that tests a call's result is asked about with the call in place
     of the result, the function read as a symbol no environment defines: a
     validity proved for every interpretation of that symbol holds for the
     function.  The name is chosen locally, drawing no fresh name *)
  let qguard =
    let calls_sym =
      let base = "#recon_calls_" ^ Ident.name_of_pvar rho in
      let rec choose k =
        let v = Ident.Tvar (if k = 0 then base else sprintf "%s!%d" base k) in
        if Map.Poly.mem fenv v then choose (k + 1) else v
      in
      choose 0
    in
    let sargs = List.map formals ~f:snd in
    fun b -> guard_with_calls ~fname:calls_sym ~sargs ~sret b
  in
  let guards = List.map branches ~f:qguard in
  let rec pairs = function
    | [] -> []
    | g :: gs -> List.map gs ~f:(fun h -> (g, h)) @ pairs gs
  in
  (* two branches may overlap only where neither recurses and their results
     are proved equal there: the clauses then still describe one value at
     each argument, and the [ite] below takes the first branch, whose result
     is the other's on the overlap *)
  if
    not
      (List.for_all (pairs branches) ~f:(fun (b1, b2) ->
           valid ~fenv
             (Formula.mk_neg (Formula.and_of [ qguard b1; qguard b2 ]))
           || List.is_empty b1.calls && List.is_empty b2.calls
              && valid ~fenv
                   (Formula.mk_imply
                      (Formula.and_of [ b1.guard; b2.guard ])
                      (Formula.eq b1.result b2.result))))
  then refuse "guards not proved mutually exclusive";
  (* where the guards miss a case, the clauses describe a PARTIAL function:
     the definition is completed by a default value of an integer, real or
     Boolean result (the function is then vocabulary only and is never put in
     the place of the unknown, whose least solution is false there) *)
  let exhaustive = valid ~fenv (Formula.or_of guards) in
  (* the default value of a partial function; its branch is appended once
     the function's name is drawn (below), so that its guard -- the negation
     of the others, each with its calls' values written as calls of the
     function itself -- names the function and not the symbol the questions
     above use *)
  let default =
    if exhaustive then None
    else if Term.is_int_sort sret then Some (T_int.zero ())
    else if Term.is_real_sort sret then Some (T_real.rzero ())
    else if Term.is_bool_sort sret then Some (T_bool.mk_false ())
    else refuse "guards not proved exhaustive"
  in
  (* functions applied by the guards or results must be total already *)
  let applied =
    Set.Poly.union_list
    @@ List.concat_map branches ~f:(fun b ->
        Set.Poly.filter_map (Formula.fvar_apps_of b.guard) ~f:(function
          | Term.FunApp (FVar (g, _, _), _, _) when Map.Poly.mem fenv g ->
              Some g
          | _ -> None)
        :: applied_functions fenv b.result
        :: List.map b.calls ~f:(fun (_, args) ->
            Set.Poly.union_list (List.map args ~f:(applied_functions fenv))))
  in
  if not (Set.is_empty applied || Set.is_subset applied ~of_:(total ())) then
    refuse "a definition applies a function not proved total";
  (* totality: calls' arguments decrease under the call-free part of their
     own branch's guard (the whole guard unless it tests a call's result; a
     call the guard evaluates is reached only where that part holds); a
     result variable of an earlier call is any value *)
  let calls =
    List.concat_map branches ~f:(fun b ->
        List.map b.calls ~f:(fun (_, args) -> (b.call_free, args)))
  in
  (match find_measure ~fenv formals calls with
  | None -> refuse "no decreasing measure proved (not shown total)"
  | Some _ -> ());
  let taken v =
    Map.Poly.mem fenv v || Map.Poly.mem (PCSP.Problem.senv_of pcsp) v
  in
  let fname =
    let prefix = "recon_" ^ Ident.name_of_pvar rho ^ "_" in
    if Ident.replaying_fresh_names () then
      (* names apart: numbered by this pass's own counter, so the draw moves
         no process-global counter; [taken] keeps it fresh against the
         environments, and the prefix ends in [_] followed by digits and [a],
         which no global draw ([prefix] followed by digits) spells *)
      let rec draw () =
        let v =
          Ident.Tvar
            (sprintf "%s%da" prefix (Atomic.fetch_and_add fname_count 1))
        in
        if taken v then draw () else v
      in
      draw ()
    else Ident.mk_fresh_tvar_avoiding ~prefix ~taken ()
  in
  let branches =
    match default with
    | None -> branches
    | Some result ->
        let sargs = List.map formals ~f:snd in
        let guard =
          Formula.mk_neg
            (Formula.or_of
               (List.map branches ~f:(guard_with_calls ~fname ~sargs ~sret)))
        in
        branches @ [ { guard; call_free = guard; calls = []; result } ]
  in
  let body = build_body ~fname ~formals ~sret branches in
  (* Clause-variable elimination must cover Boolean predicate aliases too.
     Never drop the defining clauses for a body with an escaped variable. *)
  if not (Evaluator.known_function_body_is_closed formals body) then
    refuse "a clause variable remains free in the reconstructed body";
  { pvar = rho; fname; formals; sret; body; branches; exhaustive }

(* the clause [cl] with every [rho(a, b)] of [r] in its body read as
   [b = f(a)], as a formula *)
let replace_in_clause (rs : reconstructed list)
    ((uni_senv, ps, ns, phi) : ClauseOld.t) =
  let find p = List.find rs ~f:(fun r -> Ident.pvar_equal r.pvar p) in
  let ns', extra =
    Set.fold ns ~init:([], []) ~f:(fun (keep, extra) a ->
        match Option.bind (pvar_of_atom a) ~f:find with
        | Some r ->
            let args = args_of_atom a in
            let app =
              Term.mk_fvar_app r.fname
                (List.map r.formals ~f:snd)
                r.sret (List.drop_last_exn args)
            in
            (keep, Formula.mk_neg (Formula.eq (List.last_exn args) app) :: extra)
        | None -> (a :: keep, extra))
  in
  let senv, phi' =
    ClauseOld.to_formula
      (uni_senv, ps, Set.Poly.of_list ns', Formula.or_of (phi :: extra))
  in
  (Map.Poly.map senv ~f:Logic.ExtTerm.to_old_sort, phi')

(* [equal_existing ~fenv ~total r]: a function [g] of [fenv], other than
   [r.fname], with [r]'s argument and result sorts, proved total ([total ()],
   forced only when some [g] has those sorts), such that

     forall x. body_g(x) = body_r(x)[f := g]

   is valid with [f] and [g] both read as ONE UNINTERPRETED function symbol
   (a name no environment defines).  Then [g = f] in every model: [f] is
   total, so its defining equation [forall x. f(x) = body_r(x)] has exactly
   one solution in each model (WHY TOTALITY, at the top); [g], interpreted by
   its own definition, satisfies [g(x) = body_g(x)], hence by the validity,
   which holds for every interpretation of the symbol and so for [g]'s,
   [g(x) = body_r(x)[f := g]]: [g] solves [f]'s equation and is therefore
   [f].  The question needs no induction (each side is one unfolding, the
   calls compared as opaque values).  A generated size function is never
   [g].  [None] when no such [g] exists or a question is undecided (an
   undecided question counts as not proved).  Draws no fresh name. *)
let equal_existing ~(fenv : FunEnv.t) ~total (r : reconstructed) =
  let same_sorts (gformals, gsret) =
    List.length gformals = List.length r.formals
    &&
    try
      Stdlib.( = ) (List.map gformals ~f:snd) (List.map r.formals ~f:snd)
      && Stdlib.( = ) gsret r.sret
    with Invalid_argument _ -> false
  in
  let function_names symbols =
    Set.Poly.filter_map symbols ~f:(function
      | FVar (name, _, _) -> Some name
      | _ -> None)
  in
  let term_names term =
    Set.union (function_names (Term.funsyms_of term))
      (Set.Poly.map (Term.pvs_of term) ~f:Ident.pvar_to_tvar)
  in
  let formula_names phi =
    Set.union (function_names (Formula.funsyms_of phi))
      (Set.Poly.map (Formula.pvs_of phi) ~f:Ident.pvar_to_tvar)
  in
  let taken =
    Set.Poly.union_list
      (Set.add (Map.key_set fenv) r.fname :: term_names r.body
       :: Set.Poly.of_list (List.map r.formals ~f:fst)
       :: List.map (Map.Poly.data fenv) ~f:(fun (formals, _, body, _, property) ->
              Set.Poly.union_list
                [term_names body; formula_names property;
                 Set.Poly.of_list (List.map formals ~f:fst)]))
  in
  Map.Poly.to_alist fenv
  |> List.filter ~f:(fun (g, (gformals, gsret, _, isrec, _)) ->
         isrec
         && (not (Ident.tvar_equal g r.fname))
         (* a generated size function is no vocabulary (the hypothesis space
            skips it), so taking it for [r]'s function would drop that
            function from the space instead of a duplicate *)
         && (not (Ident.is_size_fun_var g))
         && same_sorts (gformals, gsret))
  |> List.find_map ~f:(fun (g, (gformals, _, gbody, _, _)) ->
         let compared_functions = Set.Poly.of_list [g; r.fname] in
         let background_heads = Set.union
           (function_names (Term.funsyms_of gbody))
           (function_names (Term.funsyms_of r.body)) in
         let substitution_domains = Set.union compared_functions background_heads in
         let formal_function_collision =
           List.exists (gformals @ r.formals) ~f:(fun (x, _) ->
             Set.mem substitution_domains x)
         in
         (* The first-order function-substitution API also accepts raw term
            variables at nullary keys. A formal spelled like a compared
            function cannot safely be fed to it as a naked body. Refuse only
            identification: reconstruction keeps its own certified function.
            Also reject a formal matching any background function head: the
            term substitution used to align formals renames FVar heads too,
            and could otherwise equate two distinct background functions.
            This conservative guard preserves the no-fresh-name contract. *)
         if formal_function_collision || not (Set.mem (total ()) g) then None
         else
           let h =
             let base =
               sprintf "#recon_equal(%s,%s)" (Ident.name_of_tvar g)
                 (Ident.name_of_tvar r.fname)
             in
             (* The induction hypothesis must be an independent symbol, not
                a user definition or an existing background application.
                Search locally so the process's fresh-name stamp stays put. *)
             let rec choose suffix =
               let name =
                 Ident.Tvar
                   (if suffix = 0 then base else base ^ "!" ^ Int.to_string suffix)
               in
               if Set.mem taken name then choose (suffix + 1) else name
             in
             choose 0
           in
           let sargs = List.map r.formals ~f:snd in
           let as_h formals =
             ( formals,
               Term.mk_fvar_app h sargs r.sret
                 (List.map formals ~f:(fun (x, s) -> Term.mk_var x s)) )
           in
           let fsub =
             Map.Poly.of_alist_exn
               [ (r.fname, as_h r.formals); (g, as_h gformals) ]
           in
           let to_r =
             Map.Poly.of_alist_exn
               (List.map2_exn gformals r.formals ~f:(fun (x, _) (y, s) ->
                    (x, Term.mk_var y s)))
           in
           let lhs = Term.subst to_r (Term.subst_funcs fsub gbody) in
           let rhs = Term.subst_funcs fsub r.body in
           let fenv' = Map.Poly.remove (Map.Poly.remove fenv g) r.fname in
           if valid ~fenv:fenv' (Formula.eq lhs rhs) then Some g else None)

(* [reconstruct ~replace ~lemmas pcsp]: the pass stated at the top.

   [~names_apart:true] runs it with its fresh names drawn apart from the
   process: every unprefixed term-variable draw is [Ident]'s replay under a
   scope of this pass's own ([#recfun<k>r], [k] from [scope_count]), and the
   function names are numbered by [fname_count].  Contract: the result is the
   one [~names_apart:false] gives up to the names this pass draws (each such
   name is bound in a definition, a property or an eliminated solution, or is
   a function name kept fresh by [taken]), and the process-global term
   variable counter is where it was before the call -- so the rest of the
   run draws the names it would have drawn had the pass not run.  Why: a
   moved counter reorders the conjuncts Z3 is given for the whole remaining
   run, which can turn a run answered in a second into one whose validation
   question never returns.  Other counters (predicate variables, dummies)
   are not detached; the trace reports how far the global fresh stamp
   moved (0 on the inputs tried). *)
let rec reconstruct ?(print = fun (_ : string lazy_t) -> ())
    ?(names_apart = false) ?(user_lemmas = false) ?(reuse_equal = false)
    ?(result_guards = false) ?(compositions = false) ~functions ~replace
    ~lemmas pcsp =
  if names_apart && not (Ident.replaying_fresh_names ()) then (
    let before = Ident.fresh_stamp () in
    let scope = sprintf "#recfun%dr" (Atomic.fetch_and_add scope_count 1) in
    let out =
      Ident.with_replayed_fresh_names ~scope (fun () ->
          reconstruct ~print ~names_apart:false ~user_lemmas ~reuse_equal
            ~result_guards ~compositions ~functions ~replace ~lemmas pcsp)
    in
    if trace then
      eprintf "[recon] names apart: global fresh stamp moved by %d\n%!"
        (Ident.fresh_stamp () - before);
    out)
  else
    reconstruct_aux ~print ~user_lemmas ~reuse_equal ~result_guards
      ~compositions ~functions ~replace ~lemmas pcsp

and reconstruct_aux ~print ~user_lemmas ~reuse_equal ~result_guards
    ~compositions ~functions ~replace ~lemmas pcsp =
  let print l =
    print l;
    if trace then eprintf "%s\n%!" (Lazy.force l)
  in
  let params = PCSP.Problem.params_of pcsp in
  let fenv0 =
    Map.force_merge params.PCSP.Params.fenv (get_fenv ()) ~catch_dup:ignore
      ~equal:(fun _ _ -> true)
  in
  (* asked only when needed: by a guard that applies an input function, and
     by the lemmas *)
  let input_total = lazy (total_functions fenv0) in
  (* the clause form is built only when a candidate survives [precheck]
     (or the pass reconstructs something and replaces it): without
     candidates nothing reads it, and where [precheck] refuses every
     candidate the full pass would have reconstructed nothing *)
  let clauses =
    lazy
      (let started = Core_unix.gettimeofday () in
       let clauses = clauses_of pcsp in
       if trace then
         eprintf "[recon] clause form: %d clauses in %.3f s\n%!"
           (List.length clauses)
           (Core_unix.gettimeofday () -. started);
       clauses)
  in
  let senv = PCSP.Problem.senv_of pcsp in
  let markers = lazy (goal_markers (Lazy.force clauses) senv) in
  let decided =
    if not functions then Some []
    else if precheck_off then None
    else
      let started = Core_unix.gettimeofday () in
      let decided =
        try precheck ~compose:compositions pcsp
        with exn when not (Common.Timer.is_async exn) -> None
      in
      if trace then
        eprintf "[recon] pre-check: %s in %.3f s\n%!"
          (match decided with
          | Some r -> sprintf "every candidate refused (%d)" (List.length r)
          | None -> "a candidate survives")
          (Core_unix.gettimeofday () -. started);
      decided
  in
  let full = Option.is_none decided || precheck_crosscheck in
  let candidates =
    if not (functions && full) then []
    else
      let markers = Lazy.force markers in
      Map.Poly.keys senv
      |> List.filter ~f:(fun v ->
          PCSP.Problem.is_bool_valued_ord_pred pcsp v
          && not (Set.mem markers (Ident.tvar_to_pvar v)))
      |> List.map ~f:Ident.tvar_to_pvar
  in
  let fenv = ref fenv0 and recon_total = ref Set.Poly.empty in
  let total () = Set.union (Lazy.force input_total) !recon_total in
  let recon = ref [] and refused = ref [] and aliased = ref [] in
  (* [compositions]: the unknowns whose eligibility needed the relaxed roles
     (COMPOSITIONS at the top); their reconstructions are vocabulary only *)
  let relaxed = ref Set.Poly.empty in
  let strictly_eligible rho =
    let markers = Lazy.force markers in
    List.for_all (Lazy.force clauses) ~f:(fun c ->
        match role_of ~markers rho c with
        | _ -> true
        | exception Refuse _ -> false)
  in
  let attempt rho =
      match
        try_reconstruct ~result_guards ~compose:compositions
          ~known:(!recon @ !aliased) ~fenv:!fenv ~total pcsp
          (Lazy.force clauses) ~markers:(Lazy.force markers) rho
      with
      | r -> (
          match
            if reuse_equal then equal_existing ~fenv:!fenv ~total r else None
          with
          | Some g ->
              (* [reuse_equal]: [r]'s function is one the environment already
                 has ([equal_existing] proves them equal in every model), so
                 that function is [rho]'s reconstruction and no name is added;
                 the record keeps [r]'s formals, branches and body, the
                 body's recursive calls renamed to [g] *)
              print
                (lazy
                  (sprintf "[recon] %s reconstructed as %s, equal to %s"
                     (Ident.name_of_pvar rho) (Ident.name_of_tvar r.fname)
                     (Ident.name_of_tvar g)));
              let to_g =
                Map.Poly.singleton r.fname
                  ( r.formals,
                    Term.mk_fvar_app g
                      (List.map r.formals ~f:snd)
                      r.sret
                      (List.map r.formals ~f:(fun (x, s) -> Term.mk_var x s))
                  )
              in
              aliased :=
                { r with fname = g; body = Term.subst_funcs to_g r.body }
                :: !aliased
          | None ->
              print
                (lazy
                  (sprintf "[recon] %s reconstructed as %s = %s"
                     (Ident.name_of_pvar rho)
                     (Ident.name_of_tvar r.fname)
                     (Term.str_of r.body)));
              fenv :=
                Map.Poly.set !fenv ~key:r.fname
                  ~data:(r.formals, r.sret, r.body, true, Formula.mk_true ());
              recon_total := Set.add !recon_total r.fname;
              recon := r :: !recon)
      | exception Refuse why ->
          print
            (lazy
              (sprintf "[recon] %s refused: %s" (Ident.name_of_pvar rho) why));
          refused := (rho, why) :: !refused
  in
  (* without [compositions], one pass in the signature's order, as before;
     with it, the refused unknowns are tried again while a pass reconstructs
     something, so that an unknown is read through the functions of the
     unknowns its defining clauses apply, reconstructed in an earlier pass
     (dependency order); at most one pass per candidate *)
  let rec passes todo =
    refused := [];
    let before = List.length !recon + List.length !aliased in
    List.iter todo ~f:attempt;
    let progressed = List.length !recon + List.length !aliased > before in
    if compositions && progressed && not (List.is_empty !refused) then
      passes (List.rev_map !refused ~f:fst)
  in
  passes candidates;
  let image_matches () =
    let image =
      Set.Poly.of_list
      @@ List.map (Lazy.force clauses) ~f:(fun (_, ps, ns, _) ->
          ( Set.canon (Set.Poly.filter_map ps ~f:pvar_of_atom),
            Set.canon (Set.Poly.filter_map ns ~f:pvar_of_atom) ))
    in
    Set.equal image (clause_names_of pcsp)
  in
  (match decided with
  | Some refusals when not full ->
      List.iter refusals ~f:(fun (rho, why) ->
          print
            (lazy
              (sprintf "[recon] %s refused: %s" (Ident.name_of_pvar rho) why)));
      refused := refusals
  | Some refusals ->
      (* [precheck_crosscheck]: the full pass ran; the pre-check's claim is
         that it reconstructed nothing *)
      let names l = Set.Poly.of_list (List.map l ~f:fst) in
      eprintf
        "[recon-precheck-crosscheck] names form equals image %b; precheck \
         refused %d; full reconstructed %d refused %d; same refused set %b; \
         claim %s\n%!"
        (image_matches ())
        (List.length refusals)
        (List.length !recon + List.length !aliased)
        (List.length !refused)
        (Set.equal (names refusals) (names !refused))
        (if List.is_empty !recon && List.is_empty !aliased then "holds"
         else "VIOLATED")
  | None ->
      (* [precheck_crosscheck] where a candidate survived: the names form
         against the image of the clauses built *)
      if precheck_crosscheck && functions && not precheck_off then
        eprintf "[recon-precheck-crosscheck] undecided; names form equals \
                 image %b\n%!" (image_matches ()));
  if compositions then
    relaxed :=
      Set.Poly.of_list
        (List.filter_map (!recon @ !aliased) ~f:(fun r ->
             if strictly_eligible r.pvar then None else Some r.pvar));
  (* [user_lemmas]: the lemmas the input states ([get_user_lemmas]) are
     tried too, whether or not the built-in candidates are; a function with
     a user lemma also gets the built-in candidates, which are what makes
     most user lemmas inductive (a lemma [is_nil x \/ length x > 0] holds
     inductively only together with [length x >= 0]) *)
  let user_lemmas =
    user_lemmas && not (List.is_empty (get_user_lemmas ()))
  in
  let total = if lemmas || user_lemmas then total () else !recon_total in
  let recon = List.rev !recon and aliased = List.rev !aliased in
  (* Retain factory size entries verbatim. Extending their properties loses
     the factory certificate and needlessly ties them to a proof-registration
     snapshot. Match full entries, not the SizeOf_ spelling of a user function. *)
  let generated_sizes =
    if not (lemmas || user_lemmas) then Set.Poly.empty
    else
      Map.Poly.data (get_dtenv ())
      |> List.filter ~f:(Fn.non Datatype.is_poly)
      |> List.map ~f:Datatype.size_fun_of
      |> Map.Poly.of_alist_multi
      |> Map.Poly.filteri ~f:(fun ~key:f ~data:expected ->
             match Map.Poly.find !fenv f with
             | None -> false
             | Some actual ->
                 (try List.for_all expected ~f:(Poly.equal actual)
                  with Invalid_argument _ -> false))
      |> Map.key_set
  in
  (* lemmas for total user/reconstructed functions, preserving factory sizes *)
  let lemma_list =
    if not (lemmas || user_lemmas) then []
    else
      List.filter_map (Set.to_list (Set.diff total generated_sizes)) ~f:(fun f ->
          let user v =
            if not user_lemmas then []
            else
              let formals, _, _, _, _ = Map.Poly.find_exn !fenv f in
              user_candidates ~print ~fenv:!fenv ~total f formals v
          in
          let has_user =
            user_lemmas
            && List.exists (get_user_lemmas ()) ~f:(fun (_, phi) ->
                Set.exists (Formula.fvar_apps_of phi) ~f:(function
                  | Term.FunApp (FVar (g, _, _), _, _) -> Ident.tvar_equal g f
                  | _ -> false))
          in
          if not (lemmas || has_user) then None
          else
          match
            prove_lemmas ~print ~builtin:true ~user ~fenv:!fenv f
          with
          | [] -> None
          | invs ->
              print
                (lazy
                  (sprintf "[recon] lemmas for %s: %s" (Ident.name_of_tvar f)
                     (String.concat_map_list ~sep:"; " invs ~f:Formula.str_of)));
              Some (f, invs))
  in
  let previous_context_is_total =
    let previous = !fenv in
    lazy (Z3Smt.Z3interface.has_total_defining_context ~id:None previous)
  in
  let proved_properties = ref [] in
  let fenv_final =
    List.fold lemma_list ~init:!fenv ~f:(fun fenv (f, invs) ->
        Map.Poly.update fenv f ~f:(function
          | Some (formals, sret, body, r, prop) ->
              let prop' = extend_property formals prop invs in
              (* The whole new property is proved when the old one was
                 [true]: each lemma holds of the standard interpretation by
                 well-founded induction on the measure [total] found.  An old
                 property that is not [true] need not have been proved, so it
                 cannot be trusted alone. A universally quantified [true]
                 also counts as trivial. A nontrivial old property can be
                 retained when the complete old context is certified: all
                 premises of this batch then hold of its standard functions.
                 Checking the whole context retains the proof dependencies.
                 Exact factory size functions are excluded
                 above, so this fold preserves their built-in certificate. *)
              let trivially_true =
                Formula.is_true prop
                || Formula.is_bind prop
                   &&
                   let _, _, body, _ = Formula.let_bind prop in
                   Formula.is_true body
              in
              if trivially_true || Lazy.force previous_context_is_total then
                proved_properties := (f, prop') :: !proved_properties;
              (formals, sret, body, r, prop')
          | None -> assert false))
  in
  (* All lemmas were proved against the same original environment. Register
     their completed batch together, retaining every definition and property
     used by those proofs; an intermediate fold state is not that context. *)
  List.iter !proved_properties ~f:(fun (f, prop) ->
      Z3Smt.Z3interface.register_proved_property ~fenv:fenv_final f prop);
  (* the problem's own environment: its entries, updated, and the new ones *)
  let changed =
    Map.Poly.filter_mapi fenv_final ~f:(fun ~key ~data ->
        if
          Map.Poly.mem params.PCSP.Params.fenv key
          || List.exists (recon @ aliased) ~f:(fun r ->
                 Ident.tvar_equal r.fname key)
        then Some data
        else None)
  in
  let global_changed =
    Map.Poly.filter_keys fenv_final ~f:(fun key ->
        List.exists recon ~f:(fun r -> Ident.tvar_equal r.fname key)
        || List.exists lemma_list ~f:(fun (f, _) -> Ident.tvar_equal f key))
  in
  update_fenv_replacing global_changed;
  Atomic.set PCSP.Problem.reconstructed_functions
    (Set.union
       (Atomic.get PCSP.Problem.reconstructed_functions)
       (Set.Poly.of_list (List.map recon ~f:(fun r -> r.fname))));
  Atomic.set PCSP.Problem.reconstruction_aliases
    (Set.union
       (Atomic.get PCSP.Problem.reconstruction_aliases)
       (Set.Poly.of_list (List.map aliased ~f:(fun r -> r.fname))));
  let recon = recon @ aliased in
  let params = { params with PCSP.Params.fenv = changed } in
  let problem, replaced =
    (* only a function the defining clauses define everywhere is put in the
       unknown's place *)
    let recon =
      List.filter recon ~f:(fun r ->
          r.exhaustive && not (Set.mem !relaxed r.pvar))
    in
    if (not replace) || List.is_empty recon then
      (PCSP.Problem.update_params pcsp params, [])
    else
      let is_def_of_recon ((_, ps, _, _) : ClauseOld.t) =
        Set.exists ps ~f:(fun a ->
            match pvar_of_atom a with
            | Some p ->
                List.exists recon ~f:(fun r -> Ident.pvar_equal r.pvar p)
            | None -> false)
      in
      let phis =
        Set.Poly.of_list
        @@ List.filter_map (Lazy.force clauses) ~f:(fun c ->
            if is_def_of_recon c then None else Some (replace_in_clause recon c))
      in
      let removed = List.map recon ~f:(fun r -> Ident.pvar_to_tvar r.pvar) in
      let remove m = List.fold removed ~init:m ~f:Map.Poly.remove in
      let sols =
        Map.Poly.of_alist_exn
        @@ List.map recon ~f:(fun r ->
            let y = Ident.mk_fresh_tvar () in
            let xs = r.formals @ [ (y, r.sret) ] in
            ( Ident.pvar_to_tvar r.pvar,
              Logic.Term.mk_lambda
                (List.map xs ~f:(fun (x, s) -> (x, Logic.ExtTerm.of_old_sort s)))
              @@ Logic.ExtTerm.of_old_formula
              @@ Formula.eq (Term.mk_var y r.sret)
                   (Term.mk_fvar_app r.fname
                      (List.map r.formals ~f:snd)
                      r.sret
                      (List.map r.formals ~f:(fun (x, s) -> Term.mk_var x s)))
            ))
      in
      let params =
        {
          params with
          PCSP.Params.senv = remove params.PCSP.Params.senv;
          kind_map = remove params.PCSP.Params.kind_map;
          sol_for_eliminated =
            Map.force_merge params.PCSP.Params.sol_for_eliminated sols;
        }
      in
      ( PCSP.Problem.of_old_formulas ~params phis,
        List.map recon ~f:(fun r -> r.pvar) )
  in
  {
    problem;
    reconstructed = recon;
    refused = List.rev !refused;
    replaced;
    lemmas = lemma_list;
  }
