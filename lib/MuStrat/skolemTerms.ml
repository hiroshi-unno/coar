(* Model-guided terms for a refinement problem that is a pure existential
   over its Skolem unknowns: the shape recognised, terms selected from one Z3
   model by [StratSynth]'s selection, the result checked valid, and copies of
   one key selected at different points guarded into one definition. *)

open Core
open Common.Ext
open Common.Combinator
open Ast

let z3_solve =
  let module Z3interface =
    Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
  fun senv phi ->
    Common.PhaseTime.with_phase "fresh-ctx-check" (fun () ->
        Z3interface.check_sat [ phi ] senv (Z3.mk_context []))

(* Model-guided terms for a refinement that is a pure existential
   ([refine_terms = Terms_select]).

   The shape this recognises, per formula of the refinement problem:

     not FN_c1(s1) \/ ... \/ not FN_cn(sn) \/ R

   where every universal of the formula is one [s_i], each defined by a
   nullary Skolem unknown [FN_ci] (a constant), and [R] mentions the other
   unknowns -- the copies [K_j] of the opponent's strategy keys, all of kind
   [FN] -- only in positive atoms [K_j(a_j, r_j)] (arguments [a_j], result
   [r_j] last).  Every unknown occurs once over the whole problem.  Such a
   problem says: there are values [s] with [R], where [R] needs each [K_j] to
   map [a_j] to [r_j] at those values.  So it is solved by one model [M] of
   [R] with every [K_j] atom replaced by [true] (the atoms are positive, so
   this is a weakening that the functions then restore pointwise): each
   [FN_ci] becomes the constant [M(s_i)], and each [K_j] a function taking
   [a_j(M)] to [r_j(M)].

   The function for [K_j] is where the generalisation is.  When every
   argument [a_ji] is invertible (below) and [r_j] is a variable [s] that
   occurs in no other [K] atom and in none of [a_j], [s] is replaced by the
   term model-guided selection returns for it (Farzan and Kincaid, IJCAI
   2016: [select M s F] is free of [s] and [M |= F[s:=t]]), provided the term
   mentions only the variables the arguments determine; the model is then
   moved to [M[s := t(M)]], which still satisfies the weakened [R] by that
   contract, so the next selection starts from a model again.  Moving [s]
   cannot break an earlier key's graph, because [s] occurs in no other key
   atom.  Otherwise [K_j] is the constant function [r_j(M)] at the final
   model.

   An argument is invertible when it is affine in exactly one variable [x]
   with a coefficient that can be divided out in the sort -- [a = c*x + k],
   [c <> 0] over the reals, [c = 1] or [c = -1] over the integers -- or when
   it mentions no variable at all.  The first kind determines [x] from the
   formal parameter [p] in its position, [x = (p - k) / c]; a plain variable
   is the case [c = 1], [k = 0], and its inverse is [p] itself.  [K_j] is then
   [y = t[x := (p - k) / c]] for each determined [x] (the first position
   wins when two arguments determine the same variable).  On the graph
   point [p = a(M)] this is [t(M)], which is all [R] demands of [K_j]; off
   it the function is whatever the term gives, still total and
   single-valued.  An argument of any other shape (two variables, a
   non-linear term, an integer coefficient other than [+-1], whose inverse
   would need a divisibility guard) makes [K_j] the constant.

   Contract: [Some sol] only if every formula of the problem, with [sol]
   substituted, is valid by a Z3 check made here -- the shape argument above
   is not trusted on its own.  Each function in [sol] is total and
   single-valued ([y = t(x)]), as kind [FN] requires.  [None] whenever the
   shape does not match, the theory is not linear real or linear integer
   arithmetic over one sort, Z3 gives no model, or the final check does not
   answer valid; the caller then falls back to the constraint solver.

   Why this cannot change a verdict: the solution only proposes terms for
   the refuted side's strategy.  The refined strategy is checked by the same
   CHC query as any other before anything is concluded, and the only answers
   are the ones that check returns.  A poor selection (a constant where a
   term over the state would generalise) costs progress, never soundness. *)
exception Shape_mismatch of string

(* one Z3 validity query per formula of a small acyclic problem; a query
   that does not decide within it sends the refinement to PCSat *)
let select_check_timeout_ms = 1000

type skolem_shape = {
  vars : (Ident.tvar * Logic.Sort.t) list;
      (* every universal of every formula; pairwise distinct *)
  consts : (Ident.tvar * Ident.tvar) list;
      (* a nullary Skolem unknown and the universal it defines *)
  keys : (Ident.tvar * LogicOld.Term.t list * LogicOld.Term.t) list;
      (* a key copy, its arguments and its result, as applied in [pure] *)
  pure : LogicOld.Formula.t;
      (* the conjunction of the [R]s with every key atom replaced by true *)
}

let skolem_shape_of pfwcsp =
  let open LogicOld in
  let exi_senv = PCSP.Problem.senv_of pfwcsp in
  let is_unknown pvar = Map.Poly.mem exi_senv (Ident.pvar_to_tvar pvar) in
  if
    not
    @@ Map.Poly.for_alli exi_senv ~f:(fun ~key ~data:_ ->
        Kind.is_fn (PCSP.Problem.kind_of pfwcsp key))
  then raise (Shape_mismatch "an unknown not of kind FN");
  let keys = ref [] in
  let rec strip phi =
    if Set.is_empty (Formula.pvs_of phi) then phi
    else
      match phi with
      | Formula.Atom (Atom.App (Predicate.Var (pvar, _), args, _), _)
        when is_unknown pvar -> (
          match List.rev args with
          | r :: rev_args ->
              keys :=
                (Ident.pvar_to_tvar pvar, List.rev rev_args, r) :: !keys;
              Formula.mk_true ()
          | [] -> raise (Shape_mismatch "an unknown applied to no argument"))
      | Formula.BinaryOp (Formula.And, p1, p2, _) ->
          Formula.mk_and (strip p1) (strip p2)
      | Formula.BinaryOp (Formula.Or, p1, p2, _) ->
          Formula.mk_or (strip p1) (strip p2)
      | _ ->
          raise
            (Shape_mismatch
               "a key atom under a connective other than and/or")
  in
  let vars, consts, pures =
    Set.to_list (PCSP.Problem.formulas_of pfwcsp)
    |> List.map ~f:(fun (uni_senv, phi) ->
        let phi =
          Formula.nnf_of @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi
        in
        let consts, rest =
          List.partition_map (Formula.disjuncts_list_of phi) ~f:(function
            | Formula.UnaryOp
                ( Formula.Not,
                  Formula.Atom
                    ( Atom.App
                        (Predicate.Var (pvar, _), [ Term.Var (s, _, _) ], _),
                      _ ),
                  _ )
              when is_unknown pvar ->
                Either.First (Ident.pvar_to_tvar pvar, s)
            | d -> Either.Second d)
        in
        let defined = List.map consts ~f:snd in
        (* a universal the formula does not mention is vacuous (the
           environment keeps names an earlier rewrite eliminated), so only
           the free ones must be Skolem-defined *)
        let free = Formula.tvs_of phi in
        if
          List.contains_dup ~compare:Ident.tvar_compare defined
          || not
             @@ Set.for_all free
                  ~f:(List.mem defined ~equal:Ident.tvar_equal)
        then
          raise
            (Shape_mismatch
               "a universal not defined by exactly one Skolem constant");
        ( List.map defined ~f:(fun s -> (s, Map.Poly.find_exn uni_senv s)),
          consts,
          strip (Formula.or_of rest) ))
    |> List.unzip3
  in
  let vars = List.concat vars and consts = List.concat consts in
  let unknowns_used =
    List.map consts ~f:fst @ List.map !keys ~f:Tuple3.get1
  in
  if
    List.contains_dup vars ~compare:(fun (x, _) (y, _) ->
        Ident.tvar_compare x y)
    || List.contains_dup ~compare:Ident.tvar_compare unknowns_used
    || List.is_empty !keys
  then
    raise
      (Shape_mismatch "a variable or an unknown occurring twice, or no key");
  { vars; consts; keys = List.rev !keys; pure = Formula.and_of pures }

(* The joint demand of a ranking fixed before the terms
   ([refine_rankings = Joint_guided]).  [observer k] holds of the unknowns
   that only observe a state of the counter-play: each is applied once, as
   [V(s_1, .., s_n)], to the state at one visit of the ranked predicate, and
   asks nothing (its definition is [true]).  [dec states] is the decrease of
   every chain pair under the fixed ranking, given each observer's state as
   its argument terms; [at_m states] pins the states to the values the
   counter-play took there ([true] when unknown).  Both are quantifier-free
   formulas over the shape's universals. *)
type joint = {
  observer : Ident.tvar -> bool;
  dec : (Ident.tvar * LogicOld.Term.t list) list -> LogicOld.Formula.t;
  at_m : (Ident.tvar * LogicOld.Term.t list) list -> LogicOld.Formula.t;
  record :
    (start:(Ident.tvar * LogicOld.Term.t list) list ->
    moved:(Ident.tvar * LogicOld.Term.t list) list ->
    unit)
    option;
      (* [Some r]: after the selection's answer has passed every check made
         here (the validity check and the joint postcondition), [r] receives
         each observer's state evaluated, as ground terms, at the model the
         pass started from ([start], a model of [pure /\ dec]) and at the
         model it ended at ([moved], where the keys' results are the selected
         terms' values).  A state that does not evaluate to a ground value
         there raises [Shape_mismatch], so an answer is never returned
         without its states.  [None]: nothing is evaluated. *)
}

(* [observed_states joint shape]: [shape] without the observers' atoms, and
   each observer with its state (its arguments, result last).  Without
   [joint], [shape] unchanged and no state. *)
let observed_states_by observer shape =
  let obs, keys =
    List.partition_tf shape.keys ~f:(fun (k, _, _) -> observer k)
  in
  ({ shape with keys }, List.map obs ~f:(fun (k, args, r) -> (k, args @ [ r ])))

let observed_states joint shape =
  match joint with
  | None -> (shape, [])
  | Some j -> observed_states_by j.observer shape

(* [ground_states ~env observed]: each observer's state evaluated at [env]
   as ground terms.  Raises when a state term does not evaluate there. *)
let ground_states ~env observed =
  List.map observed ~f:(fun (k, ts) ->
      ( k,
        List.map ts ~f:(fun t ->
            LogicOld.Term.of_value (LogicOld.get_dtenv ())
              (Evaluator.eval_term ~env t)) ))

(* [mentioned_only pfwcsp]: [pfwcsp] with its signature restricted to the
   unknowns some formula mentions, and [true] when that removed one.

   Post: the formulas are [pfwcsp]'s (its stable clauses among them, as
   ordinary formulas) and every other parameter is [pfwcsp]'s but the
   signature, which loses the names no formula mentions; so the
   problem constrains exactly what [pfwcsp] constrains, and a solution of
   one over the mentioned unknowns is a solution of the other.  When every
   unknown is mentioned, [pfwcsp] itself is returned. *)
let mentioned_only pfwcsp =
  let params = PCSP.Problem.params_of pfwcsp in
  let senv = params.PCSP.Params.senv in
  let mentioned =
    Set.Poly.union_list
    @@ List.map (Set.to_list (PCSP.Problem.formulas_of pfwcsp))
         ~f:(fun (_, t) ->
           Set.filter (Logic.Term.fvs_of t) ~f:(Map.Poly.mem senv))
  in
  if Map.Poly.for_alli senv ~f:(fun ~key ~data:_ -> Set.mem mentioned key)
  then (pfwcsp, false)
  else
    ( PCSP.Problem.of_formulas
        ~params:
          {
            params with
            PCSP.Params.senv = Map.Poly.filter_keys senv ~f:(Set.mem mentioned);
            stable_clauses = Set.Poly.empty;
          }
        (PCSP.Problem.formulas_of pfwcsp),
      true )

(* The inverse of one key argument, as described above: [None] when the
   argument is not invertible, [Some None] when it mentions no variable,
   and [Some (Some (x, inv))] when it determines [x], [inv p] being [x]
   written over the formal parameter [p]. *)
let inverse_of_arg ~real arg =
  let open LogicOld in
  match arg with
  | Term.Var (x, _, _) ->
      Some (Some (x, fun p -> Logic.Term.mk_var p))
  | _ -> (
      match
        if real then Normalizer.linear_real_monomials_of (Value.Real Q.one) arg
        else Normalizer.linear_int_monomials_of (Value.Int Z.one) arg
      with
      | exception exn when not (Common.Timer.is_async exn) -> None
      | monos -> (
          let k =
            match Map.Poly.find monos None with
            | None -> Q.zero
            | Some v -> Value.cast_real_of v
          in
          let vars =
            Map.Poly.to_alist monos
            |> List.filter_map ~f:(fun (key, v) ->
                match key with
                | None -> None
                | Some t -> Some (t, Value.cast_real_of v))
          in
          match vars with
          | [] -> Some None
          | [ (Term.Var (x, _, _), c) ]
            when Q.(c <> zero) && (real || Q.(c = one || c = minus_one)) ->
              let inv p =
                let pv = Term.mk_var p (if real then T_real.SReal else T_int.SInt) in
                Logic.ExtTerm.of_old_term
                @@
                if real then
                  T_real.mk_radd
                    (T_real.mk_rmul (T_real.mk_real Q.(one / c)) pv)
                    (T_real.mk_real Q.(neg k / c))
                else
                  (* [c] is [1] or [-1], so [(p - k) / c = c * (p - k)] *)
                  let kz = Q.to_bigint k in
                  if Q.(c = one) then T_int.mk_sub pv (T_int.mk_int kz)
                  else T_int.mk_sub (T_int.mk_int kz) pv
              in
              Some (Some (x, inv))
          | _ -> None))

(* Guards by separation ([refine_guards = Separation]): the copies of one key
   whose selected terms differ are combined into one guarded definition,
   the guards separating the argument points each term was selected at;
   see [Linarith.Separate.guarded_body]. *)
let guarded_body = Linarith.Separate.guarded_body

(* the check every solution passes before it is used: each formula of the
   problem, with the solution substituted, valid by Z3 within
   [select_check_timeout_ms] *)
let valid_solution pfwcsp sol =
  Set.for_all (PCSP.Problem.formulas_of pfwcsp) ~f:(fun (uni_senv, phi) ->
      let phi =
        Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv
        @@ Logic.ExtTerm.subst sol phi
      in
      (not (Z3Smt.Z3interface.may_not_return phi))
      &&
      match
        Z3Smt.Z3interface.check_valid
          ~timeout:(Some select_check_timeout_ms)
          ~id:None (LogicOld.get_fenv ()) phi
      with
      | `Valid -> true
      | _ -> false)

(* [satisfied_by pfwcsp sol]: for a problem of the selection's shape
   ([skolem_shape_of]) and [sol] a function for each of its key copies,
   whether some values of the Skolem constants make every formula hold.  Each
   formula is [not C_1(s_1) \/ .. \/ R] with its universals the [s_i], pairwise
   distinct across the formulas, so this is the satisfiability of the
   conjunction of the [R]s with the keys substituted: one Z3 question within
   [select_check_timeout_ms], with each constant read as [true].  It is the
   validity the selection checks, with the constants left to Z3 instead of
   fixed by a model; a definition the selection could not take as pinned (a
   guarded term) is read as any other term.  [false] when the shape does not
   match, a key is missing, or Z3 does not answer [sat]. *)
let satisfied_by pfwcsp sol =
  match skolem_shape_of pfwcsp with
  | exception Shape_mismatch _ -> false
  | shape ->
      List.for_all shape.keys ~f:(fun (k, _, _) -> Map.Poly.mem sol k)
      &&
      let exi_senv = PCSP.Problem.senv_of pfwcsp in
      let sol =
        List.fold shape.consts ~init:sol ~f:(fun sol (c, _) ->
            let params =
              Logic.mk_fresh_sort_env_list
                (Logic.Sort.args_of (Map.Poly.find_exn exi_senv c))
            in
            Map.Poly.set sol ~key:c
              ~data:(Logic.Term.mk_lambda params (Logic.BoolTerm.mk_bool true)))
      in
      let phis =
        List.map (Set.to_list (PCSP.Problem.formulas_of pfwcsp))
          ~f:(fun (uni_senv, phi) ->
            Evaluator.simplify
            @@ Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv
            @@ Logic.ExtTerm.subst sol phi)
      in
      (not (List.exists phis ~f:Z3Smt.Z3interface.may_not_return))
      &&
      match
        Z3Smt.Z3interface.check_sat
          ~timeout:(Some select_check_timeout_ms)
          ~id:None (LogicOld.get_fenv ()) phis
      with
      | `Sat _ -> true
      | _ -> false

(* [observed_resolution ~observer ~extra pfwcsp]: for a problem of the
   selection's shape ([skolem_shape_of]) whose observers [observer] names, a
   model of its pure part -- every key atom read as [true], so the keys'
   results are constrained by the clauses alone: a resolution of the
   counter-play's skeleton with the ranked side's moves free -- that also
   satisfies [extra observed], given as each observer's state there as
   ground terms.  A variable a state mentions that the model leaves out (the
   formula does not constrain it) reads as zero.  [None] when the shape does
   not match, Z3 does not answer [sat] within [select_check_timeout_ms], or
   a state does not evaluate.  One Z3 question. *)
let observed_resolution ~observer ~extra pfwcsp =
  let open LogicOld in
  match skolem_shape_of pfwcsp with
  | exception Shape_mismatch _ -> None
  | shape -> (
      let shape, observed = observed_states_by observer shape in
      let phi = Evaluator.simplify (Formula.and_of [ shape.pure; extra observed ]) in
      if Z3Smt.Z3interface.may_not_return phi then None
      else
        match
          Z3Smt.Z3interface.check_sat
            ~timeout:(Some select_check_timeout_ms)
            ~id:None (get_fenv ()) [ phi ]
        with
        | `Sat m -> (
            let m = model_subst ~target:(Formula.term_sort_env_of phi) m in
            let vars =
              Set.Poly.union_list
                (List.concat_map observed ~f:(fun (_, ts) ->
                     List.map ts ~f:(fun t -> Term.term_sort_env_of t)))
            in
            try
              let env =
                Set.fold vars ~init:Map.Poly.empty ~f:(fun env (x, s) ->
                    Map.Poly.set env ~key:x
                      ~data:
                        (match Map.Poly.find m x with
                        | Some t -> Evaluator.eval_term t
                        | None ->
                            if Stdlib.(s = T_real.SReal) then Value.Real Q.zero
                            else Value.Int Z.zero))
              in
              Some (ground_states ~env observed)
            with exn when not (Common.Timer.is_async exn) -> None)
        | _ -> None)

(* [resolution_at pfwcsp ~states sol]: whether, with the key copies set to
   [sol] and each observer of [states] defined as the equality of its
   arguments with the ground state given, some values of the Skolem
   constants satisfy every formula of [pfwcsp] ([satisfied_by]): whether the
   selected functions and the states form one resolution of the problem's
   clauses.  Used to check an answer against the clauses it must satisfy,
   independently of the problem it was selected from.  [false] when an
   observer is not declared, a state's length is not its arity, or the
   question is not answered [sat]. *)
let resolution_at pfwcsp ~states sol =
  let open LogicOld in
  let exi_senv = PCSP.Problem.senv_of pfwcsp in
  match
    List.fold states ~init:sol ~f:(fun sol (k, ts) ->
        let params =
          Logic.mk_fresh_sort_env_list
            (Logic.Sort.args_of (Map.Poly.find_exn exi_senv k))
        in
        Map.Poly.set sol ~key:k
          ~data:
            (Logic.Term.mk_lambda params
               (Logic.ExtTerm.of_old_formula
                  (Formula.and_of
                     (List.map2_exn params ts ~f:(fun (x, s) t ->
                          Formula.eq
                            (Term.mk_var x (Logic.ExtTerm.to_old_sort s))
                            t))))))
  with
  | exception exn when not (Common.Timer.is_async exn) -> false
  | sol -> satisfied_by pfwcsp sol

(* [guard_terms ~real ~sort ~exi_senv ~valid ~groups sol]: the guard seam
   ([refine_guards]) applied to the selected terms.  [groups] maps each
   opponent key to the copies of it that selection solved, each as
   [(copy, point, body)]: the argument point the copy was selected at (read
   off the final model; [None] when a value was not readable) and its body as
   a function of the parameters.  [Separation] is this function; [Unguarded]
   is the identity, which the caller reaches by building no group.

   Assumes: [sol] solves the problem [valid] checks (the ungrouped selection,
   checked valid before the call), every copy in [groups] is a key of [sol]
   and of [exi_senv], and [groups] has only keys with two or more copies.
   Guarantees: the result's solution is [sol] itself (physically) when no
   group combined, otherwise the solution with every copy of each combined
   group set to one guarded definition -- a total, single-valued function,
   since [Linarith.Separate.guarded_body] returns a body defined on every
   point -- and that solution is returned only when [valid] accepts it; when
   [valid] rejects it, [sol] is returned with a note per group.  The notes
   (one per group, for tracing only) are in the order of [groups]' keys.
   [moved] (empty by default) gives per group further unknowns and their
   definitions, set together with the group's combined definition and only
   when the group combines: the nullary unknowns whose value
   [cav24_regroup] moved with a copy's value (see there).
   Preserves: asks [valid] at most once, and nothing else of Z3. *)
let guard_terms ?(moved = Map.Poly.empty) ~real ~sort ~exi_senv ~valid ~groups
    sol =
  let sol', notes =
    Map.Poly.fold groups ~init:(sol, [])
      ~f:(fun ~key:o ~data:members (sol', notes) ->
        let sorts =
          List.map members ~f:(fun (k, _, _) -> Map.Poly.find_exn exi_senv k)
        in
        let sort_k = List.hd_exn sorts in
        if not (List.for_all sorts ~f:(fun s -> Stdlib.(s = sort_k))) then
          (sol', (o, "copies of different sorts; ungrouped") :: notes)
        else
          let params =
            Logic.mk_fresh_sort_env_list (Logic.Sort.args_of sort_k)
          in
          match List.rev params with
          | [] -> (sol', (o, "no result position; ungrouped") :: notes)
          | (y, _) :: rev -> (
              let xs = List.rev_map rev ~f:fst in
              match
                guarded_body ~real xs
                  (List.map members ~f:(fun (_, p, b) -> (p, b)))
              with
              | Error reason -> (sol', (o, reason ^ "; ungrouped") :: notes)
              | Ok (body, what) ->
                  let fn =
                    Logic.Term.mk_lambda params
                    @@ Logic.Term.mk_apps
                         (Logic.ExtTerm.mk_eq sort)
                         [ Logic.Term.mk_var y; body ]
                  in
                  let sol' =
                    List.fold
                      (Option.value ~default:[] (Map.Poly.find moved o))
                      ~init:sol'
                      ~f:(fun sol' (k, def) -> Map.Poly.set sol' ~key:k ~data:def)
                  in
                  ( List.fold members ~init:sol' ~f:(fun sol' (k, _, _) ->
                        Map.Poly.set sol' ~key:k ~data:fn),
                    ( o,
                      sprintf "%d copies combined; %s" (List.length members)
                        what )
                    :: notes )))
  in
  let notes = List.rev notes in
  if phys_equal sol' sol then (sol, notes)
  else if valid sol' then (sol', notes)
  else
    ( sol,
      notes
      @ List.map (Map.Poly.keys groups) ~f:(fun o ->
          ( o,
            "the guarded definitions not checked valid; the ungrouped \
             solution is used" )) )

module SkolemSelect (A : sig
  type domain
  type term
  type atom

  val sort : Logic.Sort.t
  val default_value : domain
  val to_value : domain -> Value.t

  val formula_of_term :
    Logic.term -> atom StratSynth.PreFormula.formula option

  val select :
    (Ident.tvar, domain) Map.Poly.t ->
    Ident.tvar ->
    atom StratSynth.PreFormula.formula ->
    term

  val select_bounds :
    (Ident.tvar, domain) Map.Poly.t ->
    Ident.tvar ->
    atom StratSynth.PreFormula.formula ->
    (term * term) option

  val eval_term : (Ident.tvar, domain) Map.Poly.t -> term -> domain
  val term_of_term : term -> Logic.term
  val const_of : domain -> term

  (* [select_snapped M x F ~existing]: a constant [c] with
     [M[x := c] |= F], preferring a value of [existing], or [None] (the
     theory does not snap, or no choice is left); [holds M F] whether the
     ground formula holds at [M] ([false] when the theory cannot tell);
     [domain_of_value] and [domain_of_const] read a value or a closed term
     back, [None] when it is not one of the theory's constants *)
  val select_snapped :
    (Ident.tvar, domain) Map.Poly.t ->
    Ident.tvar ->
    atom StratSynth.PreFormula.formula ->
    existing:domain list ->
    term option

  val holds :
    (Ident.tvar, domain) Map.Poly.t ->
    atom StratSynth.PreFormula.formula ->
    bool

  (* [snap_affine M F r ~existing ~frozen]: a variable of the linear term
     [r] outside [frozen] and a value for it that keeps [F] true at [M] and
     gives [r] an [existing] value or the simplest one moving it can give;
     [None] when the theory does not snap or nothing qualifies *)
  val snap_affine :
    (Ident.tvar, domain) Map.Poly.t ->
    atom StratSynth.PreFormula.formula ->
    Logic.term ->
    existing:domain list ->
    frozen:(Ident.tvar -> bool) ->
    (Ident.tvar * domain) option

  val domain_of_value : Value.t -> domain option
  val domain_of_const : Logic.term -> domain option

  val check_sat :
    (Logic.sort_env_list ->
    Logic.term ->
    (Ident.tvar * Logic.term option) list option) ->
    atom StratSynth.PreFormula.formula ->
    Logic.sort_env_list ->
    (Ident.tvar, domain) Map.Poly.t option
end) =
struct
  let rec quantifier_free = function
    | StratSynth.PreFormula.Atom _ -> true
    | And l | Or l -> List.for_all l ~f:quantifier_free
    | Bind _ -> false

  (* [snap_model ~keys ~modes ~f0 ~f ~snap model]: the model [model] of
     [f] with the result of each argument-free key for which [snap] gives
     the key's existing terms moved against [f0] -- [f] without the
     equations [z = r] that name the results of [`Value] keys.  First each
     such key whose result is a variable [s]: [s] is moved by
     [A.select_snapped], one key after the other in [keys]' order.  Then
     each whose result is a linear term [r] (an initial move written as the
     difference of two positions): one variable of [r] that no earlier step
     moved and that is no [`Select] key's result (the pass below would move
     it again) is moved by [A.snap_affine], so that [r]'s value is snapped.
     Finally every [z] is set to its [r]'s value at the moved model.

     Contract: the result is a model of [f] binding the same variables, and
     equal to [model] wherever nothing moved.  Each move keeps [f0] true
     ([A.select_snapped]'s contract), the variables [z] occur in [f] only in
     their own equations, so re-reading them restores those equations, and
     the whole is checked with [A.holds] before it is returned; any failure,
     an exception from evaluating a result included, returns [model].
     Also returned: the variable results moved in the first step, which the
     selection pass keeps where they are. *)
  let snap_model ~keys ~modes ~f0 ~f ~snap model =
    let snappable =
      List.filter_map (List.zip_exn keys modes) ~f:(fun ((k, args, r), _) ->
          match (args, snap k) with
          | [], Some existing ->
              Some (r, List.filter_map existing ~f:A.domain_of_const)
          | _ -> None)
    in
    let select_results =
      List.filter_map modes ~f:(function
        | `Select (s, _) -> Some s
        | `Value _ -> None)
    in
    let mem l v = List.mem l v ~equal:Ident.tvar_equal in
    if List.is_empty snappable then (model, [])
    else
      let model', var_moved =
        List.fold snappable ~init:(model, []) ~f:(fun (m, moved) (r, existing) ->
            match r with
            | LogicOld.Term.Var (s, _, _) -> (
                match A.select_snapped m s f0 ~existing with
                | None -> (m, moved)
                | Some t ->
                    (Map.Poly.set m ~key:s ~data:(A.eval_term m t), s :: moved))
            | _ -> (m, moved))
      in
      let model', moved =
        List.fold snappable ~init:(model', var_moved)
          ~f:(fun (m, moved) (r, existing) ->
            match r with
            | LogicOld.Term.Var _ -> (m, moved)
            | _ -> (
                match
                  try
                    A.snap_affine m f0 (Logic.ExtTerm.of_old_term r) ~existing
                      ~frozen:(fun v -> mem moved v || mem select_results v)
                  with exn when not (Common.Timer.is_async exn) -> None
                with
                | None -> (m, moved)
                | Some (v, c) -> (Map.Poly.set m ~key:v ~data:c, v :: moved)))
      in
      if List.is_empty moved then (model, [])
      else
        try
          let env = Map.Poly.map model' ~f:A.to_value in
          let model'' =
            List.fold (List.zip_exn keys modes) ~init:model'
              ~f:(fun m ((_, _, r), mode) ->
                match mode with
                | `Value z -> (
                    match
                      A.domain_of_value (Evaluator.eval_term ~env r)
                    with
                    | Some v -> Map.Poly.set m ~key:z ~data:v
                    | None -> raise Exit)
                | `Select _ -> m)
          in
          if A.holds model'' f then (model'', var_moved) else (model, [])
        with exn when not (Common.Timer.is_async exn) -> (model, [])

  (* [cav24_regroup ~real ~exi_senv ~solve_labels ~model ~pure ~result_of
     ~consts groups]: the guard seam's [Cav24_sound] step, applied to the groups
     [guard_terms] receives (each opponent key's copies as
     [(copy, point, body)], two or more per key).  Per key its distinct
     selected bodies are ordered -- bodies over the parameters first, then
     by the number of copies that selected them, then by first occurrence
     -- and every copy is offered each body's value at its point; the
     copies with two or more distinct offered values are the chain nodes of
     [Cav24Guards.determinize], over [pure] with every variable but those
     nodes' results ([result_of]) at its value in [model].  Each node then
     takes the body the run chose, and a copy with one offered value keeps
     its own.  With [assign_all] (the [Labels_regions] arm) the copies are
     re-decided also when no copy has two values to choose from: each takes
     the most preferred body with its own value at its point, so a key whose
     bodies agree at every point keeps one body; without it such groups are
     returned unchanged.

     A node's result variable is in general itself a universal of the
     problem, defined by a nullary Skolem unknown ([consts] lists each such
     unknown with the universal it defines), and the selection moved that
     unknown's value together with the copy's.  A node that takes another
     value therefore needs that unknown moved to the same value: kept at its
     selected value, the unknown fixes the universal there and the copy's
     atom becomes [old value = new value], which is false, so the combined
     solution would fail the validity check although the values it chose
     win.  The third component gives, per key, those unknowns with their
     moved definitions; [guard_terms ~moved] sets them when the key's copies
     combine.

     Assumes: [model] satisfies [pure] (the final model of the selection),
     and no copy's argument mentions a node's result, so its point does not
     move with the choices (a [`Select] result occurs in no other key atom,
     and a [`Value] result is a fresh name).
     Guarantees: the same keys and copies, each copy's body one of its key's
     selected bodies, and at the points the bodies' values a winning choice
     of [pure] ([Cav24Guards.determinize]'s contract), the nullary unknown
     of every node's result (if any) defined as the node's value; when the
     step does not apply, or [determinize] answers [Error], the groups
     unchanged and nothing moved, with one note saying why.  The validity
     check [guard_terms] makes afterwards is unchanged.  Asks [solve_labels]
     at most once and Z3 never. *)
  let cav24_regroup ?(assign_all = false) ~real ~exi_senv ~solve_labels ~model
      ~pure ~result_of ~consts groups =
    let open LogicOld in
    let note what = [ (Ident.Tvar "cav24", what) ] in
    let unchanged what = (groups, note what, Map.Poly.empty) in
    try
      let const_of q =
        if real then Logic.RealTerm.mk_real q
        else if Z.equal (Q.den q) Z.one then Logic.IntTerm.mk_int (Q.num q)
        else raise Exit
      in
      (* per key: its classes of equal bodies in preference order, each with
         a representative body function *)
      let classes_of members =
        let k0, _, _ = List.hd_exn members in
        let params =
          Logic.mk_fresh_sort_env_list
            (List.drop_last_exn
               (Logic.Sort.args_of (Map.Poly.find_exn exi_senv k0)))
        in
        let xs = List.map params ~f:fst in
        let same t1 t2 = try Stdlib.(t1 = t2) with _ -> false in
        let classes =
          List.foldi members ~init:[] ~f:(fun i classes (_, _, body_of) ->
              let body = body_of xs in
              match
                List.findi classes ~f:(fun _ (b, _, _, _) -> same b body)
              with
              | Some (ci, _) ->
                  List.mapi classes ~f:(fun cj (b, f, n, first) ->
                      if ci = cj then (b, f, n + 1, first) else (b, f, n, first))
              | None -> classes @ [ (body, body_of, 1, i) ])
        in
        let symbolic b =
          not
            (Set.is_empty
               (Set.inter (Logic.Term.fvs_of b) (Set.Poly.of_list xs)))
        in
        let ordered =
          List.stable_sort classes ~compare:(fun (b1, _, n1, f1) (b2, _, n2, f2) ->
              match Bool.compare (symbolic b2) (symbolic b1) with
              | 0 -> ( match Int.compare n2 n1 with 0 -> Int.compare f1 f2 | c -> c)
              | c -> c)
        in
        (params, List.map ordered ~f:(fun (_, f, _, _) -> f))
      in
      let value_at params body_of point =
        let xs = List.map params ~f:fst in
        let sub =
          Map.Poly.of_alist_exn (List.zip_exn xs (List.map point ~f:const_of))
        in
        let t =
          Logic.ExtTerm.to_old_trm Map.Poly.empty Map.Poly.empty
          @@ Logic.Term.subst sub (body_of xs)
        in
        match Evaluator.eval_term t with
        | Value.Int n -> Logic.IntTerm.mk_int n
        | Value.Real q -> if real then Logic.RealTerm.mk_real q else raise Exit
        | _ -> raise Exit
      in
      (* per copy: its key, its offered (class index, value) list deduplicated
         by value, its result variable *)
      let per_key =
        Map.Poly.mapi groups ~f:(fun ~key:_ ~data:members ->
            let params, classes = classes_of members in
            let copies =
              List.map members ~f:(fun (k, point, _) ->
                  let point =
                    match point with Some p -> p | None -> raise Exit
                  in
                  let offered =
                    List.foldi classes ~init:[] ~f:(fun ci acc body_of ->
                        let v = value_at params body_of point in
                        if List.exists acc ~f:(fun (_, w) -> Stdlib.(v = w))
                        then acc
                        else acc @ [ (ci, v) ])
                  in
                  (k, offered))
            in
            (classes, copies))
      in
      let chain =
        List.concat_map (Map.Poly.data per_key) ~f:(fun (_, copies) ->
            List.filter copies ~f:(fun (_, offered) -> List.length offered >= 2))
      in
      if List.is_empty chain && not assign_all then
        unchanged "no copy has two values to choose from; groups unchanged"
      else
        let kept = Set.Poly.of_list (List.map chain ~f:(fun (k, _) -> Map.Poly.find_exn result_of k)) in
        let env =
          Map.Poly.filter_mapi model ~f:(fun ~key ~data ->
              if Set.mem kept key then None
              else Some (Term.of_value (get_dtenv ()) (A.to_value data)))
        in
        let phi =
          Logic.ExtTerm.of_old_formula @@ Evaluator.simplify
          @@ Formula.subst env pure
        in
        let nodes =
          List.map chain ~f:(fun (k, offered) ->
              {
                Cav24Guards.result = Map.Poly.find_exn result_of k;
                options = List.map offered ~f:snd;
              })
        in
        match
          if List.is_empty nodes then Ok []
          else
            Cav24Guards.determinize ~solve:solve_labels ~sort:A.sort ~phi nodes
        with
        | Error reason -> unchanged (reason ^ "; groups unchanged")
        | Ok idx ->
            let chosen =
              Map.Poly.of_alist_exn
                (List.map2_exn chain idx ~f:(fun (k, offered) i ->
                     (k, fst (List.nth_exn offered i))))
            in
            let before, after = (ref 0, ref 0) in
            let groups =
              Map.Poly.mapi groups ~f:(fun ~key ~data:members ->
                  let classes, copies = Map.Poly.find_exn per_key key in
                  let members =
                    List.map2_exn members copies
                      ~f:(fun (k, point, body_of) (_, offered) ->
                        match Map.Poly.find chosen k with
                        | Some ci -> (k, point, List.nth_exn classes ci)
                        | None -> (
                            match offered with
                            | [ (ci, _) ] -> (k, point, List.nth_exn classes ci)
                            | _ -> (k, point, body_of)))
                  in
                  let distinct ms =
                    let xs =
                      List.map
                        (Logic.mk_fresh_sort_env_list
                           (List.drop_last_exn
                              (Logic.Sort.args_of
                                 (Map.Poly.find_exn exi_senv
                                    (Tuple3.get1 (List.hd_exn ms))))))
                        ~f:fst
                    in
                    List.length
                      (List.dedup_and_sort ~compare:Stdlib.compare
                         (List.map ms ~f:(fun (_, _, b) -> b xs)))
                  in
                  before := !before + List.length classes;
                  after := !after + distinct members;
                  members)
            in
            (* the nullary unknowns of the nodes' results, each defined as
               its node's value, per key *)
            let moved =
              Map.Poly.filter_map
                (Map.Poly.mapi groups ~f:(fun ~key:_ ~data:members ->
                     List.concat_map members ~f:(fun (k, _, _) ->
                         match
                           ( List.findi chain ~f:(fun _ (k', _) ->
                                 Ident.tvar_equal k k'),
                             Map.Poly.find result_of k )
                         with
                         | Some (i, (_, offered)), Some s ->
                             let v = snd (List.nth_exn offered (List.nth_exn idx i)) in
                             List.filter_map consts ~f:(fun (kc, s') ->
                                 if not (Ident.tvar_equal s s') then None
                                 else
                                   match
                                     Logic.mk_fresh_sort_env_list
                                       (Logic.Sort.args_of
                                          (Map.Poly.find_exn exi_senv kc))
                                   with
                                   | [ (x, _) ] as params ->
                                       Some
                                         ( kc,
                                           Logic.Term.mk_lambda params
                                           @@ Logic.Term.mk_apps
                                                (Logic.ExtTerm.mk_eq A.sort)
                                                [ Logic.Term.mk_var x; v ] )
                                   | _ -> None)
                         | _ -> [])))
                ~f:(fun l -> if List.is_empty l then None else Some l)
            in
            ( groups,
              note
                (sprintf
                   "%d copies decided by the losing relations; distinct terms over the grouped keys %d -> %d; %d nullary unknowns moved with their nodes"
                   (List.length chain) !before !after
                   (Map.Poly.fold moved ~init:0 ~f:(fun ~key:_ ~data acc ->
                        acc + List.length data))),
              moved )
    with
    | Exit -> unchanged "a point or a value not readable; groups unchanged"
    | exn when not (Common.Timer.is_async exn) ->
        unchanged ("failed (" ^ Exn.to_string exn ^ "); groups unchanged")

  (* The most label regions one guard step projects (one per copy of a key
     whose copies play two or more terms); past it a key is left to
     separation.  Each projection is one model-based projection of the whole
     weakened refinement formula, the size of the play. *)
  let max_region_projections = 64

  (* [region_guards ~exi_senv ~valid ~model ~pure ~copies groups sol]: the
     guard seam's [Cav24_sound] step with [refine_labels = Labels_regions],
     after [cav24_regroup ~assign_all:true] has assigned each grouped copy
     a body.  [copies] lists every key copy of the problem whose body is a
     term, as [(copy, args, result, body)] -- its argument terms, its result
     variable in [pure], and its assigned (grouped) or selected body as a
     function of the parameters; a pinned copy is not listed.  For each key
     of [groups] whose copies play two or more distinct bodies, every copy's
     label region ([Cav24Regions.label_region]) is computed over the
     symbolic play [pure /\ result_i = body_i(args_i)] at the model with
     every grouped result at the value its body gives at its point; the
     body's guard is the disjunction of its copies' regions, and the first
     order ([Cav24Regions.choose]) whose decision list meets the point
     condition is that key's definition for every copy.

     Assumes: [sol] is checked valid (the ungrouped selection), [model]
     satisfies [pure], no copy's argument mentions a grouped copy's result,
     and every grouped body's value at its copy's point is a winning value
     ([cav24_regroup]'s contract).
     Guarantees: the returned solution is [sol] (physically) or [sol] with
     every copy of each region-combined key set to [y = d(params)], [d] an
     [ite] of the key's bodies under quantifier-free guards over its
     parameters (total and single-valued), and in the second case [valid]
     accepted it; the returned groups are [groups] without the
     region-combined keys (all of them when [valid] rejects the
     combination), to be combined by [guard_terms] as before.  One note per
     key considered.  Preserves: asks [valid] at most once, and Z3
     otherwise only through the projection's model extension.  [moved] is
     [guard_terms]': per key, the nullary unknowns whose value
     [cav24_regroup] moved with a copy's, set when the key combines. *)
  let region_guards ?(moved = Map.Poly.empty) ~exi_senv ~valid ~model ~pure
      ~copies groups sol =
    let open LogicOld in
    let note o what = (o, "regions: " ^ what) in
    try
      let env = Map.Poly.map model ~f:A.to_value in
      let xs_of k =
        List.map
          (List.drop_last_exn
             (Logic.mk_fresh_sort_env_list
                (Logic.Sort.args_of (Map.Poly.find_exn exi_senv k))))
          ~f:(fun (x, s) -> (x, Logic.ExtTerm.to_old_sort s))
      in
      (* the body as an old term over [xs] *)
      let old_body xs body_of =
        Logic.ExtTerm.to_old_trm Map.Poly.empty
          (Map.Poly.of_alist_exn
             (List.map xs ~f:(fun (x, s) -> (x, Logic.ExtTerm.of_old_sort s))))
          (body_of (List.map xs ~f:fst))
      in
      (* the body applied to the arguments *)
      let applied k args body_of =
        let xs = xs_of k in
        Term.subst
          (Map.Poly.of_alist_exn (List.zip_exn (List.map xs ~f:fst) args))
          (old_body xs body_of)
      in
      let grouped =
        Set.Poly.of_list
          (List.concat_map (Map.Poly.data groups)
             ~f:(List.map ~f:(fun (k, _, _) -> k)))
      in
      (* each grouped copy's value: its assigned body at its point *)
      let values =
        List.filter_map copies ~f:(fun (k, args, y, body_of) ->
            if Set.mem grouped k then
              Some (k, (y, Evaluator.eval_term ~env (applied k args body_of)))
            else None)
        |> Map.Poly.of_alist_exn
      in
      let env' =
        Map.Poly.fold values ~init:env ~f:(fun ~key:_ ~data:(y, v) m ->
            Map.Poly.set m ~key:y ~data:v)
      in
      let psi =
        Formula.and_of
          (pure
          :: List.map copies ~f:(fun (k, args, y, body_of) ->
                 Formula.eq
                   (Term.mk_var y (Logic.ExtTerm.to_old_sort A.sort))
                   (applied k args body_of)))
      in
      if
        not
          (try Evaluator.eval ~env:env' psi
           with exn when not (Common.Timer.is_async exn) -> false)
      then
        (sol, groups, [ note (Ident.Tvar "cav24") "the assigned play not true at the model; skipped" ])
      else
        let args_of =
          Map.Poly.of_alist_exn
            (List.map copies ~f:(fun (k, args, _, _) -> (k, args)))
        in
        let budget = ref max_region_projections in
        let combined, notes =
          Map.Poly.fold groups ~init:([], [])
            ~f:(fun ~key:o ~data:members (combined, notes) ->
              let k0, _, _ = List.hd_exn members in
              let xs = xs_of k0 in
              let same t1 t2 =
                try Stdlib.(t1 = t2)
                with exn when not (Common.Timer.is_async exn) -> false
              in
              (* the distinct bodies in [cav24_regroup]'s preference order:
                 bodies over the parameters first, then by the number of
                 copies playing them, then by first occurrence *)
              let classes =
                List.fold members ~init:[] ~f:(fun cls (k, _, body_of) ->
                    let b = old_body xs body_of in
                    match List.findi cls ~f:(fun _ (b', _) -> same b b') with
                    | Some (i, _) ->
                        List.mapi cls ~f:(fun j (b', ks) ->
                            if i = j then (b', ks @ [ k ]) else (b', ks))
                    | None -> cls @ [ (b, [ k ]) ])
              in
              let symbolic b = not (Set.is_empty (Term.fvs_of b)) in
              let classes =
                List.stable_sort classes ~compare:(fun (b1, ks1) (b2, ks2) ->
                    match Bool.compare (symbolic b2) (symbolic b1) with
                    | 0 -> Int.compare (List.length ks2) (List.length ks1)
                    | c -> c)
              in
              if List.length classes < 2 then
                (combined, note o "one term after the assignment" :: notes)
              else if !budget < List.length members then
                (combined, note o "projection budget spent; separation" :: notes)
              else (
                budget := !budget - List.length members;
                let region k =
                  match Map.Poly.find args_of k with
                  | None -> None
                  | Some args ->
                      Cav24Regions.label_region ~env:env' ~psi ~xs ~args
                in
                let branches =
                  List.map classes ~f:(fun (b, ks) ->
                      Option.map
                        (Option.all (List.map ks ~f:region))
                        ~f:(fun rs -> (Formula.or_of rs, b)))
                in
                match Option.all branches with
                | None ->
                    (combined, note o "a copy without a region; separation" :: notes)
                | Some branches -> (
                    let copies_at =
                      List.map members ~f:(fun (k, _, _) ->
                          let args = Map.Poly.find_exn args_of k in
                          ( List.map args ~f:(Evaluator.eval_term ~env:env'),
                            snd (Map.Poly.find_exn values k) ))
                    in
                    match Cav24Regions.choose ~xs ~copies:copies_at branches with
                    | None ->
                        ( combined,
                          note o
                            (sprintf
                               "%d terms, no order meets the point condition; separation"
                               (List.length classes))
                          :: notes )
                    | Some (d, order) ->
                        ( (o, members, xs, d) :: combined,
                          note o
                            (sprintf
                               "%d copies combined; %d terms under region guards (order %s): %s"
                               (List.length members) (List.length classes)
                               (String.concat_map_list ~sep:"," order ~f:Int.to_string)
                               (Term.str_of d))
                          :: notes ))))
        in
        let notes = List.rev notes in
        if List.is_empty combined then (sol, groups, notes)
        else
          let sol' =
            List.fold combined ~init:sol ~f:(fun sol' (o, members, xs, d) ->
                (* the nullary unknowns of the key's moved results, as
                   [guard_terms ~moved] sets them *)
                let sol' =
                  List.fold
                    (Option.value ~default:[] (Map.Poly.find moved o))
                    ~init:sol'
                    ~f:(fun sol' (k, def) -> Map.Poly.set sol' ~key:k ~data:def)
                in
                (* one function for every copy, as [guard_terms] installs *)
                let k0, _, _ = List.hd_exn members in
                let fn =
                    let params =
                      Logic.mk_fresh_sort_env_list
                        (Logic.Sort.args_of (Map.Poly.find_exn exi_senv k0))
                    in
                    let ps, y =
                      match List.rev params with
                      | (y, _) :: rev -> (List.rev_map rev ~f:fst, y)
                      | [] -> raise Exit
                    in
                    let d =
                      Term.subst
                        (Map.Poly.of_alist_exn
                           (List.map2_exn xs ps ~f:(fun (x, s) p ->
                                (x, Term.mk_var p s))))
                        d
                    in
                    Logic.Term.mk_lambda params
                    @@ Logic.Term.mk_apps (Logic.ExtTerm.mk_eq A.sort)
                         [ Logic.Term.mk_var y; Logic.ExtTerm.of_old_term d ]
                in
                List.fold members ~init:sol' ~f:(fun sol' (k, _, _) ->
                    Map.Poly.set sol' ~key:k ~data:fn))
          in
          if valid sol' then
            ( sol',
              Map.Poly.filter_keys groups ~f:(fun o ->
                  not (List.exists combined ~f:(fun (o', _, _, _) -> Ident.tvar_equal o o'))),
              notes )
          else
            ( sol,
              groups,
              notes
              @ [ note (Ident.Tvar "cav24")
                    "the region-combined definitions not checked valid; separation" ] )
    with
    | exn when not (Common.Timer.is_async exn) ->
        (sol, groups, [ note (Ident.Tvar "cav24") ("failed (" ^ Exn.to_string exn ^ "); separation") ])

  let solve ?origin_of ?labels ?(label_regions = false) ?(prefer_bound = false)
      ?(report = fun _ -> ()) ?check ?snap ?(pinned = fun _ -> None)
      ?(eq_result = false) ?joint pfwcsp shape =
    (* [joint]: the observers leave the keys (they are not selected and do
       not keep a key's result from moving), each gets the definition [true]
       in every solution checked, and is dropped from the one returned *)
    let shape, observed = observed_states joint shape in
    if Option.is_some joint && List.is_empty shape.keys then
      raise (Shape_mismatch "no key besides the observed states");
    let observer_defs =
      List.map observed ~f:(fun (k, _) ->
          let params =
            Logic.mk_fresh_sort_env_list
              (Logic.Sort.args_of
                 (Map.Poly.find_exn (PCSP.Problem.senv_of pfwcsp) k))
          in
          (k, Logic.Term.mk_lambda params (Logic.BoolTerm.mk_bool true)))
    in
    let with_observers sol =
      List.fold observer_defs ~init:sol ~f:(fun sol (k, d) ->
          Map.Poly.set sol ~key:k ~data:d)
    in
    let without_observers sol =
      List.fold observer_defs ~init:sol ~f:(fun sol (k, _) ->
          Map.Poly.remove sol k)
    in
    let valid_solution pfwcsp sol =
      let sol = with_observers sol in
      match check with
      | None -> valid_solution pfwcsp sol
      | Some check -> valid_solution pfwcsp sol && check sol
    in
    let open LogicOld in
    let exi_senv = PCSP.Problem.senv_of pfwcsp in
    let one_sort s = Stdlib.(s = A.sort) in
    if
      not
        (List.for_all shape.vars ~f:(snd >> one_sort)
        && Map.Poly.for_all exi_senv
             ~f:(Logic.Sort.args_of >> List.for_all ~f:one_sort))
    then raise (Shape_mismatch "a sort other than the theory's");
    let old_sort = Logic.ExtTerm.to_old_sort A.sort in
    let occurs_in_key s (_, args, r) =
      List.exists (r :: args) ~f:(fun t -> Set.mem (Term.tvs_of t) s)
    in
    (* each key: [`Select s] when its result is a variable that model-guided
       selection may move, [`Value z] when its function is the constant the
       fresh [z = r_j] reads off the final model *)
    let taken =
      let names = List.map shape.vars ~f:fst in
      fun v -> List.mem names v ~equal:Ident.tvar_equal
    in
    let real = Stdlib.(A.sort = Logic.RealTerm.SReal) in
    (* [pinned k]: the solution of a key that is not to be solved, given
       as its definition; such a key takes the [`Value] mode, its
       definition enters only the query for the model (below), and the
       answer gives it that definition.  A key of the refuted side whose
       argument is such a key's result then sees that result as a variable
       of the weakened formula, with the definition's value in the model. *)
    (* [eq_result]: a key whose result [r] is not a variable the selection
       may move (a term, an argument, or a variable another key shares)
       gets a fresh result variable [z] with the atom [z = r] added to the
       weakened formula, and [z] is selected like any other result.  This
       is the published selection's own case for an equality atom (Farzan
       and Kincaid, "Linear Arithmetic Satisfiability via Strategy
       Improvement", IJCAI-16, Section 4.1: [select(M, x, F)] returns [t]
       when [F] has the atom [x = t]), so where [r] is a term over the
       key's arguments the selected term is [r] itself rather than [r]'s
       value in the model.  Off, such a key takes its model value. *)
    let eq_defs = ref [] in
    let modes =
      List.mapi shape.keys ~f:(fun j (k, args, r) ->
          let invs = Option.all (List.map args ~f:(inverse_of_arg ~real)) in
          if Option.is_some (pinned k) then
            `Value (Ident.mk_fresh_tvar_avoiding ~prefix:"sel_val" ~taken ())
          else
          match (r, invs) with
          | Term.Var (s, _, _), Some invs
            when (not
                    (List.exists args ~f:(fun t -> Set.mem (Term.tvs_of t) s)))
                 && not
                      (List.existsi shape.keys ~f:(fun i k ->
                           i <> j && occurs_in_key s k)) ->
              `Select (s, invs)
          | _, Some invs when eq_result ->
              let z =
                Ident.mk_fresh_tvar_avoiding ~prefix:"sel_res" ~taken ()
              in
              eq_defs := (z, r) :: !eq_defs;
              `Select (z, invs)
          | _ ->
              `Value
                (Ident.mk_fresh_tvar_avoiding ~prefix:"sel_val" ~taken ()))
    in
    (* [joint]: the decrease of every chain pair, over the observed states,
       is part of the formula selected from (Lemma: selection on
       [Phi_T /\ Dec] returns terms meeting both at the moved model) *)
    let dec =
      match joint with
      | None -> Formula.mk_true ()
      | Some j -> j.dec observed
    in
    let pure =
      Formula.and_of
        (shape.pure :: dec
         :: List.map !eq_defs ~f:(fun (z, r) ->
                Formula.eq (Term.mk_var z old_sort) r)
        @ List.filter_map (List.zip_exn shape.keys modes) ~f:(function
            | (_, _, r), `Value z ->
                Some (Formula.eq (Term.mk_var z old_sort) r)
            | _, `Select _ -> None))
    in
    (* the stripped key atoms are [true]s, which the theory's reader has no
       case for: simplify them away, and read a formula that became [true]
       as the empty conjunction *)
    let pure = Evaluator.simplify pure in
    let f =
      if Formula.is_true pure then Some (StratSynth.PreFormula.And [])
      else A.formula_of_term (Logic.ExtTerm.of_old_formula pure)
    in
    let f =
      match f with
      | Some f when quantifier_free f -> f
      | _ -> raise (Shape_mismatch "the weakened formula outside the theory")
    in
    let senv =
      List.map shape.vars ~f:(fun (x, _) -> (x, A.sort))
      @ List.map !eq_defs ~f:(fun (z, _) -> (z, A.sort))
      @ List.filter_map modes ~f:(function
          | `Value z -> Some (z, A.sort)
          | `Select _ -> None)
    in
    (* the pinned keys' definitions at their applications, for the model
       only: the selection reads [f], in which their results are free *)
    let f_model =
      let hints =
        List.filter_map shape.keys ~f:(fun (k, args, r) ->
            Option.map (pinned k) ~f:(fun lam ->
                Logic.Term.beta_reduction
                  (Logic.Term.mk_apps lam
                     (List.map (args @ [ r ]) ~f:Logic.ExtTerm.of_old_term))))
      in
      if List.is_empty hints then f
      else
        match
          List.map hints ~f:A.formula_of_term |> Option.all
        with
        | Some hs when List.for_all hs ~f:quantifier_free ->
            StratSynth.PreFormula.And (f :: hs)
        | _ -> raise (Shape_mismatch "a pinned definition outside the theory")
    in
    (* [joint]: the model is asked at the counter-play's own visit states
       first ([at_m]), and of the formula alone when that has none *)
    let at_m =
      match joint with
      | None -> None
      | Some j -> (
          let phi = Evaluator.simplify (j.at_m observed) in
          if Formula.is_true phi then None
          else
            match A.formula_of_term (Logic.ExtTerm.of_old_formula phi) with
            | Some h when quantifier_free h -> Some h
            | _ -> None)
    in
    let model =
      match
        match at_m with
        | None -> A.check_sat z3_solve f_model senv
        | Some h -> (
            match
              A.check_sat z3_solve (StratSynth.PreFormula.And [ f_model; h ])
                senv
            with
            | Some m ->
                report "the joint model at the play's visit states";
                Some m
            | None ->
                report "the joint model away from the play's visit states";
                A.check_sat z3_solve f_model senv)
      with
      | None -> raise (Shape_mismatch "no model")
      | Some m ->
          List.fold senv ~init:m ~f:(fun m (x, _) ->
              if Map.Poly.mem m x then m
              else Map.Poly.set m ~key:x ~data:A.default_value)
    in
    (* With [snap], the argument-free keys' results moved first (see
       [snap_model]); [snapped] are the variables moved, which the pass
       below keeps where they are. *)
    let model, snapped =
      match snap with
      | None -> (model, [])
      | Some snap -> (
          let pure0 = Evaluator.simplify shape.pure in
          let f0 =
            if Formula.is_true pure0 then Some (StratSynth.PreFormula.And [])
            else A.formula_of_term (Logic.ExtTerm.of_old_formula pure0)
          in
          match f0 with
          | Some f0 when quantifier_free f0 ->
              let model, snapped =
                snap_model ~keys:shape.keys ~modes ~f0 ~f ~snap model
              in
              if not (List.is_empty snapped) then
                report
                  (sprintf "%d argument-free key(s) snapped"
                     (List.length snapped));
              (model, snapped)
          | _ -> (model, []))
    in
    (* One pass of the selection over the keys, in order, each moving the
       model to the value of its term.  [`Midpoint] is [A.select], the
       published selection.  [`Near] and [`Far] take, for a key whose result
       [F] bounds from both sides at the current model, the end of the
       admissible interval nearer to (farther from) the model's value
       ([A.select_bounds]), and [A.select] for any other key; each end
       satisfies [A.select]'s contract, so the model stays one of the
       weakened formula after every step, as in the published pass.  The
       flag says whether a key's term came from a bound, which is when the
       pass can differ from [`Midpoint]. *)
    let pass policy =
      List.fold_map (List.zip_exn shape.keys modes) ~init:(model, false)
        ~f:(fun (model, bounded) (_, mode) ->
          match mode with
          | `Value _ -> ((model, bounded), None)
          | `Select (s, invs) ->
              let t, from_bound =
                if List.mem snapped s ~equal:Ident.tvar_equal then
                  (* the model is one of [f], so its own value satisfies
                     [A.select]'s contract *)
                  (A.const_of (Map.Poly.find_exn model s), false)
                else
                match policy with
                | `Midpoint -> (A.select model s f, false)
                | (`Near | `Far) as side -> (
                    match A.select_bounds model s f with
                    | Some (near, far) ->
                        ((match side with `Near -> near | `Far -> far), true)
                    | None -> (A.select model s f, false))
              in
              let arg_vars = List.filter_map invs ~f:(Option.map ~f:fst) in
              if
                Set.for_all
                  (Logic.Term.fvs_of (A.term_of_term t))
                  ~f:(List.mem arg_vars ~equal:Ident.tvar_equal)
              then
                ( ( Map.Poly.set model ~key:s ~data:(A.eval_term model t),
                    bounded || from_bound ),
                  Some t )
              else ((model, bounded), None))
    in
    (* the model the pass starts from: a model of [f] (the decrease
       included), after the snapping *)
    let start_model = model in
    let value model x =
      A.term_of_term @@ A.const_of @@ Map.Poly.find_exn model x
    in
    let fn_of key body_of =
      let params =
        Logic.mk_fresh_sort_env_list
          (Logic.Sort.args_of (Map.Poly.find_exn exi_senv key))
      in
      let xs, y =
        match List.rev params with
        | (y, _) :: rev -> (List.rev_map rev ~f:fst, y)
        | [] -> raise (Shape_mismatch "a function sort with no result")
      in
      Logic.Term.mk_lambda params
      @@ Logic.Term.mk_apps (Logic.ExtTerm.mk_eq A.sort)
           [ Logic.Term.mk_var y; body_of xs ]
    in
    let body_of model mode t xs =
      match (mode, t) with
      | `Select (_, invs), Some t ->
          let ren =
            List.fold (List.zip_exn invs xs) ~init:Map.Poly.empty
              ~f:(fun ren (inv, x) ->
                match inv with
                | None -> ren
                | Some (v, inv) ->
                    if Map.Poly.mem ren v then ren
                    else Map.Poly.set ren ~key:v ~data:(inv x))
          in
          Logic.Term.subst ren (A.term_of_term t)
      | `Select (s, _), None -> value model s
      | `Value z, _ -> value model z
    in
    let sol_of model terms =
      List.map shape.consts ~f:(fun (k, s) ->
          (k, fn_of k (fun _ -> value model s)))
      @ List.map3_exn shape.keys modes terms ~f:(fun (k, _, _) mode t ->
          match pinned k with
          | Some lam -> (k, lam)
          | None -> (k, fn_of k (body_of model mode t)))
      |> Map.Poly.of_alist_exn
    in
    (* With [prefer_bound], the [`Near] pass and then the [`Far] pass are
       tried first, and the first whose solution passes the validity check
       is used; a pass that took no term from a bound is the [`Midpoint]
       pass and is not tried twice.  Otherwise, and when neither passes,
       the [`Midpoint] pass decides exactly as without the flag. *)
    let chosen =
      if not prefer_bound then None
      else
        let rec try_passes = function
          | [] ->
              report "neither bound pass checked valid; the midpoint pass";
              None
          | (policy, name) :: rest ->
              let (model, bounded), terms = pass policy in
              if not bounded then (
                (* the first key's pair is the same in both passes and every
                   other key's term is [A.select]'s, so the other pass takes
                   no bound either *)
                report "no key bounded on both sides; the midpoint pass";
                None)
              else
                let sol = sol_of model terms in
                if valid_solution pfwcsp sol then (
                  report (sprintf "the %s-bound pass checked valid" name);
                  Some (model, terms, sol))
                else (
                  report (sprintf "the %s-bound pass not checked valid" name);
                  try_passes rest)
        in
        try_passes [ (`Near, "near"); (`Far, "far") ]
    in
    let model, terms, sol, valid =
      match chosen with
      | Some (model, terms, sol) -> (model, terms, sol, true)
      | None ->
          let (model, _), terms = pass `Midpoint in
          let sol = sol_of model terms in
          (model, terms, sol, valid_solution pfwcsp sol)
    in
    (* for the trace: what became of each key whose arguments needed
       inverting *)
    let inverted =
      List.filter_map (List.zip_exn (List.zip_exn shape.keys modes) terms)
        ~f:(fun (((k, args, _), mode), t) ->
          match mode with
          | `Select _ when not (List.for_all args ~f:Term.is_var) ->
              Some
                ( k,
                  match t with
                  | Some t
                    when not
                           (Set.is_empty
                              (Logic.Term.fvs_of (A.term_of_term t))) ->
                      "inverted; a term over its parameters"
                  | Some _ -> "inverted; the selected term is a constant"
                  | None ->
                      "inverted; the selected term mentions a variable no \
                       argument determines, so a constant" )
          | _ -> None)
    in
    if not valid then
      raise (Shape_mismatch "the substituted problem not checked valid");
    (* [joint]: the moved model still satisfies the formula selected from,
       the decrease included; checked, not assumed *)
    if
      Option.is_some joint
      && not
           (try
              Evaluator.eval ~env:(Map.Poly.map model ~f:A.to_value) pure
            with exn when not (Common.Timer.is_async exn) -> false)
    then raise (Shape_mismatch "the joint demand not met at the moved model");
    (* [joint.record]: the observed states at the start and at the end of the
       pass, evaluated only once every check above has passed *)
    (match joint with
    | Some { record = Some record; _ } -> (
        let env_of m = Map.Poly.map m ~f:A.to_value in
        match
          ( ground_states ~env:(env_of start_model) observed,
            ground_states ~env:(env_of model) observed )
        with
        | exception exn when not (Common.Timer.is_async exn) ->
            raise (Shape_mismatch "a visit state not ground at the models")
        | start, moved -> record ~start ~moved)
    | _ -> ());
    let sol = without_observers sol in
    match origin_of with
    | None -> (sol, inverted, [])
    | Some origin_of ->
        (* the guard seam's input, over the copies of each key that has
           more than one: each copy's argument point, read off the final
           model, and its selected body; [guard_terms] combines them *)
        let env = Map.Poly.map model ~f:A.to_value in
        let point_of args =
          try
            Some
              (List.map args ~f:(fun a ->
                   Value.cast_real_of (Evaluator.eval_term ~env a)))
          with exn when not (Common.Timer.is_async exn) -> None
        in
        let groups =
          List.filter_map (List.zip_exn (List.zip_exn shape.keys modes) terms)
            ~f:(fun (((k, args, _), mode), t) ->
              Option.map (origin_of k) ~f:(fun o ->
                  (o, (k, point_of args, body_of model mode t))))
          |> Map.Poly.of_alist_multi
          |> Map.Poly.filter ~f:(fun ms -> List.length ms >= 2)
        in
        let region_sol = ref sol in
        let groups, cav_notes, moved =
          match labels with
          | None -> (groups, [], Map.Poly.empty)
          | Some solve_labels ->
              let result_of =
                Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
                  (List.map (List.zip_exn shape.keys modes)
                     ~f:(fun ((k, _, _), mode) ->
                       ( k,
                         match mode with
                         | `Select (s, _) -> s
                         | `Value z -> z )))
              in
              let groups, notes, moved =
                cav24_regroup ~assign_all:label_regions ~real ~exi_senv
                  ~solve_labels ~model ~pure ~result_of ~consts:shape.consts
                  groups
              in
              if not label_regions then (groups, notes, moved)
              else
                (* every key copy whose body is a term: grouped copies with
                   their assigned body, the others with their selected one *)
                let assigned =
                  Map.Poly.of_alist_exn
                    (List.concat_map (Map.Poly.data groups)
                       ~f:(List.map ~f:(fun (k, _, b) -> (k, b))))
                in
                let copies =
                  List.filter_map
                    (List.zip_exn (List.zip_exn shape.keys modes) terms)
                    ~f:(fun (((k, args, _), mode), t) ->
                      if Option.is_some (pinned k) then None
                      else
                        Some
                          ( k,
                            args,
                            Map.Poly.find_exn result_of k,
                            match Map.Poly.find assigned k with
                            | Some b -> b
                            | None -> body_of model mode t ))
                in
                let sol', groups, reg_notes =
                  region_guards ~moved ~exi_senv ~valid:(valid_solution pfwcsp)
                    ~model ~pure ~copies groups !region_sol
                in
                region_sol := sol';
                (groups, notes @ reg_notes, moved)
        in
        let sol, notes =
          guard_terms ~moved ~real ~sort:A.sort ~exi_senv
            ~valid:(valid_solution pfwcsp) ~groups !region_sol
        in
        (without_observers sol, inverted, cav_notes @ notes)
end

module SkolemSelectLRA = SkolemSelect (struct
  include StratSynth.LRA

  let sort = Logic.RealTerm.SReal
  let to_value q = Value.Real q
  let const_of = StratSynth.RTerm.of_q

  let select_snapped model x f ~existing =
    StratSynth.LRA.select_snapped model x f ~existing

  let domain_of_value = function
    | Value.Real q -> Some q
    | Value.Int n -> Some (Q.of_bigint n)
    | _ -> None

  (* a closed linear term, read as its value *)
  let domain_of_const t =
    match StratSynth.RTerm.of_term t with
    | Some a when Map.Poly.for_alli a ~f:(fun ~key ~data:_ -> Option.is_none key)
      ->
        Some (Option.value ~default:Q.zero (Map.Poly.find a None))
    | _ -> None
end)

module SkolemSelectLIA = SkolemSelect (struct
  include StratSynth.LIA

  (* a formula whose reading needs a case split over more residues than the
     integer form enumerates is outside the theory here, like any other
     formula the reader declines *)
  let formula_of_term t =
    try StratSynth.LIA.formula_of_term t
    with StratSynth.LIA.Too_many_residues _ -> None

  let sort = Logic.IntTerm.SInt
  let to_value z = Value.Int z
  let const_of z = (Affine.of_z z, Z.one, Z.zero)

  (* no snapping over the integers: [snap_model] then moves nothing *)
  let select_snapped _ _ _ ~existing:_ = None
  let snap_affine _ _ _ ~existing:_ ~frozen:_ = None
  let holds _ _ = false
  let domain_of_value = function Value.Int n -> Some n | _ -> None
  let domain_of_const _ = None
end)

(* Further rows for the keys with no argument ([select_initial_atom_rows]).

   A key with no argument is the side's choice of a value made once, before
   the play starts: an initial state.  [solve_constants] reads it off one
   model, and a model of a formula that only excludes some values sets each
   unconstrained integer to an arbitrary one, so whether the initial state
   sits on a boundary the game tests (a flag equal to 1) is decided by how
   the solver happened to complete the model.  A boundary is an atom of the
   weakened formula over those keys' results alone; this offers, for each
   such atom, one more model of the same formula in which the atom takes
   the other truth value than in the first model -- those that make an
   equation true first (the formula is in negation normal form, so a
   tested point often appears as a disequation the first model satisfies).

   [rows ~max_rows ~shape ~pure ~named ~model ~value_in ~const_fn ~valid]:
   [pure] is the formula [model] satisfies ([shape.pure] with [z_j = r_j]
   conjoined for every [named] key [(k_j, z_j, sort_j, r_j)], in the order
   of [shape.keys]), [value_in m z sort] the value of [z] in [m] as a term,
   [const_fn k t] the constant function of [t] for key [k], [consts_in m]
   every nullary Skolem constant [FN_ci] with the constant function of its
   universal's value in [m], and [valid row] whether the first solution with
   the unknowns of [row] replaced checks valid.
   Postcondition: a list of at most [max_rows] maps, each from every key
   with no argument and every [FN_ci] to a constant function (an [FN_ci]
   defines a universal, which may be a key's result, so it moves with the
   row; it is not part of a strategy), such that (1) the model it was
   read from satisfies [pure], one of the atoms above or its negation
   (whichever [model] falsifies) and, for every key
   with arguments, [z_j]'s value in [model] -- so it changes the initial
   keys only -- (2) [valid] holds of it, and (3) its tuple of values differs
   from [model]'s and from every earlier row's.  Empty when no key has no
   argument or no such atom exists.  At most [max_rows * 4] models are
   asked, each under the selection's one-second budget, and any failure of
   an ask or of reading a value drops that atom only. *)
module InitialAtomRows = struct
  let asks_per_row = 4

  (* the last call's counts, for a census line only: keys with no
     argument, atoms over their results, literals to make true, models
     asked, models found, new value tuples, rows kept *)
  let last_counts = Array.create ~len:7 0

  (* is the literal [a] (positive when [pos]) an equation? *)
  let is_eq ~pos a =
    let open LogicOld in
    match a with
    | Atom.App (Predicate.Psym T_bool.Eq, _, _) -> pos
    | Atom.App (Predicate.Psym T_bool.Neq, _, _) -> not pos
    | _ -> false

  let rows ~max_rows ~shape ~pure ~named ~model ~value_in ~const_fn ~consts_in
      ~valid =
    let open LogicOld in
    let nullary, others =
      List.partition_tf (List.zip_exn shape.keys named)
        ~f:(fun ((_, args, _), _) -> List.is_empty args)
    in
    let nullary = List.map nullary ~f:snd and others = List.map others ~f:snd in
    Array.fill last_counts ~pos:0 ~len:7 0;
    last_counts.(0) <- List.length nullary;
    if List.is_empty nullary || max_rows <= 0 then []
    else
      let results =
        Set.Poly.union_list
          (List.map nullary ~f:(fun (_, _, _, r) -> Term.tvs_of r))
      in
      let atoms =
        let pos, neg = Formula.atoms_of ~nrec:true shape.pure in
        Set.to_list (Set.union pos neg)
        |> List.filter ~f:(fun a ->
            let vs = Atom.tvs_of a in
            (not (Set.is_empty vs)) && Set.is_subset vs ~of_:results)
      in
      let env =
        Map.Poly.filter_map model ~f:(fun t ->
            try Some (Evaluator.eval_term t)
            with exn when not (Common.Timer.is_async exn) -> None)
      in
      let holds a =
        try Some (Evaluator.eval_atom ~env a)
        with exn when not (Common.Timer.is_async exn) -> None
      in
      let pins =
        List.filter_map others ~f:(fun (_, z, sort, _) ->
            Option.map (Map.Poly.find model z) ~f:(fun t ->
                Formula.eq (Term.mk_var z (Logic.ExtTerm.to_old_sort sort)) t))
      in
      let tuple m =
        try
          Some
            (List.map nullary ~f:(fun (_, z, sort, _) ->
                 Logic.ExtTerm.str_of (value_in m z sort)))
        with exn when not (Common.Timer.is_async exn) -> None
      in
      (* each atom with the truth value it does not have in [model], as
         the literal to make true; those that make an equation true first
         (an atom [t = c], or [t <> c] negated), since a point the game
         tests is what one model is least likely to hit *)
      let targets =
        List.filter_map atoms ~f:(fun a ->
            match holds a with
            | Some false -> Some (Formula.mk_atom a, is_eq ~pos:true a)
            | Some true ->
                Some (Formula.mk_neg (Formula.mk_atom a), is_eq ~pos:false a)
            | None -> None)
        |> List.partition_tf ~f:snd
        |> fun (eqs, rest) -> List.map (eqs @ rest) ~f:fst
      in
      last_counts.(1) <- List.length atoms;
      last_counts.(2) <- List.length targets;
      let seen = ref (Option.to_list (tuple model)) in
      let asked = ref 0 in
      List.fold targets ~init:[] ~f:(fun acc target ->
          if List.length acc >= max_rows || !asked >= max_rows * asks_per_row
          then acc
          else (
            incr asked;
            last_counts.(3) <- !asked;
            match
              Z3Smt.Z3interface.check_sat
                ~timeout:(Some select_check_timeout_ms) ~id:None
                (LogicOld.get_fenv ()) (pure :: target :: pins)
            with
            | `Sat m -> (
                last_counts.(4) <- last_counts.(4) + 1;
                let m =
                  LogicOld.model_subst
                    ~target:
                      (Formula.term_sort_env_of
                         (Formula.and_of (pure :: target :: pins)))
                    m
                in
                match tuple m with
                | Some t
                  when not (List.mem !seen t ~equal:(List.equal String.equal))
                  ->
                    last_counts.(5) <- last_counts.(5) + 1;
                    seen := t :: !seen;
                    (* [tuple m] read every value, so this reads them
                       again without raising *)
                    let row =
                      Map.Poly.of_alist_exn
                        (List.map nullary ~f:(fun (k, z, sort, _) ->
                             (k, const_fn k (value_in m z sort)))
                        @ consts_in m)
                    in
                    if
                      try valid row
                      with exn when not (Common.Timer.is_async exn) -> false
                    then (
                      last_counts.(6) <- last_counts.(6) + 1;
                      row :: acc)
                    else acc
                | _ -> acc)
            | _ -> acc
            | exception exn when not (Common.Timer.is_async exn) -> acc))
      |> List.rev
end

(* [solve_constants ?check pfwcsp shape]: the solution in which every
   Skolem unknown of the shape is a constant read off one model, for a
   problem whose universals and key arguments are integers and reals
   together, which neither one-sort selection reads.  Every key is in the
   [`Value] mode of [SkolemSelect]: its result [r_j] is named by a fresh
   [z_j] of the key's result sort, one Z3 model [M] of the weakened formula
   with [z_j = r_j] conjoined is asked (the key atoms are positive, so the
   weakening is restored pointwise by the functions, as above), each
   [FN_ci] becomes the constant [M(s_i)] and each key the constant function
   [M(z_j)].  A value the model leaves out is 0.

   Contract: as [SkolemSelect.solve]'s -- a solution is returned only when
   every formula with it substituted is valid by a Z3 check made here
   ([valid_solution], and [check] when given), and each function is total and
   single-valued, so kind [FN] holds; [Shape_mismatch] otherwise.  It
   proposes the opponent's terms only, so it cannot change a verdict.  A
   constant where a term over the state would generalise costs progress,
   not soundness, exactly as the one-sort selection's [`Value] mode. *)
let solve_constants ?check ?(atom_rows = 0) ?rows_out pfwcsp shape =
  let open LogicOld in
  let exi_senv = PCSP.Problem.senv_of pfwcsp in
  let numeric s =
    Stdlib.(s = Logic.IntTerm.SInt || s = Logic.RealTerm.SReal)
  in
  if
    not
      (List.for_all shape.vars ~f:(snd >> numeric)
      && Map.Poly.for_all exi_senv
           ~f:(Logic.Sort.args_of >> List.for_all ~f:numeric))
  then raise (Shape_mismatch "a sort other than integer or real");
  let result_sort key =
    match List.last (Logic.Sort.args_of (Map.Poly.find_exn exi_senv key)) with
    | Some s -> s
    | None -> raise (Shape_mismatch "a function sort with no result")
  in
  let taken =
    let names = List.map shape.vars ~f:fst in
    fun v -> List.mem names v ~equal:Ident.tvar_equal
  in
  let named =
    List.map shape.keys ~f:(fun (k, _, r) ->
        let sort = result_sort k in
        (k, Ident.mk_fresh_tvar_avoiding ~prefix:"sel_val" ~taken (), sort, r))
  in
  let pure =
    Formula.and_of
      (shape.pure
      :: List.map named ~f:(fun (_, z, sort, r) ->
          Formula.eq (Term.mk_var z (Logic.ExtTerm.to_old_sort sort)) r))
  in
  let model =
    match
      Z3Smt.Z3interface.check_sat
        ~timeout:(Some select_check_timeout_ms)
        ~id:None (LogicOld.get_fenv ()) [ pure ]
    with
    | `Sat model ->
        LogicOld.model_subst ~target:(Formula.term_sort_env_of pure) model
    | _ -> raise (Shape_mismatch "no model")
  in
  let value_in model x sort =
    let v =
      match Map.Poly.find model x with
      | Some t -> (
          try Some (Evaluator.eval_term t)
          with exn when not (Common.Timer.is_async exn) -> None)
      | None -> None
    in
    if Stdlib.(sort = Logic.RealTerm.SReal) then
      Logic.RealTerm.mk_real
        (match v with Some v -> Value.cast_real_of v | None -> Q.zero)
    else
      Logic.IntTerm.mk_int
        (match v with
        | Some (Value.Int z) -> z
        | Some _ -> raise (Shape_mismatch "a non-integer value of an integer")
        | None -> Z.zero)
  in
  let const_fn key body =
    let sort = result_sort key in
    let params =
      Logic.mk_fresh_sort_env_list
        (Logic.Sort.args_of (Map.Poly.find_exn exi_senv key))
    in
    match List.last params with
    | None -> raise (Shape_mismatch "a function sort with no result")
    | Some (y, _) ->
        Logic.Term.mk_lambda params
        @@ Logic.Term.mk_apps (Logic.ExtTerm.mk_eq sort)
             [ Logic.Term.mk_var y; body ]
  in
  let consts_in model =
    List.map shape.consts ~f:(fun (k, s) ->
        let sort =
          match List.Assoc.find shape.vars s ~equal:Ident.tvar_equal with
          | Some sort -> sort
          | None -> result_sort k
        in
        (k, const_fn k (value_in model s sort)))
  in
  let sol =
    consts_in model
    @ List.map named ~f:(fun (k, z, sort, _) -> (k, const_fn k (value_in model z sort)))
    |> Map.Poly.of_alist_exn
  in
  let valid_with sol =
    valid_solution pfwcsp sol
    && match check with None -> true | Some check -> check sol
  in
  if not (valid_with sol) then
    raise (Shape_mismatch "the substituted problem not checked valid");
  (match rows_out with
  | Some out when atom_rows > 0 ->
      out :=
        InitialAtomRows.rows ~max_rows:atom_rows ~shape ~pure ~named ~model
          ~value_in ~const_fn ~consts_in ~valid:(fun row ->
            valid_with
              (Map.Poly.fold row ~init:sol ~f:(fun ~key ~data sol ->
                   Map.Poly.set sol ~key ~data)))
  | _ -> ());
  (sol, [], [])

(* [solve ?origin_of ?prefer_bound ?report pfwcsp] is the solution
   described above, or [Shape_mismatch] with the reason it does not apply,
   together with a line for each key whose arguments were inverted saying
   whether its function came out a term or a constant, and a line for each
   key whose copies were considered for guards (both for tracing only).
   [origin_of k] names the opponent key a copy [k] was made from; without
   it, or where it answers [None], no copies are grouped and the solution is
   exactly the ungrouped one.  [prefer_bound] (default [false]) first tries
   the selection that puts each key's result at an end of its admissible
   interval -- the end nearer the model's value, then the other -- and keeps
   the first whose solution checks valid, falling back to the published
   selection otherwise; the selection's contract holds for every candidate,
   so the argument above is unchanged, and only which valid solution is
   proposed differs.  An opponent's winning move is often an extreme one,
   which the midpoint of constant bounds never is.  [report] receives one
   line saying which selection was used (tracing only).  [check], when
   given, is conjoined with the validity check at every place a solution is
   checked; it exists so that a test can make a candidate fail the check,
   which within the shape recognised here a candidate satisfying the
   selection's contract never does except by a non-answer of Z3.  [snap],
   when given, names for a key copy the result terms of the opponent key it
   was made from ([None]: the copy is not snapped); an argument-free copy
   whose result is a variable then has that result moved to one of those
   terms' values, or to the simplest rational, wherever the weakened formula
   still holds ([snap_model]); over the integers nothing is moved.  The theory is the
   sort of the universals, and [SkolemSelect.solve] refuses a problem whose
   universals and unknowns are not all of that sort. *)
let solve ?origin_of ?labels ?label_regions ?prefer_bound ?(report = fun _ -> ())
    ?check ?snap ?pinned ?eq_result ?(mixed_sorts = false) ?atom_rows ?rows_out
    ?joint pfwcsp =
  let shape = skolem_shape_of pfwcsp in
  let sorts =
    List.map shape.vars ~f:snd
    @ List.concat_map (Map.Poly.data (PCSP.Problem.senv_of pfwcsp))
        ~f:Logic.Sort.args_of
  in
  let has s = List.exists sorts ~f:(fun s' -> Stdlib.(s = s')) in
  if mixed_sorts && has Logic.IntTerm.SInt && has Logic.RealTerm.SReal then (
    report "integer and real together; constants from one model";
    if Option.is_some pinned then
      raise (Shape_mismatch "pinned keys with integer and real together");
    if Option.is_some joint then
      raise (Shape_mismatch "a joint demand with integer and real together");
    solve_constants ?check ?atom_rows ?rows_out pfwcsp shape)
  else
  match shape.vars with
  | (_, s) :: _ when Stdlib.(s = Logic.RealTerm.SReal) ->
      SkolemSelectLRA.solve ?origin_of ?labels ?label_regions ?prefer_bound ~report
        ?check ?snap ?pinned ?eq_result ?joint pfwcsp shape
  | _ ->
      SkolemSelectLIA.solve ?origin_of ?labels ?label_regions ?prefer_bound ~report
        ?check ?snap ?pinned ?eq_result ?joint pfwcsp shape
