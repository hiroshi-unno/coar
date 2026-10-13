(* MuStrat: validity checking of fixpoint logic (muCLP) by strategy synthesis.

   A muCLP problem is read as a game between a primal side, which proves the
   formula, and a dual side, which proves its negation ([MuCLP.Util.get_dual]).
   [solve] preprocesses the problem and reduces each side to a pfwCSP
   ([to_pfwcsp]): existential choices become functional (FN) unknowns by
   Skolemization, and least fixpoints become well-foundedness (WF) unknowns by
   the reduction of [MuCLP.Reducer].  A side's strategy is a ranking for each
   WF unknown and a set of candidate terms for each FN unknown
   ([init_strat_of]).

   [solve_primal_dual] alternates turns.  The side to move substitutes its
   strategy into its problem, which leaves a CHC that the configured CHC solver
   checks under a growing budget ([chc_budget]).  A satisfiable check is a win
   and the answer (valid for the primal side, invalid for the dual), subject to
   the extra conditions some configurations demand of it (transitivity of the
   rankings, an established copy-blind encoding).  An unsatisfiable check gives
   a counter-play, a derivation of the CHC; [refine_strat] turns it into a
   refinement problem for the opponent's strategy, solved by PCSat, and the
   turn passes.  [SkolemTerms] solves the pure-existential refinements by a
   model-guided search for terms instead.

   [solve_pcsp] takes a predicate constraint problem through the same route
   (ordinary unknowns only, since a fixpoint problem has no place for a kind);
   [solve_smt] decides quantified linear arithmetic by [StratSynth].

   Implements the strategy-synthesis view of fixpoint logic solving of Tsukada,
   Unno, Padon and Shoham, A Primal-Dual Perspective on Program Verification
   Algorithms (POPL 2025). *)

open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open MuCLP.Problem
open Preprocessing

module SkolemTerms = struct
  let z3_solve =
    let module Z3interface =
      Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
    fun senv phi -> Z3interface.check_sat [ phi ] senv (Z3.mk_context [])

  (* Model-guided terms for a refinement that is a pure existential
     ([select_skolem_terms]).

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

  (* Guards by separation ([select_skolem_guards]).

     A refinement problem may hold several copies [K$1 .. K$m] of one
     opponent key [K], one per visit of the derivation to [K]'s decision
     point.  Each copy is a separate unknown, so the selection gives each its
     own function [y = t_i(x)], selected at its own argument point
     [P_i = a_i(M)]; the caller then adds all of them to [K]'s term set.  When
     the [t_i] differ, [K]'s move depends on where it is made, and a single
     guarded definition says so where the term set only lists the moves:

       y = ite(g_1(x), t_1(x), ite(g_2(x), t_2(x), .. t_k(x)))

     The copies are grouped by their term (copies with one term share one
     branch), the groups are ordered, and guard [g_i] holds at every point of
     group [i] and at no point of a later group, so the definition takes
     [P_i] to [t_i(P_i)] for every copy: exactly the graph point each copy was
     selected for.  The last group needs no guard.

     The guard is the cheapest separator that exists: a threshold on one
     parameter ([x_j >= c] or [x_j <= c], [c] halfway between the two groups'
     values, rounded towards the separated group over the integers), else a
     linear one [w . x + b > 0] from one Z3 query over [w] and [b]
     ([w . P >= 1] on the group, [<= -1] on the rest; over the integers an
     integral [w], [b] exists whenever a rational one does, by clearing
     denominators).  A projection of the formula at the model onto [K]'s
     parameters would generalise further but needs the other keys' results
     eliminated first; soundness does not need either, because the guard only
     decides which of the selected terms is used where, the definition is a
     single-valued total function whatever the guard, and the whole problem
     is checked valid with it substituted before it is used.

     When a group's points cannot be separated -- two copies selected at one
     argument point with different terms, which is where the move would have
     to read something outside [K]'s parameters -- the key is left ungrouped;
     forcing the copies to agree there is not built. *)
  let separator_timeout_ms = 1000

  (* a formula over [xs] true at every point of [pos] and false at every point
     of [neg] (both non-empty), or [None] *)
  let separator ~real xs pos neg =
    let open LogicOld in
    let old_sort = if real then T_real.SReal else T_int.SInt in
    let const q =
      if real then T_real.mk_real q else T_int.mk_int (Q.to_bigint q)
    in
    let var x = Term.mk_var x old_sort in
    let n = List.length xs in
    let coord i = List.map ~f:(fun p -> List.nth_exn p i) in
    let min_of l = Option.value_exn (List.min_elt l ~compare:Q.compare) in
    let max_of l = Option.value_exn (List.max_elt l ~compare:Q.compare) in
    let half a b = Q.((a + b) / of_int 2) in
    let axis =
      List.find_map (List.zip_exn (List.init n ~f:Fn.id) xs) ~f:(fun (i, x) ->
          let s = coord i pos and r = coord i neg in
          if Q.(max_of r < min_of s) then
            let c = half (max_of r) (min_of s) in
            let c =
              if real then c else Q.of_bigint (Z.cdiv (Q.num c) (Q.den c))
            in
            Some (Formula.geq (var x) (const c))
          else if Q.(min_of r > max_of s) then
            let c = half (max_of s) (min_of r) in
            let c =
              if real then c else Q.of_bigint (Z.fdiv (Q.num c) (Q.den c))
            in
            Some (Formula.leq (var x) (const c))
          else None)
    in
    match axis with
    | Some g -> Some g
    | None when n = 0 -> None
    | None -> (
        let ws =
          List.init n ~f:(fun _ ->
              Ident.mk_fresh_tvar ~prefix:(Some "sep_w") ())
        in
        let b = Ident.mk_fresh_tvar ~prefix:(Some "sep_b") () in
        let lin p =
          List.fold (List.zip_exn ws p) ~init:(var b) ~f:(fun acc (w, pi) ->
              if real then
                T_real.mk_radd acc (T_real.mk_rmul (var w) (const pi))
              else T_int.mk_add acc (T_int.mk_mul (var w) (const pi)))
        in
        let phi =
          Formula.and_of
            (List.map pos ~f:(fun p -> Formula.geq (lin p) (const Q.one))
            @ List.map neg ~f:(fun p ->
                Formula.leq (lin p) (const Q.minus_one)))
        in
        match
          Z3Smt.Z3interface.check_sat ~timeout:(Some separator_timeout_ms)
            ~id:None (LogicOld.get_fenv ()) [ phi ]
        with
        | `Sat model ->
            let model =
              Map.Poly.of_alist_exn @@ LogicOld.remove_dontcare model
            in
            let value v =
              match Map.Poly.find model v with
              | Some t -> Value.cast_real_of (Evaluator.eval_term t)
              | None -> Q.zero
            in
            let sum =
              List.fold (List.zip_exn ws xs) ~init:(const (value b))
                ~f:(fun acc (w, x) ->
                  if real then
                    T_real.mk_radd acc
                      (T_real.mk_rmul (const (value w)) (var x))
                  else T_int.mk_add acc (T_int.mk_mul (const (value w)) (var x)))
            in
            Some (Evaluator.simplify (Formula.gt sum (const Q.zero)))
        | _ -> None)

  (* The combined body over the formal parameters [xs] for the copies
     [members] of one key -- each its argument point (the arguments' values at
     the final model, [None] when a value could not be read) and its body over
     given parameters -- together with a line for the trace; or the reason
     there is none. *)
  let guarded_body ~real xs members =
    let same t1 t2 = try Stdlib.(t1 = t2) with _ -> false in
    let classes =
      List.fold members ~init:[] ~f:(fun classes (point, body_of) ->
          let body = body_of xs in
          if List.exists classes ~f:(fun (b, _) -> same b body) then
            List.map classes ~f:(fun (b, ps) ->
                if same b body then (b, ps @ [ point ]) else (b, ps))
          else classes @ [ (body, [ point ]) ])
    in
    match classes with
    | [ (body, _) ] -> Ok (body, "one term for every copy; no guard needed")
    | _ -> (
        match
          Option.all
            (List.map classes ~f:(fun (b, ps) ->
                 Option.map (Option.all ps) ~f:(fun ps -> (b, ps))))
        with
        | None -> Error "an argument value not readable off the model"
        | Some classes -> (
            let equal_point p q = List.equal Q.equal p q in
            let clash =
              List.existsi classes ~f:(fun i (_, ps) ->
                  List.existsi classes ~f:(fun j (_, qs) ->
                      i < j
                      && List.exists ps ~f:(fun p ->
                          List.mem qs p ~equal:equal_point)))
            in
            if clash then
              Error
                "two copies selected at one argument point with different \
                 terms (agreement there is not built)"
            else
              let rec decision_list = function
                | [] -> None
                | [ (b, _) ] -> Some ([], b)
                | classes ->
                    List.find_mapi classes ~f:(fun i (b, ps) ->
                        let rest = List.filteri classes ~f:(fun j _ -> j <> i) in
                        match
                          separator ~real xs ps (List.concat_map rest ~f:snd)
                        with
                        | None -> None
                        | Some g ->
                            Option.map (decision_list rest)
                              ~f:(fun (branches, default) ->
                                ((g, b) :: branches, default)))
              in
              match decision_list classes with
              | None -> Error "no separator over the key's parameters"
              | Some (branches, default) ->
                  let sort =
                    if real then Logic.RealTerm.SReal else Logic.IntTerm.SInt
                  in
                  let body =
                    List.fold_right branches ~init:default
                      ~f:(fun (g, b) acc ->
                        Logic.BoolTerm.ite_of sort
                          (Logic.ExtTerm.of_old_formula g)
                          b acc)
                  in
                  Ok
                    ( body,
                      sprintf "%d terms under %d guards: %s"
                        (List.length classes) (List.length branches)
                        (String.concat_map_list ~sep:"; " branches
                           ~f:(fun (g, _) -> LogicOld.Formula.str_of g)) )))

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

    let solve ?origin_of ?(prefer_bound = false) ?(report = fun _ -> ())
        ?check pfwcsp shape =
      let valid_solution pfwcsp sol =
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
      let modes =
        List.mapi shape.keys ~f:(fun j (_, args, r) ->
            let invs = Option.all (List.map args ~f:(inverse_of_arg ~real)) in
            match (r, invs) with
            | Term.Var (s, _, _), Some invs
              when (not
                      (List.exists args ~f:(fun t -> Set.mem (Term.tvs_of t) s)))
                   && not
                        (List.existsi shape.keys ~f:(fun i k ->
                             i <> j && occurs_in_key s k)) ->
                `Select (s, invs)
            | _ ->
                `Value
                  (Ident.mk_fresh_tvar_avoiding ~prefix:"sel_val" ~taken ()))
      in
      let pure =
        Formula.and_of
          (shape.pure
          :: List.filter_map (List.zip_exn shape.keys modes) ~f:(function
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
        @ List.filter_map modes ~f:(function
            | `Value z -> Some (z, A.sort)
            | `Select _ -> None)
      in
      let model =
        match A.check_sat z3_solve f senv with
        | None -> raise (Shape_mismatch "no model")
        | Some m ->
            List.fold senv ~init:m ~f:(fun m (x, _) ->
                if Map.Poly.mem m x then m
                else Map.Poly.set m ~key:x ~data:A.default_value)
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
            (k, fn_of k (body_of model mode t)))
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
      match origin_of with
      | None -> (sol, inverted, [])
      | Some origin_of ->
          (* guards by separation, over the copies of each key that has more
             than one; the argument points are read off the final model *)
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
          let sol', notes =
            Map.Poly.fold groups ~init:(sol, [])
              ~f:(fun ~key:o ~data:members (sol', notes) ->
                let sorts =
                  List.map members ~f:(fun (k, _, _) ->
                      Map.Poly.find_exn exi_senv k)
                in
                let sort = List.hd_exn sorts in
                if not (List.for_all sorts ~f:(fun s -> Stdlib.(s = sort)))
                then (sol', (o, "copies of different sorts; ungrouped") :: notes)
                else
                  let params =
                    Logic.mk_fresh_sort_env_list (Logic.Sort.args_of sort)
                  in
                  match List.rev params with
                  | [] -> (sol', (o, "no result position; ungrouped") :: notes)
                  | (y, _) :: rev -> (
                      let xs = List.rev_map rev ~f:fst in
                      match
                        guarded_body ~real xs
                          (List.map members ~f:(fun (_, p, b) -> (p, b)))
                      with
                      | Error reason ->
                          (sol', (o, reason ^ "; ungrouped") :: notes)
                      | Ok (body, what) ->
                          let fn =
                            Logic.Term.mk_lambda params
                            @@ Logic.Term.mk_apps
                                 (Logic.ExtTerm.mk_eq A.sort)
                                 [ Logic.Term.mk_var y; body ]
                          in
                          ( List.fold members ~init:sol' ~f:(fun sol' (k, _, _) ->
                                Map.Poly.set sol' ~key:k ~data:fn),
                            ( o,
                              sprintf "%d copies combined; %s"
                                (List.length members) what )
                            :: notes )))
          in
          let notes = List.rev notes in
          if phys_equal sol' sol then (sol, inverted, notes)
          else if valid_solution pfwcsp sol' then (sol', inverted, notes)
          else
            ( sol,
              inverted,
              notes
              @ List.map (Map.Poly.keys groups) ~f:(fun o ->
                  ( o,
                    "the guarded definitions not checked valid; the \
                     ungrouped solution is used" )) )
  end

  module SkolemSelectLRA = SkolemSelect (struct
    include StratSynth.LRA

    let sort = Logic.RealTerm.SReal
    let to_value q = Value.Real q
    let const_of = StratSynth.RTerm.of_q
  end)

  module SkolemSelectLIA = SkolemSelect (struct
    include StratSynth.LIA

    let sort = Logic.IntTerm.SInt
    let to_value z = Value.Int z
    let const_of z = (Affine.of_z z, Z.one, Z.zero)
  end)

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
     selection's contract never does except by a non-answer of Z3.  The theory is the
     sort of the universals, and [SkolemSelect.solve] refuses a problem whose
     universals and unknowns are not all of that sort. *)
  let solve ?origin_of ?prefer_bound ?report ?check pfwcsp =
    let shape = skolem_shape_of pfwcsp in
    match shape.vars with
    | (_, s) :: _ when Stdlib.(s = Logic.RealTerm.SReal) ->
        SkolemSelectLRA.solve ?origin_of ?prefer_bound ?report ?check pfwcsp
          shape
    | _ ->
        SkolemSelectLIA.solve ?origin_of ?prefer_bound ?report ?check pfwcsp
          shape
end


(* Nested Skolem keys in a strategy check.

   A Skolem key [K] occurs in a check's clause as applications
   [K a_1 .. a_n r], whose last argument [r] (the result) is a universal of
   the clause.  A key [L] one of whose applications has an argument that
   mentions [K]'s result is the Skolem function of an existential nested
   inside [K]'s: its result is chosen after [K]'s, as a function of it.

   The check substitutes a key's term set by copying a formula once per term
   [t], the key replaced by [t] and its result renamed apart per copy, and
   joins the copies by a disjunction.  The result of every application nested
   in [K] must be renamed apart per copy as well.  A universal shared by two
   disjuncts of a clause is one value for both, while the nested application
   has different arguments in the two copies (its argument [r] is renamed);
   once [L]'s terms are substituted, the shared result must equal two
   different values, which none does, and the clause holds vacuously:
   [forall y. (y <> s t1 \/ B1 y) \/ (y <> s t2 \/ B2 y)] is true whenever
   [s t1 <> s t2], where the copies mean [B1 (s t1) \/ B2 (s t2)].  A vacuous
   clause of the check removes a derivation of the refuter's counter-play, so
   the side under check was reported winning when it was not.  Renaming each
   nested result apart per copy gives the disjunction of the copies'
   meanings, which is exact by the same argument as for the key's own result.
   Conversely, after such copying a key has several applications with
   distinct results, and each of them is renamed apart per term. *)
module NestedKeys = struct
  (* Every application of [key] in [t] as its arguments without the result
     and the result variable, in the order of a left-to-right traversal.
     Precondition: the last argument of every application of [key] is a
     variable (a Skolem key's result is a universal of the clause). *)
  let apps_of key t =
    let rec go acc t =
      if
        Logic.Term.is_var_app t
        && Ident.tvar_equal (Logic.Term.pvar_of_atom t) key
      then
        let _, args = Logic.Term.let_var_app t in
        match List.rev args with
        | ret :: rargs ->
            (List.rev rargs, fst (Logic.Term.let_var ret)) :: acc
        | [] -> acc
      else
        match t with
        | Logic.Var (_, _) | Logic.Con (_, _) -> acc
        | Logic.App (t1, t2, _) | Logic.Let (_, _, t1, t2, _) ->
            go (go acc t1) t2
        | Logic.Bin (_, _, _, t1, _)
        | Logic.TyApp (t1, _, _)
        | Logic.TyLam (_, t1, _) ->
            go acc t1
    in
    List.rev (go [] t)

  (* The results of the applications of [key] in [t], each once. *)
  let rets_of key t =
    List.map (apps_of key t) ~f:snd
    |> List.dedup_and_sort ~compare:Ident.tvar_compare

  (* The results of the applications of the keys [keys] in [t] that are
     nested, transitively, in a variable of [rets]: an application is nested
     when one of its arguments mentions [rets] or a nested result.
     Postcondition: disjoint from [rets]. *)
  let nested_rets ~keys t rets =
    let apps =
      List.concat_map keys ~f:(fun k ->
          List.map (apps_of k t) ~f:(fun (args, ret) ->
              ( Set.Poly.union_list (List.map args ~f:Logic.ExtTerm.fvs_of),
                ret )))
    in
    let rec fix scope =
      let scope' =
        List.fold apps ~init:scope ~f:(fun scope (fvs, ret) ->
            if Set.is_empty (Set.inter fvs scope) then scope
            else Set.add scope ret)
      in
      if Set.length scope' = Set.length scope then scope else fix scope'
    in
    let rets = Set.Poly.of_list rets in
    Set.diff (fix rets) rets |> Set.to_list

  (* [keys] reordered so that a key comes after every key it is nested in
     (in [t]); keys unrelated by nesting keep their relative order, and a
     cycle (which a Skolemisation does not produce) is broken by the given
     order. *)
  let order ~keys t =
    let rets = List.map keys ~f:(fun k -> (k, rets_of k t)) in
    let inside k k' =
      (* some application of [k] is nested in a result of [k'] *)
      (not (Ident.tvar_equal k k'))
      && List.exists (apps_of k t) ~f:(fun (args, _) ->
          let fvs = Set.Poly.union_list (List.map args ~f:Logic.ExtTerm.fvs_of) in
          List.exists
            (List.Assoc.find_exn ~equal:Ident.tvar_equal rets k')
            ~f:(Set.mem fvs))
    in
    let rec go acc = function
      | [] -> List.rev acc
      | remaining -> (
          match
            List.find remaining ~f:(fun k ->
                not (List.exists remaining ~f:(inside k)))
          with
          | Some k ->
              go (k :: acc)
                (List.filter remaining ~f:(Fn.non (Ident.tvar_equal k)))
          | None ->
              let k = List.hd_exn remaining in
              go (k :: acc) (List.tl_exn remaining))
    in
    go [] keys

  (* A renaming of the variables [vs] to fresh names absent from [taken]
     (and pairwise distinct, every name being drawn fresh). *)
  let renaming ~taken vs =
    Map.Poly.of_alist_exn
    @@ List.map vs ~f:(fun v ->
        (v, Ident.mk_fresh_tvar_avoiding ~prefix:"x" ~taken ()))
end

(* Where in a clause each key's term alternatives are placed
   ([miniscope_term_alternatives]).

   The strategy check substitutes a side's term-set strategy into its clauses:
   a Skolem key [K] with result [r] and term set [T] turns a clause [F] into
   the disjunction, over the terms [t] of [T], of [F] with [K := t] and [r]
   renamed apart per term.  Substituting into the WHOLE clause makes a clause
   that mentions keys [K_1 .. K_m] the disjunction of [prod |T_i|] copies,
   even when the keys occur in parts of the clause that have nothing to do with
   each other -- two existential blocks in two disjuncts of one fixpoint body,
   say, where the owner's choice in one block cannot interact with the other.

   This module places each key's disjunction instead at the smallest
   subformula that contains every occurrence of the key and of its result
   variable (its footprint), descending through conjunctions and disjunctions
   of the clause's negation normal form and grouping the operands of one
   n-ary connective into the connected components of the footprints they
   share.  Exact, by one identity: a context [C] built from [and] and [or]
   alone, with its hole occurring once and outside every negation, satisfies
   [C[a \/ b] <=> C[a] \/ C[b]] (by induction on [C]: [or] is associative and
   idempotent, [and] distributes over [or]).  A key's substitution at the
   subformula [s] of [C[s]], where [C] mentions neither the key nor its result
   variable, therefore gives a formula equivalent to its substitution into the
   whole clause: every copy of [C] is [C] itself, since the substitution and
   the renaming change only [s].  The fresh result variables are universals of
   the clause either way, one per copy, and nothing is moved across a
   quantifier.  So the clause decides exactly what the whole-clause
   substitution decides, and only the number and size of the alternatives
   change: two independent blocks of two keys with three terms each give
   [9 + 9] alternatives instead of [81].

   The result is a tree whose [Alts] nodes are the disjunctions created by the
   substitution (the alternatives), so that the caller can name each
   alternative by a fresh predicate wherever it sits; the tree read as a
   formula ([to_term]) is the substituted clause. *)
module TermAlternatives = struct
  type t =
    | Leaf of Logic.term
    | And of t list
    | Or of t list
    | Alts of t list  (** one disjunct per term of a key (alternatives) *)

  let rec to_term = function
    | Leaf t -> t
    | And ts -> Logic.BoolTerm.and_of (List.map ts ~f:to_term)
    | Or ts | Alts ts -> Logic.BoolTerm.or_of (List.map ts ~f:to_term)

  (* The tree of the connectives [and]/[or] of an NNF formula; everything else
     (a literal, a quantifier, an equality between Booleans, an if-then-else)
     is a leaf, and a key inside a leaf is substituted at the leaf. *)
  let rec of_nnf t =
    match Logic.Term.let_apps t with
    | Logic.Con (Logic.BoolTerm.And, _), _ :: _ :: _ ->
        And (List.map (Logic.BoolTerm.conjuncts_of t) ~f:of_nnf)
    | Logic.Con (Logic.BoolTerm.Or, _), _ :: _ :: _ ->
        Or (List.map (Logic.BoolTerm.disjuncts_of t) ~f:of_nnf)
    | _ -> Leaf t

  let rec map_leaves ~f = function
    | Leaf t -> Leaf (f t)
    | And ts -> And (List.map ts ~f:(map_leaves ~f))
    | Or ts -> Or (List.map ts ~f:(map_leaves ~f))
    | Alts ts -> Alts (List.map ts ~f:(map_leaves ~f))

  let rec fvs_of = function
    | Leaf t -> Logic.ExtTerm.fvs_of t
    | And ts | Or ts | Alts ts -> Set.Poly.union_list (List.map ts ~f:fvs_of)

  (* The number of alternatives the substitution created: the disjuncts of
     every [Alts] node, nested ones included. *)
  let rec num_alternatives = function
    | Leaf _ -> 0
    | And ts | Or ts -> List.sum (module Int) ts ~f:num_alternatives
    | Alts ts -> List.length ts + List.sum (module Int) ts ~f:num_alternatives

  (* A key to place: its name, its parameters, its terms (already
     deduplicated by the caller), its footprint and every key of the clause.
     The footprint is the names of the keys related to it by nesting
     ([NestedKeys]), transitively in either direction, and of their results:
     a key nested in [K] is copied and renamed with [K]'s copies, so all
     occurrences of either must lie inside the subformula where [K] is
     substituted, and a nested key must be placed at that subformula and not
     below it, where its own copies would be copied again by [K] with their
     results shared. *)
  type key = {
    key : Ident.tvar;
    params : Logic.sort_env_list;
    terms : Logic.term list;
    footprint : Ident.tvar Set.Poly.t;
    all_keys : Ident.tvar list;
  }

  let meets k fvs = not (Set.is_empty (Set.inter k.footprint fvs))

  (* [substitute ~uni_senv ~taken k tree]: [Alts] of one copy of [tree] per
     term of [k], the key replaced by the term and the results of its
     applications and of the applications nested in them ([NestedKeys])
     renamed apart, per copy, to names absent from [uni_senv] and from
     [taken], which must hold every free variable of the clause; the renamed
     environment is returned too.  A copy that is itself an [Alts] is spliced
     in ([or] is associative).  Precondition: every key [k] is nested in has
     been substituted already, and every occurrence of the renamed results in
     the clause lies inside [tree]. *)
  let substitute ~uni_senv ~taken k tree =
    let whole = to_term tree in
    let rets = NestedKeys.rets_of k.key whole in
    let local = rets @ NestedKeys.nested_rets ~keys:k.all_keys whole rets in
    let copies =
      List.map k.terms ~f:(fun term ->
          let term_fvs = Logic.ExtTerm.fvs_of term in
          let ren =
            NestedKeys.renaming local ~taken:(fun v ->
                Map.Poly.mem uni_senv v || Set.mem taken v
                || Set.mem term_fvs v)
          in
          let copy =
            map_leaves tree ~f:(fun leaf ->
                Logic.ExtTerm.rename ren
                @@ Logic.ExtTerm.subst
                     (Map.Poly.singleton k.key
                        (Logic.ExtTerm.mk_lambda k.params term))
                     leaf)
          in
          (Map.rename_keys_map ren uni_senv, copy))
    in
    let uni_senv' =
      match copies with
      | [] -> List.fold local ~init:uni_senv ~f:Map.Poly.remove
      | _ -> Map.force_merge_list (List.map copies ~f:fst)
    in
    ( uni_senv',
      Alts
        (List.concat_map copies ~f:(fun (_, c) ->
             match c with Alts cs -> cs | c -> [ c ])) )

  (* Union-find over the operand indices [0 .. n-1] of one connective: two
     operands are in one component when some key's footprint meets both. *)
  let components ks fvss =
    let n = Array.length fvss in
    let parent = Array.init n ~f:Fn.id in
    let rec find i = if parent.(i) = i then i else find parent.(i) in
    let union i j =
      let ri = find i and rj = find j in
      if ri <> rj then parent.(ri) <- rj
    in
    List.iter ks ~f:(fun k ->
        match List.filter (List.init n ~f:Fn.id) ~f:(fun i -> meets k fvss.(i)) with
        | i :: is -> List.iter is ~f:(union i)
        | [] -> ());
    List.init n ~f:Fn.id
    |> List.map ~f:(fun i -> (find i, i))
    |> List.Assoc.sort_and_group ~compare:Int.compare
    |> List.map ~f:snd

  (* [place ~uni_senv ~taken ks tree]: every key of [ks] -- each one's
     footprint lying inside [tree] -- substituted at the smallest subformula
     holding its footprint, keys in the order of [ks] wherever two are placed
     at one node. *)
  let rec place ~uni_senv ~taken ks tree =
    let subst_all uni_senv tree =
      List.fold ks ~init:(uni_senv, tree) ~f:(fun (uni_senv, tree) k ->
          substitute ~uni_senv ~taken k tree)
    in
    match (ks, tree) with
    | [], _ -> (uni_senv, tree)
    | _, ((And ts | Or ts) as node) ->
        let rebuild ts = match node with And _ -> And ts | _ -> Or ts in
        let arr = Array.of_list ts in
        let fvss = Array.map arr ~f:fvs_of in
        let uni_senv, parts =
          List.fold_map (components ks fvss) ~init:uni_senv
            ~f:(fun uni_senv idxs ->
              let kc =
                List.filter ks ~f:(fun k ->
                    List.exists idxs ~f:(fun i -> meets k fvss.(i)))
              in
              match idxs with
              | [ i ] -> place ~uni_senv ~taken kc arr.(i)
              | _ ->
                  let spanning, local =
                    List.partition_tf kc ~f:(fun k ->
                        List.count idxs ~f:(fun i -> meets k fvss.(i)) >= 2)
                  in
                  let uni_senv, sub =
                    List.fold_map idxs ~init:uni_senv ~f:(fun uni_senv i ->
                        place ~uni_senv ~taken
                          (List.filter local ~f:(fun k -> meets k fvss.(i)))
                          arr.(i))
                  in
                  List.fold spanning ~init:(uni_senv, rebuild sub)
                    ~f:(fun (uni_senv, tree) k ->
                      substitute ~uni_senv ~taken k tree))
        in
        (uni_senv, rebuild parts)
    | _, (Leaf _ | Alts _) -> subst_all uni_senv tree

  (* [one_point ~uni_senv ks tree]: the placement of the keys [ks] (terms
     already deduplicated) in the NNF tree [tree] of a clause by the one-point
     rule, or [None] when its preconditions fail and the caller is to place
     by footprints as above.

     A Skolemised clause states a key [K] with result [y] as a disjunct
     [not K(a, y)] of an [or] node (the clause's top for an outermost
     existential, an inner disjunction for a nested one), [y] a universal of
     the clause.  [place] counts that literal in [K]'s footprint, so every
     key's footprint reaches the literal's node, and a clause with keys
     [K_1 .. K_m] becomes the
     disjunction of [prod |T_i|] copies even when each result occurs in one
     small part of it: an integer transition system's initial clause draws
     six to twenty nondeterministic values, each a key, and its check grew to
     thousands of named alternatives after one refinement.  When every term
     of [K] has the form [y = s] (or [s = y]) with [y] not in [s], the copy
     for that term is [forall y. C[y <> s(a) \/ R(y)]], which is [C[R(s(a))]]
     when [y] occurs nowhere outside the literal's node and the context [C] is
     built from [and]/[or] alone (take [y := s(a)] one way; the other way,
     [y = s(a)] gives [C[R(s(a))]] itself and any other [y] makes the node
     true, and [C] is monotone); so the literal is dropped (a node left with
     no disjunct is [false]) and [y] is replaced by [s(a)] wherever it
     occurs.  The footprint of [K] is then the occurrences of its
     results alone, and [K] is substituted at the smallest subformula holding
     them, the operands of an [and]/[or] node that hold them regrouped into
     one node of the same connective (associativity and commutativity): by
     the identity stated above ([C[a \/ b] <=> C[a] \/ C[b]] for a context of
     [and]/[or] with its hole once), the result is equivalent to the
     whole-clause substitution.

     Preconditions, each checked (any failure answers [None]): a key occurs
     only as such a disjunct, a negated application whose last argument is a
     variable of [uni_senv] occurring nowhere outside the disjunct's [or]
     node; results are pairwise distinct and
     none occurs in an argument of an application of its own key; every term
     of every key has the one-point form; and the keys can be ordered so that
     a key comes before every key whose results its arguments mention (a key
     nested in another is substituted first, so that no dropped literal still
     mentions a result being replaced).  Among the keys allowed next, one
     whose results occur only in predicate-free leaves is taken first, so that
     its alternatives stay inside a predicate-free part and are not copied
     with the predicate atoms of the keys taken later; any order gives an
     equivalent formula, since the disjunction over a product of term choices
     does not depend on the order the choices are made in.
     Postcondition: the tree read as a formula ([to_term]) is equivalent,
     under the returned environment (the clause's without the eliminated
     results), to the substitution of the strategy into the whole clause.  No
     variable is renamed, since no result survives. *)
  (* how many clauses [of_clause] has placed by [one_point] in this process;
     read only by the trace of a strategy check *)
  let one_point_count = Atomic.make 0

  let one_point ~uni_senv ks tree =
    let exception Fallback in
    try
      let key_of v = List.find ks ~f:(fun k -> Ident.tvar_equal k.key v) in
      (* A key literal [not K(a, y)] as a disjunct of an [or] node (the
         clause's top counts as one), with [y] a universal of the clause. *)
      let key_app = function
        | Leaf l when Logic.BoolTerm.is_not l -> (
            match Logic.Term.let_apps (Logic.BoolTerm.let_not l) with
            | Logic.Var (v, _), args when Option.is_some (key_of v) -> (
                match List.rev args with
                | Logic.Var (y, _) :: rargs when Map.Poly.mem uni_senv y ->
                    Some (Option.value_exn (key_of v), List.rev rargs, y)
                | _ -> raise Fallback)
            | _ -> None)
        | _ -> None
      in
      (* The tree without its key literals, and each literal with the path
         (child indices from the root) of the [or] node it was a disjunct of;
         an [or] node left with no disjunct is [false]. *)
      let apps = ref [] in
      let rec strip path t =
        match t with
        | Or ts ->
            let kept =
              List.filter_mapi ts ~f:(fun i d ->
                  match key_app d with
                  | Some (k, args, y) ->
                      apps := (k, args, y, path) :: !apps;
                      None
                  | None -> Some (strip (path @ [ i ]) d))
            in
            (match kept with
            | [] -> Leaf (Logic.BoolTerm.mk_bool false)
            | [ d ] -> d
            | ds -> Or ds)
        | And ts -> And (List.mapi ts ~f:(fun i d -> strip (path @ [ i ]) d))
        | Leaf _ | Alts _ -> t
      in
      let body =
        match tree with
        | Or _ -> strip [] tree
        | t -> (
            match key_app t with
            | Some (k, args, y) ->
                apps := [ (k, args, y, []) ];
                Leaf (Logic.BoolTerm.mk_bool false)
            | None -> strip [] t)
      in
      let apps = List.rev !apps in
      (* [y] occurs in the original tree outside the node at [path] (its own
         literal and every other occurrence must lie inside that node, so that
         the one-point rule may be applied there). *)
      let occurs_outside path y =
        let rec go p t =
          if List.equal Int.equal p path then false
          else
            match t with
            | Leaf l -> Set.mem (Logic.ExtTerm.fvs_of l) y
            | And ts | Or ts | Alts ts ->
                List.existsi ts ~f:(fun i d -> go (p @ [ i ]) d)
        in
        go [] tree
      in
      if List.exists apps ~f:(fun (_, _, y, path) -> occurs_outside path y)
      then raise Fallback;
      let apps = List.map apps ~f:(fun (k, args, y, _) -> (k, args, y)) in
      let key_set = Set.Poly.of_list (List.map ks ~f:(fun k -> k.key)) in
      let rets = List.map apps ~f:(fun (_, _, y) -> y) in
      let args_fvs args =
        Set.Poly.union_list (List.map args ~f:Logic.ExtTerm.fvs_of)
      in
      let rets_of_key k apps =
        List.filter_map apps ~f:(fun (k', _, y) ->
            if Ident.tvar_equal k.key k'.key then Some y else None)
      in
      if
        (not (Set.is_empty (Set.inter (fvs_of body) key_set)))
        || List.contains_dup rets ~compare:Ident.tvar_compare
        || List.exists ks ~f:(fun k -> List.is_empty (rets_of_key k apps))
        || List.exists apps ~f:(fun (k, args, _) ->
               List.exists (rets_of_key k apps) ~f:(Set.mem (args_fvs args)))
      then raise Fallback;
      (* Each term as the right-hand side [s] of [ret = s], [ret] the key's
         last parameter. *)
      let rhs_of k term =
        match List.last k.params with
        | None -> raise Fallback
        | Some (ret, _) -> (
            let is_ret = function
              | Logic.Var (v, _) -> Ident.tvar_equal v ret
              | _ -> false
            in
            let free_of_ret t = not (Set.mem (Logic.ExtTerm.fvs_of t) ret) in
            match Logic.Term.let_apps term with
            | Logic.TyApp (Logic.Con (Logic.BoolTerm.Eq, _), _, _), [ a; b ]
              when is_ret a && free_of_ret b ->
                b
            | Logic.TyApp (Logic.Con (Logic.BoolTerm.Eq, _), _, _), [ a; b ]
              when is_ret b && free_of_ret a ->
                a
            | _ -> raise Fallback)
      in
      let rhss =
        List.map ks ~f:(fun k -> (k.key, List.map k.terms ~f:(rhs_of k)))
      in
      let pure_leaf t =
        Set.for_all (Logic.ExtTerm.fvs_of t) ~f:(Map.Poly.mem uni_senv)
      in
      let rec only_pure ys = function
        | Leaf t ->
            Set.is_empty (Set.inter (Logic.ExtTerm.fvs_of t) ys) || pure_leaf t
        | And ts | Or ts | Alts ts -> List.for_all ts ~f:(only_pure ys)
      in
      (* [k], with its applications [kapps] (arguments and result), substituted
         at the smallest subformula of [tree] holding the results [ys]. *)
      let substitute_at k kapps ys tree =
        let params =
          List.map ~f:fst (List.take k.params (List.length k.params - 1))
        in
        let subs =
          List.map (List.Assoc.find_exn rhss ~equal:Ident.tvar_equal k.key)
            ~f:(fun s ->
              Map.Poly.of_alist_exn
              @@ List.map kapps ~f:(fun (args, y) ->
                  ( y,
                    Logic.ExtTerm.subst
                      (Map.Poly.of_alist_exn (List.zip_exn params args))
                      s )))
        in
        let meets t = not (Set.is_empty (Set.inter (fvs_of t) ys)) in
        let subst_here t =
          Alts
            (List.concat_map subs ~f:(fun sub ->
                 match map_leaves t ~f:(Logic.ExtTerm.subst sub) with
                 | Alts cs -> cs
                 | c -> [ c ]))
        in
        let rec go t =
          if not (meets t) then t
          else
            match t with
            | And ts | Or ts -> (
                let rebuild ts = match t with And _ -> And ts | _ -> Or ts in
                match List.partition_tf ts ~f:meets with
                | [ _ ], _ ->
                    rebuild (List.map ts ~f:(fun u -> if meets u then go u else u))
                | _, [] -> subst_here t
                | ms, others -> rebuild (others @ [ subst_here (rebuild ms) ]))
            | Leaf _ | Alts _ -> subst_here t
        in
        go tree
      in
      let rec loop tree pending =
        if List.is_empty pending then tree
        else
          let keys =
            List.dedup_and_sort
              ~compare:(fun a b -> Ident.tvar_compare a.key b.key)
              (List.map pending ~f:(fun (k, _, _) -> k))
          in
          let allowed =
            List.filter keys ~f:(fun k ->
                let ys = Set.Poly.of_list (rets_of_key k pending) in
                not
                  (List.exists pending ~f:(fun (k', args, _) ->
                       (not (Ident.tvar_equal k.key k'.key))
                       && not (Set.is_empty (Set.inter (args_fvs args) ys)))))
          in
          let k =
            match
              List.find allowed ~f:(fun k ->
                  only_pure (Set.Poly.of_list (rets_of_key k pending)) tree)
            with
            | Some k -> k
            | None -> ( match allowed with k :: _ -> k | [] -> raise Fallback)
          in
          let mine, others =
            List.partition_tf pending ~f:(fun (k', _, _) ->
                Ident.tvar_equal k.key k'.key)
          in
          let ys = Set.Poly.of_list (List.map mine ~f:(fun (_, _, y) -> y)) in
          loop
            (substitute_at k
               (List.map mine ~f:(fun (_, args, y) -> (args, y)))
               ys tree)
            others
      in
      let tree = loop body apps in
      Some (List.fold rets ~init:uni_senv ~f:Map.Poly.remove, tree)
    with Fallback -> None

  (* [of_clause ~dedup strat_fn (uni_senv, phi)]: the clause [phi] (with its
     ranking keys already substituted) with every Skolem key of [strat_fn]
     that it mentions placed as above, [dedup params terms] giving the terms
     of a key, together with the renamed environment and the number of
     alternatives the whole-clause substitution would have made (the product
     of the term counts, saturating at 10^9; 1 for a clause with no key).
     Keys are substituted outer ones first ([NestedKeys.order]), as in the
     whole-clause substitution, so the two read one strategy the same way;
     where [one_point] applies, no result survives and no order between
     unrelated keys is needed. *)
  let of_clause ~dedup strat_fn (uni_senv, phi) =
    let fvs = Logic.ExtTerm.fvs_of phi in
    let present =
      Map.Poly.keys strat_fn |> List.filter ~f:(Set.mem fvs)
      |> fun keys -> NestedKeys.order ~keys phi
    in
    (* The nesting relation's classes: a key and the keys nested in it, or it
       in them, transitively. *)
    let related k k' =
      let nested_in a b =
        let rets = NestedKeys.rets_of b phi in
        let nested = NestedKeys.nested_rets ~keys:present phi rets in
        List.exists (NestedKeys.rets_of a phi)
          ~f:(List.mem nested ~equal:Ident.tvar_equal)
      in
      nested_in k k' || nested_in k' k
    in
    let rec closure cls =
      let cls' =
        List.filter present ~f:(fun k ->
            List.mem cls k ~equal:Ident.tvar_equal
            || List.exists cls ~f:(related k))
      in
      if List.length cls' = List.length cls then cls else closure cls'
    in
    let footprint_of key =
      closure [ key ]
      |> List.concat_map ~f:(fun k -> k :: NestedKeys.rets_of k phi)
      |> Set.Poly.of_list
    in
    let ks =
      List.map present ~f:(fun key ->
          let params, terms = Map.Poly.find_exn strat_fn key in
          {
            key;
            params;
            terms = dedup params terms;
            footprint = footprint_of key;
            all_keys = present;
          })
    in
    let taken =
      Set.Poly.union_list
        (fvs
        :: List.concat_map ks ~f:(fun k ->
            List.map k.terms ~f:Logic.ExtTerm.fvs_of))
    in
    let whole =
      if List.is_empty ks then 1
      else
        List.fold ks ~init:1 ~f:(fun acc k ->
            let n = List.length k.terms in
            if acc > 1_000_000_000 / Int.max 1 n then 1_000_000_000 else acc * n)
    in
    (* A clause that mentions no key is kept as it is, so that it reaches the
       backend exactly as with the whole-clause substitution. *)
    if List.is_empty ks then (uni_senv, Leaf phi, whole)
    else
      let nnf_tree = of_nnf (Logic.ExtTerm.nnf_of phi) in
      let uni_senv, tree =
        match one_point ~uni_senv ks nnf_tree with
        | Some placed ->
            Atomic.incr one_point_count;
            placed
        | None -> place ~uni_senv ~taken ks nnf_tree
      in
      (uni_senv, tree, whole)
end

(* Tautological clauses of a strategy check.

   A clause whose head holds an atom that its body also holds -- the same
   predicate applied to the same argument terms, compared syntactically after
   the conversion to clausal form -- is true under every interpretation, so
   removing it leaves the check's set of solutions unchanged; and a derivation
   of the remaining clauses is a derivation of the whole set, since they are a
   subset of it.  So the check with such clauses removed has the same answer,
   and every counter-play it returns is a counter-play of the original.  The
   greatest-fixpoint encoding of a ranked predicate produces such clauses
   whenever the prover may stay where it is: the stay move's two copies of the
   ranked predicate are the clause's head, once the refuter's view has
   distributed the prover's moves into clauses.  They are a third of the
   check's clauses on the elevator-signal and resource inputs, and the CHC
   backend, which is run with rule subsumption off so that its counterexample
   keeps every named decision point, does not remove them itself. *)
module TautologicalClauses = struct
  (* Precondition: none on the form of [pcsp]; a problem not in clausal form
     is converted first, as the CHC backends do.  Postcondition: the returned
     problem holds exactly the clauses of [pcsp] (without its stable clauses,
     which stay in the parameters) that have no atom both positively and
     negatively, and the count is how many were removed; the parameters are
     those of [pcsp]. *)
  let drop pcsp =
    let params = PCSP.Problem.params_of pcsp in
    let cnf =
      PCSP.Problem.clauses_of ~full_clauses:false
      @@ PCSP.Problem.to_cnf
      @@ PCSP.Problem.to_nnf pcsp
    in
    let kept =
      Set.filter cnf ~f:(fun (_, ps, ns, _) -> Set.is_empty (Set.inter ps ns))
    in
    ( Set.length cnf - Set.length kept,
      Set.length cnf,
      PCSP.Problem.of_formulas ~params (ClauseSet.to_formulas kept) )
end

(* The clausal form of a strategy check with every step clause guarded.

   A formula of the check such as [U(s) \/ (G(s) /\ not U(s'))], with [G] the
   move's predicate-free condition, has the clauses [U(s) \/ G(s)] and
   [U(s) \/ not U(s')] in the ordinary clausal form, and the second lets a
   derivation of the CHC backend step from [s] to [s'] at a state where [G(s)]
   is false, so that a counter-play read off the derivation continues past
   the end of the play.  The refinement takes every step of a counter-play as
   a move ([chain_pairs_of] asks the opponent's ranking to decrease along each
   one), so such steps ask a ranking for pairs the game never produces, and
   on an integer transition system whose exits are many states (every [x <= 0]
   of a loop guarded by [x > 0]) the rankings fitted to them never generalise.
   [Logic.BoolTerm.cnf_of_guarded] puts [not G(s)] into the step clause, which
   is exact; see its contract. *)
module GuardedClauses = struct
  (* Precondition: none on the form of [pcsp]; a problem in clausal form is
     returned unchanged.  Postcondition: a problem with the parameters of
     [pcsp] whose formulas are clauses (each a disjunction of literals and one
     predicate-free part), together equivalent to the formulas of [pcsp], and
     each clause from a conjunction that holds an unknown carries the
     negation of the conjunction's predicate-free part. *)
  let apply pcsp =
    if PCSP.Problem.is_cnf pcsp then pcsp
    else
        let params = PCSP.Problem.params_of pcsp in
        let exi_senv = PCSP.Problem.senv_of pcsp in
        PCSP.Problem.formulas_of pcsp
        |> Set.concat_map ~f:(fun (uni_senv, phi) ->
            Logic.BoolTerm.cnf_of_guarded exi_senv uni_senv
              (Logic.BoolTerm.nnf_of phi)
            |> Set.Poly.map ~f:(fun (ps, ns, phi) ->
                Clause.to_senv_formula (uni_senv, ps, ns, phi)))
        |> PCSP.Problem.of_formulas ~params
end

(* Restricted copies of a term-set strategy: the demonic question a timed-out
   strategy check falls back to ([demonic_fallback_on_undecided_check]).

   A side's term-set strategy maps each Skolem key to a set of terms, and its
   check is angelic: at every instance the side picks one term per key, so a
   counter-play must refute every pick at once -- on a loop whose two
   alternatives are refuted by a long play and a short one, Spacer has to find
   both.  A copy maps every key to ONE of its terms.  The copy's check asks for
   a play refuting that pick alone.  Since the term-set substitution is the
   disjunction of the copies' substitutions, each copy's clauses imply the
   whole strategy's: a win of a copy would carry over, but a refuted copy says
   nothing about the whole strategy.  So a copy's counter-play is a genuine
   play against the restricted strategy and serves only as a source of
   candidates for the opponent; no answer is read from a copy's check. *)
module DemonicCopies = struct
  exception Enough

  (* [copies ~max ~is_fresh strat_fn]: at most [max] maps with the keys and
     parameters of [strat_fn], each key's term set replaced by a singleton of
     one of its terms (a key with no term keeps its empty set), pairwise
     distinct; none at all when no key has two terms, since the only copy
     would be the strategy itself.
     Order: each key's terms with those satisfying [is_fresh key] first (each
     group in the set's order); tuples by ascending sum of the chosen
     positions, so the first copy takes every key's first term and the next
     ones move one key at a time; then, stably, the tuples choosing a fresh
     term for some key before those choosing none.  At most [8 max + 8]
     tuples are enumerated, so the cost does not depend on the product of the
     set sizes. *)
  let copies ~max ~is_fresh strat_fn =
    let entries =
      Map.Poly.to_alist strat_fn
      |> List.map ~f:(fun (key, (params, terms)) ->
          let fresh, old =
            List.partition_tf (Set.to_list terms) ~f:(is_fresh key)
          in
          (key, params, Array.of_list (fresh @ old), List.length fresh))
    in
    if max <= 0 || List.for_all entries ~f:(fun (_, _, a, _) -> Array.length a <= 1)
    then []
    else
      let limit = (8 * max) + 8 in
      let found = ref [] and count = ref 0 in
      let span (_, _, a, _) = Int.max 0 (Array.length a - 1) in
      (* [rest_span.(i)]: the largest sum the entries from [i] on can take *)
      let n = List.length entries in
      let rest_span = Array.create ~len:(n + 1) 0 in
      List.iteri (List.rev entries) ~f:(fun j e ->
          let i = n - 1 - j in
          rest_span.(i) <- rest_span.(i + 1) + span e);
      let rec go i s acc = function
        | [] ->
            if s = 0 then (
              found := List.rev acc :: !found;
              incr count;
              if !count >= limit then raise Enough)
        | ((_, _, a, _) as e) :: rest ->
            if s <= rest_span.(i) then
              if Array.length a = 0 then go (i + 1) s ((e, -1) :: acc) rest
              else
                for k = 0 to Int.min s (Array.length a - 1) do
                  go (i + 1) (s - k) ((e, k) :: acc) rest
                done
      in
      (try
         for s = 0 to rest_span.(0) do
           go 0 s [] entries
         done
       with Enough -> ());
      let uses_fresh t =
        List.exists t ~f:(fun ((_, _, _, nf), k) -> k >= 0 && k < nf)
      in
      let with_fresh, without =
        List.partition_tf (List.rev !found) ~f:uses_fresh
      in
      List.take (with_fresh @ without) max
      |> List.map ~f:(fun t ->
          Map.Poly.of_alist_exn
          @@ List.map t ~f:(fun ((key, params, a, _), k) ->
              ( key,
                ( params,
                  if k < 0 then Set.Poly.empty else Set.Poly.singleton a.(k) )
              )))

  (* The counter-play a copy's check returned, if any.  Every other outcome --
     a win, an undecided check, an unsatisfiable answer without a play -- is
     [None]: the copy yields nothing, and in particular no verdict. *)
  let counter_play = function
    | PCSP.Problem.Unsat (Some (PCSP.Problem.Formula cex)) -> Some cex
    | _ -> None
end

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* a verbose run also prints the environments a failed term conversion
     searched; a quiet run catches those failures silently and retries *)
  let () = if config.verbose then Atomic.set Ast.Logic.print_unbound_envs true

  module Reducer = MuCLP.Reducer.Make (
    struct
      let config =
        MuCLP.Reducer.Config.
          { verbose = config.verbose; mode = WF (true, true, true) }
    end :
      MuCLP.Reducer.Config.ConfigType)

  module Qelim = MuCLP.Qelim.Make (
    struct
      let config =
        MuCLP.Qelim.Config.{ verbose = config.verbose; mode = SkolemPred }
    end :
      MuCLP.Qelim.Config.ConfigType)

  let chc_solver () =
    let open Or_error in
    ExtFile.unwrap config.chc_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  (* The main solver of the check of a side with no strategy unknown: the
     configured replacement if there is one, else [chc_solver ()].  Only the
     solver changes; the CHC it is given and the rule its answer is read by are
     those of any other check. *)
  module type CheckSolverType = PCSPSolver.Solver.SolverType

  let empty_strategy_chc_solver () =
    let open Or_error in
    match config.empty_strategy_chc_solver with
    | None -> chc_solver ()
    | Some f ->
        ExtFile.unwrap f >>= fun cfg ->
        PCSPSolver.Solver.(
          Ok
            (module Make (struct
              let config = cfg
            end) : SolverType))

  (* Budgets, in seconds, of the strategy check, each starting from
     [chc_initial_timeout].  Under [Global_doubling] both sides read the shared
     pair; under [Pass_turn_on_timeout] each side reads its own.  None is reset
     between turns: a budget only grows, and only when a check at that budget
     timed out. *)
  let chc_timeout = ref config.chc_initial_timeout
  let chc_timeout_backup = ref config.chc_initial_timeout
  let chc_timeout_primal = ref config.chc_initial_timeout
  let chc_timeout_dual = ref config.chc_initial_timeout
  let chc_timeout_backup_primal = ref config.chc_initial_timeout
  let chc_timeout_backup_dual = ref config.chc_initial_timeout

  (* The budget the check of side [turn] (true = primal) uses, with the main or
     the backup CHC solver. *)
  let chc_budget ~backup turn =
    match (config.chc_timeout_policy, backup, turn) with
    | Config.Global_doubling, false, _ -> chc_timeout
    | Global_doubling, true, _ -> chc_timeout_backup
    | Pass_turn_on_timeout, false, true -> chc_timeout_primal
    | Pass_turn_on_timeout, false, false -> chc_timeout_dual
    | Pass_turn_on_timeout, true, true -> chc_timeout_backup_primal
    | Pass_turn_on_timeout, true, false -> chc_timeout_backup_dual

  let backup_chc_solver () =
    let open Or_error in
    ExtFile.unwrap config.backup_chc_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let pcsp_solver () =
    let open Or_error in
    ExtFile.unwrap config.pcsp_solver >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let pcsp_solver_determ () =
    let open Or_error in
    ExtFile.unwrap config.pcsp_solver_determ >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  let optimizer_cfg = ExtFile.unwrap config.optimizer
  let verbose = true

  let preprocess ?(id = None) ?(elim_forall = true) ?(elim_exists = true)
      ?(elim_pvar_args = true) muclp =
    let open Or_error in
    optimizer_cfg >>= fun optimizer_cfg ->
    Ok (MuCLP.Optimizer.make optimizer_cfg)
    >>= fun (module Optimizer : MuCLP.Optimizer.OptimizerType) ->
    let muclp = if config.check_problem then check_problem muclp else muclp in
    Debug.print ~id
    @@ lazy
         (sprintf "######################\nbefore optimization: %s\n"
         @@ str_of muclp);
    let muclp =
      Optimizer.f ~id ~elim_forall ~elim_exists ~elim_pvar_args (simplify muclp)
    in
    Debug.print ~id
    @@ lazy
         (sprintf "after optimization: %s\n######################\n"
         @@ str_of muclp);
    Ok muclp

  (* [layout], when given, is cleared and receives, for every predicate of the
     returned problem that the reduction extended, the argument positions it
     prepended, keyed by the problem's name of the predicate ([U_P_]). *)
  let to_pfwcsp ?layout muclp =
    (* Skolemize quantifiers *)
    if verbose then
      Debug.print @@ lazy (sprintf "Input muCLP: %s\n" @@ str_of muclp);
    let muclp, univ_fns =
      Qelim.elim_exists ~conv_forall:(Config.name_universals config)
        (muclp, (Map.Poly.empty, Map.Poly.empty))
    in
    Debug.print ~id:None @@ lazy (sprintf "Skolemized: %s\n" @@ str_of muclp);
    let muclp =
      muclp |> aconv_tvar |> complete_tsort
      |> complete_psort (Kind.pred_sort_env_map_of univ_fns)
    in
    if verbose then
      Debug.print @@ lazy (sprintf "Preprocessed muCLP: %s\n" @@ str_of muclp);
    let pfwcsp, wfs =
      (* The greatest-fixpoint remembered-state encoding is not used: it
         served only the per-step facts below, which are disabled, and
         nothing else reads what it produces.  The opponent's decisions are
         still named ([conv_forall] above).  With it the first check alone
         grew by doubled arguments and a guard per recursive call, enough for
         inputs the plain encoding decides in seconds to exhaust a minute. *)
      let tbl = Hashtbl.Poly.create () in
      let res =
        Reducer.f ~id:None ~conv_nu:false ~layout:tbl ~exchange:false
          ~messenger:None muclp univ_fns
      in
      Option.iter layout ~f:(fun out ->
          Hashtbl.clear out;
          Hashtbl.iteri tbl ~f:(fun ~key ~data ->
              Hashtbl.set out
                ~key:(Ident.name_of_pvar @@ Ident.uninterp_pvar key)
                ~data));
      res
    in
    let pfwcsp =
      PCSP.Problem.add_formulas
        (* The dummy predicate variables for universal quantifiers are fixed to false *)
        (Set.Poly.filter_map
           (Map.to_set @@ fst univ_fns)
           ~f:(fun (x, s) ->
             if Kind.is_ord @@ Map.Poly.find_exn (snd univ_fns) x then
               let args =
                 Logic.mk_fresh_sort_env_list @@ Logic.Sort.args_of s
               in
               let papp =
                 Logic.ExtTerm.mk_var_app x
                   (List.map args ~f:(fst >> Logic.ExtTerm.mk_var))
               in
               Some
                 ( Map.Poly.of_alist_exn args,
                   Logic.BoolTerm.imply_of papp (Logic.BoolTerm.mk_bool false)
                 )
             else None))
        pfwcsp
    in
    Debug.print ~id:None
    @@ lazy
         (sprintf "******* Generated pfwCSP:\n%s" @@ PCSP.Problem.str_of pfwcsp);
    ( PCSP.Problem.map pfwcsp ~f:Logic.Term.refresh,
      Map.filter_keys (fst wfs) ~f:(Map.Poly.find_exn (snd wfs) >> Kind.is_ord)
    )

  let let_conc t =
    let open Ast.LogicOld in
    if Term.is_var t then
      Formula.mk_atom
      @@ Atom.mk_pvar_app (Ident.tvar_to_pvar @@ Term.tvar_of t) [] []
    else if T_bool.is_formula t then T_bool.let_formula t
    else failwith @@ Term.str_of t

  let rec let_asserted t =
    let open Ast.LogicOld in
    let ts =
      try
        let fvar, _, _, ts, _ = Term.let_fvar_app t in
        assert (String.(Ident.name_of_tvar fvar = "asserted"));
        ts
      with exn_ when not (Common.Timer.is_async exn_) ->
        let sym, ts, _ = Term.let_app t in
        Debug.print @@ lazy ("why " ^ Term.str_of_funsym sym);
        ts
    in
    match ts with
    | [ t ] -> let_conc t
    | _ ->
        if T_bool.is_formula t && (Formula.is_eq @@ T_bool.let_formula t) then
          let phi = T_bool.let_formula t in
          let t, _ (*ToDo*), _ = Formula.let_eq phi in
          let_asserted t
        else failwith @@ "let_asserted: " ^ Term.str_of t

  let rec let_hyper_res t =
    let open Ast.LogicOld in
    let ts =
      try
        let fvar, _, _, ts, _ = Term.let_fvar_app t in
        assert (String.(Ident.name_of_tvar fvar = "hyper-res"));
        ts
      with exn_ when not (Common.Timer.is_async exn_) ->
        let sym, ts, _ = Term.let_app t in
        Debug.print @@ lazy ("why " ^ Term.str_of_funsym sym);
        ts
    in
    match ts with
    | asserted :: rest ->
        let hress, con = List.rest_last rest in
        (let_asserted asserted, hress, let_conc con)
    | _ ->
        if T_bool.is_formula t && (Formula.is_eq @@ T_bool.let_formula t) then
          let phi = T_bool.let_formula t in
          let t, _ (*ToDo*), _ = Formula.let_eq phi in
          let_hyper_res t
        else failwith @@ "let_hyper_res: " ^ Term.str_of t

  let let_mp phi =
    let open Ast.LogicOld in
    let t, _, _ = Formula.let_eq phi in
    let ts =
      try
        let fvar, _, _, ts, _ = Term.let_fvar_app t in
        assert (String.(Ident.name_of_tvar fvar = "mp"));
        ts
      with exn_ when not (Common.Timer.is_async exn_) ->
        let sym, ts, _ = Term.let_app t in
        Debug.print @@ lazy ("why " ^ Term.str_of_funsym sym);
        ts
    in
    match ts with
    | [ ant1; ant2; con ] -> (ant1, let_asserted ant2, let_conc con)
    | _ -> assert false

  let rec analyze_cex hres ren =
    let open Ast.LogicOld in
    let ant, hress, con0 = let_hyper_res hres in
    let senv, ant, _ =
      if Formula.is_forall ant then Formula.let_forall ant else ([], ant, Dummy)
    in
    let (ants1, ants2), con =
      if Formula.is_imply ant then
        let ant, con, _ = Formula.let_imply ant in
        ( List.partition_tf ~f:(fun phi ->
              Formula.is_atom phi
              && (Atom.is_pvar_app @@ fst @@ Formula.let_atom phi))
          @@ Formula.conjuncts_list_of ant,
          con )
      else (([], []), ant)
    in
    let css, ants1 =
      List.unzip
      @@ List.map2_exn hress ants1 ~f:(fun hres ant ->
          let pvs = Formula.pvs_of ant in
          let ren =
            Map.of_set_exn
            @@ Set.Poly.map pvs ~f:(fun pvar ->
                ( pvar,
                  Ident.mk_fresh_pvar
                    ~prefix:(Some (Ident.name_of_pvar pvar ^ "$"))
                    () ))
          in
          (analyze_cex hres ren, Formula.rename_pvars ren ant))
    in
    let css1, css2 = List.unzip css in
    ( Set.add (Set.Poly.union_list css1)
      @@ Formula.mk_forall_if_bounded senv
      @@ Formula.mk_imply
           (Formula.and_of @@ ants1 @ ants2)
           (Formula.rename_pvars ren con),
      Set.add (Set.Poly.union_list css2) @@ Formula.rename_pvars ren con0 )

  (* The ground play a Spacer derivation records: each node is the conclusion
     the derivation derives there (a predicate application to ground terms) and
     its premises.  Read only for the conclusions, so the clause structure that
     [analyze_cex] builds is not repeated here. *)
  type play_node = {
    pvar : Ident.pvar;
    args : LogicOld.Term.t list;
    children : play_node list;
    clause : LogicOld.Formula.t;
        (** the clause the derivation applied to derive this node, as the
            derivation states it (universally closed, premises in the order of
            [children]) *)
  }

  let rec play_tree_of hres =
    let open Ast.LogicOld in
    let clause, hress, con = let_hyper_res hres in
    let pvar, args =
      if Formula.is_atom con then
        match fst @@ Formula.let_atom con with
        | Atom.App (Predicate.Var (pvar, _), args, _) -> (pvar, args)
        | _ -> (Ident.Pvar "", [])
      else (Ident.Pvar "", [])
    in
    { pvar; args; children = List.map hress ~f:play_tree_of; clause }

  (* For the opponent's ranking key [WF_P_], the pairs of ground states its
     ranking must contain for the checked side's derivation to be a play the
     opponent wins.  The opponent's least-fixpoint predicate [P] is visited at
     every node whose conclusion is an application of [U_P_] (the reduction's
     name for [P] in the checked side's clauses); along a root-to-leaf path the
     visits are in play order, root first.  Because the reduction lets the
     checked side keep any earlier visit as the remembered state, the ranking
     must contain EVERY pair (s_i, s_j) with i < j on a path, not only the
     consecutive ones -- Podelski and Rybalchenko's transition-invariant
     condition.  The state is the last [n] arguments of the conclusion, [n]
     being half the key's arity, since the reduction puts the remembered copy
     (and, for a predicate called from outside its component, a flag) first.
     The chain is RESET at a visit to a predicate of lower index (an outer
     equation of the hierarchical system), as in Kura and Unno's disjunctively
     well-founded game (Def. 6.4): the ranking of [P] need only decrease between
     visits to [P] with no outer predicate visited in between.  Without the
     reset the pairs would span outer visits, and on a play that returns to the
     same [P]-state through an outer predicate no ranking contains them, which
     is how a refinement came out unsatisfiable on every turn of an input whose
     outer least-fixpoint predicate shares a component with inner ones.
     [pred_index] maps the reduction's name for each predicate ([U_Q_]) to its
     position in the equation list; a name it does not hold (the query, the
     Skolem dummies) neither extends nor resets a chain. *)
  let pred_index : (string, int) Hashtbl.t = Hashtbl.create (module String)

  let set_pred_index muclp =
    Hashtbl.clear pred_index;
    List.iteri muclp.MuCLP.Problem.preds ~f:(fun i pred ->
        Hashtbl.set pred_index
          ~key:(Ident.name_of_pvar @@ Ident.uninterp_pvar pred.MuCLP.Pred.name)
          ~data:i)

  (* The argument positions the reduction prepended to each predicate, one
     table for the primal problem and one for the dual, keyed by the problem's
     name of the predicate ([U_P_]; see [MuCLP.Reducer.prefix_entry]).  Filled
     by [solve] from the reduction itself and read only under
     [copy_blind_choices]; a predicate absent from its side's table carries no
     copy. *)
  let copy_layout_primal : (string, MuCLP.Reducer.prefix_entry list) Hashtbl.t
      =
    Hashtbl.create (module String)

  let copy_layout_dual : (string, MuCLP.Reducer.prefix_entry list) Hashtbl.t =
    Hashtbl.create (module String)

  (* The reduction's name of the predicate the ranking key [WF_P_] ranks, as
     it occurs in the checked side's clauses; [None] for a key not so named. *)
  let rank_target_of wf_key =
    match
      String.chop_prefix (Ident.name_of_tvar wf_key) ~prefix:"WF_"
      |> Option.bind ~f:(String.chop_suffix ~suffix:"_")
    with
    | Some p -> Some (Ident.name_of_pvar @@ Ident.uninterp_pvar (Ident.Pvar p))
    | None -> None

  (* The play [tree] with every revisit cut out, and the number of cuts.  A
     node whose [state_of] is [Some s] and below which, with no [resets] node
     in between, another node has state [s] is replaced by the lowest such
     node on the first branch that has one; the search repeats from the node
     put in its place, which has no [s] below it in its segment, and then
     descends.

     Contract.  (1) Every root-to-leaf path of the result is a subsequence of
     a path of [tree] that removes only a stretch between two visits at one
     state with no reset in it, so the reset structure of the pairs that
     remain is unchanged and the pairs read from the result are a subset of
     those read from [tree].  (2) On every path of the result, the states of
     the nodes between two consecutive resets are pairwise distinct.  (3) The
     result is a subtree-replacement of [tree]: a node's children are those
     of some node of [tree].  When the two visits carry the same ground atom
     (not only the same state) the result is again a derivation of the same
     conclusion; otherwise it is the play the ranked side makes by taking, at
     a repeated state, the move of its last visit there, which the real game
     admits because a call's position is its arguments.

     Why.  A ranking is disjunctively well-founded, so it contains no (s, s);
     and a path s, t, s with no reset asks it for (s, t) and (t, s), which no
     well-founded relation holds, so a one-piece ranking cannot be found and a
     union can be found only by splitting the cycle between two pieces. *)
  let splice_revisits ~state_of ~resets tree =
    let cuts = ref 0 in
    (* the lowest node below [node] with state [st] on the first branch that
       has one, not crossing a reset *)
    let rec find_revisit st node =
      List.find_map node.children ~f:(fun child ->
          if resets child then None
          else
            match state_of child with
            | Some st' when Stdlib.( = ) st st' -> (
                match find_revisit st child with
                | Some lower -> Some lower
                | None -> Some child)
            | _ -> find_revisit st child)
    in
    let rec go node =
      match state_of node with
      | Some st -> (
          match find_revisit st node with
          | Some lower ->
              incr cuts;
              go lower
          | None -> { node with children = List.map node.children ~f:go })
      | None -> { node with children = List.map node.children ~f:go }
    in
    let tree = go tree in
    (tree, !cuts)

  let chain_pairs_of tree ~wf_key ~arity =
    let n = arity / 2 in
    match rank_target_of wf_key with
    | None -> []
    | Some target ->
        let state_of node =
          if
            String.(Ident.name_of_pvar node.pvar = target)
            && List.length node.args >= n
          then Some (List.drop node.args (List.length node.args - n))
          else None
        in
        let target_index = Hashtbl.find pred_index target in
        let resets node =
          match
            (target_index, Hashtbl.find pred_index (Ident.name_of_pvar node.pvar))
          with
          | Some ti, Some i -> i < ti
          | _ -> false
        in
        let rec go ancestors node =
          let here, ancestors' =
            match state_of node with
            | Some st ->
                ( List.map ancestors ~f:(fun a -> (a, st)),
                  st :: ancestors )
            | None -> ([], if resets node then [] else ancestors)
          in
          here @ List.concat_map node.children ~f:(go ancestors')
        in
        let tree =
          if config.splice_chain_revisits then (
            let tree, cuts = splice_revisits ~state_of ~resets tree in
            if cuts > 0 then
              Debug.print
              @@ lazy
                   (sprintf "## %d revisit(s) of %s cut out of the play" cuts
                      (Ident.name_of_tvar wf_key));
            tree)
          else tree
        in
        (* Without the cut, a pair (s, s) is a revisit, which no ranking
           contains; it is dropped and the rest of the cycle stays asked for.
           After the cut no path repeats a state within a segment, and the
           filter removes nothing. *)
        go [] tree
        |> List.dedup_and_sort ~compare:Stdlib.compare
        |> List.filter ~f:(fun (a, b) -> not (Stdlib.( = ) a b))

  (* For the ranking key [wf_key], the chain pairs of the play [tree] (as
     [chain_pairs_of] reads them, without the revisit cut) each stated as a
     REGION: the list of [((s, t), (vars, region))], where [vars] are fresh
     variables for the two states (the upper visit's first, then the lower
     visit's, [arity] of them in all, in the key's parameter order) and
     [region] a quantifier-free formula over [vars].

     How a region is formed.  Let [u = n_0, n_1, .., n_k = v] be the path of
     the derivation from the visit at [s] down to the visit at [t].  Each
     [n_i] ([i < k]) was derived by one clause instance whose head is [n_i]'s
     atom and one of whose premises is [n_{i+1}]'s; the conjunction of these
     instances, with fresh variables [x_i] for every node's arguments, is the
     path condition.  A premise off the path is dropped, except that when it
     is an application of one of [decisions] (the dummies naming the ranked
     side's own decisions, whose last argument is the value decided) that
     value is fixed at the one the play took, so the region is the steps the
     ranked side makes by repeating its move, under every choice of the
     checked side's universals.  The path condition is then projected onto
     the states of [x_0] and [x_k] by model-based projection, at the model
     assigning every [x_i] the play's arguments.  [passed node x_i] adds, for
     each [n_i] ([i < k]), conditions over [x_i] that hold at the play's
     arguments of [n_i] (the losing conditions of the alternatives the ranked
     side passed over there, see [PassedChoices]); they only narrow the path
     condition, so the region they give is a subset of the one without them
     and still contains [(s, t)].

     Contract.  (1) [region] holds at [(s, t)]: a region the ground pair does
     not satisfy is discarded, which the projection's own postcondition makes
     unreachable.  (2) [region] implies the existential closure of the path
     condition, so every pair in it is joined by a path of this shape.  (3) A
     pair whose path cannot be read (a clause not of the implication shape,
     premises not matching the node's children), whose projection raises, or
     whose region is [true] or mentions no variable, gets no entry: its
     ground pair is still asked by the caller.  Nothing here decides an
     answer: the regions only constrain a copy the strategy check judges. *)
  let chain_regions_of ?(passed = fun _ _ -> []) ~decisions tree ~wf_key
      ~arity =
    let open Ast.LogicOld in
    let n = arity / 2 in
    match rank_target_of wf_key with
    | None -> []
    | Some target ->
        let state_of node =
          if
            String.(Ident.name_of_pvar node.pvar = target)
            && List.length node.args >= n
          then Some (List.drop node.args (List.length node.args - n))
          else None
        in
        let target_index = Hashtbl.find pred_index target in
        let resets node =
          match
            (target_index, Hashtbl.find pred_index (Ident.name_of_pvar node.pvar))
          with
          | Some ti, Some i -> i < ti
          | _ -> false
        in
        (* every chain pair with the path segment that asks it, upper visit
           first; the same traversal as [chain_pairs_of] *)
        let rec go path_rev ancestors node =
          let path_rev' = node :: path_rev in
          let here, ancestors' =
            match state_of node with
            | Some st ->
                ( List.map ancestors ~f:(fun (a, depth) ->
                      ( (a, st),
                        List.rev
                          (List.take path_rev'
                             (List.length path_rev' - depth)) )),
                  (st, List.length path_rev) :: ancestors )
            | None -> ([], if resets node then [] else ancestors)
          in
          here @ List.concat_map node.children ~f:(go path_rev' ancestors')
        in
        let segments =
          go [] [] tree
          |> List.filter ~f:(fun ((a, b), _) -> not (Stdlib.( = ) a b))
          |> List.stable_sort ~compare:(fun (p1, _) (p2, _) ->
              Stdlib.compare p1 p2)
          |> List.remove_consecutive_duplicates ~equal:(fun (p1, _) (p2, _) ->
              Stdlib.( = ) p1 p2)
        in
        let region_of path =
          let vars =
            List.map path ~f:(fun node ->
                List.map node.args ~f:(fun arg ->
                    ( Ident.mk_fresh_tvar ~prefix:(Some "GP_") (),
                      Term.sort_of arg )))
          in
          let eqs ts vs =
            List.map2_exn ts vs ~f:(fun t (v, s) -> Formula.eq t (Term.mk_var v s))
          in
          let atom_args phi =
            match fst (Formula.let_atom phi) with
            | Atom.App (Predicate.Var (pvar, _), args, _) -> (pvar, args)
            | _ -> raise Exit
          in
          let rec instances = function
            | (node, xs) :: ((next, xs') :: _ as rest) ->
                let senv, body =
                  if Formula.is_forall node.clause then
                    let senv, body, _ = Formula.let_forall node.clause in
                    (senv, body)
                  else ([], node.clause)
                in
                let body =
                  Formula.rename
                    (Map.Poly.of_alist_exn
                    @@ List.map senv ~f:(fun (x, _) ->
                        (x, Ident.mk_fresh_tvar ~prefix:(Some "GC_") ())))
                    body
                in
                if not (Formula.is_imply body) then raise Exit;
                let ant, con, _ = Formula.let_imply body in
                let premises, pure =
                  List.partition_tf (Formula.conjuncts_list_of ant)
                    ~f:(fun phi ->
                      Formula.is_atom phi
                      && Atom.is_pvar_app (fst (Formula.let_atom phi)))
                in
                if List.length premises <> List.length node.children then
                  raise Exit;
                let _, head_args = atom_args con in
                if List.length head_args <> List.length xs then raise Exit;
                let premise_eqs =
                  List.concat
                  @@ List.map2_exn premises node.children ~f:(fun phi child ->
                      let pvar, args = atom_args phi in
                      if phys_equal child next then (
                        if List.length args <> List.length xs' then raise Exit;
                        eqs args xs')
                      else if
                        Set.mem decisions (Ident.name_of_pvar pvar)
                        && (not (List.is_empty args))
                        && List.length args = List.length child.args
                      then
                        [ Formula.eq (List.last_exn args) (List.last_exn child.args) ]
                      else [])
                in
                (eqs head_args xs @ premise_eqs @ pure @ passed node xs)
                @ instances rest
            | _ -> []
          in
          let phi = Formula.and_of (instances (List.zip_exn path vars)) in
          let states xs = List.drop xs (List.length xs - n) in
          let kept = states (List.hd_exn vars) @ states (List.last_exn vars) in
          let model =
            Map.Poly.of_alist_exn
            @@ List.concat
            @@ List.map2_exn path vars ~f:(fun node xs ->
                List.map2_exn xs node.args ~f:(fun (v, _) t -> (v, t)))
          in
          let kept_set = Set.Poly.of_list (List.map kept ~f:fst) in
          let eliminated =
            Set.filter (Formula.term_sort_env_of phi) ~f:(fun (x, _) ->
                not (Set.mem kept_set x))
          in
          let region =
            Evaluator.simplify
            @@ MuCyc.ProofSearch.get_mbp_with ~ite_size_limit:(Some 1_000)
                 ~check_validity:false
                 ~print:(fun _ -> ())
                 model eliminated phi
          in
          let holds =
            Evaluator.eval @@ Evaluator.simplify
            @@ Formula.subst
                 (Map.Poly.filter_keys model ~f:(Set.mem kept_set))
                 region
          in
          (* A region the ranking must contain is useless when it is not
             well-founded itself: the re-synthesis then has no solution and
             its budget is spent before the ground attempt runs.  Projection
             can drop the floor that made the play's chain finite, so a region
             with no linear ranking is dropped (the ground pair stays asked). *)
          let xs = states (List.hd_exn vars) and ys = states (List.last_exn vars) in
          if
            holds
            && Set.is_subset (Formula.fvs_of region) ~of_:kept_set
            && (not (Set.is_empty (Formula.fvs_of region)))
            && not
                 (Stdlib.( = )
                    (RankingCheck.region_has_linear_ranking xs ys region)
                    (Some false))
          then Some (kept, region)
          else (
            Debug.print
            @@ lazy
                 (sprintf "## region dropped (no linear ranking, or not a region): %s"
                    (Formula.str_of region));
            None)
        in
        List.filter_map segments ~f:(fun (pair, path) ->
            match region_of path with
            | Some r -> Some (pair, r)
            | None -> None
            | exception exn_ when not (Common.Timer.is_async exn_) ->
                Debug.print
                @@ lazy
                     (sprintf "## no region for a chain pair of %s: %s"
                        (Ident.name_of_tvar wf_key) (Exn.to_string exn_));
                None)

  (* The EXITS of the play [tree] from the chains the opponent's rankings
     cover, as the atoms to block, per predicate name: its arity and its
     ground argument tuples.  A node is on a chain path when it is the root,
     or an application of a predicate some key of [wf_strat] ranks, or has
     such an application below it; an exit is a child of an on-path node that
     is not itself on a path -- a side premise of the query, or the premise by
     which a chain ends (the base case under its last visit).  Blocking the
     exits and nothing on the paths leaves the chains themselves available, so
     the next derivation has to reach the query by another side premise or
     continue a chain past the state where the previous one stopped, which is
     what lengthens the chain pairs.  Blocking the ranked states instead
     removes the chain a counter-play is forced through and leaves no play.
     Empty when the play visits no ranked predicate. *)
  let exits_of tree wf_strat =
    let targets =
      Set.Poly.of_list @@ List.filter_map ~f:rank_target_of
      @@ Map.Poly.keys wf_strat
    in
    let is_target node = Set.mem targets (Ident.name_of_pvar node.pvar) in
    let rec on_path node =
      is_target node || List.exists node.children ~f:on_path
    in
    let exits = ref [] in
    let rec go node =
      List.iter node.children ~f:(fun child ->
          if on_path child then go child
          else if not (String.is_empty (Ident.name_of_pvar child.pvar)) then
            exits := (Ident.name_of_pvar child.pvar, child.args) :: !exits)
    in
    if not (on_path tree) then Map.Poly.empty
    else (
      go tree;
      List.fold !exits ~init:Map.Poly.empty ~f:(fun acc (name, args) ->
          Map.Poly.update acc name ~f:(function
            | None -> (List.length args, [ args ])
            | Some (n, argss) -> (n, args :: argss)))
      |> Map.Poly.map ~f:(fun (n, argss) ->
             (n, List.dedup_and_sort ~compare:Stdlib.compare argss)))

  (* The checked CHC [chc] with the atoms [blocked] (per predicate name, the
     arity and the ground argument tuples) excluded as PREMISES: every
     negative occurrence of [P(t)] becomes [P(t) /\ t <> a_1 /\ ..].  A negative
     occurrence made smaller makes its formula larger, so each blocked formula
     is implied by the original and the blocked system is a weakening: when it
     is unsatisfiable so is the original, and every clause instance its
     derivation uses is an instance of the original clause, so the derivation
     is a counter-play of the checked strategy.  Head occurrences are left
     alone (a guard there would add a goal rather than remove a derivation).
     Formulas mentioning no blocked predicate are passed through unconverted.
     [None] when no occurrence was blocked. *)
  let block_states chc blocked =
    let open LogicOld in
    let exi_senv = PCSP.Problem.senv_of chc in
    let blocked_names = Set.Poly.of_list @@ Map.Poly.keys blocked in
    let changed = ref false in
    let phis =
      Set.Poly.map (PCSP.Problem.formulas_of chc) ~f:(fun (uni_senv, phi) ->
          if
            not
              (Set.exists (Logic.Term.fvs_of phi) ~f:(fun v ->
                   Set.mem blocked_names (Ident.name_of_tvar v)))
          then (uni_senv, phi)
          else
            let phi' =
              Formula.map_atom_polarity
                (Logic.ExtTerm.to_old_fml exi_senv uni_senv phi)
                true
                ~f:(fun polarity atom ->
                  match atom with
                  | Atom.App (Predicate.Var (pvar, _), ts, _) when not polarity
                    -> (
                      match Map.Poly.find blocked (Ident.name_of_pvar pvar) with
                      | Some (n, states) when List.length ts >= n ->
                          let st = List.drop ts (List.length ts - n) in
                          let guards =
                            List.filter_map states ~f:(fun s ->
                                if List.length s = n then
                                  Some
                                    (Formula.mk_neg @@ Formula.and_of
                                    @@ List.map2_exn st s ~f:Formula.eq)
                                else None)
                          in
                          if List.is_empty guards then Formula.mk_atom atom
                          else (
                            changed := true;
                            Formula.and_of (Formula.mk_atom atom :: guards))
                      | _ -> Formula.mk_atom atom)
                  | _ -> Formula.mk_atom atom)
            in
            (uni_senv, Logic.ExtTerm.of_old_formula phi'))
    in
    if !changed then
      Some (PCSP.Problem.of_formulas ~params:(PCSP.Problem.params_of chc) phis)
    else None

  (* Up to [counter_plays_per_check - 1] further counter-plays of the check
     [chc] beyond the one [cex] records, each asked of [solver] at [budget]
     seconds with the exits of every play found so far blocked ([exits_of],
     [block_states]), so that each answer is a different play.  Collection
     stops at the first query that does not return a counter-play, when a play
     adds no state to block, or on any failure but an asynchronous one; the
     plays found until then are kept.  So the check takes at most
     [counter_plays_per_check] times its budget.  Nothing here decides an
     answer: the plays only feed the opponent's ranking refinement. *)
  let extra_counter_plays (module S : CheckSolverType) ~budget wf_strat chc
      cex =
    let k = config.counter_plays_per_check in
    if k <= 1 || not (Config.chain_pairs_from_play config) then []
    else
      let found = ref [] in
      let merge m1 m2 =
        Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
          | `Left v | `Right v -> Some v
          | `Both ((n, a), (_, b)) ->
              Some (n, List.dedup_and_sort ~compare:Stdlib.compare (a @ b)))
      in
      let same m1 m2 =
        Map.Poly.equal (fun (n1, a) (n2, b) -> n1 = n2 && Stdlib.( = ) a b) m1 m2
      in
      let count m =
        Map.Poly.fold m ~init:0 ~f:(fun ~key:_ ~data:(_, sts) acc ->
            acc + List.length sts)
      in
      let rec loop blocked tree i =
        if i < k then
          let blocked' = merge blocked (exits_of tree wf_strat) in
          if not (same blocked blocked') then
            match block_states chc blocked' with
            | None -> ()
            | Some chc' -> (
                Debug.print
                @@ lazy
                     (sprintf
                        "### Asking for counter-play %d of %d (%d sec.) with %d \
                         exit atom(s) blocked: %s"
                        (i + 1) k budget (count blocked')
                        (String.concat_map_list ~sep:"; "
                           (Map.Poly.to_alist blocked') ~f:(fun (p, (_, argss)) ->
                             String.concat_map_list ~sep:" " argss ~f:(fun ts ->
                                 sprintf "%s(%s)" p
                                   (String.concat_map_list ~sep:","
                                      ~f:LogicOld.Term.str_of ts)))));
                match S.solve ~timeout:(Some budget) chc' with
                | Ok (PCSP.Problem.Unsat (Some (PCSP.Problem.Formula cex')), _)
                  ->
                    let hres, _, _ = let_mp cex' in
                    let tree' = play_tree_of hres in
                    found := tree' :: !found;
                    Debug.print
                    @@ lazy (sprintf "### Counter-play %d found" (i + 1));
                    loop blocked' tree' (i + 1)
                | Ok (sol, _) ->
                    Debug.print
                    @@ lazy
                         (sprintf "### No counter-play %d: %s" (i + 1)
                            (PCSP.Problem.str_of_sol_with_witness sol))
                | Error err ->
                    Debug.print
                    @@ lazy
                         (sprintf "### No counter-play %d: %s" (i + 1)
                            (Error.to_string_hum err)))
      in
      (try
         let hres, _, _ = let_mp cex in
         loop Map.Poly.empty (play_tree_of hres) 1
       with exn when not (Common.Timer.is_async exn) ->
         Debug.print
         @@ lazy
              (sprintf "### Extra counter-plays stopped (%s)"
                 (Exn.to_string exn)));
      List.rev !found

  exception NoRefinement

  (* Under [demonic_fallback_on_undecided_check]: per side ([true] the primal)
     and key name, the term set the side's strategy had at its last check and
     the terms that set added over the one checked before it.  Updated only
     when the set changes, so a retried check of the same strategy keeps the
     record of what was new.  It only orders the restricted copies. *)
  let checked_terms :
      (bool * string, Logic.term Set.Poly.t * Logic.term Set.Poly.t) Hashtbl.Poly.t =
    Hashtbl.Poly.create ()

  let note_checked_terms turn strat_fn =
    Map.Poly.iteri strat_fn ~f:(fun ~key ~data:(_, terms) ->
        let k = (turn, Ident.name_of_tvar key) in
        match Hashtbl.find checked_terms k with
        | Some (last, _) when Set.equal last terms -> ()
        | Some (last, _) ->
            Hashtbl.set checked_terms ~key:k ~data:(terms, Set.diff terms last)
        | None -> Hashtbl.set checked_terms ~key:k ~data:(terms, Set.Poly.empty))

  let is_fresh_term turn key term =
    match Hashtbl.find checked_terms (turn, Ident.name_of_tvar key) with
    | Some (_, fresh) -> Set.mem fresh term
    | None -> false

  (* Consecutive turns on which a refinement added nothing, counted only under
     [pass_turn_on_no_refinement].  A refinement that adds nothing leaves the
     strategies as they were, so the next check returns the same derivation and
     the alternation would repeat forever; two such turns in a row (one per side)
     end the run with [unknown].  The verdicts themselves do not depend on this:
     [valid] and [invalid] come only from an exact check of one side's strategy
     against every behaviour of the other.  Reset at each [solve]. *)
  let stalls = ref 0

  (* Under [resynthesise_wf_rankings]: per ranking key (by name), every chain
     pair an accepted refinement of it has asked for.  A key names the ranking
     of one fixpoint predicate on the side where that predicate is a least
     fixpoint, so primal and dual keys never share a name.  Reset at each
     [solve]. *)
  let wf_rank_pairs :
      (string, (LogicOld.Term.t list * LogicOld.Term.t list) list) Hashtbl.t =
    Hashtbl.create (module String)

  (* Per ranking key (by name), the ranking last produced by re-synthesis as
     one [WF]-kind template instance, which is well-founded whatever the
     template's parameters.  Compared with the strategy's current term by
     physical equality, so a ranking changed in any other way (a disjoined
     piece) is never taken for one of these.  Reset at each [solve]. *)
  let wf_by_construction : (string, Logic.term) Hashtbl.t =
    Hashtbl.create (module String)

  (* Under [generalise_chain_pairs]: per ranking key (by name), the regions
     (see [chain_regions_of]) of the refinements whose generalised problem
     was the one solved, each as its variables (the two states, in the key's
     parameter order) and a formula over them.  Every later generalised
     re-synthesis of the key asks its copy to contain all of them again, as
     [wf_rank_pairs] does for the ground pairs.  Reset at each [solve]. *)
  let wf_rank_regions :
      (string, (LogicOld.sort_env_list * LogicOld.Formula.t) list) Hashtbl.t =
    Hashtbl.create (module String)

  (* [ranking_contains ranking (a, b)]: whether the ranking [ranking] (a
     lambda over the two states' positions) holds at the ground pair [(a, b)],
     decided by substituting the pair and simplifying.  True only when the
     simplified formula is [true]; a ranking of another arity, a formula the
     simplifier leaves undecided, or a failed conversion answers false, the
     answer that lets the caller change the ranking. *)
  let ranking_contains ranking (a, b) =
    let args, body = Logic.Term.let_lam ranking in
    let pair = a @ b in
    if List.length args <> List.length pair then false
    else
      try
        let sub =
          Map.Poly.of_alist_exn
            (List.map2_exn args pair ~f:(fun (x, _) t ->
                 (x, Logic.ExtTerm.of_old_term t)))
        in
        LogicOld.Formula.is_true @@ Evaluator.simplify
        @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
             (Map.Poly.of_alist_exn args)
             (Logic.ExtTerm.subst sub body)
      with exn when not (Common.Timer.is_async exn) -> false

  (* Whether the directed graph of the ground pairs [pairs] has a cycle.  A
     relation containing a cycle is not well-founded, and a finite acyclic set
     of pairs is contained in its transitive closure, a finite strict order,
     which is well-founded; so this decides whether SOME well-founded relation
     contains the pairs (whether the ranking template can express one is a
     separate question).  States are compared as [chain_pairs_of] compares
     them. *)
  let pairs_cyclic pairs =
    let succs =
      List.fold pairs ~init:Map.Poly.empty ~f:(fun m (a, b) ->
          Map.Poly.update m a ~f:(function None -> [ b ] | Some l -> b :: l))
    in
    (* 1 on the current path, 2 finished *)
    let colour = ref Map.Poly.empty in
    let rec visit s =
      match Map.Poly.find !colour s with
      | Some 1 -> true
      | Some _ -> false
      | None ->
          colour := Map.Poly.set !colour ~key:s ~data:1;
          let found =
            List.exists
              (Option.value ~default:[] (Map.Poly.find succs s))
              ~f:visit
          in
          colour := Map.Poly.set !colour ~key:s ~data:2;
          found
    in
    List.exists pairs ~f:(fun (a, _) -> visit a)

  (* Compared on the simplified first-order form, as [print_strat] shows it: a
     refinement that joins a ranking already present grows the term
     syntactically ([or] of the old and the new) without changing it, and a
     comparison of the raw terms would count that as progress.  A ranking is
     a lambda over its parameters; a Skolem key's term is a body over the
     key's parameters, which are therefore passed for it (read without them,
     every such term failed the conversion as an unbound variable and fell
     back to the raw comparison). *)
  let same_strategy (wf1, fn1, _) (wf2, fn2, _) =
    let str_body params body t =
      try
        LogicOld.Formula.str_of @@ Evaluator.simplify
        @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
             (Map.Poly.of_alist_exn params) body
      with exn when not (Common.Timer.is_async exn) -> Logic.ExtTerm.str_of t
    in
    let str t =
      let args, body = Logic.Term.let_lam t in
      str_body args body t
    in
    Map.Poly.equal (fun t1 t2 -> String.(str t1 = str t2)) wf1 wf2
    && Map.Poly.equal
         (fun (ps1, ts1) (ps2, ts2) ->
           Set.equal
             (Set.Poly.map ts1 ~f:(fun t -> str_body ps1 t t))
             (Set.Poly.map ts2 ~f:(fun t -> str_body ps2 t t)))
         fn1 fn2

  let solspace =
    ref
      (Map.Poly.of_alist_exn
         [
           (SolSpace.ND, Some 1);
           (SolSpace.NC, Some 1);
           (SolSpace.NP, Some 1);
           (SolSpace.NDC, Some 1);
           (SolSpace.NL, Some 1);
         ])

  let refine_solspace wf fn =
    let f = function
      | None -> None
      | Some None -> Some 1
      | Some (Some n) -> Some (n + 1)
    in
    if fn then
      solspace :=
        Map.Poly.update ~f
          (Map.Poly.update ~f !solspace SolSpace.ND)
          SolSpace.NC;
    if wf then
      solspace :=
        Map.Poly.update ~f
          (Map.Poly.update ~f
             (Map.Poly.update ~f !solspace SolSpace.NP)
             SolSpace.NDC)
          SolSpace.NL

  let use_solspace = false

  let print_strat key args phi' =
    Debug.print
    @@ lazy
         (sprintf "%s(%s) := %s" (Ident.name_of_tvar key)
            (String.concat_map_list ~sep:"," args
               ~f:(fst >> Ident.name_of_tvar))
            (LogicOld.Formula.str_of @@ Evaluator.simplify
            @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                 (Map.Poly.of_alist_exn args)
                 phi'))

  let z3_solve =
    let module Z3interface =
      Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
    fun senv phi -> Z3interface.check_sat [ phi ] senv (Z3.mk_context [])

  (* [Some sol] when the refinement problem is a pure existential over its
     Skolem unknowns and [SkolemTerms.solve] solves it; [None] sends the
     caller to the constraint solver.  Any exception but an asynchronous one
     (a timeout must reach the timer) is a fallback too: the selection is an
     optimisation and must never be the reason a refinement fails. *)
  let select_skolem_solution ?origin_of pfwcsp =
    try
      let policy = ref [] in
      let sol, inverted, guarded =
        SkolemTerms.solve ?origin_of
          ~prefer_bound:config.select_prefer_bound
          ~report:(fun line -> policy := line :: !policy)
          pfwcsp
      in
      Debug.print
      @@ lazy
           (sprintf "## Skolem terms by model-guided selection%s:\n%s%s%s"
              (if List.is_empty !policy then ""
               else " (" ^ String.concat ~sep:"; " (List.rev !policy) ^ ")")
              (String.concat_map_list ~sep:"\n" (Map.Poly.to_alist sol)
                 ~f:(fun (k, t) ->
                   Ident.name_of_tvar k ^ " := " ^ Logic.ExtTerm.str_of t))
              (String.concat_map_list inverted ~f:(fun (k, what) ->
                   sprintf "\n## argument of %s %s" (Ident.name_of_tvar k)
                     what))
              (String.concat_map_list guarded ~f:(fun (k, what) ->
                   sprintf "\n## guards for the copies of %s: %s"
                     (Ident.name_of_tvar k) what)));
      Some sol
    with
    | SkolemTerms.Shape_mismatch reason ->
        Debug.print
        @@ lazy
             (sprintf "## Skolem term selection does not apply (%s); asking PCSat"
                reason);
        None
    | exn when not (Common.Timer.is_async exn) ->
        Debug.print
        @@ lazy
             (sprintf "## Skolem term selection failed (%s); asking PCSat"
                (Exn.to_string exn));
        None

  (* [Some (skolem_part, ranking_part)] when [pfwcsp] mixes Skolem keys
     ([FN]) with ranking copies ([WF]/[DWF]) and its formulas split into those
     mentioning a ranking copy and the rest with no unknown shared between the
     two groups; [None] otherwise.  Each part keeps the whole problem's
     parameters with its unknowns restricted to the ones it mentions.  Sharing
     no unknown, the two parts are independent: a solution of each is a
     solution of the whole, and a solution of the whole restricts to one of
     each.  On the refinement problems built here the ranking copies are
     constrained by ground chain-pair facts alone, so the split is the
     separation of the ranking fit from the Skolem part.  Measured on three
     games: the split replaced 13 to 19 template terms per refinement by one
     to four selected terms, and the check that followed timed out as before,
     so the term count was not what made that check slow. *)
  let split_mixed_refinement pfwcsp =
    let params = PCSP.Problem.params_of pfwcsp in
    let senv = params.PCSP.Params.senv in
    let kind x = PCSP.Problem.kind_of pfwcsp x in
    let is_rank x = Kind.is_wf (kind x) || Kind.is_dwf (kind x) in
    let unknowns_of (_, t) =
      Set.filter (Logic.Term.fvs_of t) ~f:(Map.Poly.mem senv)
    in
    let rank_fs, rest_fs =
      Set.partition_tf (PCSP.Problem.formulas_of pfwcsp) ~f:(fun f ->
          Set.exists (unknowns_of f) ~f:is_rank)
    in
    let unknowns fs =
      Set.Poly.union_list (List.map (Set.to_list fs) ~f:unknowns_of)
    in
    let rank_us = unknowns rank_fs and rest_us = unknowns rest_fs in
    if
      Set.is_empty rank_fs || Set.is_empty rest_fs
      || (not (Set.is_empty (Set.inter rank_us rest_us)))
      || not (Set.exists rest_us ~f:(fun x -> Kind.is_fn (kind x)))
    then None
    else
      let part fs us =
        PCSP.Problem.of_formulas
          ~params:
            {
              params with
              PCSP.Params.senv = Map.Poly.filter_keys senv ~f:(Set.mem us);
              (* already among [formulas_of]'s formulas *)
              stable_clauses = Set.Poly.empty;
            }
          fs
      in
      Some (part rest_fs rest_us, part rank_fs rank_us)

  (* A diagnostic, never a decision: re-check the kind constraints of an
     accepted refinement's solution [sol] of [pfwcsp] -- each ranking copy is
     declared [DWF], and it passes when [sol] lies inside the decrease relation
     of the ranking certificate [certs] records for it, so that every piece is
     well-founded -- and print the tally.  Nothing it finds changes the
     refinement; a failure is printed prominently so that it is seen.  A
     ranking with no recorded certificate (an answer that did not come from
     the ranking template) is counted unchecked. *)
  let check_refinement_kinds pfwcsp sol ~certs =
    let module W = PCSat.WitnessChecker in
    match
      try
        Ok
          (W.check_kind_constraints ~id:(PCSP.Problem.id_of pfwcsp) ~certs
             pfwcsp sol W.empty)
      with exn_ when not (Common.Timer.is_async exn_) -> Error exn_
    with
    | Ok r ->
        Debug.print @@ lazy (W.str_of_report "refinement-kind" r);
        if not (List.is_empty r.W.failed) then
          Debug.print
          @@ lazy
               (sprintf
                  "!!!!!!!! REFINEMENT KIND CHECK FAILED (%d): an accepted \
                   ranking is not certified well-founded by its recorded \
                   certificate; the refinement is used unchanged !!!!!!!!"
                  (List.length r.W.failed))
    | Error exn_ ->
        Debug.print
        @@ lazy
             (sprintf
                "(refinement-kind-check (passed 0) (unchecked 1) (failed 0)\n\
                \ (unchecked \"the checker raised: %s\" 1))"
                (String.substr_replace_all ~pattern:"\"" ~with_:"'"
                   (Exn.to_string exn_)))

  (* [solve_certs], when given, is [solve] returning the kind certificates of
     a [Sat] answer as well; it is used in place of [solve] only under
     [check_refinement_kinds], to re-check an accepted refinement's rankings.
     The answer it gives is the one [solve] gives. *)
  let refine_strat ?(extra_plays = []) ?check ?solve_certs ?solve_wf solve
      cex (dual_strat_wf, dual_strat_fn, dual_nu_wfs) =
    let open Ast.LogicOld in
    (* Under [chain_pair_regions_with_passed_choices] (read only with
       [generalise_chain_pairs]): the losing conditions of the alternatives
       the ranked side passed over at a node of the play, read from the
       clauses of the check [check] that returned the play
       ([PassedChoices]), computed once per predicate and kept here.  They
       narrow the chain-pair regions and nothing else; without [check] or
       with the field off, no condition. *)
    let passed =
      match check with
      | Some chc
        when config.generalise_chain_pairs
             && config.chain_pair_regions_with_passed_choices ->
          let clauses =
            lazy
              (try
                 let exi_senv = PCSP.Problem.senv_of chc in
                 PCSP.Problem.clauses_of (PCSP.Problem.to_cnf chc)
                 |> Set.to_list
                 |> List.map ~f:(fun c ->
                     let senv, ps, ns, phi = Clause.to_old_clause exi_senv c in
                     (Logic.to_old_sort_env_map senv, ps, ns, phi))
               with exn when not (Common.Timer.is_async exn) ->
                 Debug.print
                 @@ lazy
                      (sprintf "## passed-choice conditions unavailable: %s"
                         (Exn.to_string exn));
                 [])
          in
          let cache = Hashtbl.create (module String) in
          let qelim phi =
            Z3Smt.Z3interface.qelim ~timeout:(Some 1000) ~id:None
              ~fenv:(get_fenv ()) phi
          in
          fun (node : play_node) xs ->
            if List.is_empty xs || String.is_empty (Ident.name_of_pvar node.pvar)
            then []
            else
              let params, conds =
                Hashtbl.find_or_add cache (Ident.name_of_pvar node.pvar)
                  ~default:(fun () ->
                    let params =
                      List.map xs ~f:(fun (_, s) ->
                          (Ident.mk_fresh_tvar ~prefix:(Some "PCP_") (), s))
                    in
                    let conds =
                      PassedChoices.losing_conditions ~qelim
                        (Lazy.force clauses) node.pvar params
                    in
                    Debug.print
                    @@ lazy
                         (sprintf
                            "## passed-choice condition(s) of %s over (%s): %s"
                            (Ident.name_of_pvar node.pvar)
                            (String.concat_map_list ~sep:"," params
                               ~f:(fst >> Ident.name_of_tvar))
                            (if List.is_empty conds then "none"
                             else
                               String.concat_map_list ~sep:"; " conds
                                 ~f:Formula.str_of));
                    (params, conds))
              in
              if List.is_empty conds || List.length params <> List.length xs
                 || List.length node.args <> List.length xs
              then []
              else
                PassedChoices.at_point conds params ~point:node.args ~vars:xs
      | _ -> fun _ _ -> []
    in
    (*if verbose then*)
    Debug.print @@ lazy (sprintf "## cex: %s\n" (Formula.str_of cex));
    let play =
      if Config.chain_pairs_from_play config then
        let hres, _, _ = let_mp cex in
        Some (play_tree_of hres)
      else None
    in
    let problem, _model =
      let hres, query, _ = let_mp cex in
      let ren, query =
        let ant, con, _ = Formula.let_imply query in
        let pvs = Formula.pvs_of ant in
        let ren =
          Map.of_set_exn
          @@ Set.Poly.map pvs ~f:(fun pvar ->
              ( pvar,
                Ident.mk_fresh_pvar
                  ~prefix:(Some (Ident.name_of_pvar pvar ^ "$"))
                  () ))
        in
        (ren, Formula.mk_imply (Formula.rename_pvars ren ant) con)
      in
      let cs, model = analyze_cex hres ren in
      let cs = Set.add cs query in
      let model =
        Set.Poly.map model ~f:(fun phi ->
            let pvar, _sorts, ts, _ =
              Atom.let_pvar_app @@ fst @@ Formula.let_atom phi
            in
            (pvar, List.map ~f:Logic.ExtTerm.of_old_term ts))
      in
      let params =
        PCSP.Params.make @@ Logic.of_old_sort_env_map @@ Map.of_set_exn
        @@ Set.concat_map cs
             ~f:(Formula.pred_sort_env_of >> Term.pred_to_sort_env)
      in
      let cs =
        Set.Poly.map cs ~f:(fun phi ->
            let senv, phi = Formula.rm_quant ~forall:true phi in
            (Map.of_set_exn senv, phi))
      in
      (PCSP.Problem.of_old_formulas ~params cs, model)
    in
    Debug.print
    @@ lazy (sprintf "## cex in CHCs:\n%s\n" @@ PCSP.Problem.str_of problem);
    let module Preprocessor = Preprocessor.Make (struct
      (* every preprocessing field takes its default; the call below passes
         [~refute:false], since this clause set is not asked whether it is
         satisfiable (its strategy predicates are placeholders to be
         synthesised anew, and it may be unsatisfiable as it stands) *)
      let config = Preprocessor.Config.make true false Int.max_value 4 false
    end) in
    let orig_keys_wf = Map.Poly.key_set dual_strat_wf in
    let orig_keys_fn = Map.Poly.key_set dual_strat_fn in
    let wf_senv_problem =
      Map.Poly.filter_keys (PCSP.Problem.senv_of problem) ~f:(fun x ->
          Set.exists orig_keys_wf ~f:(fun key ->
              String.is_prefix (Ident.name_of_tvar x)
                ~prefix:(Ident.name_of_tvar key ^ "$")))
    in
    let keys_wf = Map.Poly.key_set wf_senv_problem in
    let fn_senv_problem =
      Map.Poly.filter_keys (PCSP.Problem.senv_of problem) ~f:(fun x ->
          Set.exists orig_keys_fn ~f:(fun key ->
              String.is_prefix (Ident.name_of_tvar x)
                ~prefix:(Ident.name_of_tvar key ^ "$")))
    in
    let keys_fn = Map.Poly.key_set fn_senv_problem in
    let senv_problem = Map.force_merge wf_senv_problem fn_senv_problem in
    let _, problem =
      let bpvs = Map.Poly.key_set senv_problem in
      Preprocessor.preprocess problem ~bpvs ~refute:false
    in
    Debug.print
    @@ lazy
         (sprintf "## preprocessed cex in CHCs:\n%s\n"
         @@ PCSP.Problem.str_of problem);
    (* The refinement problem for the plays [plays] (the first play, then any
       extra ones): the clauses read off the first play's derivation, and, per
       ranking key, one fresh copy constrained by the chain pairs of all the
       plays together, so that one ranking has to cover every play. *)
    (* Under [~wf_mode] (only with [resynthesise_wf_rankings]), a key whose
       ranking is constrained by chain-pair facts alone gets its fresh copy
       declared [WF] and constrained by every pair accepted refinements have
       asked of it as well as the new ones, unless those contain a cycle; its
       solution then REPLACES the ranking (see the read-back below).  What the
       last build asked, per key, and which copies it declared [WF], are left
       in these two references for the read-back. *)
    let last_asked = ref [] in
    let last_wf_copies = ref Set.Poly.empty in
    (* Under [~generalise] (only with [generalise_chain_pairs]): the regions
       the last build read off the plays, per key whose copy it declared [WF],
       and how many region clauses (stored and new) it added in all. *)
    let last_regions = ref [] in
    let last_region_clauses = ref 0 in
    let decisions =
      Set.Poly.map orig_keys_fn ~f:Ident.name_of_tvar
    in
    let has_derivation_copy key =
      Set.exists keys_wf ~f:(fun x ->
          String.is_prefix (Ident.name_of_tvar x)
            ~prefix:(Ident.name_of_tvar key ^ "$"))
    in
    let build_pfwcsp ?(wf_mode = false) ?(generalise = false) plays =
      last_asked := [];
      last_wf_copies := Set.Poly.empty;
      last_regions := [];
      last_region_clauses := 0;
      let pfwcsp =
        let fsenvs, cs =
          PCSP.Problem.clauses_of problem
          |> Set.Poly.filter_map ~f:(fun (uni_senv, pos, neg, phi) ->
              let pos =
                Set.filter pos
                  ~f:
                    (Logic.Term.pvar_of_atom
                    >> Set.mem (Set.union keys_fn keys_wf)
                    >> not)
              in
              if Set.is_empty neg && Set.is_empty pos then None
              else
                let senv1, (senv2, fsenv, phi) =
                  Tuple2.map_snd
                    ~f:
                      (Logic.ExtTerm.neg_of
                      >> Logic.ExtTerm.to_old_fml senv_problem uni_senv
                      >> Evaluator.simplify
                      >> (fun phi ->
                      if false then
                        print_endline
                          ("before: " ^ LogicOld.Formula.str_of @@ snd
                          @@ LogicOld.Formula.quantify_except ~exists:true
                               Set.Poly.empty phi);
                      phi)
                      >> LogicOld.Formula.negate >> Evaluator.simplify
                      >> Tuple2.curry
                           (Ast.Qelim.elim_free_univ_vars_old Map.Poly.empty
                              senv_problem)
                           uni_senv
                      >> snd >> LogicOld.Formula.negate >> Evaluator.simplify
                      >> LogicOld.Formula.quantify_except ~exists:true
                           Set.Poly.empty
                      >> snd
                      >> (fun phi ->
                      if false then
                        print_endline ("after: " ^ LogicOld.Formula.str_of phi);
                      phi)
                      >> LogicOld.Formula.skolemize ~uni_senv:Map.Poly.empty
                           ~use_fn_pred:true ~only_impure:true)
                  @@ Clause.to_senv_formula (uni_senv, pos, neg, phi)
                in
                Some
                  ( fsenv,
                    Logic.ExtTerm.of_old
                      ( Map.force_merge (Logic.to_old_sort_env_map senv1) senv2,
                        phi ) ))
          |> Set.unzip
        in
        (* With the opponent's decisions named, the derivation is a complete
           play and the pairs its rankings must cover are read off it (see
           [chain_pairs_of]); each key gets a fresh copy constrained by those
           pairs as facts, joined into the key's strategy like any other copy. *)
        let pair_senv, pair_cs =
          match plays with
          | [] -> (Map.Poly.empty, Set.Poly.empty)
          | trees ->
              Map.Poly.fold dual_strat_wf
                ~init:(Map.Poly.empty, Set.Poly.empty)
                ~f:(fun ~key ~data (senv, cs) ->
                  let args, _ = Logic.Term.let_lam data in
                  let pairs =
                    List.concat_map trees ~f:(fun tree ->
                        chain_pairs_of tree ~wf_key:key
                          ~arity:(List.length args))
                    |> List.dedup_and_sort ~compare:Stdlib.compare
                  in
                  if not (List.is_empty extra_plays) then
                    Debug.print
                    @@ lazy
                         (sprintf "## chain pairs of %s from %d play(s): %s"
                            (Ident.name_of_tvar key) (List.length trees)
                            (String.concat_map_list ~sep:"; " pairs
                               ~f:(fun (a, b) ->
                                 sprintf "(%s) -> (%s)"
                                   (String.concat_map_list ~sep:","
                                      ~f:LogicOld.Term.str_of a)
                                   (String.concat_map_list ~sep:","
                                      ~f:LogicOld.Term.str_of b))));
                  if List.is_empty pairs then (senv, cs)
                  else
                    let copy =
                      Ident.mk_fresh_tvar
                        ~prefix:(Some (Ident.name_of_tvar key ^ "$"))
                        ()
                    in
                    last_asked := (key, pairs) :: !last_asked;
                    let pairs =
                      if wf_mode && not (has_derivation_copy key) then
                        let all =
                          Option.value ~default:[]
                            (Hashtbl.find wf_rank_pairs
                               (Ident.name_of_tvar key))
                          @ pairs
                          |> List.dedup_and_sort ~compare:Stdlib.compare
                        in
                        if pairs_cyclic all then (
                          Debug.print
                          @@ lazy
                               (sprintf
                                  "## the chain pairs asked of %s so far \
                                   contain a cycle; it is refined by a \
                                   disjoined piece"
                                  (Ident.name_of_tvar key));
                          pairs)
                        else (
                          last_wf_copies := Set.add !last_wf_copies copy;
                          Debug.print
                          @@ lazy
                               (sprintf
                                  "## re-synthesising %s as one WF relation \
                                   over %d chain pair(s)"
                                  (Ident.name_of_tvar key) (List.length all));
                          all)
                      else pairs
                    in
                    let sort =
                      Logic.Sort.mk_fun (List.map args ~f:snd @ [ Logic.BoolTerm.SBool ])
                    in
                    let facts =
                      Set.Poly.of_list
                      @@ List.map pairs ~f:(fun (a, b) ->
                          ( Map.Poly.empty,
                            Logic.Term.mk_var_app copy
                              (List.map (a @ b) ~f:Logic.ExtTerm.of_old_term) ))
                    in
                    (* Each region [(vars, region)] becomes the clause
                       [forall vars. region => copy(vars)]; the ground facts
                       stay, so the problem only gains constraints. *)
                    let facts =
                      if generalise && Set.mem !last_wf_copies copy then (
                        let regions =
                          List.concat_map trees ~f:(fun tree ->
                              chain_regions_of ~passed ~decisions tree
                                ~wf_key:key
                                ~arity:(List.length args))
                          |> List.stable_sort ~compare:(fun (p1, _) (p2, _) ->
                              Stdlib.compare p1 p2)
                          |> List.remove_consecutive_duplicates
                               ~equal:(fun (p1, _) (p2, _) ->
                                 Stdlib.( = ) p1 p2)
                          |> List.map ~f:snd
                        in
                        let stored =
                          Option.value ~default:[]
                            (Hashtbl.find wf_rank_regions
                               (Ident.name_of_tvar key))
                        in
                        last_regions := (key, regions) :: !last_regions;
                        last_region_clauses :=
                          !last_region_clauses + List.length stored
                          + List.length regions;
                        Debug.print
                        @@ lazy
                             (sprintf
                                "## %s: %d region(s) from the plays, %d \
                                 stored:\n%s"
                                (Ident.name_of_tvar key) (List.length regions)
                                (List.length stored)
                                (String.concat_map_list ~sep:"\n" regions
                                   ~f:(fun (vars, region) ->
                                     sprintf "  (%s) : %s"
                                       (String.concat_map_list ~sep:","
                                          vars ~f:(fst >> Ident.name_of_tvar))
                                       (LogicOld.Formula.str_of region))));
                        Set.union facts
                        @@ Set.Poly.of_list
                        @@ List.map (stored @ regions) ~f:(fun (vars, region) ->
                            ( Logic.of_old_sort_env_map
                                (Map.Poly.of_alist_exn vars),
                              Logic.BoolTerm.imply_of
                                (Logic.ExtTerm.of_old_formula region)
                                (Logic.Term.mk_var_app copy
                                   (List.map vars
                                      ~f:(fst >> Logic.Term.mk_var))) )))
                      else facts
                    in
                    (Map.Poly.set senv ~key:copy ~data:sort, Set.union cs facts))
        in
        let cs = Set.union cs pair_cs in
        let params =
          let fsenv =
            Map.force_merge_list @@ Set.to_list
            @@ Set.Poly.map ~f:Logic.of_old_sort_env_map fsenvs
          in
          let kind_map =
            Kind.add_kinds !last_wf_copies Kind.WF
            @@ Kind.add_kinds keys_wf Kind.DWF
                 (Kind.add_kinds
                    (Set.diff (Map.key_set pair_senv) !last_wf_copies)
                    Kind.DWF
                    (Kind.add_kinds keys_fn Kind.FN
                       (Kind.add_kinds (Map.key_set fsenv) Kind.FN
                          Map.Poly.empty)))
          in
          PCSP.Params.make ~kind_map
            (Map.force_merge_list [ senv_problem; fsenv; pair_senv ])
        in
        PCSP.Problem.normalize @@ PCSP.Problem.of_formulas ~params cs
      in
      if use_solspace then
        PCSP.Problem.set_params_sol_space pfwcsp
          (Map.of_set_exn
          @@ Set.Poly.map (Set.union keys_wf keys_fn) ~f:(fun key ->
              (key, !solspace)))
      else pfwcsp
    in
    (* the kind certificates of the latest refinement solved, read by the
       check of an accepted refinement; empty when the answer did not come
       from a call that records them *)
    let last_certs = ref Map.Poly.empty in
    let solve_unbounded =
      match solve_certs with
      | Some solve_certs when config.check_refinement_kinds ->
          fun pfwcsp ->
            Or_error.map (solve_certs pfwcsp) ~f:(fun (sol, n, certs) ->
                last_certs := certs;
                (sol, n))
      | _ -> solve
    in
    (* The re-synthesis attempt is bounded ([solve_wf], the check's budget)
       so that the refinement asked without it is always reached. *)
    let solve pfwcsp =
      match solve_wf with
      | Some solve_wf when not (Set.is_empty !last_wf_copies) ->
          solve_wf pfwcsp
      | _ -> solve_unbounded pfwcsp
    in
    let solve_refinement pfwcsp =
    last_certs := Map.Poly.empty;
    (*if verbose then*)
    Debug.print
    @@ lazy
         (sprintf "## pfwCSP for ranking and Skolem function synthesis:\n%s\n"
         @@ PCSP.Problem.str_of pfwcsp);
      if config.select_skolem_terms then
        (* the key a copy was made from, by the naming rule the solution is
           read back with below; a copy matching no key, or more than one,
           is not grouped *)
        let origin_of =
          if config.select_skolem_guards then
            Some
              (fun x ->
                match
                  Set.to_list
                  @@ Set.filter (Set.union orig_keys_wf orig_keys_fn)
                       ~f:(fun key ->
                         String.is_prefix (Ident.name_of_tvar x)
                           ~prefix:(Ident.name_of_tvar key ^ "$"))
                with
                | [ key ] when Set.mem orig_keys_fn key -> Some key
                | _ -> None)
          else None
        in
        match select_skolem_solution ?origin_of pfwcsp with
        | Some sol -> Result.Ok (PCSP.Problem.Sat sol, 0)
        | None -> (
            match
              if config.split_mixed_refinements then
                split_mixed_refinement pfwcsp
              else None
            with
            | None -> solve pfwcsp
            | Some (skolem_part, ranking_part) -> (
                match select_skolem_solution ?origin_of skolem_part with
                | None -> solve pfwcsp
                | Some sol_skolem -> (
                    match solve ranking_part with
                    | Result.Ok (PCSP.Problem.Sat sol_ranking, n) ->
                        Debug.print
                        @@ lazy
                             "## the refinement split: Skolem terms by \
                              selection, rankings by PCSat";
                        Result.Ok
                          ( PCSP.Problem.Sat
                              (Map.force_merge sol_skolem sol_ranking),
                            n )
                    | _ ->
                        Debug.print
                        @@ lazy
                             "## the ranking part of the split refinement \
                              was not solved; asking PCSat for the whole";
                        solve pfwcsp)))
      else solve pfwcsp
    in
    let first_plays = Option.to_list play in
    let pfwcsp, result =
      (* The generalised attempt: the re-synthesis problem with each key's
         regions added.  Skipped when it would add no region clause, since it
         would then be the plain attempt below asked twice. *)
      let gen_attempt =
        if config.resynthesise_wf_rankings && config.generalise_chain_pairs
        then (
          let pfwcsp =
            build_pfwcsp ~wf_mode:true ~generalise:true
              (first_plays @ extra_plays)
          in
          if Set.is_empty !last_wf_copies || !last_region_clauses = 0 then None
          else
            match solve_refinement pfwcsp with
            | Result.Ok (PCSP.Problem.Sat _, _) as result ->
                Debug.print
                @@ lazy
                     (sprintf
                        "## re-synthesis over %d region clause(s) succeeded"
                        !last_region_clauses);
                Some (pfwcsp, result)
            | _ ->
                Debug.print
                @@ lazy
                     "## re-synthesis over the regions did not succeed; \
                      asking it over the ground chain pairs";
                None)
        else None
      in
      let wf_attempt =
        if Option.is_some gen_attempt then gen_attempt
        else if config.resynthesise_wf_rankings then (
          let pfwcsp = build_pfwcsp ~wf_mode:true (first_plays @ extra_plays) in
          if Set.is_empty !last_wf_copies then None
          else
            match solve_refinement pfwcsp with
            | Result.Ok (PCSP.Problem.Sat _, _) as result ->
                Some (pfwcsp, result)
            | _ ->
                Debug.print
                @@ lazy
                     "## re-synthesis as WF relations did not succeed; asking \
                      the refinement with disjoined pieces";
                None)
        else None
      in
      match wf_attempt with
      | Some r -> r
      | None ->
          let pfwcsp = build_pfwcsp (first_plays @ extra_plays) in
          (pfwcsp, solve_refinement pfwcsp)
    in
    (* The extra plays only add chain pairs, and pairs from different plays
       can be more than one ranking covers (the checked side's strategy may
       let the plays cycle through each other's states).  So a refinement
       that does not succeed with them is asked again with the first play's
       pairs alone -- exactly the problem built with no extra play -- and the
       extra plays can never be the reason a refinement fails. *)
    let pfwcsp, result =
      match result with
      | Result.Ok (PCSP.Problem.Sat _, _) -> (pfwcsp, result)
      | _ when List.is_empty extra_plays || List.is_empty first_plays ->
          (pfwcsp, result)
      | _ ->
          Debug.print
          @@ lazy
               "## refinement with the extra counter-plays did not succeed; \
                asking again with the first play alone";
          let pfwcsp = build_pfwcsp first_plays in
          (pfwcsp, solve_refinement pfwcsp)
    in
    match result with
    | Result.Ok (PCSP.Problem.Sat sol, _) ->
        if config.check_refinement_kinds then
          check_refinement_kinds pfwcsp sol ~certs:!last_certs;
        (* [last_regions] is non-empty only when the problem solved is the
           generalised one, since every later build resets it. *)
        List.iter !last_regions ~f:(fun (key, regions) ->
            if not (List.is_empty regions) then
              Hashtbl.update wf_rank_regions (Ident.name_of_tvar key)
                ~f:(fun old -> Option.value ~default:[] old @ regions));
        if config.resynthesise_wf_rankings then
          List.iter !last_asked ~f:(fun (key, pairs) ->
              Hashtbl.update wf_rank_pairs (Ident.name_of_tvar key)
                ~f:(fun old ->
                  Option.value ~default:[] old @ pairs
                  |> List.dedup_and_sort ~compare:Stdlib.compare));
        (* [resynthesise_only_on_new_pairs]: the ranking keys whose ranking
           is kept as it is, because every chain pair this refinement asked
           of the key evaluates to true in the current ranking.
           Postcondition: a key outside this set is refined as without the
           field; a key inside it keeps its term, and with it its record in
           [wf_by_construction], and still contains every pair asked of it
           (those were just added to [wf_rank_pairs]), so the ranking still
           covers every pair any accepted refinement has asked.  A key that
           was asked no pair is never kept. *)
        let kept_rankings =
          if
            config.resynthesise_wf_rankings
            && config.resynthesise_only_on_new_pairs
          then
            Map.Poly.key_set dual_strat_wf
            |> Set.filter ~f:(fun key ->
                let asked =
                  List.concat_map !last_asked ~f:(fun (k, pairs) ->
                      if Ident.tvar_equal k key then pairs else [])
                in
                (not (List.is_empty asked))
                && List.for_all asked
                     ~f:(ranking_contains (Map.Poly.find_exn dual_strat_wf key)))
          else Set.Poly.empty
        in
        Set.iter kept_rankings ~f:(fun key ->
            Debug.print
            @@ lazy
                 (sprintf
                    "## every chain pair asked of %s is in its current ranking; the ranking is kept"
                    (Ident.name_of_tvar key)));
        let rev_ren =
          Map.Poly.mapi
            (Map.force_merge senv_problem
               (Map.Poly.filter (PCSP.Problem.senv_of pfwcsp) ~f:(fun _ -> true)
               |> Map.Poly.filter_keys ~f:(fun x ->
                   (not (Map.Poly.mem senv_problem x))
                   && Set.exists orig_keys_wf ~f:(fun key ->
                       String.is_prefix (Ident.name_of_tvar x)
                         ~prefix:(Ident.name_of_tvar key ^ "$")))))
            ~f:(fun ~key:x ~data:_ ->
              Set.find_exn (Set.union orig_keys_wf orig_keys_fn) ~f:(fun key ->
                  String.is_prefix (Ident.name_of_tvar x)
                    ~prefix:(Ident.name_of_tvar key ^ "$")))
        in
        Map.Poly.fold rev_ren ~init:(dual_strat_wf, dual_strat_fn, dual_nu_wfs)
          ~f:(fun ~key ~data (dual_strat_wf, dual_strat_fn, dual_nu_wfs) ->
            match Map.Poly.find sol key with
            | None -> (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
            | Some _ when Set.mem kept_rankings data ->
                (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
            | Some _ ->
                if Set.mem orig_keys_wf data then (
                  let args, term =
                    Logic.Term.let_lam @@ Map.Poly.find_exn dual_strat_wf data
                  in
                  let piece =
                    Logic.ExtTerm.subst sol
                    @@ Logic.Term.mk_var_app key
                         (List.map args ~f:(fst >> Logic.Term.mk_var))
                  in
                  (* A copy declared [WF] holds every pair asked of the key so
                     far, so it replaces the ranking; any other copy is one
                     more piece of a union. *)
                  let replaces = Set.mem !last_wf_copies key in
                  let term' =
                    if replaces then piece else Logic.BoolTerm.or_of [ term; piece ]
                  in
                  Debug.print @@ lazy "## Refined the current dual wf strategy:";
                  print_strat data args term';
                  let lam = Logic.Term.mk_lambda args term' in
                  if replaces then
                    Hashtbl.set wf_by_construction
                      ~key:(Ident.name_of_tvar data) ~data:lam
                  else Hashtbl.remove wf_by_construction (Ident.name_of_tvar data);
                  ( Map.Poly.set dual_strat_wf ~key:data ~data:lam,
                    dual_strat_fn,
                    dual_nu_wfs ))
                else if Set.mem orig_keys_fn data then (
                  let args, terms = Map.Poly.find_exn dual_strat_fn data in
                  let terms' =
                    Set.add terms @@ Logic.ExtTerm.subst sol
                    @@ Logic.Term.mk_var_app key
                         (List.map args ~f:(fst >> Logic.Term.mk_var))
                  in
                  Debug.print @@ lazy "## Refined the current dual fn strategy:";
                  Set.iter terms' ~f:(print_strat data args);
                  ( dual_strat_wf,
                    Map.Poly.set dual_strat_fn ~key:data ~data:(args, terms'),
                    dual_nu_wfs ))
                else (dual_strat_wf, dual_strat_fn, dual_nu_wfs))
    | Result.Ok (PCSP.Problem.Unsat _, _) -> raise NoRefinement
    | Result.Ok ((PCSP.Problem.(Unknown | Timeout) as sol), _) ->
        Debug.print @@ lazy (PCSP.Problem.str_of_sol_with_witness sol);
        (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
    | Result.Ok ((PCSP.Problem.OutSpace xs as sol), _) ->
        Debug.print @@ lazy (PCSP.Problem.str_of_sol_with_witness sol);
        refine_solspace
          (List.exists xs ~f:(Map.Poly.mem dual_strat_wf))
          (List.exists xs ~f:(Map.Poly.mem dual_strat_fn));
        (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
    | Result.Error _ ->
        Debug.print @@ lazy "error";
        (dual_strat_wf, dual_strat_fn, dual_nu_wfs (*failwith "refine_strat"*))

  let subst_strat primal_strat_wf primal_strat_fn (uni_senv, phi) =
    let uni_senv', phi' =
      if false then
        ( uni_senv,
          Logic.ExtTerm.subst
            (Map.Poly.map primal_strat_fn ~f:(fun (args, terms) ->
                 Logic.ExtTerm.mk_lambda args
                 @@ Logic.ExtTerm.or_of @@ Set.to_list terms))
          @@ Logic.ExtTerm.subst primal_strat_wf phi )
      else
        (* Keys are substituted outer ones first, and each copy renames apart
           the results of the key's applications and of the applications
           nested in them ([NestedKeys]). *)
        let phi0 = Logic.ExtTerm.subst primal_strat_wf phi in
        let keys = Map.Poly.keys primal_strat_fn in
        List.fold (NestedKeys.order ~keys phi0) ~init:(uni_senv, phi0)
          ~f:(fun (uni_senv, phi) key ->
            let params, terms = Map.Poly.find_exn primal_strat_fn key in
            if Set.mem (Logic.ExtTerm.fvs_of phi) key then
              let rets = NestedKeys.rets_of key phi in
              let local = rets @ NestedKeys.nested_rets ~keys phi rets in
              let phi_fvs = Logic.ExtTerm.fvs_of phi in
              let uni_senvs, phis =
                List.unzip @@ Set.to_list
                @@ Set.Poly.map terms ~f:(fun term ->
                    (* The return variable is renamed into the clause's
                       universals, where [Map.rename_keys_map] overwrites any
                       entry of the same name, so the new name must be absent
                       from the clause's environment and from the free
                       variables of the formula and of the substituted term;
                       otherwise two universals of the clause would become
                       one. *)
                    let term_fvs = Logic.ExtTerm.fvs_of term in
                    let ren =
                      NestedKeys.renaming local ~taken:(fun v ->
                          Map.Poly.mem uni_senv v || Set.mem phi_fvs v
                          || Set.mem term_fvs v)
                    in
                    let phi' =
                      Logic.ExtTerm.rename ren
                      @@ Logic.ExtTerm.subst
                           (Map.Poly.singleton key
                              (Logic.ExtTerm.mk_lambda params term))
                           phi
                    in
                    let uni_senv' = Map.rename_keys_map ren uni_senv in
                    if false then
                      Debug.print
                      @@ lazy
                           (sprintf "renamed: %s\n" (Logic.ExtTerm.str_of phi'));
                    (uni_senv', phi'))
              in
              (Map.force_merge_list uni_senvs, Logic.ExtTerm.or_of phis)
            else (uni_senv, phi))
    in
    if false then
      Debug.print
      @@ lazy
           (sprintf "### Formula converted:\n%s\n=>\n%s\n"
              (Logic.ExtTerm.str_of phi)
              (Logic.ExtTerm.str_of phi'));
    (uni_senv', phi')

  (* ---------------------------------------------------------------------
     The named encoding of term alternatives ([name_term_alternatives]).

     [subst_strat] above substitutes each term of a key's term set into the
     whole formula and joins the copies with [or]; the CNF of that join is the
     product of the copies' clause counts.  The functions below compute the
     same copies as a LIST (the alternatives), so that the CHC can name each
     one by a fresh predicate instead of distributing the join.  Nothing here
     is reached with the field off. *)

  (* [dedup_terms params terms]: [terms] with every term dropped that is
     equivalent to one kept before it under every value of [params], the
     key's parameters.  Exact: the alternatives are joined by a disjunction,
     which is idempotent.  Equivalence is decided syntactically on the
     simplified first-order form and, failing that, by asking Z3 whether the
     biconditional is valid within [dedup_timeout_ms]; any answer other than
     valid (a timeout or an exception included) keeps both terms, which is
     the encoding without deduplication and therefore still exact.  Two
     entries of a refuter's set that print alike ([x1 = 0] twice) doubled the
     alternatives of every clause mentioning the key. *)
  let dedup_timeout_ms = 1000

  let dedup_terms params terms =
    let senv = Map.Poly.of_alist_exn params in
    let old_of term =
      try
        Some
          (Evaluator.simplify
          @@ Logic.ExtTerm.to_old_fml Map.Poly.empty senv term)
      with exn when not (Common.Timer.is_async exn) -> None
    in
    let equivalent (t1, f1) (t2, f2) =
      Stdlib.(t1 = t2)
      ||
      match (f1, f2) with
      | Some f1, Some f2 -> (
          (try Stdlib.(f1 = f2)
           with exn when not (Common.Timer.is_async exn) -> false)
          ||
          let iff = LogicOld.Formula.mk_iff f1 f2 in
          if Z3Smt.Z3interface.may_not_return iff then false
          else
            try
              match
                Z3Smt.Z3interface.check_valid ~timeout:(Some dedup_timeout_ms)
                  ~id:None (LogicOld.get_fenv ()) iff
              with
              | `Valid -> true
              | _ -> false
            with exn when not (Common.Timer.is_async exn) -> false)
      | _ -> false
    in
    Set.to_list terms
    |> List.fold ~init:[] ~f:(fun kept term ->
        let entry = (term, old_of term) in
        if List.exists kept ~f:(equivalent entry) then kept else entry :: kept)
    |> List.rev_map ~f:fst

  (* [subst_strat_alternatives]: the alternatives [subst_strat] joins, as a
     list, with each key's term set deduplicated.
     Contract: [or_of] of the returned alternatives, under the returned
     environment, is equivalent to [subst_strat]'s formula under its
     environment (up to the names of the fresh result universals).  An
     alternative that does not mention a key is kept once rather than copied
     per term, by idempotence. *)
  let subst_strat_alternatives primal_strat_wf primal_strat_fn (uni_senv, phi)
      =
    let phi0 = Logic.ExtTerm.subst primal_strat_wf phi in
    let keys = Map.Poly.keys primal_strat_fn in
    List.fold (NestedKeys.order ~keys phi0) ~init:(uni_senv, [ phi0 ])
      ~f:(fun (uni_senv, alts) key ->
        let params, terms = Map.Poly.find_exn primal_strat_fn key in
        let mentions alt = Set.mem (Logic.ExtTerm.fvs_of alt) key in
        match List.filter alts ~f:mentions with
        | [] -> (uni_senv, alts)
        | mentioning ->
            let whole = Logic.BoolTerm.or_of mentioning in
            let rets = NestedKeys.rets_of key whole in
            let local = rets @ NestedKeys.nested_rets ~keys whole rets in
            let alts_fvs =
              Set.Poly.union_list (List.map alts ~f:Logic.ExtTerm.fvs_of)
            in
            (* As in [subst_strat]: the result variable is renamed into the
               clause's universals, so the new name must be absent from the
               environment and from the free variables of every alternative
               and of the substituted term. *)
            let copies =
              List.map (dedup_terms params terms) ~f:(fun term ->
                  let term_fvs = Logic.ExtTerm.fvs_of term in
                  let ren =
                    NestedKeys.renaming local ~taken:(fun v ->
                        Map.Poly.mem uni_senv v || Set.mem alts_fvs v
                        || Set.mem term_fvs v)
                  in
                  (term, ren))
            in
            let uni_senv' =
              Map.force_merge_list
              @@ List.map copies ~f:(fun (_, ren) ->
                  Map.rename_keys_map ren uni_senv)
            in
            let alts' =
              List.concat_map alts ~f:(fun alt ->
                  if mentions alt then
                    List.map copies ~f:(fun (term, ren) ->
                        Logic.ExtTerm.rename ren
                        @@ Logic.ExtTerm.subst
                             (Map.Poly.singleton key
                                (Logic.ExtTerm.mk_lambda params term))
                             alt)
                  else [ alt ])
            in
            (uni_senv', alts'))

  (* The head variable of [t] if [t] is an application of a predicate of
     [exi_senv]; a universal of [uni_senv] shadows a predicate of its name. *)
  let pred_app_of exi_senv uni_senv t =
    match Logic.Term.let_apps t with
    | Logic.Var (v, _), _
      when Map.Poly.mem exi_senv v && not (Map.Poly.mem uni_senv v) ->
        Some v
    | _ -> None

  let mentions_pred exi_senv uni_senv t =
    Set.exists (Logic.ExtTerm.fvs_of t) ~f:(fun v ->
        Map.Poly.mem exi_senv v && not (Map.Poly.mem uni_senv v))

  (* Does the NNF formula [t] have predicate atoms only negatively, directly
     under a [not], with only [and]/[or] above them?  Anything else that
     mentions a predicate (a quantifier, a boolean equality, an [ite]) answers
     no, so that the caller falls back rather than guesses a polarity. *)
  let rec negative_only exi_senv uni_senv t =
    (not (mentions_pred exi_senv uni_senv t))
    ||
    match Logic.Term.let_apps t with
    | Logic.Con ((Logic.BoolTerm.And | Logic.BoolTerm.Or), _), args ->
        List.for_all args ~f:(negative_only exi_senv uni_senv)
    | Logic.Con (Logic.BoolTerm.Not, _), [ a ] ->
        Option.is_some (pred_app_of exi_senv uni_senv a)
    | _ -> false

  (* An upper bound on the number of clauses the CNF conversion produces for
     the NNF formula [t], read off its structure without converting it: a
     disjunction multiplies its operands' counts, a conjunction adds them (its
     predicate-free operands merging into one clause), and anything else is
     one clause.  The conversion may produce fewer, since it deduplicates.
     It draws no fresh name and builds no clause, so it can be printed for a
     check whose conversion would not finish.  Saturates at [cnf_size_cap]. *)
  let cnf_size_cap = 1_000_000_000_000

  let cnf_mul a b =
    if a = 0 || b = 0 then 0
    else if a > cnf_size_cap / b then cnf_size_cap
    else a * b

  let cnf_add a b = Int.min cnf_size_cap (a + b)

  let rec cnf_size exi_senv uni_senv t =
    if not (mentions_pred exi_senv uni_senv t) then 1
    else
      match Logic.Term.let_apps t with
      | Logic.Con (Logic.BoolTerm.Or, _), args ->
          List.fold args ~init:1 ~f:(fun acc a ->
              cnf_mul acc (cnf_size exi_senv uni_senv a))
      | Logic.Con (Logic.BoolTerm.And, _), args ->
          let pure, impure =
            List.partition_tf args
              ~f:(Fn.non (mentions_pred exi_senv uni_senv))
          in
          List.fold impure
            ~init:(if List.is_empty pure then 0 else 1)
            ~f:(fun acc a -> cnf_add acc (cnf_size exi_senv uni_senv a))
      | _ -> 1

  (* The bound above summed over a problem's formulas, and the largest. *)
  let cnf_size_of_problem pcsp =
    let exi_senv = PCSP.Problem.senv_of pcsp in
    Set.fold (PCSP.Problem.formulas_of pcsp) ~init:(0, 0)
      ~f:(fun (total, largest) (uni_senv, phi) ->
        let n =
          try cnf_size exi_senv uni_senv (Logic.ExtTerm.nnf_of phi)
          with exn when not (Common.Timer.is_async exn) -> 1
        in
        (cnf_add total n, Int.max largest n))

  (* [name_alternatives ~fresh exi_senv (uni_senv, alts)]: the named encoding
     of the CHC formula [or_of alts] (each alternative already in CHC form),
     or [None] when it does not apply and the disjunction is to be kept.

     It applies when there are at least two alternatives; each alternative's
     NNF is [H \/ R_tau] with [H] the same single positive predicate atom in
     every alternative, or absent from all of them (a goal clause); every
     [R_tau] has its predicate atoms only negatively; and the product of the
     CNF sizes [c_tau] of the [R_tau] exceeds their sum plus one, so that
     naming is smaller.  The result is the clause [H \/ not N_1(z_1) \/ .. \/
     not N_k(z_k)] and, per alternative, the definition [N_tau(z_tau) \/
     R_tau], [z_tau] being the universals [R_tau] mentions; [fresh sort]
     draws each [N_tau].

     Exact: an interpretation of the original predicates satisfies [H \/
     \/_tau R_tau] iff it extends to the [N_tau] so that the new formulas all
     hold (take [N_tau := not R_tau]; conversely, where [H] fails some
     [N_tau] is false and its definition gives [R_tau]).  Each [N_tau] is
     non-recursive and defined by its definition only, so unfolding the [N]
     nodes of a derivation of the new system gives one of the old. *)
  let name_alternatives ~fresh exi_senv (uni_senv, alts) =
    if List.length alts < 2 then None
    else
      let split alt =
        let heads, rest =
          List.partition_tf
            (Logic.BoolTerm.disjuncts_of (Logic.ExtTerm.nnf_of alt))
            ~f:(fun d -> Option.is_some (pred_app_of exi_senv uni_senv d))
        in
        (heads, Logic.BoolTerm.or_of rest)
      in
      let splits = List.map alts ~f:split in
      let heads = fst (List.hd_exn splits) in
      let same_heads =
        List.length heads <= 1
        && List.for_all splits ~f:(fun (hs, _) ->
            try Stdlib.(hs = heads)
            with exn when not (Common.Timer.is_async exn) -> false)
      in
      let rests = List.map splits ~f:snd in
      if
        (not same_heads)
        || not (List.for_all rests ~f:(negative_only exi_senv uni_senv))
      then None
      else
        let sizes = List.map rests ~f:(cnf_size exi_senv uni_senv) in
        let product = List.fold sizes ~init:1 ~f:cnf_mul in
        let sum = List.fold sizes ~init:0 ~f:cnf_add in
        if product <= sum + 1 then None
        else
          let named =
            List.map rests ~f:(fun r ->
                let zs =
                  Set.to_list (Logic.ExtTerm.fvs_of r)
                  |> List.filter_map ~f:(fun v ->
                      Option.map (Map.Poly.find uni_senv v) ~f:(fun s -> (v, s)))
                in
                let n =
                  fresh
                    (Logic.Sort.mk_fun
                       (List.map zs ~f:snd @ [ Logic.BoolTerm.SBool ]))
                in
                let napp =
                  Logic.ExtTerm.mk_var_app n
                    (List.map zs ~f:(fst >> Logic.ExtTerm.mk_var))
                in
                ( napp,
                  (Map.Poly.of_alist_exn zs, Logic.BoolTerm.or_of [ napp; r ])
                ))
          in
          let clause =
            ( uni_senv,
              Logic.BoolTerm.or_of
                (heads @ List.map named ~f:(fst >> Logic.BoolTerm.neg_of)) )
          in
          Some (clause :: List.map named ~f:snd)

  (* [name_tree ~fresh ~exi_senv_of sub (uni_senv, tree)]: the CHC form of a
     clause placed by [TermAlternatives.of_clause] ([sub] is the substitution
     [cochc_to_chc] applies), with every [Alts] node that meets
     [name_alternatives]'s conditions -- at least two alternatives, each with
     predicate atoms only negatively, the product of their CNF sizes above
     their sum plus one -- replaced by [not N_1(z_1) \/ .. \/ not N_k(z_k)],
     returned with the definitions [N_tau(z_tau) \/ R_tau], [z_tau] the
     universals [R_tau] mentions.  Inner nodes are named first, so an outer
     alternative may mention an inner name, negatively.  An [Alts] node that
     does not meet the conditions stays a disjunction.  [exi_senv_of ()] is
     the problem's predicates together with the names drawn so far, so that
     an inner name counts as an atom when an outer node is sized.

     Exact at any position, not only at the top of the clause: an [Alts] node
     sits under [and] and [or] only, so the clause is monotone in it.  Taking
     [N_tau := not R_tau] turns the named clause back into the clause; and the
     definitions give [not N_tau => R_tau], so by monotonicity the named clause
     implies the clause.  So an interpretation of the original predicates
     satisfies the clause iff it extends to the [N_tau] satisfying the named
     clause and the definitions.  Each [N_tau] is non-recursive and defined
     only by its definition, so unfolding the [N] nodes of a derivation of the
     named system gives a derivation of the unnamed one. *)
  let name_tree ~fresh ~exi_senv_of sub (uni_senv, tree) =
    let defs = ref [] in
    let rec go = function
      | TermAlternatives.Leaf t -> Logic.ExtTerm.subst sub t
      | TermAlternatives.And ts -> Logic.BoolTerm.and_of (List.map ts ~f:go)
      | TermAlternatives.Or ts -> Logic.BoolTerm.or_of (List.map ts ~f:go)
      | TermAlternatives.Alts ts ->
          let rs = List.map ts ~f:(go >> Logic.ExtTerm.nnf_of) in
          let exi_senv = exi_senv_of () in
          let sizes = List.map rs ~f:(cnf_size exi_senv uni_senv) in
          if
            List.length rs < 2
            || (not (List.for_all rs ~f:(negative_only exi_senv uni_senv)))
            || List.fold sizes ~init:1 ~f:cnf_mul
               <= List.fold sizes ~init:0 ~f:cnf_add + 1
          then Logic.BoolTerm.or_of rs
          else
            Logic.BoolTerm.or_of
            @@ List.map rs ~f:(fun r ->
                let zs =
                  Set.to_list (Logic.ExtTerm.fvs_of r)
                  |> List.filter_map ~f:(fun v ->
                      Option.map (Map.Poly.find uni_senv v) ~f:(fun s -> (v, s)))
                in
                let n =
                  fresh
                    (Logic.Sort.mk_fun
                       (List.map zs ~f:snd @ [ Logic.BoolTerm.SBool ]))
                in
                let napp =
                  Logic.ExtTerm.mk_var_app n
                    (List.map zs ~f:(fst >> Logic.ExtTerm.mk_var))
                in
                defs :=
                  (Map.Poly.of_alist_exn zs, Logic.BoolTerm.or_of [ napp; r ])
                  :: !defs;
                Logic.BoolTerm.neg_of napp)
    in
    let phi = go tree in
    ((uni_senv, phi), List.rev !defs)

  (* The check's CHC under [name_term_alternatives]: [subst_strat]'s
     formulas, each formula's alternatives converted to CHC form one by one
     (by the substitution [cochc_to_chc] applies) and then named where
     [name_alternatives] applies.  The new predicates are ordinary and are
     drawn fresh against the problem's predicates, every universal and free
     variable of every formula, and every strategy key [keys]: a derivation
     node's copy is named [<pred>$<n>] and the refinement recognises a key's
     copy by the prefix [<key>$], so a new predicate must not be named as a
     key. *)
  let named_chc ~params ~keys primal_strat_wf primal_strat_fn primal =
    let pcsp0 = PCSP.Problem.of_formulas ~params Set.Poly.empty in
    let sub = PCSP.Problem.cochc_subst_of pcsp0 in
    let chc_params =
      PCSP.Problem.params_of (PCSP.Problem.cochc_to_chc pcsp0)
    in
    let exi_senv = chc_params.PCSP.Params.senv in
    let clauses = Set.to_list (PCSP.Problem.formulas_of primal) in
    (* Either each formula's whole-clause alternatives in CHC form, or (with
       [miniscope_term_alternatives]) each formula's placed tree, still in
       co-CHC form: [name_tree] converts its leaves. *)
    let formulas, trees =
      if config.miniscope_term_alternatives then
        ( [],
          List.map clauses ~f:(fun (uni_senv, phi) ->
              TermAlternatives.of_clause ~dedup:dedup_terms primal_strat_fn
                (uni_senv, Logic.ExtTerm.subst primal_strat_wf phi)) )
      else
        ( List.map clauses ~f:(fun (uni_senv, phi) ->
              let uni_senv, alts =
                subst_strat_alternatives primal_strat_wf primal_strat_fn
                  (uni_senv, phi)
              in
              (uni_senv, List.map alts ~f:(Logic.ExtTerm.subst sub))),
          [] )
    in
    let input_names =
      Set.Poly.union_list
      @@ List.concat_map formulas ~f:(fun (uni_senv, alts) ->
          Map.Poly.key_set uni_senv :: List.map alts ~f:Logic.ExtTerm.fvs_of)
      @ List.concat_map trees ~f:(fun (uni_senv, tree, _) ->
          [ Map.Poly.key_set uni_senv; TermAlternatives.fvs_of tree ])
    in
    let new_senv = ref Map.Poly.empty in
    let fresh sort =
      let n =
        Ident.mk_fresh_tvar_avoiding ~prefix:"Alt_"
          ~taken:(fun v ->
            Map.Poly.mem exi_senv v || Set.mem input_names v || Set.mem keys v
            || Map.Poly.mem !new_senv v)
          ()
      in
      new_senv := Map.Poly.set !new_senv ~key:n ~data:sort;
      n
    in
    let named = ref 0 in
    let phis =
      List.concat_map formulas ~f:(fun (uni_senv, alts) ->
          match name_alternatives ~fresh exi_senv (uni_senv, alts) with
          | Some phis ->
              incr named;
              phis
          | None -> [ (uni_senv, Logic.BoolTerm.or_of alts) ])
      @ List.concat_map trees ~f:(fun (uni_senv, tree, _) ->
          let clause, defs =
            name_tree ~fresh
              ~exi_senv_of:(fun () -> Map.force_merge exi_senv !new_senv)
              sub (uni_senv, tree)
          in
          if not (List.is_empty defs) then incr named;
          clause :: defs)
    in
    if config.miniscope_term_alternatives then
      Debug.print
      @@ lazy
           (let placed, whole =
              List.fold trees ~init:(0, 0) ~f:(fun (p, w) (_, tree, n) ->
                  let a = TermAlternatives.num_alternatives tree in
                  if a = 0 then (p, w) else (p + a, w + n))
            in
            sprintf
              "### Term alternatives placed at subformulas: %d alternative(s) \
               where the whole-clause substitution makes %d (clauses \
               placed by the one-point rule so far: %d)"
              placed whole
              (Atomic.get TermAlternatives.one_point_count));
    Debug.print
    @@ lazy
         (sprintf
            "### Term alternatives named in %d formula(s) by %d new \
             predicate(s)"
            !named (Map.Poly.length !new_senv));
    let params =
      {
        chc_params with
        PCSP.Params.senv = Map.force_merge chc_params.PCSP.Params.senv !new_senv;
        kind_map =
          Kind.add_kinds (Map.Poly.key_set !new_senv) Kind.Ord
            chc_params.PCSP.Params.kind_map;
      }
    in
    PCSP.Problem.of_formulas ~params (Set.Poly.of_list phis)

  (* ---------------------------------------------------------------------
     Choices that do not read the remembered copy ([copy_blind_choices]).

     The disjunctively well-founded reduction gives a least-fixpoint predicate
     [P] and the members of its component a copy [c] of an earlier visit to
     [P], and the check is satisfiable exactly when the reduced
     greatest-fixpoint system holds at the query.  A choice the checked side
     leaves open in such a body -- a disjunct, or a term of a key's term set,
     which the join of [subst_strat] makes a disjunct -- is then resolved
     pointwise in [c]: at one position the check may take one alternative for
     one copy value and another for another, which no strategy on the original
     game can do, and on an invalid input with a union of two well-founded
     rankings the check becomes satisfiable.

     The encoding below makes every such choice a function of the body's
     variables other than the copy.  In a CHC-form body, a choice node
     [K \/ D_1 \/ .. \/ D_k] ([k >= 2]; the [D_tau] are the disjuncts that
     mention a fixpoint predicate or the copy, [K] the others) becomes
     [K \/ not N_1(v_1) \/ .. \/ not N_k(v_k)], each [v_tau] holding no copy
     variable, with the Horn definition

       N_tau(v_tau) <= Reach_X(c, x) /\ Pi /\ not D_tau

     ([X(c, x)] the body's head, [Pi] the conditions under which the node is
     reached inside the body).  [N_tau(v)] reads "alternative [tau] loses at
     some copy at which the position [x] is reachable", so the head is
     derivable at [(c, x)] only when every alternative loses at some reachable
     copy, and a solution fixes, per value of [v], one alternative that wins at
     every reachable copy.  [Reach_Y] is the forward reachability of each
     fixpoint predicate from the query, over-approximated by the Horn clauses

       Reach_Y(t) <= Reach_X(p) /\ Pi_atom        (one per call Y(t) in X's body)
       Reach_Y(t) <= Pi_atom                      (one per call in the query)

     with [Pi_atom] the pure conjuncts beside the call and the negated pure
     disjuncts around it.  Without the reachability guard every alternative
     that calls [P] would have to win at the copy equal to the callee's state,
     where the comparison of a well-founded ranking fails, so every such answer
     would be lost. *)

  exception Unreadable of string

  (* A leaf of a body's connective tree, read against [exi_senv] (the check's
     predicates), [uni_senv] (the formula's universals, which shadow a
     predicate of their name) and [tracked] (the fixpoint predicates).
     [`Unreadable] is a leaf that mentions a fixpoint predicate other than as
     one application, positive or negated; [`Opaque] a leaf that mentions only
     other predicates (the dummies naming the opponent's decisions). *)
  let cb_leaf ~exi_senv ~uni_senv ~tracked t =
    let app t =
      match Logic.Term.let_apps t with
      | Logic.Var (v, _), args
        when Map.Poly.mem exi_senv v && not (Map.Poly.mem uni_senv v) ->
          Some (v, args)
      | _ -> None
    in
    let mentions_tracked t =
      Set.exists (Logic.ExtTerm.fvs_of t) ~f:(fun v ->
          Set.mem tracked v && not (Map.Poly.mem uni_senv v))
    in
    if not (mentions_pred exi_senv uni_senv t) then `Pure
    else
      match app t with
      | Some (v, args) when Set.mem tracked v ->
          if List.exists args ~f:mentions_tracked then `Unreadable
          else `Tracked_pos (v, args)
      | Some _ when not (mentions_tracked t) -> `Opaque_pos
      | _ -> (
          match Logic.Term.let_apps t with
          | Logic.Con (Logic.BoolTerm.Not, _), [ a ] -> (
              match app a with
              | Some (v, args)
                when Set.mem tracked v
                     && not (List.exists args ~f:mentions_tracked) ->
                  `Tracked_neg (v, args)
              | _ -> if mentions_tracked t then `Unreadable else `Opaque)
          | _ -> if mentions_tracked t then `Unreadable else `Opaque)

  (* The operands of an [Or] or [Alts] node, with nested nodes of the same
     connective spliced in: an [Or] inside an [Or], an [Alts] inside an
     [Alts].  An [Alts] inside an [Or], or an [Or] (a term alternative's copy
     of a disjunction) inside an [Alts], stays one operand.  Keeping each
     term alternative's copy apart keeps its own kept disjuncts (among them
     the copy's result guard) out of the premises of the other copies'
     choices: spliced into one node, every copy's kept disjuncts became a
     premise of every other copy's choice definitions and reachability
     clauses, and every copy's renamed result an argument of every choice
     predicate, so a node of [n] term alternatives emitted about [n^2]
     premise literals. *)
  let cb_disjuncts = function
    | TermAlternatives.Or ts ->
        let rec go = function
          | TermAlternatives.Or ts -> List.concat_map ts ~f:go
          | t -> [ t ]
        in
        List.concat_map ts ~f:go
    | TermAlternatives.Alts ts ->
        let rec go = function
          | TermAlternatives.Alts ts -> List.concat_map ts ~f:go
          | t -> [ t ]
        in
        List.concat_map ts ~f:go
    | t -> [ t ]

  (* Every leaf reached from the root through [Or] and [Alts] nodes only: the
     candidates for a formula's head, which may sit inside each term
     alternative's copy when a key's footprint spans the whole clause. *)
  let rec cb_frontier = function
    | TermAlternatives.Or ts | TermAlternatives.Alts ts ->
        List.concat_map ts ~f:cb_frontier
    | t -> [ t ]

  exception Too_large of int

  (* [copy_blind_chc ~params ~layout ~keys strat_wf strat_fn primal]: the part
     of the check [copy_blind_choices] encodes itself, [`Not_needed] when no
     formula of [primal] (the checked side's co-CHC) is the body of a
     predicate that carries a copy, in which case the check is built as
     without the field, or [`Too_large n] when the clauses emitted reached
     [n] premise literals and choice-predicate arguments, above
     [copy_blind_max_premises], and the encoding was abandoned.  [params]
     are the check's parameters (the checked side's keys relabelled
     ordinary), [layout] the checked side's table of prepended positions,
     [keys] every strategy key of both sides.

     Otherwise the result is [`Built (rest, added, new_senv, established)]:
     - [rest], the formulas of [primal] to be encoded as without the field
       (every formula that is not a copy-carrying body, and a copy-carrying
       body this encoding cannot read);
     - [added], CHC-form formulas: each readable copy-carrying body with its
       choices named as described above, the definitions of the names, and the
       reachability clauses of every formula of [primal];
     - [new_senv], the new predicates ([Choice_*], [Reach_*]), all ordinary;
     - [established], false when some formula mentions a fixpoint predicate in
       a way this encoding cannot read, so that the reachability predicates may
       miss a call or a copy-carrying choice stayed open: a satisfiable check
       is then no evidence that the checked side wins.

     Precondition: the formulas of [primal] are co-CHC (every fixpoint
     predicate positive except the one head of a body, with the checked side's
     keys still unsubstituted), as [to_pfwcsp] produces them.
     Postcondition: every formula of [added] is Horn after the substitution of
     the check's ordinary predicates by their negations has been applied to
     the part that came from [primal]; [added] mentions the choice and
     reachability predicates only as described, so each [Choice_*] and each
     [Reach_*] is defined by its own clauses alone. *)
  let copy_blind_chc ~params ~layout ~keys primal_strat_wf primal_strat_fn
      primal =
    let exi_senv = PCSP.Problem.senv_of primal in
    let tracked =
      Map.Poly.key_set exi_senv
      |> Set.filter ~f:(fun v -> Hashtbl.mem pred_index (Ident.name_of_tvar v))
    in
    let sub =
      PCSP.Problem.cochc_subst_of (PCSP.Problem.of_formulas ~params Set.Poly.empty)
    in
    (* Each formula with its ranking keys substituted and its Skolem keys'
       term alternatives placed at subformulas, as a connective tree. *)
    let trees =
      List.map (Set.to_list (PCSP.Problem.formulas_of primal))
        ~f:(fun (uni_senv, phi) ->
          let uni_senv', tree, _ =
            TermAlternatives.of_clause ~dedup:dedup_terms primal_strat_fn
              (uni_senv, Logic.ExtTerm.subst primal_strat_wf phi)
          in
          let tree =
            match tree with
            | TermAlternatives.Leaf l ->
                TermAlternatives.of_nnf (Logic.ExtTerm.nnf_of l)
            | t -> t
          in
          ((uni_senv, phi), uni_senv', tree))
    in
    (* The head of a formula (its one negated application of a fixpoint
       predicate, among the top-level disjuncts) and the formula's copy
       variables, read off the head's prepended positions. *)
    let head_of uni_senv tree =
      let leaf t = cb_leaf ~exi_senv ~uni_senv ~tracked t in
      let heads =
        List.filter_map (cb_frontier tree) ~f:(function
          | TermAlternatives.Leaf l -> (
              match leaf l with `Tracked_neg (v, args) -> Some (v, args) | _ -> None)
          | _ -> None)
        |> List.dedup_and_sort ~compare:(fun (v1, a1) (v2, a2) ->
               match Ident.tvar_compare v1 v2 with
               | 0 -> (
                   try Stdlib.compare a1 a2
                   with exn when not (Common.Timer.is_async exn) -> -1)
               | c -> c)
      in
      match heads with
      | [] -> Ok None
      | [ (v, args) ] ->
          let entries =
            Option.value ~default:[]
              (Hashtbl.find layout (Ident.name_of_tvar v))
          in
          let n = List.length entries in
          if n > List.length args then Error "a head shorter than its prefix"
          else
            let prefix, _ = List.split_n args n in
            let copies =
              List.map2_exn entries prefix ~f:(fun e a ->
                  match (e, a) with
                  | MuCLP.Reducer.Copy, Logic.Var (x, _) -> Ok (Some x)
                  | MuCLP.Reducer.Copy, _ -> Error "a copy argument that is not a variable"
                  | MuCLP.Reducer.Flag, _ -> Ok None)
              |> Result.all
            in
            Result.map copies ~f:(fun cs ->
                let copies = Set.Poly.of_list (List.filter_opt cs) in
                Some
                  ( v,
                    args,
                    copies,
                    Set.diff
                      (Set.Poly.union_list (List.map args ~f:Logic.ExtTerm.fvs_of))
                      copies ))
      | _ -> Error "two heads"
    in
    let parsed =
      List.map trees ~f:(fun (orig, uni_senv, tree) ->
          (orig, uni_senv, tree, head_of uni_senv tree))
    in
    (* Decided on the reduction's own record rather than on the heads found,
       so that a copy-carrying body whose head cannot be read is reported as
       not established instead of passing unencoded. *)
    let any_copy =
      Hashtbl.existsi layout ~f:(fun ~key ~data ->
          Map.Poly.mem exi_senv (Ident.Tvar key)
          && List.exists data ~f:(function
               | MuCLP.Reducer.Copy -> true
               | MuCLP.Reducer.Flag -> false))
    in
    if not any_copy then `Not_needed
    else
      let taken =
        Set.Poly.union_list
          (Map.Poly.key_set exi_senv :: keys
          :: List.concat_map parsed ~f:(fun (_, uni_senv, tree, _) ->
              [ Map.Poly.key_set uni_senv; TermAlternatives.fvs_of tree ]))
      in
      let new_senv = ref Map.Poly.empty in
      let fresh prefix sort =
        let n =
          Ident.mk_fresh_tvar_avoiding ~prefix
            ~taken:(fun v -> Set.mem taken v || Map.Poly.mem !new_senv v)
            ()
        in
        new_senv := Map.Poly.set !new_senv ~key:n ~data:sort;
        n
      in
      let reach_names = Hashtbl.Poly.create () in
      let reach_app v args =
        let r =
          Hashtbl.find_or_add reach_names v ~default:(fun () ->
              fresh "Reach_" (Map.Poly.find_exn exi_senv v))
        in
        Logic.ExtTerm.mk_var_app r args
      in
      let established = ref true in
      let unread = ref [] in
      (* A predicate of the check that carries a copy but is not tracked:
         [head_of] finds heads among tracked predicates only, so a body
         headed by it would be read as having no head and go to the
         ordinary encoding, its choices resolved pointwise in the copy.
         Every predicate with a copy is tracked when the reduction and
         [pred_index] were computed from the same problem; if one is not,
         the encoding is marked not established, so that a satisfiable
         check is not taken as a win. *)
      let untracked_copy_preds =
        Hashtbl.fold layout ~init:[] ~f:(fun ~key ~data acc ->
            if
              Map.Poly.mem exi_senv (Ident.Tvar key)
              && (not (Set.mem tracked (Ident.Tvar key)))
              && List.exists data ~f:(function
                   | MuCLP.Reducer.Copy -> true
                   | MuCLP.Reducer.Flag -> false)
            then key :: acc
            else acc)
      in
      if not (List.is_empty untracked_copy_preds) then (
        Debug.print
        @@ lazy
             (sprintf
                "### Copy-blind choices: predicate(s) %s carry a copy but are not tracked"
                (String.concat ~sep:", " untracked_copy_preds));
        established := false;
        unread := "a copy-carrying predicate that is not tracked" :: !unread);
      let rest = ref [] in
      let added = ref [] in
      let nodes = ref 0 in
      (* the lifted kept operands added under [copy_blind_lift_kept] *)
      let lifted = ref 0 in
      (* The premise literals and choice-predicate arguments emitted so far,
         against [copy_blind_max_premises]. *)
      let emitted = ref 0 in
      let charge n =
        emitted := !emitted + n;
        if !emitted > config.copy_blind_max_premises then
          raise (Too_large !emitted)
      in
      (* Read from the free variables rather than by filtering [uni_senv]: a
         formula with many term alternatives has one renamed result per
         alternative in [uni_senv], and each of its clauses mentions few. *)
      let clause_of uni_senv phi =
        let fvs = Logic.ExtTerm.fvs_of phi in
        ( Set.fold fvs ~init:Map.Poly.empty ~f:(fun acc v ->
              match Map.Poly.find uni_senv v with
              | Some s -> Map.Poly.set acc ~key:v ~data:s
              | None -> acc),
          phi )
      in
      match
      List.iter parsed ~f:(fun (orig, uni_senv, tree, head) ->
          let leaf t = cb_leaf ~exi_senv ~uni_senv ~tracked t in
          let to_term = TermAlternatives.to_term in
          let is_pure t =
            not (mentions_pred exi_senv uni_senv (to_term t))
          in
          let copies, premise, head_leaf, visible =
            match head with
            | Ok (Some (v, args, copies, visible)) ->
                ( copies,
                  Some (reach_app v args),
                  Some
                    (Logic.BoolTerm.neg_of (Logic.ExtTerm.mk_var_app v args)),
                  visible )
            | _ -> (Set.Poly.empty, None, None, Set.Poly.empty)
          in
          (* A disjunct kept outside the alternatives: it mentions neither a
             fixpoint predicate nor the copy, so resolving it reads only what
             the position shows. *)
          let is_kept t =
            let fvs = TermAlternatives.fvs_of t in
            Set.are_disjoint fvs copies
            && not
                 (Set.exists fvs ~f:(fun v ->
                      Set.mem tracked v && not (Map.Poly.mem uni_senv v)))
          in
          (* What is known when a sibling of a node's operand does not hold
             ([Or]) or holds ([And]), as a CHC-world premise: a pure formula,
             or a positive application of an untracked predicate, whose
             co-CHC occurrence is its negation.  Anything else yields nothing,
             which only weakens the premise. *)
          let neg_premise k =
            if is_pure k then Some (Logic.BoolTerm.neg_of (to_term k))
            else
              match k with
              | TermAlternatives.Leaf l -> (
                  match leaf l with `Opaque_pos -> Some l | _ -> None)
              | _ -> None
          in
          (* The operands of an [Or]/[Alts] node: the kept disjuncts, and the
             alternatives, in which every pure disjunct (one that mentions the
             copy but no predicate) is merged into one.  Pure disjuncts make no
             move between them: whichever holds, no call is followed, so
             choosing among them is only testing their disjunction, and a
             node whose alternatives are all pure is a test rather than a
             choice.  Naming each pure disjunct separately would demand one of
             them to hold at every reachable copy, which a substituted ranking
             (a disjunction over the copy) rarely satisfies.  A pure disjunct
             beside a call is still an alternative of its own node, since it
             lets the branch stop at one copy and continue at another. *)
          (* [copy_blind_lift_kept]: the lifted kept disjunct of a node of
             term alternatives whose alternatives (its spliced operands that
             are not kept) are [ts], or [None].  [results] are the formula's
             renamed result variables (its universals the placement of term
             alternatives introduced).  Each alternative that is a disjunction
             contributes its kept disjuncts but its guards, with each result
             [r] that has a guard [r <> t] among them (a kept disjunct
             [not (r = t)] or [r <> t], [r] not in [t]) replaced by [t].  An
             alternative with no other kept disjunct contributes nothing.
             Contract: at every assignment of the formula's variables the
             result implies the node, so adding it as a disjunct leaves the
             formula's meaning unchanged.  For one alternative: where each
             substituted result equals the value of its term, the contribution
             evaluates as the alternative's own kept disjuncts, which imply the
             alternative; where one differs, its guard, a disjunct of the
             alternative, holds.  This needs no quantifier over the results,
             so a contribution that still mentions a result (one with no guard
             in that alternative, or an enclosing node's) is as sound as one
             that does not.  The result is returned only when it is kept and
             pure (no copy, no predicate), so that it is a kept operand in the
             sense [is_kept] tests: if the lifted form mentioned the copy it
             would not be kept, and it is dropped. *)
          let lifted_kept ts =
            let results =
              Set.diff (Map.Poly.key_set uni_senv) (Map.Poly.key_set (fst orig))
            in
            let guard_of l =
              let side a b =
                match a with
                | Logic.Var (r, _)
                  when Set.mem results r
                       && not (Set.mem (Logic.ExtTerm.fvs_of b) r) ->
                    Some (r, b)
                | _ -> None
              in
              let eq_sides t =
                match Logic.Term.let_apps t with
                | Logic.TyApp (Logic.Con (Logic.BoolTerm.Eq, _), _, _), [ a; b ]
                  ->
                    Some (a, b)
                | _ -> None
              in
              let pair =
                match Logic.Term.let_apps l with
                | Logic.TyApp (Logic.Con (Logic.BoolTerm.Neq, _), _, _), [ a; b ]
                  ->
                    Some (a, b)
                | Logic.Con (Logic.BoolTerm.Not, _), [ e ] -> eq_sides e
                | _ -> None
              in
              Option.bind pair ~f:(fun (a, b) ->
                  match side a b with Some g -> Some g | None -> side b a)
            in
            let lift c =
              match c with
              | TermAlternatives.Or _ -> (
                  let ks = List.filter (cb_disjuncts c) ~f:is_kept in
                  let guards, others =
                    List.partition_map ks ~f:(fun k ->
                        match k with
                        | TermAlternatives.Leaf l -> (
                            match guard_of l with
                            | Some g -> First g
                            | None -> Second k)
                        | _ -> Second k)
                  in
                  let sub =
                    List.fold guards ~init:Map.Poly.empty
                      ~f:(fun m (r, t) ->
                        if Map.Poly.mem m r then m
                        else Map.Poly.set m ~key:r ~data:t)
                  in
                  match others with
                  | [] -> None
                  | _ ->
                      Some
                        (Logic.ExtTerm.subst sub
                           (Logic.BoolTerm.or_of (List.map others ~f:to_term))))
              | _ -> None
            in
            match List.filter_map ts ~f:lift with
            | [] -> None
            | ds ->
                let k = TermAlternatives.Leaf (Logic.BoolTerm.or_of ds) in
                if is_kept k && is_pure k then Some k else None
          in
          let operands t =
            let disjuncts = cb_disjuncts t in
            let kept, alts = List.partition_tf disjuncts ~f:is_kept in
            let kept =
              match t with
              | TermAlternatives.Alts _ when config.copy_blind_lift_kept -> (
                  match lifted_kept alts with
                  | Some k ->
                      incr lifted;
                      kept @ [ k ]
                  | None -> kept)
              | _ -> kept
            in
            let pure_alts, calls = List.partition_tf alts ~f:is_pure in
            let merged =
              match pure_alts with
              | [] -> []
              | [ d ] -> [ d ]
              | ds ->
                  [ TermAlternatives.Leaf
                      (Logic.BoolTerm.or_of (List.map ds ~f:to_term)) ]
            in
            (kept, merged @ calls)
          in
          (* A pure sibling at an [And] is a premise of the other operands.
             That is sound because a pure subtree contains no choice node (every
             node in it has at most its one merged pure alternative), so it is
             its own CHC form and holds in a solution of the check exactly when
             it holds.  A pure sibling whose truth at a copy were established
             only through named alternatives could not be assumed: two such
             conjuncts would each be assumed while justifying the other, and at
             a reachable copy where both fail no definition would fire. *)
          let pos_premise t = if is_pure t then Some (to_term t) else None in
          let siblings ts i =
            List.filter_mapi ts ~f:(fun j t -> if i = j then None else pos_premise t)
          in
          let rec reach ~pi = function
            | TermAlternatives.Leaf l -> (
                match leaf l with
                | `Tracked_pos (v, args) ->
                    charge (List.length pi + 2);
                    added :=
                      clause_of uni_senv
                        (Logic.BoolTerm.or_of
                           (reach_app v args
                           :: (Option.to_list premise @ pi
                              |> List.map ~f:Logic.BoolTerm.neg_of)))
                      :: !added
                | `Tracked_neg _ -> raise (Unreadable "a negated call in a body")
                | `Unreadable -> raise (Unreadable "an unreadable call")
                | `Pure | `Opaque_pos | `Opaque -> ())
            | TermAlternatives.And ts ->
                List.iteri ts ~f:(fun i t -> reach ~pi:(pi @ siblings ts i) t)
            | (TermAlternatives.Or _ | TermAlternatives.Alts _) as t ->
                let kept, alts = operands t in
                let pi = pi @ List.filter_map kept ~f:neg_premise in
                List.iter alts ~f:(reach ~pi)
          in
          let rec transform ~pi = function
            | TermAlternatives.Leaf l -> (
                match leaf l with
                | `Tracked_neg _ -> raise (Unreadable "a negated call in a body")
                | `Unreadable -> raise (Unreadable "an unreadable call")
                | _ -> l)
            | TermAlternatives.And ts ->
                Logic.BoolTerm.and_of
                  (List.mapi ts ~f:(fun i t ->
                       transform ~pi:(pi @ siblings ts i) t))
            | (TermAlternatives.Or _ | TermAlternatives.Alts _) as t ->
                let kept, alts = operands t in
                let pi = pi @ List.filter_map kept ~f:neg_premise in
                let alts' = List.map alts ~f:(transform ~pi) in
                let kept' = List.map kept ~f:to_term in
                if List.length alts' <= 1 then Logic.BoolTerm.or_of (kept' @ alts')
                else (
                  incr nodes;
                  let reach_head =
                    match premise with
                    | Some p -> p
                    | None -> raise (Unreadable "a choice outside a body")
                  in
                  let pi_fvs =
                    Set.Poly.union_list (List.map pi ~f:Logic.ExtTerm.fvs_of)
                  in
                  Logic.BoolTerm.or_of
                    (kept'
                    @ List.map alts' ~f:(fun d ->
                        let vs =
                          Set.Poly.union_list
                            [ Logic.ExtTerm.fvs_of d; pi_fvs; visible ]
                          |> Set.filter ~f:(fun v ->
                                 Map.Poly.mem uni_senv v && not (Set.mem copies v))
                        in
                        let zs =
                          List.map (Set.to_list vs) ~f:(fun v ->
                              (v, Map.Poly.find_exn uni_senv v))
                        in
                        charge (List.length pi + List.length zs + 2);
                        let n =
                          fresh "Choice_"
                            (Logic.Sort.mk_fun
                               (List.map zs ~f:snd @ [ Logic.BoolTerm.SBool ]))
                        in
                        let napp =
                          Logic.ExtTerm.mk_var_app n
                            (List.map zs ~f:(fst >> Logic.ExtTerm.mk_var))
                        in
                        added :=
                          clause_of uni_senv
                            (Logic.BoolTerm.or_of
                               ((napp :: Logic.BoolTerm.neg_of reach_head
                                 :: List.map pi ~f:Logic.BoolTerm.neg_of)
                               @ [ Logic.ExtTerm.subst sub d ]))
                          :: !added;
                        Logic.BoolTerm.neg_of napp)))
          in
          (* The body: the top-level disjuncts but the head.  [head_of]
             found one head at most (up to repetition), so every negated call
             among them is that head. *)
          let body_of tree =
            let is_head = function
              | TermAlternatives.Leaf l -> (
                  match leaf l with `Tracked_neg _ -> true | _ -> false)
              | _ -> false
            in
            (* The head removed wherever [cb_frontier] can reach it, the
               [Or]/[Alts] structure kept: in [H \/ Alts (A_1 .. A_k)] with
               [H] a disjunct of every [A_tau] this is exact, since [\/] is
               associative and idempotent. *)
            let rec strip = function
              | TermAlternatives.Or ts ->
                  TermAlternatives.Or
                    (List.filter_map ts ~f:(fun t ->
                         if is_head t then None else Some (strip t)))
              | TermAlternatives.Alts ts ->
                  TermAlternatives.Alts
                    (List.map ts ~f:(fun t ->
                         if is_head t then TermAlternatives.Or [] else strip t))
              | t -> t
            in
            match head_leaf with
            | None -> tree
            | Some _ -> (
                match tree with
                | TermAlternatives.Or _ | TermAlternatives.Alts _ ->
                    TermAlternatives.Or [ strip tree ]
                | t -> TermAlternatives.Or (if is_head t then [] else [ t ]))
          in
          let saved = !added in
          match
            (match head with
            | Error msg -> raise (Unreadable msg)
            | Ok _ -> ());
            let body = body_of tree in
            reach ~pi:[] body;
            if Set.is_empty copies then None
            else
              let h = Option.value_exn head_leaf in
              Some
                ( uni_senv,
                  Logic.ExtTerm.subst sub
                    (Logic.BoolTerm.or_of [ h; transform ~pi:[] body ]) )
          with
          | None -> rest := orig :: !rest
          | Some main -> added := main :: !added
          | exception Unreadable msg ->
              added := saved;
              established := false;
              unread := msg :: !unread;
              rest := orig :: !rest)
      with
      | exception Too_large n ->
          Debug.print
          @@ lazy
               (sprintf
                  "### Copy-blind choices: abandoned after %d premise \
                   literal(s), above the bound of %d"
                  n config.copy_blind_max_premises);
          `Too_large n
      | () ->
      Debug.print
      @@ lazy
           (sprintf
              "### Copy-blind choices: %d choice node(s) named by %d \
               predicate(s), %d reachability predicate(s), %d formula(s) left \
               to the ordinary encoding, %d lifted kept operand(s)%s"
              !nodes
              (Map.Poly.length !new_senv - Hashtbl.length reach_names)
              (Hashtbl.length reach_names) (List.length !rest) !lifted
              (if !established then ""
               else
                 sprintf "; NOT established (%s): a satisfiable check is not a win"
                   (String.concat ~sep:", "
                      (List.dedup_and_sort ~compare:String.compare !unread))));
      `Built (List.rev !rest, List.rev !added, !new_senv, !established)

  (* [copy_blind_now]: encode this one check copy-blind, whatever
     [copy_blind_choices] says; set only by [certify_wins_by_copy_blind] to
     re-check a win whose rankings are not proved transitive. *)
  (* [for_refinement]: set only on the copy-blind check of strategies whose
     ordinary check timed out ([copy_blind_on_timeout]).  A win or a
     counter-play of this check is handled as usual, and any outcome that
     yields neither runs [for_refinement], the ordinary check's own handling
     of its timeout. *)
  (* [cb_first_done]: set on the ordinary check that [copy_blind_first] runs
     after its copy-blind check yielded neither a win nor a counter-play, so
     that the ordinary check neither starts another copy-blind check first nor
     repeats it on a timeout. *)
  let rec solve_primal_dual ?(copy_blind_now = false) ?for_refinement
      ?(cb_first_done = false) turn
      ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
      ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual) =
    if
      config.copy_blind_first && (not copy_blind_now) && (not cb_first_done)
      && (not config.copy_blind_choices)
      && Option.is_none for_refinement
      && not
           (Map.Poly.is_empty primal_strat_wf && Map.Poly.is_empty primal_strat_fn)
    then (
      (* [copy_blind_first]: the copy-blind encoding is a fraction of the
         ordinary one and is sometimes decided where the ordinary check times
         out; its win is an answer and its counter-play refines the opponent,
         exactly as after a timeout.  Anything else falls back to the ordinary
         check, at the same budget. *)
      Debug.print
      @@ lazy
           (sprintf "### Checking the %s strategies copy-blind first"
              (if turn then "primal" else "dual"));
      solve_primal_dual ~copy_blind_now:true
        ~for_refinement:(fun () ->
          solve_primal_dual ~cb_first_done:true turn
            ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual))
        turn
        ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
        ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual))
    else
    let open Or_error.Monad_infix in
    let use_copy_blind = config.copy_blind_choices || copy_blind_now in
    chc_solver () >>= fun (module CHCSolver) ->
    backup_chc_solver () >>= fun (module CHCSolverBackUp) ->
    pcsp_solver () >>= fun (module PCSPSolver) ->
    let params =
      let params = PCSP.Problem.params_of primal in
      {
        params with
        kind_map =
          Map.Poly.map params.kind_map ~f:(function
            | Kind.FN | Kind.DWF -> Kind.Ord
            | k -> k);
      }
    in
    let keys =
      Set.Poly.union_list
        [
          Map.Poly.key_set primal_strat_wf;
          Map.Poly.key_set primal_strat_fn;
          Map.Poly.key_set dual_strat_wf;
          Map.Poly.key_set dual_strat_fn;
        ]
    in
    (* Under [copy_blind_choices], the copy-carrying bodies (and the
       reachability clauses) are encoded by [copy_blind_chc]; the formulas it
       leaves go through the encoding below as without the field. *)
    let copy_blind =
      if use_copy_blind then
        match
          copy_blind_chc ~params
            ~layout:(if turn then copy_layout_primal else copy_layout_dual)
            ~keys primal_strat_wf primal_strat_fn primal
        with
        | `Built b -> Some b
        | `Not_needed -> None
        | `Too_large _ when Option.is_some for_refinement ->
            (* A re-check after a timeout: skipped, and the timeout is
               handled as without the re-check. *)
            None
        | `Too_large _ ->
            (* Every formula through the ordinary encoding, and the check
               not established: a satisfiable answer is then no win. *)
            Some
              ( Set.to_list (PCSP.Problem.formulas_of primal),
                [],
                Map.Poly.empty,
                false )
      else None
    in
    let checked =
      match copy_blind with
      | None -> primal
      | Some (rest, _, _, _) ->
          PCSP.Problem.of_formulas ~params:(PCSP.Problem.params_of primal)
            (Set.Poly.of_list rest)
    in
    let copy_blind_established =
      match copy_blind with None -> true | Some (_, _, _, e) -> e
    in
    match for_refinement, copy_blind with
    | Some ordinary, None ->
        (* No copy-carrying body on this side: the re-check would be the
           ordinary check again. *)
        ordinary ()
    | _ ->
    (* The check of [strat_fn] (the checked side's term sets; its rankings
       are always [primal_strat_wf]): built for the strategy itself below, and
       for its restricted copies by [demonic_fallback]. *)
    let build_chc strat_fn =
    let chc =
      if config.name_term_alternatives then
        named_chc ~params ~keys primal_strat_wf strat_fn checked
      else
      checked |> PCSP.Problem.formulas_of
      |> Set.Poly.map ~f:(subst_strat primal_strat_wf strat_fn)
      |> PCSP.Problem.of_formulas ~params
      |> PCSP.Problem.cochc_to_chc
      |>
      (* The facts below assumed that the opponent's ranking covers every
         greatest-fixpoint step.  That named the steps but let a derivation end
         after one step in an arbitrary direction, so refinements covered single
         pairs and did not generalise.  They are not used: the check stays exact,
         the derivation is a complete play, and the pairs are read off it
         ([chain_pairs_of]). *)
      if true then Fn.id
      else
        PCSP.Problem.add_formulas
          (Set.Poly.map (Map.to_set primal_nu_wfs) ~f:(fun (x, s) ->
               let args =
                 Logic.mk_fresh_sort_env_list @@ Logic.Sort.args_of s
               in
               let papp =
                 Logic.ExtTerm.mk_var_app x
                   (List.map args ~f:(fst >> Logic.ExtTerm.mk_var))
               in
               (Map.Poly.of_alist_exn args, papp)))
    in
    let chc =
      match copy_blind with
      | None -> chc
      | Some (_, added, new_senv, _) ->
          let p = PCSP.Problem.params_of chc in
          PCSP.Problem.of_formulas
            ~params:
              {
                p with
                PCSP.Params.senv = Map.force_merge p.PCSP.Params.senv new_senv;
                kind_map =
                  Kind.add_kinds (Map.Poly.key_set new_senv) Kind.Ord
                    p.PCSP.Params.kind_map;
              }
            (Set.union (PCSP.Problem.formulas_of chc) (Set.Poly.of_list added))
    in
    let chc = GuardedClauses.apply chc in
    let chc =
      if config.drop_tautological_check_clauses then (
        let dropped, total, chc = TautologicalClauses.drop chc in
        Debug.print
        @@ lazy
             (sprintf
                "### Dropped %d tautological clause(s) of the check's %d"
                dropped total);
        chc)
      else chc
    in
    chc
    in
    let chc = build_chc primal_strat_fn in
    if config.demonic_fallback_on_undecided_check && not use_copy_blind then
      note_checked_terms turn primal_strat_fn;
    Debug.print
    @@ lazy
         (sprintf
            "\n\
             ### Checking whether the current %s strategy is winning via CHC \
             solving (%d sec.)"
            (if turn then "primal" else "dual")
            !(chc_budget ~backup:false turn));
    if verbose then
      Debug.print @@ lazy (sprintf "%s\n" @@ PCSP.Problem.str_of chc);
    Debug.print
    @@ lazy
         (let total, largest = cnf_size_of_problem chc in
          sprintf
            "### CNF size of the check (a bound from the formula structure): \
             %d clause(s) over %d formula(s), the largest formula %d"
            total
            (Set.length (PCSP.Problem.formulas_of chc))
            largest);
    (* Every ranking the checked side substitutes is known well-founded:
       produced by re-synthesis as one [WF] template instance (and unchanged
       since), or proved transitive, a transitive finite union of
       well-founded relations being well-founded.  The reason for each one
       that is neither is printed. *)
    let rankings_transitive () =
      Map.Poly.for_alli primal_strat_wf ~f:(fun ~key ~data ->
          match Hashtbl.find wf_by_construction (Ident.name_of_tvar key) with
          | Some t when phys_equal t data -> true
          | _ ->
          match RankingCheck.check data with
          | Ok () -> true
          | Error reason ->
              Debug.print
              @@ lazy (sprintf "### %s: %s" (Ident.name_of_tvar key) reason);
              false)
    in
    (* [demonic_fallback ()], under [demonic_fallback_on_undecided_check] and
       after this side's ordinary check timed out: the checks of the
       strategy's restricted copies ([DemonicCopies]), in their order, each at
       [demonic_fallback_timeout].  [Some r] when a copy's counter-play refined
       the opponent to a different strategy: [r] is the run continued with the
       opponent's turn, exactly as after an ordinary counter-play (the budget
       is not doubled, as after a copy-blind counter-play).  [None] when no
       copy did -- every copy won, was undecided, returned no play, or its
       refinement left the opponent unchanged -- and the timeout is then
       handled as without the field.  A copy's outcome is never a verdict:
       its counter-play is a play against the restricted strategy only, and
       it enters the run only through the opponent's refinement. *)
    let demonic_fallback () =
      if not (config.demonic_fallback_on_undecided_check && not use_copy_blind)
      then None
      else
        let copies =
          DemonicCopies.copies ~max:config.demonic_fallback_max_copies
            ~is_fresh:(is_fresh_term turn) primal_strat_fn
        in
        Debug.print
        @@ lazy
             (sprintf
                "### Demonic fallback: the %s check timed out; asking %d \
                 restricted cop%s at %d sec. each"
                (if turn then "primal" else "dual")
                (List.length copies)
                (if List.length copies = 1 then "y" else "ies")
                config.demonic_fallback_timeout);
        let refine_from chc' cex =
          let wf_records =
            Map.Poly.mapi dual_strat_wf ~f:(fun ~key ~data:_ ->
                Hashtbl.find wf_by_construction (Ident.name_of_tvar key))
          in
          let restore () =
            Map.Poly.iteri wf_records ~f:(fun ~key ~data ->
                match data with
                | Some t ->
                    Hashtbl.set wf_by_construction
                      ~key:(Ident.name_of_tvar key) ~data:t
                | None ->
                    Hashtbl.remove wf_by_construction (Ident.name_of_tvar key))
          in
          let current = (dual_strat_wf, dual_strat_fn, dual_nu_wfs) in
          try
            let refined =
              refine_strat ~check:chc'
                ~solve_wf:
                  (PCSPSolver.solve
                     ~timeout:(Some !(chc_budget ~backup:false turn))
                     ~bpvs:Set.Poly.empty)
                ~solve_certs:
                  (PCSPSolver.solve_with_kind_certificates ~timeout:None
                     ~bpvs:Set.Poly.empty)
                PCSPSolver.solve cex current
            in
            if same_strategy refined current then (
              restore ();
              None)
            else Some refined
          with
          | NoRefinement ->
              restore ();
              None
          | exn when not (Common.Timer.is_async exn) ->
              Debug.print
              @@ lazy
                   (sprintf "### Demonic fallback: refinement failed (%s)"
                      (Exn.to_string exn));
              restore ();
              None
        in
        let rec go i = function
          | [] ->
              Debug.print
              @@ lazy "### Demonic fallback: no copy refined the opponent";
              None
          | strat_fn' :: rest -> (
              let outcome =
                try
                  let chc' = build_chc strat_fn' in
                  match
                    CHCSolver.solve
                      ~timeout:(Some config.demonic_fallback_timeout) chc'
                  with
                  | Ok (sol, _) ->
                      Debug.print
                      @@ lazy
                           (sprintf "### Demonic fallback: copy %d: %s" i
                              (match sol with
                              | PCSP.Problem.Sat _ -> "the copy wins"
                              | Unsat (Some (Formula _)) -> "a counter-play"
                              | sol -> PCSP.Problem.str_of_sol_with_witness sol));
                      Option.map (DemonicCopies.counter_play sol) ~f:(fun cex ->
                          (chc', cex))
                  | Error err ->
                      Debug.print
                      @@ lazy
                           (sprintf "### Demonic fallback: copy %d: %s" i
                              (Error.to_string_hum err));
                      None
                with exn when not (Common.Timer.is_async exn) ->
                  Debug.print
                  @@ lazy
                       (sprintf "### Demonic fallback: copy %d: %s" i
                          (Exn.to_string exn));
                  None
              in
              match outcome with
              | None -> go (i + 1) rest
              | Some (chc', cex) -> (
                  match refine_from chc' cex with
                  | None -> go (i + 1) rest
                  | Some dual_strat ->
                      stalls := 0;
                      Debug.print
                      @@ lazy
                           (sprintf
                              "### Demonic fallback: copy %d refined the \
                               opponent; pass the turn to %s\n"
                              i
                              (if turn then "dual" else "primal"));
                      Some
                        ( solve_primal_dual (not turn) (dual_strat, dual)
                            ((primal_strat_wf, primal_strat_fn, primal_nu_wfs),
                             primal)
                        >>= fun s -> Ok (Verdict.flip s) )))
        in
        go 1 copies
    in
    let rec f retry res =
      match res with
      | ( ( PCSP.Problem.Timeout | Unknown
          | Unsat (None | Some (Proof _ | External _)) ),
          _ )
        when Option.is_some for_refinement ->
          Debug.print
          @@ lazy
               "### The copy-blind check gave neither a win nor a \
                counter-play; handling the ordinary check's timeout";
          (Option.value_exn for_refinement) ()
      | PCSP.Problem.Sat _, _
        when Option.is_some for_refinement && not copy_blind_established ->
          Debug.print
          @@ lazy
               "### The copy-blind check is satisfiable but not established; \
                handling the ordinary check's timeout";
          (Option.value_exn for_refinement) ()
      | Timeout, _
        when config.copy_blind_on_timeout && (not use_copy_blind)
             && (not cb_first_done)
             && not
                  (Map.Poly.is_empty primal_strat_wf
                  && Map.Poly.is_empty primal_strat_fn) ->
          Debug.print
          @@ lazy
               (sprintf
                  "### The %s check timed out; checking the same strategies \
                   with copy-blind choices"
                  (if turn then "primal" else "dual"));
          solve_primal_dual ~copy_blind_now:true
            ~for_refinement:(fun () -> f_ordinary retry res)
            turn
            ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
      | res -> f_ordinary retry res
    and f_ordinary retry = function
      | PCSP.Problem.Sat _, _
        when config.certify_wins_by_copy_blind && (not use_copy_blind)
             && not (rankings_transitive ()) ->
          (* A win with a ranking not proved transitive may rest on choices
             that read the remembered copy.  The same strategies are checked
             again with every such choice made blind to the copy, and that
             check decides: a win there is an answer, a counter-play there
             refines the opponent as any counter-play does. *)
          Debug.print
          @@ lazy
               (sprintf
                  "### Current %s strategy wins the check, but a ranking is \
                   not proved transitive; checking again with copy-blind \
                   choices"
                  (if turn then "primal" else "dual"));
          solve_primal_dual ~copy_blind_now:true turn
            ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
      | PCSP.Problem.Sat _, _ when not copy_blind_established ->
          (* The copy-blind encoding could not read every formula, so the
             reachability predicates may miss a call or a choice may still read
             the copy: a satisfiable check proves nothing.  Pass the turn as a
             failed refinement does, ending the run with [unknown] after two
             such turns in a row. *)
          incr stalls;
          if !stalls >= 2 then (
            Debug.print
            @@ lazy
                 "### Copy-blind encoding not established and no progress: \
                  unknown\n";
            Ok Unknown)
          else (
            Debug.print
            @@ lazy
                 (sprintf
                    "### The %s check is satisfiable but the copy-blind \
                     encoding is not established; pass the turn to %s\n"
                    (if turn then "primal" else "dual")
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
      | PCSP.Problem.Sat _, _
        when config.require_transitive_rankings
             && not (rankings_transitive ()) ->
          (* A win with a ranking not proved transitive may rest on choices
             that read the remembered copy, so it is not an answer. *)
          incr stalls;
          if !stalls >= 2 then (
            Debug.print
            @@ lazy
                 "### A win with a ranking not proved transitive, twice in a \
                  row: unknown\n";
            Ok Unknown)
          else (
            Debug.print
            @@ lazy
                 (sprintf
                    "### Current %s strategy wins the check, but a ranking is \
                     not proved transitive; pass the turn to %s\n"
                    (if turn then "primal" else "dual")
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
      | PCSP.Problem.Sat _, _ ->
          Debug.print
          @@ lazy
               (sprintf "### Current %s strategy is winning\n"
                  (if turn then "primal" else "dual"));
          Ok Valid
      | Unsat (Some (Formula cex)), _ ->
          if
            Map.Poly.is_empty primal_strat_wf
            && Map.Poly.is_empty primal_strat_fn
          then
            (* The checked side makes no decision, so there is no strategy
               to refine and a counter-play refutes it outright.  This holds
               under named opponent decisions too, provided the named
               encoding with empty strategies is equisatisfiable with the
               original; that condition is argued, not proved.  Without the
               shortcut the run refines only the opponent and can end only
               by synthesising the opponent's whole winning strategy. *)
            Ok Invalid
          else (
            Debug.print
            @@ lazy
                 (sprintf
                    "### Counter strategy found! Refining the current %s \
                     strategy via pfwCSP solving"
                    (if turn then "primal" else "dual"));
            try
              let primal_strat =
                (primal_strat_wf, primal_strat_fn, primal_nu_wfs)
              in
              let extra_plays =
                extra_counter_plays
                  (if retry then (module CHCSolverBackUp : CheckSolverType)
                   else (module CHCSolver : CheckSolverType))
                  ~budget:
                    (if config.extra_plays_at_initial_budget then
                       Int.min config.chc_initial_timeout
                         !(chc_budget ~backup:retry turn)
                     else !(chc_budget ~backup:retry turn))
                  dual_strat_wf chc cex
              in
              (* The records of [wf_by_construction] for the keys about to
                 be refined, restored if the refinement is rejected as
                 unchanged: the read-back of an accepted PCSat answer sets a
                 key's record to the term it produced, and when that
                 strategy is then rejected because it equals the current one
                 in simplified form, the current term stays and must keep the
                 record it had.  Restoring only returns each key to its state
                 before this refinement, so a ranking has a record only when
                 re-synthesis produced that very term (the record is compared
                 by physical equality) and it is well-founded as a [WF]
                 template instance; the one effect is that a later win with
                 that ranking is accepted as having well-founded rankings
                 instead of going to the transitivity test and the copy-blind
                 re-check, which is sound for the same reason the record is. *)
              let wf_records =
                Map.Poly.mapi dual_strat_wf ~f:(fun ~key ~data:_ ->
                    Hashtbl.find wf_by_construction (Ident.name_of_tvar key))
              in
              let restore_wf_records () =
                Map.Poly.iteri wf_records ~f:(fun ~key ~data ->
                    match data with
                    | Some t ->
                        Hashtbl.set wf_by_construction
                          ~key:(Ident.name_of_tvar key) ~data:t
                    | None ->
                        Hashtbl.remove wf_by_construction
                          (Ident.name_of_tvar key))
              in
              let dual_strat =
                refine_strat ~extra_plays ~check:chc
                  ~solve_wf:
                    (PCSPSolver.solve
                       ~timeout:(Some !(chc_budget ~backup:false turn))
                       ~bpvs:Set.Poly.empty)
                  ~solve_certs:(PCSPSolver.solve_with_kind_certificates
                                  ~timeout:None ~bpvs:Set.Poly.empty)
                  PCSPSolver.solve cex
                  (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
              in
              if
                Config.detect_unchanged_refinement config
                && same_strategy dual_strat
                     (dual_strat_wf, dual_strat_fn, dual_nu_wfs)
              then (
                restore_wf_records ();
                raise NoRefinement);
              stalls := 0;
              Debug.print
              @@ lazy
                   (sprintf "\n### Strategy refined and pass the turn to %s\n"
                      (if turn then "dual" else "primal"));
              solve_primal_dual (not turn) (dual_strat, dual)
                (primal_strat, primal)
              >>= fun s -> Ok (Verdict.flip s)
            with NoRefinement ->
              if
                Config.pass_turn_on_no_refinement config
                (* Under [copy_blind_choices] the check restricts the checked
                   side's choices, so its failure is not a loss even when the
                   opponent cannot be refined. *)
                || use_copy_blind
              then (
                (* A counter-play the opponent cannot generalise within the
                   template space is not a proof that the checked side loses;
                   pass the turn instead, and give up after both sides have
                   failed to refine in a row. *)
                incr stalls;
                if !stalls >= 2 then (
                  Debug.print
                  @@ lazy "### Neither side's refinement made progress: unknown\n";
                  Ok Unknown)
                else (
                Debug.print
                @@ lazy
                     (sprintf "### No refinement found; pass the turn to %s\n"
                        (if turn then "dual" else "primal"));
                solve_primal_dual (not turn)
                  ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
                  ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
                >>= fun s -> Ok (Verdict.flip s)))
              else Ok Invalid)
      | Unsat (None | Some (Proof _ | External _)), _ ->
          if
            Map.Poly.is_empty primal_strat_wf
            && Map.Poly.is_empty primal_strat_fn
          then
            (* The checked side makes no decision, so there is no strategy
               to refine and a counter-play refutes it outright.  This holds
               under named opponent decisions too, provided the named
               encoding with empty strategies is equisatisfiable with the
               original; that condition is argued, not proved.  Without the
               shortcut the run refines only the opponent and can end only
               by synthesising the opponent's whole winning strategy. *)
            Ok Invalid
          else (
            Debug.print
            @@ lazy
                 (sprintf
                    "### Current %s strategy is not winning (no cex obtained) \
                     and pass the turn to %s\n"
                    (if turn then "primal" else "dual")
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
      | Unknown, _ ->
          if retry then (
            Debug.print
            @@ lazy
                 (sprintf "### Unknown result and pass the turn to %s\n"
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
          else (
            Debug.print
            @@ lazy
                 (sprintf
                    "\n\
                     ### Checking again whether the current %s strategy is \
                     winning via CHC solving (%d sec.)"
                    (if turn then "primal" else "dual")
                    !(chc_budget ~backup:true turn));
            CHCSolverBackUp.solve
              ~timeout:(Some !(chc_budget ~backup:true turn))
              chc
            >>= f true)
      | Timeout, _ -> (
          match demonic_fallback () with
          | Some r -> r
          | None -> f_timeout retry)
      | OutSpace _, _ -> failwith "out of space" (* TODO *)
    and f_timeout retry =
          (* A timeout is not a verdict.  Both policies only choose which
             check runs next -- this side again, or the other side, with the
             strategies unchanged -- and with what budget; neither reads the
             timeout as a win or a loss.  Every answer is still produced by
             one of the other arms of this function, from a check that
             returned, by the same rule as under the other policy, and passing
             the turn is what an [unknown] from the backup solver already
             does.  So the policy changes whether and when a run answers, not
             which rule an answer rests on: as long as those rules are sound,
             no schedule can produce both answers, since the sides' claims are
             each other's negation. *)
          let budget = chc_budget ~backup:retry turn in
          budget := !budget * 2;
          (match config.chc_timeout_policy with
          | Config.Global_doubling ->
            Debug.print @@ lazy (sprintf "timeout and retry\n");
            solve_primal_dual turn
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
            >>= fun s -> Ok s
          | Pass_turn_on_timeout ->
            (* The stall rule answers [unknown] after both sides failed to
               refine in a row.  A side whose check timed out has not tried,
               so the run of failures is broken here; otherwise a failed
               refinement, this timeout, and a second failed refinement of the
               same side would end the run without the other side ever having
               been checked to an answer. *)
            stalls := 0;
            Debug.print
            @@ lazy
                 (sprintf "timeout and pass the turn to %s\n"
                    (if turn then "dual" else "primal"));
            solve_primal_dual (not turn)
              ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
              ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
            >>= fun s -> Ok (Verdict.flip s))
    in
    (* A side without a strategy unknown answers from the check alone (the two
       [Unsat] arms above return [Invalid] before reading any counterexample),
       so its main solver may be one that returns none. *)
    (if
       Map.Poly.is_empty primal_strat_wf && Map.Poly.is_empty primal_strat_fn
     then (
       if Option.is_some config.empty_strategy_chc_solver then
         Debug.print
         @@ lazy
              "### No strategy unknown on this side: the check goes to \
               empty_strategy_chc_solver\n";
       empty_strategy_chc_solver ())
     else Ok (module CHCSolver : CheckSolverType))
    >>= fun (module MainSolver) ->
    MainSolver.solve ~timeout:(Some !(chc_budget ~backup:false turn)) chc
    >>= f false

  let init_strat_of pfwcsp =
    let fn_strat =
      Map.Poly.map (PCSP.Problem.fnpvs_senv_of pfwcsp) ~f:(fun sort ->
          let params =
            let sargs, sret = Logic.Sort.args_ret_of sort in
            assert (Logic.BoolTerm.is_bool_sort sret);
            Logic.sort_env_list_of_sorts sargs
          in
          let arg_params, (xret, sret) = List.rest_last params in
          ( params,
            Set.Poly.of_list
            @@ List.map
                 ~f:(Logic.BoolTerm.eq_of sret (Logic.ExtTerm.mk_var xret))
            @@ Logic.ExtTerm.mk_dummy sret
               :: List.filter_map arg_params ~f:(fun (x, s) ->
                   if Stdlib.(s = sret) then Some (Logic.ExtTerm.mk_var x)
                   else None) ))
    in
    (* The candidate sets multiply in a clause mentioning several keys, so a
       side whose product exceeds the configured bound starts from each key's
       default term alone (the first element of the list above); the check of
       that smaller strategy is the same query, so no answer depends on it. *)
    let fn_strat =
      let fn_strat, fired =
        InitStrategy.bound_candidate_sets
          ~bound:config.init_fn_terms_product_bound
          ~default:(fun params ->
            let _, (xret, sret) = List.rest_last params in
            Logic.BoolTerm.eq_of sret (Logic.ExtTerm.mk_var xret)
            @@ Logic.ExtTerm.mk_dummy sret)
          fn_strat
      in
      if fired then
        Debug.print
        @@ lazy
             (sprintf
                "### Initial Skolem term sets multiply past %d; each key \
                 starts from its default term alone\n"
                (Option.value_exn config.init_fn_terms_product_bound));
      fn_strat
    in
    ( Map.Poly.map (PCSP.Problem.dwfpvs_senv_of pfwcsp) ~f:(fun sort ->
          let params =
            let sargs, sret = Logic.Sort.args_ret_of sort in
            assert (Logic.BoolTerm.is_bool_sort sret);
            Logic.sort_env_list_of_sorts sargs
          in
          Logic.ExtTerm.mk_lambda params @@ Logic.BoolTerm.mk_bool false),
      fn_strat )

  let solve ?(print_sol = false) muclp =
    let open Or_error.Monad_infix in
    stalls := 0;
    Hashtbl.clear wf_rank_pairs;
    Hashtbl.clear wf_by_construction;
    Hashtbl.clear wf_rank_regions;
    Debug.print @@ lazy "======== MuStrat ========";
    Debug.print @@ lazy "-=-=-=-= proving/disproving -=-=-=-=";
    preprocess ~elim_forall:true ~elim_exists:true ~elim_pvar_args:true muclp
    >>= fun muclp ->
    (* The two sides are linked only by the names of their Skolem keys: the
       refinement moves a counter-play's decision for the checked side's
       universal to the opponent's existential of the same name.  A key is
       named after its block's bound variable, a repeated name getting a
       suffix in traversal order, and [get_dual] reorders the operands of
       [and]/[or]; so in [(forall n m. g \/ A) /\ (forall n m. not g \/ B)]
       the primal's first [n] key sat in the A-block and the dual's in the
       B-block, every decision was filed under the block whose guard made it
       useless, and both sides stalled.  With every binder named apart first,
       a key's name is its own variable's on both sides and denotes the same
       block.  Meaning is kept (alpha-renaming); names only choose which
       candidate terms are tried, and every verdict still comes from a won
       check. *)
    let muclp = MuCLP.Problem.rename_binders_apart muclp in
    set_pred_index muclp;
    Debug.print @@ lazy "### Generating Primal Problem\n";
    let primal, primal_nu_wfs =
      (if true then Tuple2.map_fst ~f:Fn.id
       else Tuple2.map_fst ~f:(PCSP.Problem.to_nnf >> PCSP.Problem.to_cnf))
      @@ to_pfwcsp ~layout:copy_layout_primal muclp
    in
    Debug.print
    @@ lazy (sprintf "\n### Primal Problem:\n%s\n" @@ PCSP.Problem.str_of primal);
    Debug.print @@ lazy "### Generating Dual Problem\n";
    let dual, dual_nu_wfs =
      (if true then Tuple2.map_fst ~f:Fn.id
       else Tuple2.map_fst ~f:(PCSP.Problem.to_nnf >> PCSP.Problem.to_cnf))
      @@ to_pfwcsp ~layout:copy_layout_dual (MuCLP.Util.get_dual muclp)
    in
    Debug.print
    @@ lazy (sprintf "\n### Dual Problem:\n%s\n" @@ PCSP.Problem.str_of dual);
    let primal_strat_wf, primal_strat_fn = init_strat_of primal in
    let dual_strat_wf, dual_strat_fn = init_strat_of dual in
    Debug.print @@ lazy "\n## Initialized the current primal wf strategy:";
    Map.Poly.iteri primal_strat_wf ~f:(fun ~key ~data ->
        let args, phi' = Logic.Term.let_lam data in
        print_strat key args phi');
    Debug.print @@ lazy "\n## Initialized the current primal fn strategy:";
    Map.Poly.iteri primal_strat_fn ~f:(fun ~key ~data:(args, terms') ->
        Set.iter terms' ~f:(print_strat key args));
    Debug.print @@ lazy "\n## Initialized the current dual wf strategy:";
    Map.Poly.iteri dual_strat_wf ~f:(fun ~key ~data ->
        let args, phi' = Logic.Term.let_lam data in
        print_strat key args phi');
    Debug.print @@ lazy "\n## Initialized the current dual fn strategy:";
    Map.Poly.iteri dual_strat_fn ~f:(fun ~key ~data:(args, terms') ->
        Set.iter terms' ~f:(print_strat key args));
    solve_primal_dual true
      ((primal_strat_wf, primal_strat_fn, primal_nu_wfs), primal)
      ((dual_strat_wf, dual_strat_fn, dual_nu_wfs), dual)
    >>= function
    | sol ->
        Debug.print @@ lazy "=========================";
        if print_sol then
          print_endline
          @@ sprintf "%s"
               (if config.output_yes_no then lts_str_of_solution sol
                else str_of_solution sol);
        Or_error.return (sol, -1, "" (*ToDo*))

  let solve_pcsp ?(print_sol = false) pcsp =
    (* This backend reduces a predicate constraint problem to fixpoint logic,
       and a fixpoint problem has no place to carry a predicate's KIND: the
       reduction makes every predicate an ordinary least fixpoint.  Every kind
       but the ordinary one states an obligation the clauses do not -- a
       functional predicate must be total and deterministic, a well-founded one
       may not contain a cycle, a non-empty one may not be false everywhere --
       so dropping it answers a weaker question, and the answer comes back
       "satisfiable" on inputs the kind is what refutes.  A three-line file
       whose two clauses force one functional predicate to take two values at
       the same argument is answered satisfiable here and refuted by the
       predicate constraint solver.

       The problem constructor is shared -- the class name on the command line
       documents the input and nothing checks it -- so the compatibility table
       cannot refuse the pairing and the check has to happen here.  Naming the
       one kind that IS supported cannot go stale the way a list of kinds to
       refuse did: the kinds nobody thought of were accepted by such a list. *)
    PCSP.Problem.refuse_non_ord_kinds ~backend:"MuStrat" pcsp;
    let (module Preprocessor : Preprocessor.PreprocessorType) =
      Preprocessor.(make @@ Config.make true config.verbose 4 4 true)
    in
    Debug.print
    @@ lazy "************* converting pfwCSP to muCLP ***************";
    Preprocessor.solve
      (fun ?oracle pcsp ->
        ignore oracle;
        let open Or_error.Monad_infix in
        solve ~print_sol:false (MuCLP.Util.of_chc ~print:Debug.print pcsp)
        >>= fun (sol, _, _) ->
        let sol =
          match sol with
          | Valid -> PCSP.Problem.Sat Map.Poly.empty (* ToDo *)
          | Invalid -> PCSP.Problem.Unsat None (* ToDo *)
          | Unknown -> PCSP.Problem.Unknown
          | Timeout -> PCSP.Problem.Timeout
        in
        if print_sol then
          print_endline @@ sprintf "%s" (PCSP.Problem.str_of_solution sol);
        Or_error.return
          ( sol,
            {
              PCSatCommon.State.num_cegis_iters = -1;
              unsat_witness = None;
              kind_certificates = Map.Poly.empty;
            } ))
      pcsp

  let determinize fml chc det params =
    Debug.print @@ lazy "strategy template:";
    Map.Poly.iteri det ~f:(fun ~key ~data:(senv, t) ->
        Debug.print
        @@ lazy
             (sprintf "%s: %s" (Ident.name_of_tvar key)
                (Logic.ExtTerm.str_of_term Map.Poly.empty
                   (Map.force_merge (Map.Poly.of_alist_exn params) senv)
                   t)));
    Debug.print @@ lazy "";
    let chc =
      ( Map.Poly.empty,
        Logic.Term.mk_apps
          (Logic.BoolTerm.mk_imply ())
          [ fml; Logic.BoolTerm.mk_bool false ] )
      :: chc
    in
    let params = PCSP.Params.make @@ Map.Poly.of_alist_exn params in
    let problem = PCSP.Problem.of_formulas ~params (Set.Poly.of_list chc) in
    Debug.print @@ lazy "recursion-free CHC problem for determinization:";
    Debug.print @@ lazy (PCSP.Problem.str_of problem);
    Debug.print @@ lazy "";
    let open Or_error in
    pcsp_solver_determ () >>= fun (module PCSPSolver) ->
    PCSPSolver.solve problem >>= function
    | PCSP.Problem.Sat subs, _num_iters ->
        Debug.print
        @@ lazy
             ("solution:\n" ^ Logic.str_of_term_subst Logic.ExtTerm.str_of subs);
        Ok (Map.Poly.map det ~f:(Tuple2.map_snd ~f:(Logic.ExtTerm.subst subs)))
    | PCSP.Problem.Unsat _, _num_iters -> assert false
    | PCSP.Problem.Unknown, _num_iters -> assert false
    | PCSP.Problem.OutSpace _, _ -> assert false
    | PCSP.Problem.Timeout, _ -> assert false

  let lia_solve_smt f print_sol to_determinize =
    let open StratSynth in
    let f = Option.value_exn @@ LIA.formula_of_term f in
    Debug.print @@ lazy (sprintf "theory is LIA");
    Debug.print
    @@ lazy (sprintf "input: %s\n" (LIAStrategySynthesis.formula_to_string f));
    let p, s = LIAStrategySynthesis.nondet_strategy_synthesis z3_solve f in
    Debug.print
    @@ lazy
         (sprintf "strategy skelton for %s:\n%s"
            (LIAStrategySynthesis.player_to_string p)
            (LIAStrategySynthesis.ssforest_to_string s));
    let f =
      match p with SAT -> f | UNSAT -> PreFormula.neg_formula LIA.neg_atom f
    in
    (if to_determinize then
       let fml, chc, det, params = LIAStrategySynthesis.loseCHC [] s f in
       match determinize fml chc det params with
       | Ok ds ->
           Debug.print
           @@ lazy
                (sprintf "determinized strategy for %s:"
                   (LIAStrategySynthesis.player_to_string p));
           Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
               Debug.print
               @@ lazy
                    (sprintf "%s: %s" (Ident.name_of_tvar key)
                       (Logic.ExtTerm.str_of_term Map.Poly.empty senv t)))
       | Error err -> failwith (Error.to_string_hum err));
    let solution =
      match p with
      | SAT -> SMT.Problem.Sat [] (*ToDo*)
      | UNSAT -> SMT.Problem.Unsat
    in
    Debug.print @@ lazy "=========================";
    if print_sol then
      print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
    Ok solution

  let lra_solve_smt f print_sol to_determinize =
    let open StratSynth in
    let f = Option.value_exn @@ LRA.formula_of_term f in
    Debug.print @@ lazy (sprintf "theory is LRA");
    Debug.print
    @@ lazy (sprintf "input: %s\n" (LRAStrategySynthesis.formula_to_string f));
    let p, s = LRAStrategySynthesis.nondet_strategy_synthesis z3_solve f in
    Debug.print
    @@ lazy
         (sprintf "strategy skelton for %s:\n%s"
            (LRAStrategySynthesis.player_to_string p)
            (LRAStrategySynthesis.ssforest_to_string s));
    let f =
      match p with SAT -> f | UNSAT -> PreFormula.neg_formula LRA.neg_atom f
    in
    (if to_determinize then
       let fml, chc, det, params = LRAStrategySynthesis.loseCHC [] s f in
       match determinize fml chc det params with
       | Ok ds ->
           Debug.print
           @@ lazy
                (sprintf "determinized strategy for %s:"
                   (LRAStrategySynthesis.player_to_string p));
           Map.Poly.iteri ds ~f:(fun ~key ~data:(senv, t) ->
               Debug.print
               @@ lazy
                    (sprintf "%s: %s" (Ident.name_of_tvar key)
                       (Logic.ExtTerm.str_of_term Map.Poly.empty senv t)))
       | Error err -> failwith (Error.to_string_hum err));
    let solution =
      match p with
      | SAT -> SMT.Problem.Sat [] (*ToDo*)
      | UNSAT -> SMT.Problem.Unsat
    in
    Debug.print @@ lazy "=========================";
    if print_sol then
      print_endline @@ sprintf "%s" (SMT.Problem.str_of_solution solution);
    Ok solution

  let solve_smt ?(print_sol = false) g =
    Debug.print
    @@ lazy (sprintf "original input: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      let senv = Set.to_list @@ LogicOld.Formula.sort_env_of g in
      LogicOld.Formula.mk_exists_if_bounded senv g
    in
    Debug.print @@ lazy (sprintf "closed: %s\n" @@ LogicOld.Formula.str_of g);
    let g =
      Normalizer.normalize @@ Evaluator.simplify @@ LogicOld.Formula.rm_div_mod
      @@ LogicOld.Formula.elim_redundant_quantifiers @@ Normalizer.normalize
      @@ Evaluator.simplify @@ LogicOld.Formula.elim_ite @@ Normalizer.normalize
      @@ LogicOld.Formula.elim_let
      @@ Normalizer.normalize_let ~rename:true
      @@ Typeinf.typeinf_formula
           ~print:(*Debug.print*) (fun _ -> ())
           ~default:(Some LogicOld.T_int.SInt (*ToDo*))
      @@ LogicOld.Formula.aconv_tvar g
    in
    Debug.print @@ lazy (sprintf "input: %s\n" (LogicOld.Formula.str_of g));
    let f = Logic.ExtTerm.of_old_formula g in
    if false then
      Debug.print
      @@ lazy (sprintf "original input: %s\n" (Logic.ExtTerm.str_of f));
    if Option.is_some @@ StratSynth.LIA.formula_of_term f then
      lia_solve_smt f print_sol config.determinize
    else if Option.is_some @@ StratSynth.LRA.formula_of_term f then
      lra_solve_smt f print_sol config.determinize
    else
      (* a refusal of the input, so an error value, not an exception: the
         strategy synthesis has an integer and a real arithmetic form and no
         other *)
      Or_error.error_string
        "MuStrat's SMT solver handles linear integer arithmetic or linear \
         real arithmetic (LIA or LRA) only, and this formula is in neither"
end

(*
module RandomFormula = struct
  let random_affine vars =
    let vars' = None :: List.map ~f:(fun x -> Some x) vars in
    let max = 20 in
    List.map ~f:(fun x -> (x, Z.of_int (Random.int max - (max / 2)))) vars'
    |> Map.Poly.of_alist_exn

  let random_atom_gt0 vars = LIA.Gt0 (random_affine vars)

  let random_atom_div vars =
    LIA.Div (Z.of_int (Random.int 10 + 1), random_affine vars)

  let random_atom = if Random.bool () then random_atom_gt0 else random_atom_div

  let rec random_formula depth vars var_prefix r =
    let open PreFormula in
    let get_newvar () =
      let n = !r in
      r := n + 1;
      Ident.Tvar (var_prefix ^ string_of_int n)
    in
    if depth <= 0 then Atom (random_atom vars)
    else
      match Random.int 5 with
      | 0 -> Atom (random_atom_gt0 vars)
      | 1 ->
          And
            (List.init (Random.int 5) ~f:(fun _ ->
                 random_formula (depth - 1) vars var_prefix r))
      | 2 ->
          Or
            (List.init (Random.int 5) ~f:(fun _ ->
                 random_formula (depth - 1) vars var_prefix r))
      | 3 ->
          let newvar = get_newvar () in
          Bind
            ( Forall,
              (newvar, IntTerm.SInt),
              random_formula (depth - 1) (newvar :: vars) var_prefix r )
      | 4 ->
          let newvar = get_newvar () in
          Bind
            ( Exists,
              (newvar, IntTerm.SInt),
              random_formula (depth - 1) (newvar :: vars) var_prefix r )
      | _ -> assert false

  let rec winning ds =
    let open LIAStrategySynthesis in
    let open PreFormula in
    function
    | Atom a -> (LIA.term_of_atom a, [])
    | And l ->
        let fs, vars = List.map ~f:(winning ds) l |> List.unzip in
        (BoolTerm.and_of fs, List.concat vars)
    | Or l ->
        let fs, vars = List.map ~f:(winning ds) l |> List.unzip in
        (BoolTerm.or_of fs, List.concat vars)
    | Bind (Forall, v, f) ->
        let f', vars = winning ds f in
        (f', v :: vars)
    | Bind (Exists, (tvar, _), f) ->
        let f', vars = winning ds f in
        let _, t = Map.Poly.find_exn ds tvar in
        (Term.subst (Map.Poly.singleton tvar t) f', vars)

  let test n =
    let open LIAStrategySynthesis in
    for _ = 1 to n do
      let depth = Random.int 10 in
      let f = random_formula depth [] "x" (ref 0) in
      printf "input: %s\n" (formula_to_string f);
      let p, s = nondet_strategy_synthesis f in
      printf "%s\n%s\n" (player_to_string p) (ssforest_to_string s);
      let f =
        match p with SAT -> f | UNSAT -> PreFormula.neg_formula LIA.neg_atom f
      in
      match determinize solve_pcsp s f with
      | Ok ds ->
          print_endline "strategy:";
          Map.Poly.iteri
            ~f:(fun ~key ~data:(senv, t) ->
              printf "%s: %s\n" (Ident.name_of_tvar key)
                (Logic.ExtTerm.str_of_term senv t))
            ds;
          let win, vars = winning ds f in
          let not_win = BoolTerm.neg_of win in
          let module Z3interface =
            Z3Smt.Z3interfaceNew.Make (Z3Smt.Z3interfaceNew.ExtTerm) in
          assert (
            Option.is_none
              (Z3interface.check_sat [ not_win ] vars (Z3.mk_context [])))
      | Error _ -> assert false
    done
end

let () =
  let open LIAStrategySynthesis in
  let open PreFormula in
  (match SMT.Smtlib2.from_smt2_file (Sys.get_argv ()).(1) with
  | Ok f -> (
      print_endline @@ LogicOld.Formula.str_of f;
      let f = Logic.ExtTerm.of_old_formula f |> LIA.formula_of_term in
      let f = Option.value_exn f in
      printf "input: %s\n" (formula_to_string f);
      let p, s = nondet_strategy_synthesis f in
      printf "%s\n%s\n" (player_to_string p) (ssforest_to_string s);
      let f =
        match p with SAT -> f | UNSAT -> PreFormula.neg_formula LIA.neg_atom f
      in
      match determinize solve_pcsp s f with
      | Ok ds ->
          Map.Poly.iteri
            ~f:(fun ~key ~data:(senv, t) ->
              printf "%s: %s\n" (Ident.name_of_tvar key)
                (Logic.ExtTerm.str_of_term senv t))
            ds
      | Error _ -> ())
  | Error _ -> assert false);
  print_string "random test\n";
  Random.self_init ();
  RandomFormula.test 100
*)
