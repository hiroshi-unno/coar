open Core
open Common.Ext
open Ast
open Ast.LogicOld
open Common.Combinator

(* Refuting a problem by a goal clause read against a finite unfolding of the
   clauses that derive its predicates.

   The procedure.  For an unknown [P], call a clause a FACT of [P] when its
   only atom is [P(u)] in the head, and a STEP of [P] when its head is [P(h)]
   and every atom of its body is an application of [P] -- such as the law
   [P(a, s1, b) /\ P(b, s2, c) => P(a, s1 ++ s2, c)] of a transitive relation
   -- in both cases with a pure part that mentions no unknown.  Write a clause
   [phi \/ P(u)] as "[not phi] implies [P(u)]".  The unfoldings of [P] are the
   formulas over fresh parameters [x]

     L_1(x)     = \/_facts  exists y. not phi /\ x = u
     L_{i+1}(x) = L_1(x) \/ \/_steps exists y. not phi /\ x = h /\ /\_j L_i(a_j)

   where [y] are the clause's own variables.  A GOAL clause is one with no
   head atom whose body atoms are all applications of unknowns that have
   unfoldings, [phi \/ \/_j not Q_j(t_j)]; its resolvent at depth [d] is the
   formula [phi \/ \/_j not L^Q_d(t_j)], which mentions no unknown.

   Why it is sound.  Fix a model [M] of the background theory and an
   interpretation [I] of the unknowns under which every clause holds.  By
   induction on [i], [L_i(x)] implies [P(x)] in [M] under [I]: a fact gives
   [L_1], and a step whose body atoms each hold by the induction hypothesis
   gives the next level.  So if a goal's resolvent is false in [M] for some
   value of its variables, each [Q_j(t_j)] holds there and the goal clause is
   false under [I]; as [I] was arbitrary, no interpretation satisfies the
   problem in [M], which is unsatisfiable under the definition (every model
   admits an interpretation).  A validity question answered [Invalid] exhibits
   such a model and value.  The model Z3 returns interprets whatever the theory
   leaves open (a selector off its constructor, a division by zero, a free
   function), and that interpretation is one of the models the definition
   ranges over, so no guard for interpretation-dependent terms is needed: this
   reads "invalid" as "false in some model", never as "false in every model".
   All of this rests on the solver's [sat] being a model of the question.  It
   is not for a question that applies a recursive function under a quantifier:
   Z3 5.1.0 answers such an unsatisfiable question [sat]
   ([Z3interface.recursive_function_under_binder]), which made a satisfiable
   input answer [unsat] -- an unfolded count compared, under the universals the
   goal's premises put around it, with the recursive count it unfolds.  The
   solver boundary ([Z3interface.check_sat], under [check_valid] too) reads
   such a [sat] as [`Unknown], and [ask] does not ask such a question.
   Kinds are not used: a solution of a kinded unknown also satisfies the
   clauses, so the inclusion holds for it too, and leaving the kind out only
   weakens the refutation.  Only a subset of the clauses is read, which is
   also safe: the inclusion needs only the facts and steps to hold.

   What it does not do.  It never concludes [sat]: a resolvent shown valid,
   undecided or not asked changes nothing.  The unfolding is an
   under-approximation of the least solution, so a refutation that needs a
   derivation deeper than [d] levels is not found.  A step with two body atoms
   doubles the formula per level, so [L_d] has about [2^d] copies of the facts
   and covers derivations of up to [2^(d-1)] facts chained by such a step.
   Steps through other unknowns (mutual recursion) are not unfolded. *)

(** the clause's pure part mentions no unknown, as an applied predicate or as a
    term variable *)
let pure_known unknowns (phi : Formula.t) =
  Set.for_all (Formula.fvs_of phi) ~f:(fun x -> not (Set.mem unknowns x))

let pvar_args (atm : Atom.t) =
  match atm with
  | Atom.App (Predicate.Var (p, sorts), ts, _) -> Some (p, sorts, ts)
  | _ -> None

(** [exists y. /\ conjs /\ /\_j l(ts_j)] for [bodies = [ts_1; ...]], where [y]
    are the free term variables other than [params]. Before closing, the
    one-point rule [exists y. y = t /\ phi  <=>  phi[t/y]] (for [y] bound and
    not in [t]) is applied to the equations among [conjs], and each step is
    applied to the argument lists in [bodies] too, so that the copies of [l] are
    made at the substituted arguments: exact, and it keeps the variables of a
    fact or step that only name an argument out of the formula *)
let close_exists ?(solve_linear = false) ?(l = fun _ _ -> Formula.mk_true ())
    params conjs bodies =
  let params = Set.Poly.of_list (List.map params ~f:fst) in
  (* with [solve_linear], an integer equation [t1 = t2] whose difference is
     [a y + r] for a bound [y] with [a] = 1 or -1 and [r] a linear sum of
     variables and a literal, [y] not among them, is the equation [y = -a r]:
     the one-point rule then applies to it as to [y = t], which is exact by
     the same argument.  [r] is kept free of any other term: an accumulator
     [n = n' + ubv_to_int (...)] solved for [n'] would carry every level's
     summand down into the levels below, and on a bit-vector loop whose
     counter is a word (so not solved) that made the resolvent a third
     larger and left it undecided where the default refutes it in seconds *)
  let solve t1 t2 =
    if not (T_int.is_sint t1 && T_int.is_sint t2) then None
    else
      let m, us, c = BoundHoist.comb Z.one t1 Z.minus_one t2 in
      if not (List.is_empty us) then None
      else
      List.find_map (Map.Poly.to_alist m) ~f:(fun (y, a) ->
          if Z.equal (Z.abs a) Z.one && not (Set.mem params y) then
            let rest = (Map.Poly.remove m y, us, c) in
            Some (y, BoundHoist.rebuild (BoundHoist.scale (Z.neg a) rest))
          else None)
  in
  let point c =
    if not (Formula.is_eq c) then None
    else
      let t1, t2, _ = Formula.let_eq c in
      let var x t =
        match x with
        | Term.Var (y, _, _)
          when (not (Set.mem params y)) && not (Set.mem (Term.tvs_of t) y) ->
            Some (y, t)
        | _ -> None
      in
      match var t1 t2 with
      | Some r -> Some r
      | None -> (
          match var t2 t1 with
          | Some r -> Some r
          | None -> if solve_linear then solve t1 t2 else None)
  in
  let norm_t = if solve_linear then BoundHoist.norm_term else Fn.id in
  let norm_f = if solve_linear then BoundHoist.norm_formula else Fn.id in
  let rec elim conjs bodies =
    match
      List.find_mapi conjs ~f:(fun i c ->
          Option.map (point c) ~f:(fun r -> (i, r)))
    with
    | None -> (conjs, bodies)
    | Some (i, (y, t)) ->
        let sub = Map.Poly.singleton y t in
        elim
          (List.filter_mapi conjs ~f:(fun j c ->
               if j = i then None else Some (norm_f (Formula.subst sub c))))
          (List.map bodies ~f:(List.map ~f:(norm_t <<< Term.subst sub)))
  in
  let conjs, bodies =
    elim (List.concat_map conjs ~f:Formula.conjuncts_list_of) bodies
  in
  let body = Formula.and_of (conjs @ List.mapi bodies ~f:l) in
  let ys =
    Set.to_list
    @@ Set.filter (Formula.term_sort_env_of body) ~f:(fun (x, _) ->
        not (Set.mem params x))
  in
  Formula.exists ys body

(** [size_up_to cap phi] is [min (n, cap + 1)] for [n] the number of nodes of
    [phi] read as a tree (formula, atom and term constructors, an embedded
    formula and a fixpoint's body included, a let's definition counted once),
    computed in time proportional to its result rather than to [phi]'s size:
    the unfoldings share their lower levels physically, so the tree of one
    can be far larger than its memory. *)
let size_up_to cap (phi : Formula.t) =
  let exception Over in
  let n = ref 0 in
  let tick () =
    incr n;
    if !n > cap then raise Over
  in
  let rec term (t : Term.t) =
    tick ();
    match t with
    | Term.Var _ -> ()
    | Term.FunApp (sym, args, _) ->
        (match sym with T_bool.Formula phi -> formula phi | _ -> ());
        List.iter args ~f:term
    | Term.LetTerm (_, _, def, body, _) ->
        term def;
        term body
  and atom (a : Atom.t) =
    tick ();
    match a with
    | Atom.True _ | Atom.False _ -> ()
    | Atom.App (pred, args, _) ->
        (match pred with
        | Predicate.Fixpoint def -> formula def.body
        | Predicate.Var _ | Predicate.Psym _ -> ());
        List.iter args ~f:term
  and formula (phi : Formula.t) =
    match phi with
    | Formula.Atom (a, _) -> atom a
    | Formula.UnaryOp (_, phi, _) | Formula.Bind (_, _, phi, _) ->
        tick ();
        formula phi
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        tick ();
        formula phi1;
        formula phi2
    | Formula.LetRec (defs, phi, _) ->
        tick ();
        List.iter defs ~f:(fun def -> formula def.body);
        formula phi
    | Formula.LetFormula (_, _, def, body, _) ->
        tick ();
        term def;
        formula body
  in
  try
    formula phi;
    !n
  with Over -> cap + 1

let exceeds max_size phi =
  match max_size with None -> false | Some m -> size_up_to m phi > m

(** the classification of one clause: [`Fact (p, sorts, u, phi)],
    [`Step (p, h, bodies, phi)], [`Goal (atoms, phi)] or [`Other] *)
let classify unknowns (c : ClauseOld.t) =
  let _, ps, ns, phi = c in
  if not (pure_known unknowns phi) then `Other
  else
    let ps = Set.to_list ps and ns = Set.to_list ns in
    let apps l = List.map l ~f:pvar_args |> Option.all in
    match (apps ps, apps ns) with
    | Some [ (p, sorts, u) ], Some [] -> `Fact (p, sorts, u, phi)
    | Some [ (p, _, h) ], Some (_ :: _ as bodies)
      when List.for_all bodies ~f:(fun (q, _, _) -> Ident.pvar_equal p q) ->
        `Step (p, h, List.map bodies ~f:trd3, phi)
    | Some [], Some (_ :: _ as atoms) ->
        `Goal (List.map atoms ~f:(fun (q, _, t) -> (q, t)), phi)
    | _ -> `Other

(** [x = u], argument by argument *)
let eqs (xs : sort_env_list) (us : Term.t list) =
  List.map2_exn (Term.of_sort_env xs) us ~f:Formula.eq

(** [counter_depth facts steps] reads a depth off an unknown's own clauses: the
    number of levels after which a counter argument can grow no further.  It is
    [Some (bound - start + 1)] when some [Int] argument position [i] has
    - in every fact, an integer literal at [i], or a variable its guard fixes
      to one by an equation ([start] is the least of them),
    - every step with exactly one body atom, whose argument at [i] is a
      variable [v], whose head has [v + 1] at [i] (as a linear term, or
      [bvadd v 1]), and whose guard (the negated pure part) has a conjunct
      bounding [v] above by a literal, [v < bound] read through [<], [<=],
      [>], [>=], their unsigned bit-vector forms and negation (a counter of
      sort [(_ BitVec n)] is bounded by the guard and so never wraps);
    the least such depth over the positions, and [None] when there is no step
    or no position qualifies.  Then a derivation of [L] levels gives the
    counter the value [start + L - 1], and no derivation passes [bound], so a
    goal that needs the counter at [bound] is reached at exactly that many
    levels and no fewer.  Only a depth is chosen here, which is never a
    question of soundness: the refutation is sound at every depth. *)
let counter_depth facts steps =
  let rec lin (t : Term.t) =
    match t with
    | Term.Var (x, T_int.SInt, _) -> Some (Map.Poly.singleton x Z.one, Z.zero)
    | Term.FunApp (T_int.Int c, [], _) -> Some (Map.Poly.empty, c)
    | Term.FunApp (T_int.Add, [ t1; t2 ], _) -> comb Z.one t1 Z.one t2
    | Term.FunApp (T_int.Sub, [ t1; t2 ], _) -> comb Z.one t1 Z.minus_one t2
    | Term.FunApp (T_int.Neg, [ t ], _) -> comb Z.zero t Z.minus_one t
    | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int a, [], _); t ], _)
    | Term.FunApp (T_int.Mul, [ t; Term.FunApp (T_int.Int a, [], _) ], _) ->
        comb Z.zero t a t
    | _ -> None
  and comb a1 t1 a2 t2 =
    match (lin t1, lin t2) with
    | Some (m1, c1), Some (m2, c2) ->
        let scale a m = Map.Poly.map m ~f:(Z.mul a) in
        Some
          ( Map.Poly.filter ~f:(fun a -> not (Z.equal a Z.zero))
            @@ Map.Poly.merge (scale a1 m1) (scale a2 m2) ~f:(fun ~key:_ ->
                function `Left a | `Right a -> Some a | `Both (a, b) -> Some (Z.add a b)),
            Z.(add (mul a1 c1) (mul a2 c2)) )
    | _ -> None
  in
  (* the literals of a conjunction, through a negated disjunction *)
  let rec lits pos (phi : Formula.t) =
    match phi with
    | Formula.BinaryOp (Formula.And, p1, p2, _) when pos -> lits pos p1 @ lits pos p2
    | Formula.BinaryOp (Formula.Or, p1, p2, _) when not pos -> lits pos p1 @ lits pos p2
    | Formula.UnaryOp (Formula.Not, p, _) -> lits (not pos) p
    | Formula.Atom (atm, _) -> [ (pos, atm) ]
    | _ -> []
  in
  (* [Some c] when the literal says [v <= c] *)
  let upper v (pos, (atm : Atom.t)) =
    let ge0 =
      match atm with
      | Atom.App (Predicate.Psym psym, [ t1; t2 ], _) -> (
          let dec = Option.map ~f:(fun (m, c) -> (m, Z.pred c)) in
          match psym with
          | T_int.Geq -> comb Z.one t1 Z.minus_one t2
          | T_int.Leq -> comb Z.one t2 Z.minus_one t1
          | T_int.Gt -> dec (comb Z.one t1 Z.minus_one t2)
          | T_int.Lt -> dec (comb Z.one t2 Z.minus_one t1)
          | _ -> None)
      | _ -> None
    in
    let ge0 =
      if pos then ge0
      else Option.map ge0 ~f:(fun (m, c) -> (Map.Poly.map m ~f:Z.neg, Z.(pred (neg c))))
    in
    let is_v = function Term.Var (x, _, _) -> Ident.tvar_equal x v | _ -> false in
    (* an unsigned bit-vector comparison of [v] with a literal *)
    let bv =
      match atm with
      | Atom.App (Predicate.Psym psym, [ t1; Term.FunApp (T_bv.BVNum (_, k), [], _) ], _)
        when is_v t1 -> (
          match (psym, pos) with
          | T_bv.BVLt (_, Some false), true | T_bv.BVGeq (_, Some false), false -> Some (Z.pred k)
          | T_bv.BVLeq (_, Some false), true | T_bv.BVGt (_, Some false), false -> Some k
          | _ -> None)
      | Atom.App (Predicate.Psym psym, [ Term.FunApp (T_bv.BVNum (_, k), [], _); t2 ], _)
        when is_v t2 -> (
          match (psym, pos) with
          | T_bv.BVGt (_, Some false), true | T_bv.BVLeq (_, Some false), false -> Some (Z.pred k)
          | T_bv.BVGeq (_, Some false), true | T_bv.BVLt (_, Some false), false -> Some k
          | _ -> None)
      | _ -> None
    in
    match (ge0, bv) with
    | _, Some c -> Some c
    | Some (m, c), None -> (
        match Map.Poly.to_alist m with
        | [ (x, a) ] when Ident.tvar_equal x v && Z.equal a Z.minus_one -> Some c
        | _ -> None)
    | None, None -> None
  in
  (* [hi] is [v + 1], as an integer or an unsigned bit-vector term *)
  let succ_of v (hi : Term.t) =
    let is_v = function Term.Var (x, _, _) -> Ident.tvar_equal x v | _ -> false in
    match hi with
    | Term.FunApp (T_bv.BVAdd _, [ a; Term.FunApp (T_bv.BVNum (_, one), [], _) ], _)
    | Term.FunApp (T_bv.BVAdd _, [ Term.FunApp (T_bv.BVNum (_, one), [], _); a ], _) ->
        is_v a && Z.equal one Z.one
    | _ -> (
        match lin hi with
        | Some (m, c) when Z.equal c Z.one -> (
            match Map.Poly.to_alist m with
            | [ (x, a) ] -> Ident.tvar_equal x v && Z.equal a Z.one
            | _ -> false)
        | _ -> false)
  in
  match (facts, steps) with
  | [], _ | _, [] -> None
  | (sorts, _, _) :: _, _ ->
      List.filter_mapi sorts ~f:(fun i srt ->
          if not (match srt with T_int.SInt | T_bv.SBV (Some _) -> true | _ -> false) then None
          else
            let starts =
              List.map facts ~f:(fun (_, u, phi) ->
                  let literal = function
                    | Term.FunApp (T_int.Int c, [], _)
                    | Term.FunApp (T_bv.BVNum (_, c), [], _) -> Some c
                    | _ -> None
                  in
                  match List.nth u i with
                  | Some (Term.Var (y, _, _)) ->
                      (* a variable the fact's guard fixes by an equation *)
                      List.find_map (lits true (Evaluator.simplify_neg phi))
                        ~f:(function
                        | true, Atom.App (Predicate.Psym (T_bool.Eq), [ t1; t2 ], _) -> (
                            let is_y = function
                              | Term.Var (z, _, _) -> Ident.tvar_equal y z
                              | _ -> false
                            in
                            if is_y t1 then literal t2
                            else if is_y t2 then literal t1
                            else None)
                        | _ -> None)
                  | Some t -> literal t
                  | None -> None)
              |> Option.all
            in
            let bounds =
              List.map steps ~f:(fun (h, bodies, phi) ->
                  match bodies with
                  | [ a ] -> (
                      match (List.nth a i, List.nth h i) with
                      | Some (Term.Var (v, _, _)), Some hi when succ_of v hi ->
                          List.filter_map
                            (lits true (Evaluator.simplify_neg phi))
                            ~f:(upper v)
                          |> List.min_elt ~compare:Z.compare
                      | _ -> None)
                  | _ -> None)
              |> Option.all
            in
            match (starts, bounds) with
            | Some (s :: ss), Some (b :: bs) ->
                let start = List.fold ss ~init:s ~f:Z.min in
                let last = List.fold bs ~init:b ~f:Z.max in
                (* [v <= last] before the step, so the counter reaches
                   [last + 1] at most, at level [last + 1 - start + 1] *)
                let d = Z.(add (sub last start) (of_int 2)) in
                if Z.(gt d zero) && Z.fits_int d then Some (Z.to_int d) else None
            | _ -> None)
      |> List.min_elt ~compare:Int.compare

(** The levels [L_1 .. L_depth] of the unfolding of every unknown with at
    least one fact, as [(params, levels, depth)] with [levels] shallowest
    first; [max_copies] bounds the number of copies of the facts a level may
    hold, and the levels stop below [depth] when the next one would exceed it.
    With [max_size = Some m], an unknown one of whose levels has more than [m]
    nodes ([size_up_to]) gets no unfolding at all, its building stopped at
    that level: a resolvent made from it would be larger still, and is not
    asked about (see [refute]); with [keep_fitting] it keeps instead the levels
    below that one, when there are any, and [depth] is the deepest of them.
    Every level is sound to resolve with, since each one implies the unknown
    in every solution of its facts and steps (the induction of the head
    comment), so keeping fewer levels only loses refutations that need a
    deeper one.  Each comes with the depth it was unfolded to: [depth], or
    with [counter_cap = Some c] the deeper [counter_depth] of the unknown's
    clauses, at most [c], with [max_size] scaled by the same factor. *)
let levels_with_depth ?(print = fun _ -> ()) ?max_size ?counter_cap
    ?(solve_linear = false) ?(keep_fitting = false) ~linear ~depth ~max_copies
    unknowns (clauses : ClauseOld.t list) =
  let classified =
    List.map clauses ~f:(fun c -> classify unknowns (ClauseOld.refresh_tvar c))
  in
  let facts =
    List.filter_map classified ~f:(function
      | `Fact (p, sorts, u, phi) -> Some (p, (sorts, u, phi))
      | _ -> None)
    |> Map.Poly.of_alist_multi
  in
  let steps =
    List.filter_map classified ~f:(function
      | `Step (p, h, bodies, phi) -> Some (p, (h, bodies, phi))
      | _ -> None)
    |> Map.Poly.of_alist_multi
  in
  let exception Too_large of int * Formula.t list in
  Map.Poly.filter_mapi facts ~f:(fun ~key:p ~data:fs ->
      let sorts = fst3 (List.hd_exn fs) in
      let xs = mk_fresh_sort_env_list sorts in
      let level1 =
        Formula.or_of
        @@ List.map fs ~f:(fun (_, u, phi) ->
            close_exists ~solve_linear xs (Evaluator.simplify_neg phi :: eqs xs u) [])
      in
      let steps = Option.value ~default:[] (Map.Poly.find steps p) in
      (* with [counter_cap], the depth read off a counter argument, when it is
         deeper than [depth], up to the cap; the size bound grows with it,
         since each level of a linear unfolding adds one copy *)
      let depth, max_size =
        match counter_cap with
        | None -> (depth, max_size)
        | Some cap -> (
            match counter_depth fs steps with
            | Some d when d > depth ->
                let d = Int.min d cap in
                print
                @@ lazy
                     (sprintf "[unfold-refute] %s: counter depth %d"
                        (Ident.name_of_pvar p) d);
                ( d,
                  Option.map max_size ~f:(fun m ->
                      m * ((d + depth - 1) / Int.max 1 depth)) )
            | _ -> (depth, max_size))
      in
      print
      @@ lazy
           (sprintf "[unfold-refute] %s: %d fact(s), %d step(s)"
              (Ident.name_of_pvar p) (List.length fs) (List.length steps));
      let copies_per_level =
        List.sum
          (module Int)
          steps
          ~f:(fun (_, bodies, _) -> if linear then 1 else List.length bodies)
      in
      let at (l : Formula.t) (ts : Term.t list) =
        (* with [solve_linear] the arguments are integer terms over the
           parameters, and the substitution is normalised so that a chain of
           [x := x - 1] stays as small as its last step *)
        (if solve_linear then BoundHoist.norm_formula else Fn.id)
        @@ Formula.subst
          (Map.Poly.of_alist_exn
          @@ List.map2_exn (List.map xs ~f:fst) ts ~f:(fun x t -> (x, t)))
          l
      in
      (* [acc]: the levels below [l], deepest first *)
      let rec go i copies acc l =
        if exceeds max_size l then raise (Too_large (i, acc));
        let acc = l :: acc in
        let next_copies = 1 + (copies_per_level * copies) in
        if i >= depth || List.is_empty steps || next_copies > max_copies then
          acc
        else
          let l' =
            Formula.or_of
            @@ level1
               :: List.map steps ~f:(fun (h, bodies, phi) ->
                   (* each level renames the step's variables, so that no
                      binder of a lower level is captured *)
                   let ren =
                     Map.Poly.of_alist_exn
                     @@ List.map
                          (Set.to_list
                          @@ Set.Poly.union_list
                               (Formula.tvs_of phi
                               :: List.map (h :: bodies)
                                    ~f:
                                      (Set.Poly.union_list
                                     <<< List.map ~f:Term.tvs_of)))
                          ~f:(fun x -> (x, Ident.mk_fresh_tvar ()))
                   in
                   let h = List.map h ~f:(Term.rename ren) in
                   let bodies =
                     List.map bodies ~f:(List.map ~f:(Term.rename ren))
                   in
                   let phi = Formula.rename ren phi in
                   close_exists ~solve_linear
                     ~l:(fun j ts ->
                       if linear && j > 0 then at level1 ts else at l ts)
                     xs
                     (Evaluator.simplify_neg phi :: eqs xs h)
                     bodies)
          in
          go (i + 1) next_copies acc l'
      in
      match go 1 1 [] level1 with
      | acc -> Some (xs, List.rev acc, depth)
      | exception Too_large (i, acc) ->
          if keep_fitting && not (List.is_empty acc) then (
            print
            @@ lazy
                 (sprintf
                    "[unfold-refute] %s: level %d is larger than the size \
                     bound; levels 1 to %d kept"
                    (Ident.name_of_pvar p) i (i - 1));
            Some (xs, List.rev acc, i - 1))
          else (
            print
            @@ lazy
                 (sprintf
                    "[unfold-refute] %s: level %d is larger than the size \
                     bound; no unfolding"
                    (Ident.name_of_pvar p) i);
            None))

(** The unfoldings [L_depth] of every unknown with at least one fact, as
    [(params, formula, depth)]: [levels_with_depth]'s deepest level.  Without
    [keep_fitting] an unknown one of whose levels is over [max_size] gets
    none. *)
let unfoldings_with_depth ?print ?max_size ?counter_cap ?solve_linear ~linear
    ~depth ~max_copies unknowns clauses =
  levels_with_depth ?print ?max_size ?counter_cap ?solve_linear ~linear ~depth
    ~max_copies unknowns clauses
  |> Map.Poly.map ~f:(fun (xs, levels, d) -> (xs, List.last_exn levels, d))

(** [unfoldings_with_depth] without the depth each unknown was unfolded to *)
let unfoldings ?print ?max_size ?counter_cap ?solve_linear ~linear ~depth
    ~max_copies unknowns clauses =
  Map.Poly.map ~f:(fun (xs, l, _) -> (xs, l))
  @@ unfoldings_with_depth ?print ?max_size ?counter_cap ?solve_linear ~linear
       ~depth ~max_copies unknowns clauses

(** The resolvents of the goal clauses of [clauses] against [unfoldings], one
    unknown-free formula per goal whose unknowns all have one, each read as
    valid when it holds for every value of its free variables. *)
let resolvents unfoldings unknowns (clauses : ClauseOld.t list) =
  List.filter_map clauses ~f:(fun c ->
      match classify unknowns c with
      | `Goal (atoms, phi) ->
          List.map atoms ~f:(fun (q, ts) ->
              Option.map (Map.Poly.find unfoldings q) ~f:(fun (xs, l) ->
                  Formula.mk_neg
                  @@ Formula.subst
                       (Map.Poly.of_alist_exn
                       @@ List.map2_exn (List.map xs ~f:fst) ts ~f:(fun x t ->
                           (x, t)))
                       l))
          |> Option.all
          |> Option.map ~f:(fun negs -> Formula.or_of (phi :: negs))
      | _ -> None)

(** the first [(i, formula, model)] for which [ask] answers [`Invalid model]
    about the [i]-th resolvent, asking nothing once [expired ()] and nothing
    about a resolvent of more than [max_size] nodes *)
let refute ?(print = fun _ -> ()) ?max_size ?counter_cap ?solve_linear ~linear
    ~depth ~max_copies ~expired ~ask unknowns clauses =
  let unf =
    unfoldings_with_depth ~print ?max_size ?counter_cap ?solve_linear ~linear
      ~depth ~max_copies unknowns clauses
  in
  (* a resolvent over an unknown whose depth a counter raised may be larger
     by the same factor *)
  let max_size =
    match counter_cap with
    | None -> max_size
    | Some _ ->
        let deepest =
          Map.Poly.fold unf ~init:depth ~f:(fun ~key:_ ~data:(_, _, d) acc ->
              Int.max acc d)
        in
        Option.map max_size ~f:(fun m ->
            m * ((deepest + depth - 1) / Int.max 1 depth))
  in
  let unf = Map.Poly.map unf ~f:(fun (xs, l, _) -> (xs, l)) in
  if Map.Poly.is_empty unf then (0, None)
  else
    let rs = resolvents unf unknowns clauses in
    ( List.length rs,
      List.find_mapi rs ~f:(fun i phi ->
          if expired () then None
          else if exceeds max_size phi then (
            print
            @@ lazy
                 (sprintf
                    "[unfold-refute] resolvent %d: larger than the size \
                     bound; not asked"
                    i);
            None)
          else (
            print
            @@ lazy
                 (sprintf "[unfold-refute] resolvent %d: %s" i
                    (Formula.str_of phi));
            let started = Common.Clock.now_s () in
            let res = ask phi in
            print
            @@ lazy
                 (sprintf
                    "[unfold-refute] resolvent %d (%d chars): %s in %.2f s" i
                    (String.length (Formula.str_of phi))
                    (match res with
                    | `Valid -> "valid"
                    | `Invalid _ -> "invalid"
                    | _ -> "undecided")
                    (Common.Clock.now_s () -. started));
            match res with `Invalid model -> Some (i, phi, model) | _ -> None))
    )

(** [refute]'s search over every level that fits instead of the deepest one:
    each unknown keeps the levels below the first one over [max_size]
    ([levels_with_depth ~keep_fitting:true]), and each goal is asked once, at
    the deepest level [k] (the same for all its atoms, an unknown with fewer
    levels taking its deepest) whose resolvent is within [max_size]; a goal
    with no such level is not asked.  The first [(i, formula, model)] for
    which [ask] answers [`Invalid model] about the [i]-th goal, asking nothing
    once [expired ()].

    Why.  [refute] gives an unknown no unfolding once one of its levels is too
    large, and asks every goal at the one depth reached; a goal with several
    atoms is then as large as several copies of that level.  A refutation that
    needs only a few levels is lost when a deeper level is over the bound, or
    when the goal at the depth reached is.  The levels are monotone ([L_i]
    implies [L_(i+1)], each level containing the first and every step applied
    to the level below), so the deepest level that fits is the strongest
    question that can be asked of that goal.  Soundness is [refute]'s: every
    level implies the unknown in every solution of the facts and steps.

    On a Thrust loop over a mutable slice the step that resolves the loop's
    prophecy has two body atoms, of which the refutation needs the second one
    unfolded twice: the linear form, which puts the facts at a second atom,
    never refutes it, and the doubling form at depth 12 is over the size bound
    from level 4, while the doubling form at depth 3 refutes it in about a
    second. *)
let refute_fitting ?(print = fun _ -> ()) ?max_size ?solve_linear ~linear
    ~depth ~max_copies ~expired ~ask unknowns clauses =
  let levels =
    levels_with_depth ~print ?max_size ?solve_linear ~keep_fitting:true
      ~linear ~depth ~max_copies unknowns clauses
  in
  if Map.Poly.is_empty levels then (0, None)
  else
    let deepest =
      Map.Poly.fold levels ~init:0 ~f:(fun ~key:_ ~data:(_, ls, _) acc ->
          Int.max acc (List.length ls))
    in
    (* the unfoldings at level [k]: an unknown with fewer levels at its
       deepest *)
    let at_level k =
      Map.Poly.map levels ~f:(fun (xs, ls, _) ->
          (xs, List.nth_exn ls (Int.min k (List.length ls) - 1)))
    in
    let goals =
      List.filter_map clauses ~f:(fun c ->
          match classify unknowns c with
          | `Goal (atoms, _)
            when List.for_all atoms ~f:(fun (q, _) -> Map.Poly.mem levels q) ->
              Some c
          | _ -> None)
    in
    (* the resolvent of [c] at the deepest level that fits, with that level *)
    let fitting c =
      let rec down k =
        if k < 1 then None
        else
          match resolvents (at_level k) unknowns [ c ] with
          | [ phi ] when not (exceeds max_size phi) -> Some (k, phi)
          | _ -> down (k - 1)
      in
      down deepest
    in
    ( List.length goals,
      List.find_mapi goals ~f:(fun i c ->
          if expired () then None
          else
            match fitting c with
            | None ->
                print
                @@ lazy
                     (sprintf
                        "[unfold-refute] goal %d: larger than the size bound \
                         at every level; not asked"
                        i);
                None
            | Some (k, phi) -> (
                let started = Common.Clock.now_s () in
                let res = ask phi in
                print
                @@ lazy
                     (sprintf
                        "[unfold-refute] goal %d at level %d (%d nodes): %s in \
                         %.2f s"
                        i k
                        (size_up_to Int.max_value phi)
                        (match res with
                        | `Valid -> "valid"
                        | `Invalid _ -> "invalid"
                        | _ -> "undecided")
                        (Common.Clock.now_s () -. started));
                match res with
                | `Invalid model -> Some (i, phi, model)
                | _ -> None)) )

(** The negation of [phi] with each [(s, se, k)] of [pins] fixed to a literal of
    [k] fresh units: [s] is substituted by the literal, reads over it are split
    ([Evaluator.rewrite_seq_read_over_concat]), and [s = literal] is kept as a
    conjunct. A strengthening of the negation (every sequence of length [k] is
    such a literal for some elements, and the substitution is exact under the
    equation), so a model of it is a countermodel of [phi]. *)
let literal_pinned_negation pins phi =
  let defs =
    List.map pins ~f:(fun (s, se, k) -> (s, se, SeqPin.literal_of se k))
  in
  let sub =
    Map.Poly.of_alist_exn @@ List.map defs ~f:(fun (s, _, t) -> (s, t))
  in
  Formula.and_of
  @@ (Formula.nnf_of @@ Formula.negate
     @@ Evaluator.rewrite_seq_read_over_concat (Formula.subst sub phi))
     :: List.map defs ~f:(fun (s, se, t) ->
         Formula.eq (Term.mk_var s (T_seq.SSeq se)) t)

(** the form of a resolvent [ask] asks about: negation normal form, positive
    universals made free, sequence reads split (see [ask]) *)
let prepare phi =
  Evaluator.split_seq_reads_for_validity
  @@ SeqInstantiation.skolemize_positive_universals @@ Formula.nnf_of phi

(** The question the preprocessor asks of a resolvent [phi], at [timeout] ms per
    solver call; only [`Invalid] is read from the answer. [phi] is first given
    its positive universals as free variables
    ([SeqInstantiation.skolemize_positive_universals]): exact for validity, and
    a countermodel of that form falsifies [phi] in the same model, since each
    universal it replaced occurs under conjunctions and disjunctions only; every
    existential of an unfolding becomes such a universal once the resolvent is
    in negation normal form.  Then:
    - where the resolvent has free sequences, their lengths guessed from a
      model of the quantifier-free relaxation of the negation
      ([SeqPin.length_guess_query]: every model of the negation satisfies it,
      and its model is read for lengths only), and the negation with each
      sequence fixed to a literal of that length asked
      ([literal_pinned_negation]), whose model is a countermodel because the
      pinned query strengthens the negation;
    - the validity question itself only where there is no free sequence or
      the relaxation's model gives none of them a length: where the
      relaxation was answered, the question it relaxes is at least as hard.
    The unfolding fixes the derivation's shape but not the lengths of the
    sequences it builds, which the sequence solver otherwise finds only by
    search: on the input this was written for, the relaxation was answered in
    4 s and the pinned negation in 2.6 s, while the question itself was not
    answered in 10 s; on its satisfiable twin the question itself spent its
    10 s for nothing.  An unsatisfiable relaxation means a valid resolvent and
    is reported as undecided, since nothing here reads [`Valid].  [timeout]
    is the Z3 budget of each call, [None] for none ([ask_forked] asks with
    none).

    [step_ms]: when given, the question that decides -- the validity question
    itself or the pinned negation, not the relaxation -- is asked in a forked
    copy of its own killed after [step_ms] ms, and a countermodel it finds is
    reported as [`Invalid []] (no model comes back from a copy).  Why: on
    inputs the unfolding cannot refute, that question is where the time goes.
    On four Thrust inputs with one step clause (depth 12, resolvents of
    17,000 to 29,000 characters) one such question per input ran until the
    pass's 60 s budget killed it -- natively where the resolvent has no free
    sequence, pinned where it has -- while each relaxation was answered in
    under 0.4 s; on the one Thrust input the unfolding refutes, the
    relaxation took 7 s and the pinned negation 2.9 s.

    [guess_ms]: when given, the relaxation is asked in a forked copy of its
    own killed after [guess_ms] ms, and a relaxation killed there is read as
    one that gave no lengths (undecided).  The relaxation is quantifier-free
    but over sequences, and it is not always the cheap question: on a
    satisfiable Thrust input (one step clause, a resolvent of 10,000 nodes
    whose relaxation has 3,000) it did not return before the pass's 60 s kill,
    which was the whole cost of the pass.  Only refutations whose relaxation
    takes longer than [guess_ms] are lost.  [print] reports the stage reached
    and its time, flushed, so that a copy killed later still shows where its
    time went. *)
let ask ?(print = fun _ -> ()) ?step_ms ?guess_ms ?(hoist = false) ~timeout ~id
    phi =
  let t0 = Common.Clock.now_s () in
  (* the stage reached and its time since the question started, flushed, so
     that a copy killed later still shows where its time went *)
  let stage what =
    print
    @@ lazy
         (sprintf "[unfold-refute] question: %s at %.2f s" what
            (Common.Clock.now_s () -. t0));
    Out_channel.flush stdout;
    Out_channel.flush stderr
  in
  let phi = prepare phi in
  (* with [hoist], the integer bounds the negation implies however deep in
     it they sit are made top-level conjuncts of it ([BoundHoist.hoist_valid]:
     the question is unchanged), where the solver's preprocessing and the
     bounded-word rewrite read them *)
  let phi =
    if not hoist then phi
    else
      let phi, atoms = BoundHoist.hoist_valid phi in
      stage (sprintf "hoisted %d bound(s)" (List.length atoms));
      phi
  in
  stage (sprintf "prepared (%d nodes)" (Formula.ast_size phi));
  let fenv = get_fenv () in
  (* a question that applies a recursive function under a quantifier is not
     asked: the solver boundary reads its [sat] as [`Unknown]
     ([Z3interface.check_sat]), so no [`Invalid] can come of it, and its
     budget is better left to the next resolvent *)
  if Z3Smt.Z3interface.recursive_function_under_binder fenv phi then (
    stage "a recursive function under a quantifier: not asked";
    `Unknown "a recursive function under a quantifier")
  else
  (* with [step_ms], the question that decides (the validity question itself
     or the pinned negation) is asked in a forked copy of its own, killed
     after [step_ms]; only that it found a countermodel comes back, as
     [`Invalid []] *)
  let within (f : unit -> [> `Invalid of model ]) =
    match step_ms with
    | None -> f ()
    | Some ms -> (
        match
          ForkedQuery.run ~ms (fun () ->
              match f () with `Invalid _ -> true | _ -> false)
        with
        | Some true -> `Invalid []
        | Some false | None -> `Unknown "undecided within the step's budget")
  in
  let sat psi =
    match
      Z3Smt.Z3interface.check_sat ~timeout ~fresh_solver:true ~id
        fenv [ psi ]
    with
    | `Sat model -> Some model
    | `Unsat ->
        stage "the solver answered unsat";
        None
    | `Timeout ->
        stage "the solver ran out of its budget";
        None
    | `Unknown reason ->
        stage (sprintf "the solver answered unknown (%s)" reason);
        None
  in
  let native () =
    Z3Smt.Z3interface.check_valid ~timeout ~fresh_solver:false
      ~id fenv phi
  in
  let pinned pins () =
    match sat (literal_pinned_negation pins phi) with
    | Some model -> `Invalid model
    | None -> `Unknown "no countermodel at the guessed lengths"
  in
  match SeqPin.length_guess_query [ phi ] with
  | None ->
      stage "no free sequence, asking the question itself";
      within native
  | Some (q, named) -> (
      stage (sprintf "relaxation built (%d nodes)" (Formula.ast_size q));
      (* the lengths the relaxation's model gives, as [(s, se, k)]; with
         [guess_ms], asked in a forked copy killed after [guess_ms] ms, which
         sends back only the position in [named] and the length of each
         (integers survive the trip, a model does not) *)
      let lengths =
        match guess_ms with
        | None ->
            Option.map (sat q) ~f:(SeqPin.lengths_of_model named)
        | Some ms -> (
            let named_idx = List.mapi named ~f:(fun i (s, se, n) -> (i, (s, se, n))) in
            match
              ForkedQuery.run ~ms (fun () ->
                  match sat q with
                  | None -> None
                  | Some model ->
                      Some
                        (List.filter_map named_idx ~f:(fun (i, (s, se, n)) ->
                             match
                               SeqPin.lengths_of_model [ (s, se, n) ] model
                             with
                             | [ (_, _, k) ] -> Some (i, k)
                             | _ -> None)))
            with
            | Some (Some ks) ->
                Some
                  (List.map ks ~f:(fun (i, k) ->
                       let s, se, _ = List.nth_exn named i in
                       (s, se, k)))
            | Some None -> None
            | None ->
                stage "relaxation killed at its budget";
                None)
      in
      match lengths with
      | None ->
          stage "relaxation answered without a model";
          `Unknown "the relaxation gave no lengths"
      | Some lengths -> (
          stage "relaxation answered";
          match lengths with
          | [] -> within native
          | pins -> within (pinned pins)))

(** [ask_forked ~ms ~id phi] is [ask ~timeout:None ~id phi] asked in a forked
    copy killed after [ms] milliseconds ([ForkedQuery.run]): [`Invalid []] when
    the copy found a countermodel, and [`Timeout] or [`Unknown _] otherwise
    (killed, died, could not be forked, or any other answer).  The model itself
    is not sent back, since its terms are values of extensible variants that do
    not survive the trip; the caller reads only that the resolvent is invalid.

    Why a process.  Z3's own [timeout] does not bound these questions: on a
    resolvent of an unknown with two step clauses (4,095 copies of the facts at
    depth 12, a 4 MB formula with about 16,000 quantifiers over sequences) one
    call made with a 10 s budget had not returned after 89 s, and the pass's
    own budget is checked only between questions, so the run never left
    preprocessing.  Killing the copy is the one bound that holds.  The copy
    asks with no Z3 timer, the thread serving one not existing in a forked
    process; the kill is the budget.

    Contract: [`Invalid _] only if [ask] answered [`Invalid] in the copy, so a
    caller reading only [`Invalid] loses only refutations [ask] would have
    found after [ms]. *)
let ask_forked ?print ?step_ms ?guess_ms ?hoist ~ms ~id phi =
  match
    ForkedQuery.run ~ms (fun () ->
        match ask ?print ?step_ms ?guess_ms ?hoist ~timeout:None ~id phi with
        | `Invalid _ -> `I
        | `Timeout -> `T
        | `Unknown r -> `K r
        | `Valid -> `K "valid"
        | `Sat _ | `Unsat -> `K "unexpected answer")
  with
  | Some `I -> `Invalid []
  | Some `T | None -> `Timeout
  | Some (`K r) -> `Unknown r

(* A census of where forward evaluation could replace the solver, decided
   nothing by: which unfoldings, and which goal resolvents, are built from
   unknowns whose least model up to the depth is reached by evaluation.  The
   unfoldings are built as the preprocessor's pass builds them under its
   default settings (depth 12, counter depth up to 128, the linear one-point
   rule, linear unfolding, 20000 nodes, 4096 copies).  An unfolding is
   BINDER-FREE when it has no quantifier after the one-point rule; it is a set
   of GROUND TUPLES when moreover every disjunct fixes every parameter by an
   equation to a closed term; the unknown is DATALOG when its facts alone are
   ground tuples and every step computes its head and guard from its body's
   values ([step_evaluable]).  [report] prints one [UNF] line per unknown with
   an unfolding and one [GROUND] line, through [out]. *)
module GroundCensus = struct
  let binder_free phi = Set.is_empty (Formula.quantified_sort_env_of phi)

  (* every disjunct of [l] (flattened) fixes every parameter of [xs] by an
     equation [x = t] with [t] closed: [l] is a finite set of ground tuples, each
     possibly under a guard *)
  let ground_tuples xs l =
    binder_free l
    && List.for_all (Formula.disjuncts_list_of l) ~f:(fun d ->
           let eqs =
             List.filter_map (Formula.conjuncts_list_of d) ~f:(fun c ->
                 if Formula.is_eq c then
                   let t1, t2, _ = Formula.let_eq c in
                   let closed t = Set.is_empty (Term.tvs_of t) in
                   match (t1, t2) with
                   | Term.Var (x, _, _), t when closed t -> Some x
                   | t, Term.Var (x, _, _) when closed t -> Some x
                   | _ -> None
                 else None)
           in
           List.for_all xs ~f:(fun (x, _) -> List.mem eqs x ~equal:Ident.tvar_equal))

  (* a step [phi \/ P(h) \/ ~P(b_1) \/ ...] whose head and guard are computed
     from its body's values: every variable of [h] and of [not phi] is a
     variable argument of a body atom, or is defined by an equation [y = t] of
     [not phi] over such variables (closed under that rule).  Forward
     evaluation then derives the head tuple from body tuples by substitution
     and evaluation, with no solver, whatever binders the symbolic unfolding
     keeps for the step's own variables *)
  let step_evaluable (h, bodies, phi) =
    let g = Evaluator.simplify_neg phi in
    let start =
      Set.Poly.of_list
      @@ List.concat_map bodies ~f:(List.filter_map ~f:(function
           | Term.Var (x, _, _) -> Some x
           | _ -> None))
    in
    let defs =
      List.filter_map (Formula.conjuncts_list_of g) ~f:(fun c ->
          if Formula.is_eq c then
            let t1, t2, _ = Formula.let_eq c in
            match (t1, t2) with
            | Term.Var (y, _, _), t | t, Term.Var (y, _, _) -> Some (y, Term.tvs_of t)
            | _ -> None
          else None)
    in
    let rec close v =
      let v' =
        List.fold defs ~init:v ~f:(fun v (y, ts) ->
            if Set.is_subset ts ~of_:v then Set.add v y else v)
      in
      if Set.length v' = Set.length v then v else close v'
    in
    let v = close start in
    Set.is_subset
      (Set.Poly.union_list
         (Formula.tvs_of g :: List.map (h :: bodies) ~f:(fun ts ->
              Set.Poly.union_list (List.map ts ~f:Term.tvs_of))))
      ~of_:v

  let report ~out ~label unknowns clauses =
    let started = Core_unix.gettimeofday () in
    let build ~depth ~counter_cap =
      unfoldings_with_depth ~max_size:20000 ?counter_cap ~solve_linear:true
        ~linear:true ~depth ~max_copies:4096 unknowns clauses
    in
    let unf = build ~depth:12 ~counter_cap:(Some 128) in
    let first = build ~depth:1 ~counter_cap:None in
    let build_s = Core_unix.gettimeofday () -. started in
    (* Datalog-evaluable: the facts alone are ground tuples and every step of
       the unknown is [step_evaluable] *)
    let steps_of =
      List.filter_map clauses ~f:(fun c ->
          match classify unknowns (ClauseOld.refresh_tvar c) with
          | `Step (p, h, bodies, phi) -> Some (p, (h, bodies, phi))
          | _ -> None)
      |> Map.Poly.of_alist_multi
    in
    let dl =
      Map.Poly.mapi unf ~f:(fun ~key ~data:_ ->
          (match Map.Poly.find first key with
          | Some (xs, l, _) -> ground_tuples xs l
          | None -> false)
          && List.for_all
               (Option.value ~default:[] (Map.Poly.find steps_of key))
               ~f:step_evaluable)
    in
    let bf = Map.Poly.map unf ~f:(fun (_, l, _) -> binder_free l) in
    let gt = Map.Poly.map unf ~f:(fun (xs, l, _) -> ground_tuples xs l) in
    let fbf =
      Map.Poly.mapi unf ~f:(fun ~key ~data:_ ->
          match Map.Poly.find first key with
          | Some (_, l, _) -> binder_free l
          | None -> false)
    in
    Map.Poly.iteri unf ~f:(fun ~key ~data:(_, l, d) ->
        out @@ sprintf
          "UNF %s depth=%d facts_binder_free=%b binder_free=%b ground_tuples=%b \
           datalog=%b nodes=%d\n"
          (Ident.name_of_pvar key) d (Map.Poly.find_exn fbf key)
          (Map.Poly.find_exn bf key) (Map.Poly.find_exn gt key)
          (Map.Poly.find_exn dl key)
          (size_up_to 1_000_000 l));
    let goals =
      List.filter_map clauses ~f:(fun c ->
          match classify unknowns c with
          | `Goal (atoms, _) ->
              if List.for_all atoms ~f:(fun (q, _) -> Map.Poly.mem unf q) then
                Some
                  ( List.for_all atoms ~f:(fun (q, _) -> Map.Poly.find_exn bf q),
                    List.for_all atoms ~f:(fun (q, _) -> Map.Poly.find_exn gt q),
                    List.for_all atoms ~f:(fun (q, _) -> Map.Poly.find_exn dl q) )
              else None
          | _ -> None)
    in
    let rs =
      resolvents (Map.Poly.map unf ~f:(fun (xs, l, _) -> (xs, l))) unknowns clauses
    in
    let count f m = Map.Poly.count m ~f in
    out @@ sprintf
      "GROUND %s unfoldings=%d binder_free=%d facts_binder_free=%d \
       ground_tuples=%d datalog=%d resolvents=%d over_binder_free=%d \
       over_ground_tuples=%d over_datalog=%d binder_free_resolvents=%d \
       build_s=%.3f\n"
      label (Map.Poly.length unf) (count Fn.id bf) (count Fn.id fbf)
      (count Fn.id gt) (count Fn.id dl) (List.length rs)
      (List.count goals ~f:fst3) (List.count goals ~f:snd3)
      (List.count goals ~f:trd3)
      (List.count rs ~f:binder_free)
      build_s
end
