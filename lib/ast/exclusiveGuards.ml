(* Factoring a disjunction whose disjuncts carry mutually exclusive guards.

   The clausal form of a disjunction is the product of its operands' clause
   sets ([Formula.cnf_of]), and over the same atoms read as independent
   propositions no clausal form is smaller: [(g1 /\ y1) \/ ... \/ (gk /\ yk)]
   needs [2^k] clauses when every [gi] and [yi] is an unrelated atom.  The
   guards of a transition system's branches are not unrelated, though: where
   two branches test a condition and its negation, at most one of them holds
   at any valuation, and then

     (P1 /\ Y1) \/ ... \/ (Pk /\ Yk)
       <=>  (P1 \/ ... \/ Pk) /\ (not P1 \/ Y1) /\ ... /\ (not Pk \/ Yk)

   whose clausal form has [1 + |Y1| + ... + |Yk|] clauses instead of
   [(1 + |Y1|) * ... * (1 + |Yk|)].  This is the "if-then-else" reading of a
   case split; the dual of a path-composed transition system (each body the
   disjunction over a location's outgoing transitions of [guard /\ ...],
   nested once per branching location) is made of such disjunctions, and its
   distributed clausal form ran to about 2 x 10^10 clauses on a 425-location
   integer transition system.

   [factor ~unknowns phi] applies that equivalence bottom up to every
   disjunction of [phi] that mentions an unknown, to each group of at least
   two of its disjuncts whose guards are pairwise exclusive, then factors the
   guard out of disjuncts with identical guards (below), and does nothing
   else.

   Contract.  Input: [phi] in negation normal form, [unknowns] the names of
   the predicate (and function) unknowns, as [Formula.cnf_of] takes them.
   Output: [None] when no disjunction has such a group (the caller keeps
   [phi] as it is), otherwise [Some phi'] with [phi'] in negation normal form,
   over the same atoms and the same free variables, and equivalent to [phi]
   at every valuation of its free variables, in every model of the background
   theory and under every interpretation of the unknowns.  No fresh symbol is
   introduced, so a solution of a problem containing [phi'] is a solution of
   the problem containing [phi] and conversely, kinds included.  The
   predicted clausal form ([DefinitionalCnf.predicted_cnf_clauses]) of every
   rewritten disjunction is strictly smaller than before.

   Which disjuncts are guarded.  A disjunct is a conjunction (flattened) some
   of whose conjuncts mention no unknown and some of which do; its guard [P]
   is the conjunction of the former, its rest [Y] the conjunction of the
   latter.  Disjuncts of any other shape stay outside every group.

   When two guards are exclusive.  [exclusive] decides it syntactically:
   splitting disjunctions on either side, then looking for one conjunct that
   excludes the other side, down to two literals of which one is, after
   [Evaluator.simplify] and [Normalizer.normalize], the same formula as the
   negation of the other put through the same two functions (the key of the
   eliminator's syntactic tautology test), or a literal whose key is [false].
   Both functions preserve meaning in every model, so then the conjunction of
   the two guards is false at every valuation, whatever the interpretation of
   any interpretation-dependent term (division by zero and the like) is.  Two
   literals are also exclusive when both bound one linear form over integer
   variables to disjoint sets of values ([linear_exclusive]: [x = 0] against
   [x < 0] or [x >= 1]), integer arithmetic over variables and literals only,
   which reads the same in every model.  The test is sufficient only: an
   exclusion it does not see (one that needs two literals of one side, or one
   past its step bound) leaves those disjuncts unfactored, which costs size,
   never meaning.

   Why the equivalence holds.  Let the guards of a group be pairwise
   exclusive.  (=>) If [Pi /\ Yi] holds then [Pi] does, so the first
   conjunct does; [not Pi \/ Yi] holds by [Yi]; and for [j <> i], [Pj] is
   false by exclusion, so [not Pj \/ Yj] holds.  (<=) The first conjunct
   gives some [Pi], and [not Pi \/ Yi] then gives [Yi].  Inside a larger
   disjunction [R \/ G] the group [G] is replaced by an equivalent formula,
   and a disjunction of equivalent formulas is equivalent; bottom up, every
   replacement is of a subformula by an equivalent one.

   Identical guards.  Disjuncts left in no group whose guards are the same
   formula (structurally) are factored by distributivity:
   [(P /\ Y1) \/ ... \/ (P /\ Ym)] becomes [P /\ (Y1 \/ ... \/ Ym)], a
   propositional identity, with [1 + |Y1| * ... * |Ym|] clauses instead of
   [(1 + |Y1|) * ... * (1 + |Ym|)].  A transition system's nondeterministic
   branches (equal guards, different updates) are of this shape; their
   remaining product is over distinct witness atoms and no clausal form over
   these atoms avoids it.

   Grouping.  The candidates of one disjunction are taken in decreasing order
   of their rest's predicted clause count, and each is added to the first
   group all of whose members it excludes (greedy; a candidate excluding none
   starts a group).  Groups of one stay as they were.  The order is a choice
   of which equivalent form is built, not of its meaning. *)

open Core
open Common.Ext
open LogicOld

let rec flat_or phi acc =
  match phi with
  | Formula.BinaryOp (Or, a, b, _) -> flat_or a (flat_or b acc)
  | _ -> phi :: acc

let rec flat_and phi acc =
  match phi with
  | Formula.BinaryOp (And, a, b, _) -> flat_and a (flat_and b acc)
  | _ -> phi :: acc

(* the eliminator's tautology-test key: an atom or a negated atom through the
   simplifier and the normaliser, any other formula as it stands *)
let canon f =
  match f with
  | Formula.Atom _ | Formula.UnaryOp (Not, Formula.Atom _, _) ->
      Normalizer.normalize @@ Evaluator.simplify f
  | f -> f

type guarded = {
  disjunct : Formula.t;
  guard : Formula.t list;
  rest : Formula.t list;
  guard_fml : Formula.t;
  weight : int;
}

(* [linear_bound lit]: for a literal (an atom or its negation) that is a
   comparison of two integer terms built from integer variables and constants
   by [+], [-], unary minus and multiplication by a constant, [Some (u, b)]
   with [u] the linear form over the variables (an association list sorted by
   variable name, its first coefficient positive, no zero coefficient) and [b]
   the set of values of [u] the literal allows: [`Ge c] (u >= c), [`Le c],
   [`Eq c] or [`Ne c]; [None] for any other literal (a term with a division, a
   function application, a non-integer sort, or no variable at all).  The
   reading is integer arithmetic over variables and literals only, so it is
   the same in every model and under every interpretation of the unknowns. *)
let linear_bound lit =
  let rec lin t =
    match t with
    | Term.Var (x, s, _) when Stdlib.( = ) s T_int.SInt ->
        Some (Map.Poly.singleton (Ident.name_of_tvar x) (x, Z.one), Z.zero)
    | Term.FunApp (T_int.Int n, [], _) -> Some (Map.Poly.empty, n)
    | Term.FunApp (T_int.Neg, [ t ], _) ->
        Option.map (lin t) ~f:(fun (m, c) -> (scale Z.minus_one m, Z.neg c))
    | Term.FunApp (T_int.Nop, [ t ], _) -> lin t
    | Term.FunApp (T_int.Add, [ t1; t2 ], _) -> add (lin t1) (lin t2)
    | Term.FunApp (T_int.Sub, [ t1; t2 ], _) ->
        add (lin t1) (Option.map (lin t2) ~f:(fun (m, c) -> (scale Z.minus_one m, Z.neg c)))
    | Term.FunApp (T_int.Mul, [ t1; t2 ], _) -> (
        match (lin t1, lin t2) with
        | Some (m1, c1), Some (m2, c2) when Map.is_empty m1 -> Some (scale c1 m2, Z.(c1 * c2))
        | Some (m1, c1), Some (m2, c2) when Map.is_empty m2 -> Some (scale c2 m1, Z.(c1 * c2))
        | _ -> None)
    | _ -> None
  and scale k m = Map.Poly.map m ~f:(fun (x, c) -> (x, Z.(k * c)))
  and add a b =
    match (a, b) with
    | Some (m1, c1), Some (m2, c2) ->
        Some
          ( Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
              | `Left v | `Right v -> Some v
              | `Both ((x, a), (_, b)) -> Some (x, Z.(a + b))),
            Z.(c1 + c2) )
    | _ -> None
  in
  let atom, negated =
    match lit with
    | Formula.Atom (a, _) -> (Some a, false)
    | Formula.UnaryOp (Not, Formula.Atom (a, _), _) -> (Some a, true)
    | _ -> (None, false)
  in
  match atom with
  | Some (Atom.App (Predicate.Psym psym, [ t1; t2 ], _)) -> (
      let op =
        match psym with
        | T_int.Geq -> Some `Ge
        | T_int.Leq -> Some `Le
        | T_int.Gt -> Some `Gt
        | T_int.Lt -> Some `Lt
        | T_bool.Eq -> Some `Eq
        | T_bool.Neq -> Some `Ne
        | _ -> None
      in
      let op =
        if not negated then op
        else
          Option.map op ~f:(function
            | `Ge -> `Lt
            | `Le -> `Gt
            | `Gt -> `Le
            | `Lt -> `Ge
            | `Eq -> `Ne
            | `Ne -> `Eq)
      in
      match (op, lin t1, lin t2) with
      | Some op, Some (m1, c1), Some (m2, c2) -> (
          (* t1 - t2 op 0, i.e. u + c op 0 with u the variable part *)
          let m =
            Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
              | `Left v -> Some v
              | `Right (x, b) -> Some (x, Z.neg b)
              | `Both ((x, a), (_, b)) -> Some (x, Z.(a - b)))
            |> Map.Poly.filter ~f:(fun (_, c) -> not (Z.equal c Z.zero))
          in
          let c = Z.(c1 - c2) in
          match Map.Poly.min_elt m with
          | None -> None
          | Some (_, (_, lead)) ->
              (* make the first coefficient positive: negating both sides
                 turns u + c op 0 into (-u) - c op' 0 *)
              let flip = Z.lt lead Z.zero in
              let m = if flip then scale Z.minus_one m else m in
              let c = if flip then Z.neg c else c in
              let op =
                if not flip then op
                else
                  match op with
                  | `Ge -> `Le
                  | `Le -> `Ge
                  | `Gt -> `Lt
                  | `Lt -> `Gt
                  | (`Eq | `Ne) as o -> o
              in
              (* u + c op 0  <=>  u op' -c, over the integers *)
              let k = Z.neg c in
              let b =
                match op with
                | `Ge -> `Ge k
                | `Gt -> `Ge Z.(k + one)
                | `Le -> `Le k
                | `Lt -> `Le Z.(k - one)
                | `Eq -> `Eq k
                | `Ne -> `Ne k
              in
              Some
                ( List.map (Map.Poly.to_alist m) ~f:(fun (n, (_, c)) -> (n, c)),
                  b ))
      | _ -> None)
  | _ -> None

(* [linear_exclusive a b]: [true] only when the literals [a] and [b] bound the
   same linear form over integer variables ([linear_bound]) to disjoint sets
   of values, so that [a /\ b] is false at every valuation, in every model and
   under every interpretation.  Sees what the syntactic test does not: an
   equation against a strict or shifted inequality ([u = -1] and [u >= 0]),
   two bounds that do not meet ([u >= 1] and [u <= -1]) -- the three-way
   splits a transition system writes as [x < 0], [x = 0], [x > 0]. *)
let linear_exclusive a b =
  match (linear_bound a, linear_bound b) with
  | Some (u, x), Some (v, y)
    when List.equal (fun (n1, c1) (n2, c2) -> String.equal n1 n2 && Z.equal c1 c2) u v -> (
      match (x, y) with
      | `Ge p, `Le q | `Le q, `Ge p -> Z.gt p q
      | `Ge p, `Eq q | `Eq q, `Ge p -> Z.lt q p
      | `Le p, `Eq q | `Eq q, `Le p -> Z.gt q p
      | `Eq p, `Eq q -> not (Z.equal p q)
      | `Eq p, `Ne q | `Ne q, `Eq p -> Z.equal p q
      | _ -> false)
  | _ -> false

(* [exclusive ~key ~steps a b]: [true] only when [a /\ b] is false at every
   valuation, in every model and under every interpretation.  A disjunction
   on either side is exclusive with the other side when each of its
   disjuncts is; then a conjunction is when one of its conjuncts is; two
   formulas that are neither are when the key of one is the key of the
   negation of the other ([key] the normalised literal, see [canon]).  Each
   rule is sound by itself (a conjunction with a false conjunct is false, a
   disjunction of false disjuncts is false), so the answer is by induction.
   Disjunctions are split first so that each disjunct may be excluded by a
   different conjunct of the other side.  [steps] bounds the calls: past it
   the answer is [false], which leaves two disjuncts unfactored and costs
   clausal-form size, never meaning. *)
let exclusive ~key ~steps a b =
  let budget = ref steps in
  let rec go a b =
    decr budget;
    if !budget < 0 then false
    else
      match (a, b) with
      | Formula.BinaryOp (Or, _, _, _), _ ->
          List.for_all (flat_or a []) ~f:(fun a' -> go a' b)
      | _, Formula.BinaryOp (Or, _, _, _) ->
          List.for_all (flat_or b []) ~f:(fun b' -> go a b')
      | Formula.BinaryOp (And, _, _, _), _ ->
          List.exists (flat_and a []) ~f:(fun a' -> go a' b)
      | _, Formula.BinaryOp (And, _, _, _) ->
          List.exists (flat_and b []) ~f:(fun b' -> go a b')
      | _ ->
          Formula.is_false (key a) || Formula.is_false (key b)
          || Stdlib.( = ) (key a) (key (Formula.nnf_of (Formula.mk_neg b)))
          || Stdlib.( = ) (key b) (key (Formula.nnf_of (Formula.mk_neg a)))
          || linear_exclusive a b
  in
  go a b

(* the bound on [exclusive]'s calls for one pair of guards *)
let exclusive_steps = 100_000

(* the statistics of one call: disjunctions rewritten, disjuncts placed in a
   group, and the predicted clause counts summed over the rewritten
   disjunctions, before and after (each saturating at [2^40]) *)
type stats = {
  mutable rewritten : int;
  mutable grouped : int;
  mutable before : int;
  mutable after : int;
}

let factor_with_stats ~unknowns phi =
  let stats = { rewritten = 0; grouped = 0; before = 0; after = 0 } in
  let cap = 1 lsl 40 in
  let add a b = Int.min cap (a + b) in
  (* the test [Formula.cnf_of] makes, asked of the leaves only: a conjunction
     or a disjunction mentions an unknown iff one of its sides does *)
  let leaf_mentions phi =
    Set.exists (Formula.pvs_of phi) ~f:(fun pvar ->
        Set.mem unknowns (Ident.pvar_to_tvar pvar))
    || not (Set.are_disjoint (Formula.tvs_of phi) unknowns)
  in
  let count = DefinitionalCnf.predicted_cnf_clauses unknowns in
  let changed = ref false in
  let key_memo = Common.Ext.Hashtbl.PolyDeep.create () in
  let key f =
    match Hashtbl.find key_memo f with
    | Some k -> k
    | None ->
        let k = canon f in
        Hashtbl.set key_memo ~key:f ~data:k;
        k
  in
  (* [go phi] is [(phi', m)]: [phi'] the rewritten [phi] (physically [phi]
     where nothing below changed) and [m] whether [phi] mentions an unknown *)
  let rec go phi =
    match phi with
    | Formula.BinaryOp (And, a, b, info) ->
        let a', ma = go a and b', mb = go b in
        if phys_equal a a' && phys_equal b b' then (phi, ma || mb)
        else (Formula.mk_and ~info a' b', ma || mb)
    | Formula.BinaryOp (Or, _, _, _) ->
        (* each disjunct: [`G] a guarded conjunction, [`O] anything else *)
        let ds =
          List.map (flat_or phi []) ~f:(fun d ->
              match d with
              | Formula.BinaryOp (And, _, _, _) ->
                  let cs = List.map (flat_and d []) ~f:go in
                  let m = List.exists cs ~f:snd in
                  let guard, rest = List.partition_tf cs ~f:(Fn.non snd) in
                  let guard = List.map guard ~f:fst
                  and rest = List.map rest ~f:fst in
                  let d' =
                    if List.for_all2_exn (flat_and d []) cs ~f:(fun c (c', _) ->
                           phys_equal c c')
                    then d
                    else Formula.and_of (List.map cs ~f:fst)
                  in
                  if List.is_empty guard || List.is_empty rest then (`O d', m)
                  else
                      ( `G
                          {
                            disjunct = d';
                            guard;
                            rest;
                            guard_fml = Formula.and_of guard;
                            weight = count (Formula.and_of rest);
                          },
                        m )
              | _ ->
                  let d', m = go d in
                  (`O d', m))
        in
        if not (List.exists ds ~f:snd) then (phi, false)
        else
          let cands, others =
            List.partition_map ds ~f:(function
              | `G g, _ -> First g
              | `O d, _ -> Second d)
          in
          (* greedy grouping in decreasing weight: a candidate joins the
             first group (in creation order) all of whose members it
             excludes, or starts a new one *)
          let groups = ref [] in
          List.iter
            (List.stable_sort cands ~compare:(fun a b ->
                 Int.compare b.weight a.weight))
            ~f:(fun c ->
              match
                List.find (List.rev !groups) ~f:(fun g ->
                    List.for_all !g ~f:(fun c' ->
                        exclusive ~key ~steps:exclusive_steps c.guard_fml
                          c'.guard_fml))
              with
              | Some g -> g := c :: !g
              | None -> groups := ref [ c ] :: !groups);
          let groups = List.rev_map !groups ~f:(fun g -> List.rev !g) in
          (* a diagnostic only, read by nothing: the guards of every
             disjunction of three or more candidates, under
             [COAR_EXCLUSIVE_GUARDS_DEBUG] *)
          if
            List.length cands >= 3
            && Option.is_some
                 (Stdlib.Sys.getenv_opt "COAR_EXCLUSIVE_GUARDS_DEBUG")
          then (
            Stdlib.Printf.eprintf "[exclusive-guards-debug] %d candidates, %d groups, %d others\n"
              (List.length cands) (List.length groups) (List.length others);
            List.iter cands ~f:(fun c ->
                Stdlib.Printf.eprintf "  weight=%d guard: %s\n" c.weight
                  (String.concat ~sep:" /\\ "
                     (List.map c.guard ~f:(fun g ->
                          let s = Formula.str_of g in
                          if String.length s > 120 then String.prefix s 120 ^ "..." else s))));
            Stdlib.Printf.eprintf "%!");
          let factored, singles =
            List.partition_tf groups ~f:(fun g -> List.length g >= 2)
          in
          (* the disjuncts left alone whose guards are the same formula:
             [(P /\ Y1) \/ ... \/ (P /\ Ym)] is [P /\ (Y1 \/ ... \/ Ym)]
             (distributivity), whose clausal form has [1 + c1 * ... * cm]
             clauses instead of [(1 + c1) * ... * (1 + cm)] *)
          let shared, singles =
            List.concat singles
            |> List.sort_and_group ~compare:(fun a b ->
                   Stdlib.compare a.guard_fml b.guard_fml)
            |> List.partition_tf ~f:(fun g -> List.length g >= 2)
          in
          if List.is_empty factored && List.is_empty shared then
            let ds' =
              List.map ds ~f:(function `G g, _ -> g.disjunct | `O d, _ -> d)
            in
            if List.for_all2_exn (flat_or phi []) ds' ~f:phys_equal then
              (phi, true)
            else (Formula.or_of ds', true)
          else (
            changed := true;
            let factored_of g =
              stats.rewritten <- stats.rewritten + 1;
              stats.grouped <- stats.grouped + List.length g;
              stats.before <-
                add stats.before
                  (count (Formula.or_of (List.map g ~f:(fun c -> c.disjunct))));
              let phi' =
                Formula.and_of
                @@ Formula.or_of
                     (List.map g ~f:(fun c -> Formula.and_of c.guard))
                   :: List.map g ~f:(fun c ->
                       Formula.or_of
                         [
                           Formula.or_of
                             (List.map c.guard ~f:(fun l ->
                                  Formula.nnf_of (Formula.mk_neg l)));
                           Formula.and_of c.rest;
                         ])
              in
              stats.after <- add stats.after (count phi');
              phi'
            in
            let shared_of g =
              stats.rewritten <- stats.rewritten + 1;
              stats.grouped <- stats.grouped + List.length g;
              stats.before <-
                add stats.before
                  (count (Formula.or_of (List.map g ~f:(fun c -> c.disjunct))));
              let phi' =
                Formula.and_of
                  (List.hd_exn g).guard
                |> fun p ->
                Formula.mk_and p
                  (Formula.or_of
                     (List.map g ~f:(fun c -> Formula.and_of c.rest)))
              in
              stats.after <- add stats.after (count phi');
              phi'
            in
            ( Formula.or_of
              @@ List.map factored ~f:factored_of
              @ List.map shared ~f:shared_of
              @ List.concat_map singles ~f:(List.map ~f:(fun c -> c.disjunct))
              @ others,
              true ))
    | _ -> (phi, leaf_mentions phi)
  in
  let phi', _ = go phi in
  ((if !changed then Some phi' else None), stats)

let factor ~unknowns phi = fst (factor_with_stats ~unknowns phi)

(* Merging the witness variables of one Skolem predicate's copies.

   [merge_witness_copies ~fns phi] takes a clause [phi] (negation normal form,
   its free variables universally quantified) and [fns], a set of functional
   ([FN]) unknowns each of which occurs only negatively in the whole problem.
   A *witness atom* of [phi] is a negative application [not F(vs, x)] with [F]
   in [fns] and [x] a variable that occurs in none of [vs]; it is *local* when
   every occurrence of [x] in [phi] lies inside the smallest disjunction of
   which that atom is a disjunct, the path from [phi]'s root to it crossing
   only conjunctions and disjunctions, and [x] is the last argument of no other
   atom of [fns].  All local witness atoms of one [F] with syntactically equal
   [vs] have their variables renamed to the first one's.  Returns [None] when
   nothing is renamed, else [Some (phi', n)] with [n] the variables renamed.

   Why.  Quantifier elimination gives an existential [exists x. A] the
   predicate [F] and the clause form [forall x. not F(vs, x) \/ A]; when one
   witness predicate serves several occurrences (a disjunctive or same-body
   sharing), each occurrence still binds its own [x], so a disjunction over
   branches that test one choice ([x >= 0] in one, [x' < 0] in the other)
   tests independent variables, no two guards exclude each other, and the
   clausal form multiplies.  With one variable the guards are complementary
   and [factor] makes the clausal form linear in the branches.

   Contract and why it is sound (equisatisfiable, per model).  Since [F] occurs
   only negatively, shrinking an interpretation of [F] to a single-valued
   total sub-relation keeps every clause true and every kind condition ([FN]
   asks totality), so the problem is satisfiable iff it is with [F]
   single-valued; call its value [f(vs)].  For a local [x], miniscoping (sorts
   are non-empty, and no binder lies between the root and the disjunction
   [D = not F(vs, x) \/ R(x)]) makes [forall x. phi] equal to [phi] with [D]
   replaced by [forall x. D], which is [R(f(vs))]; this holds for each local
   [x] separately, so [phi] is [C[R_1(f(vs))]...[R_k(f(vs))]] for the positive
   context [C].  The renamed clause [forall z. C[not F(vs,z) \/ R_1(z)]...]
   is the same at [z = f(vs)], and at any other [z] it is [C[true]...[true]],
   which the former implies by monotonicity.  So under single-valued [F] the
   clause is equivalent to the original, and the problem's satisfiability, its
   verdict and every other unknown's solutions are unchanged; a solution of
   the renamed problem with a multi-valued [F] is a solution of the original
   after the same shrinking.  The universal environment of the clause may keep
   the renamed variables: they no longer occur, and a vacuous universal over a
   non-empty sort changes nothing. *)
let merge_witness_copies ~fns phi =
  let tvs = Formula.tvs_of in
  (* witness atoms: (F, vs, x, sort of x, the free variables outside the
     smallest disjunction holding the atom) *)
  let found = ref [] in
  (* the last argument of every [fns] atom, with multiplicity *)
  let last_args = Hashtbl.Poly.create () in
  let rec scan outside phi =
    match phi with
    | Formula.BinaryOp (((And | Or) as op), _, _, _) ->
        let flat = if Stdlib.( = ) op Formula.And then flat_and else flat_or in
        let cs = flat phi [] in
        let fvs = List.map cs ~f:tvs in
        let n = List.length cs in
        (* outside_i = outside + the variables of every other operand *)
        let pre = Array.create ~len:(n + 1) Set.Poly.empty in
        List.iteri fvs ~f:(fun i s -> pre.(i + 1) <- Set.union pre.(i) s);
        let suf = Array.create ~len:(n + 1) Set.Poly.empty in
        List.iteri (List.rev fvs) ~f:(fun i s ->
            suf.(n - i - 1) <- Set.union suf.(n - i) s);
        List.iteri cs ~f:(fun i c ->
            let outside_i = Set.union outside (Set.union pre.(i) suf.(i + 1)) in
            (match (op, c) with
            | ( Formula.Or,
                Formula.UnaryOp
                  ( Not,
                    Formula.Atom
                      (Atom.App (Predicate.Var (pvar, sorts), args, _), _),
                    _ ) )
              when Set.mem fns pvar -> (
                match (List.last args, List.last sorts) with
                | Some (Term.Var (x, s, _)), Some _ ->
                    let vs = List.drop_last_exn args in
                    if
                      not
                        (List.exists vs ~f:(fun t -> Set.mem (Term.tvs_of t) x))
                    then
                      (* the disjunction holding the atom is [phi]: [x] is
                         local when it occurs nowhere outside [phi] *)
                      found := (pvar, vs, x, s, outside) :: !found
                | _ -> ())
            | _ -> ());
            (match c with
            | Formula.UnaryOp
                (Not, Formula.Atom (Atom.App (Predicate.Var (pvar, _), args, _), _), _)
            | Formula.Atom (Atom.App (Predicate.Var (pvar, _), args, _), _)
              when Set.mem fns pvar -> (
                match List.last args with
                | Some (Term.Var (x, _, _)) -> Hashtbl.incr last_args x
                | _ -> ())
            | _ -> ());
            match c with
            | Formula.BinaryOp _ -> scan outside_i c
            | _ -> ())
    | _ -> ()
  in
  scan Set.Poly.empty phi;
  let local =
    List.filter (List.rev !found) ~f:(fun (_, _, x, _, outside) ->
        (not (Set.mem outside x))
        && Hashtbl.find last_args x |> Option.value ~default:0 = 1)
  in
  let safe_equal a b = try Stdlib.( = ) a b with Invalid_argument _ -> false in
  let groups = ref [] in
  List.iter local ~f:(fun ((pvar, vs, _, _, _) as w) ->
      match
        List.find !groups ~f:(fun g ->
            match !g with
            | (pvar', vs', _, _, _) :: _ ->
                Ident.pvar_equal pvar pvar' && safe_equal vs vs'
            | [] -> false)
      with
      | Some g -> g := w :: !g
      | None -> groups := ref [ w ] :: !groups);
  let sub =
    List.fold !groups ~init:Map.Poly.empty ~f:(fun sub g ->
        match List.rev !g with
        | (_, _, x0, s0, _) :: rest ->
            List.fold rest ~init:sub ~f:(fun sub (_, _, x, _, _) ->
                if Ident.tvar_equal x x0 then sub
                else Map.Poly.set sub ~key:x ~data:(Term.mk_var x0 s0))
        | [] -> sub)
  in
  if Map.is_empty sub then None
  else Some (Formula.subst sub phi, Map.length sub)
