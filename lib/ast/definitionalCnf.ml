(* A definitional clausal form for formulas whose clausal form multiplies.

   The clausal form of a disjunction is the product of its operands' clause
   sets, so a disjunction of conjunctions that mention unknowns has
   exponentially many clauses: [(a1 /\ b1) \/ ... \/ (ak /\ bk)] has [2^k], and
   no clausal form over the same atoms read as independent propositions has
   fewer (a clause implied by it must contain one literal of each pair, and
   distinct choices need distinct clauses).  Pure atoms that contradict each
   other in the theory escape that bound: [ExclusiveGuards] factors such
   disjunctions exactly, and what it leaves is the product this module
   names.  Naming each multiplied conjunction [C] by a fresh unknown [D] over
   its free variables -- [D(xs)] in [C]'s place and [D(xs) => C] beside it --
   gives one clause per conjunct instead (the "structure-preserving" or
   definitional normal form of Tseitin, "On the complexity of derivation in
   propositional calculus", 1968, in the one-sided variant of Plaisted and
   Greenbaum, "A structure-preserving clause form translation", J. Symbolic
   Computation 2(3), 1986, which needs only the implication because [C] occurs
   positively).

   The functions here work on [LogicOld] formulas; [predicted_cnf_clauses]
   follows [Formula.cnf_of]'s cases, so the count it gives bounds the clause
   set that function would build. *)

open Core
open Common.Ext
open LogicOld

(* An upper bound on the number of clauses [Formula.cnf_of unknowns] (without
   [process_pure]) gives [phi], read in one pass without building them.

   Contract: for [phi] in negation normal form, as [cnf_of] assumes, the result
   is at least [Set.length (Formula.cnf_of exi_senv phi)] whenever [unknowns]
   is the key set of [exi_senv], saturating at [2^40].  It follows
   [cnf_of_aux] case by case: a subtree mentioning no unknown is one clause (or
   none); a conjunction gives at most the sum of its sides' clauses; a
   disjunction the product; an implication, an equivalence and an exclusive or
   the expansions [cnf_of_aux] makes; a [let] its body's.  A leaf that mentions
   an unknown is one clause. *)
let predicted_cnf_clauses unknowns phi =
  let cap = 1 lsl 40 in
  let mentions phi =
    Set.exists (Formula.pvs_of phi) ~f:(fun pvar ->
        Set.mem unknowns (Ident.pvar_to_tvar pvar))
    || not (Set.are_disjoint (Formula.tvs_of phi) unknowns)
  in
  let add a b = Int.min cap (a + b) in
  let mul a b =
    if a = 0 || b = 0 then 0 else if a > cap / b then cap else a * b
  in
  let rec go phi =
    match phi with
    | Formula.BinaryOp (And, a, b, _) ->
        let ma, ca = go a and mb, cb = go b in
        if ma || mb then (true, add ca cb) else (false, 1)
    | Formula.BinaryOp (Or, a, b, _) ->
        let ma, ca = go a and mb, cb = go b in
        if ma || mb then (true, mul ca cb) else (false, 1)
    | Formula.BinaryOp (Imply, a, b, _) ->
        go
          (Formula.mk_or
             (Formula.nnf_of @@ Formula.mk_neg a)
             (Formula.nnf_of b))
    | Formula.BinaryOp (Iff, a, b, _) ->
        go
          (Formula.mk_and
             (Formula.mk_or
                (Formula.nnf_of @@ Formula.mk_neg a)
                (Formula.nnf_of b))
             (Formula.mk_or
                (Formula.nnf_of a)
                (Formula.nnf_of @@ Formula.mk_neg b)))
    | Formula.BinaryOp (Xor, a, b, _) ->
        go
          (Formula.mk_and
             (Formula.mk_or (Formula.nnf_of a) (Formula.nnf_of b))
             (Formula.mk_or
                (Formula.nnf_of @@ Formula.mk_neg a)
                (Formula.nnf_of @@ Formula.mk_neg b)))
    | Formula.LetFormula (_, _, _, body, _) ->
        let m, c = go body in
        (m || mentions phi, c)
    | _ -> (mentions phi, 1)
  in
  snd (go phi)

(* [gains p c]: naming one disjunct of [c] clauses in a disjunction whose other
   disjuncts multiply to [p] clauses turns [p * c] clauses into [p + c] (the
   other disjuncts with the fresh atom, [p] clauses; the definition, [c]); it
   shortens the clausal form exactly when [(p - 1) * (c - 1) > 1].  In
   particular it never does when [p = 1]: a disjunct beside one clause is not
   multiplied by anything, and naming it adds a clause and an unknown.  That is
   the shape of a proving side's [U(xs) => /\_i (guard_i => successor_i)],
   whose naming put a fresh unknown between the invariant and every
   obligation it had, and turned a two-round refutation into one that did not
   converge. *)
let gains p c = p > 1 && c > 1 && not (p = 2 && c = 2)

(* [gain_plan ~bound counts]: which disjuncts of a disjunction whose disjuncts
   have the predicted clause counts [counts] to name under the gaining rule,
   and which one to distribute.

   Guarantees: the result is [(named, distribute)] with [named] as long as
   [counts].  Disjuncts are named one at a time, the unnamed one of the
   largest count first (the first such), only while the product of the counts
   left (a named disjunct counting one) exceeds [bound], and only when naming
   it shortens the clausal form ([gains]).  When the product still exceeds
   [bound] and naming the largest gains nothing, [distribute] is that
   disjunct's index if its count exceeds one: its conjuncts are then
   distributed over the other disjuncts, which costs no fresh unknown and
   gives the clauses the plain clausal form would ([p = 1]: the others are
   one clause), or four for four ([p = c = 2]).  Otherwise [distribute] is
   [None] and the product is within [bound]. *)
let gain_plan ~bound counts =
  let cap = 1 lsl 40 in
  let mul a b =
    if a = 0 || b = 0 then 0 else if a > cap / b then cap else a * b
  in
  let counts = Array.of_list counts in
  let n = Array.length counts in
  let named = Array.create ~len:n false in
  let eff i = if named.(i) then 1 else counts.(i) in
  let product_except j =
    let acc = ref 1 in
    for i = 0 to n - 1 do
      if i <> j then acc := mul !acc (eff i)
    done;
    !acc
  in
  let rec loop () =
    if product_except (-1) <= bound then None
    else
      let m = ref (-1) in
      for i = 0 to n - 1 do
        if (not named.(i)) && (!m < 0 || counts.(i) > counts.(!m)) then m := i
      done;
      if !m < 0 || counts.(!m) <= 1 then None
      else if gains (product_except !m) counts.(!m) then (
        named.(!m) <- true;
        loop ())
      else Some !m
  in
  let distribute = loop () in
  (Array.to_list named, distribute)

let rec flat op phi =
  match phi with
  | Formula.BinaryOp (op', a, b, _) when Stdlib.( = ) op op' ->
      flat op a @ flat op b
  | _ -> [ phi ]

(* [multiplies ~bound ~unknowns phi]: does [split ~gain:true] name anything in
   [phi], i.e. does [phi]'s clausal form exceed [bound] through a product that
   a fresh unknown shortens.  Decided without building the split's formulas
   (only the distributed disjunctions it would recurse into).

   Why it is the test for setting a formula aside: when it is false the
   clausal form is the plain one, and it is at most [bound] times the
   formula's number of leaves (by induction along the split: a conjunction
   sums; a disjunction that gains nothing has one disjunct of more than one
   clause beside one clause, whose count it keeps, or two of two clauses, four
   against at least four leaves), so keeping the formula whole saves nothing
   that its own size does not already cost. *)
let multiplies ~bound ~unknowns phi =
  let count = predicted_cnf_clauses unknowns in
  let rec go phi =
    count phi > bound
    &&
    match phi with
    | Formula.BinaryOp (Formula.And, _, _, _) ->
        List.exists (flat Formula.And phi) ~f:go
    | Formula.BinaryOp (Formula.Or, _, _, _) -> (
        let parts = flat Formula.Or phi in
        let named, distribute = gain_plan ~bound (List.map parts ~f:count) in
        List.exists named ~f:Fn.id
        ||
        match distribute with
        | Some m -> (
            match List.nth_exn parts m with
            | Formula.BinaryOp (Formula.And, _, _, _) as c ->
                let others = List.filteri parts ~f:(fun j _ -> j <> m) in
                List.exists (flat Formula.And c) ~f:(fun cj ->
                    go (Formula.or_of (others @ [ cj ])))
            | _ -> false)
        | None -> false)
    | _ -> false
  in
  go phi

(* [split ~bound ~unknowns ~universals ~fresh phi] is [(phis, defs)]: formulas
   whose clausal forms together replace the clausal form of [phi], with fresh
   unknowns naming the conjunctions it multiplies.

   Assumes: [phi] is in negation normal form, quantifier-free at the top (its
   universals stripped into [universals]); [unknowns] are the problem's
   unknowns; [universals] holds the clause's universally quantified variables
   with their sorts, Boolean variables included; [fresh ()] returns a predicate
   variable used nowhere else in the problem.

   With [~fewest:true] a disjunction over the bound has only as many of its
   disjuncts named, largest count first, as bring the product of the others'
   counts within the bound; the soundness argument below is per named
   disjunct and does not depend on which are named.

   With [~gain:true] (which implies [~fewest]) a disjunct is named only where
   the naming shortens the clausal form ([gain_plan]), and where no naming does
   while the disjunction still exceeds the bound, the largest disjunct's
   conjuncts are distributed over the others and each resulting disjunction
   split in turn (a strictly smaller formula, so this terminates).  No fresh
   unknown is then made where the clausal form does not multiply.

   Guarantees: [defs] lists the fresh unknowns with their argument sorts, each
   to be added as an ordinary unknown.  When [predicted_cnf_clauses] of [phi] is
   at most [bound], the result is [([phi], [])].  Otherwise a conjunction is
   split into its conjuncts, and in a disjunction every disjunct whose own
   clausal form has more than one clause is replaced by [D(xs)] for a fresh [D]
   over the disjunct's free term variables plus the clause's Boolean universals
   (the unknowns excepted), and [not D(xs) \/ cj] is split in turn for each
   conjunct [cj] of the disjunct.  An implication, a [let] or a binder is a leaf
   the split does not enter, so a formula of [phis] can still exceed [bound]
   when such a leaf does.  Recursion is on proper subformulas only, so it
   terminates; every output formula is one of the input's subformulas or a
   disjunction of them with negated fresh atoms, so [phis] is at most linear in
   the size of [phi] times its depth.

   Why it is sound, in every model [M] of the theory: the formula with [D(xs)]
   in [C]'s place together with [D(xs) => C] implies the original, whatever [D]
   denotes, since [C] occurs positively and a negation-normal formula is
   monotone in its positive occurrences; and an interpretation satisfying the
   original extends to one satisfying the new formulas by reading [D] as [C]
   (under the same interpretation of the old unknowns).  So [M] admits an
   interpretation of the original iff it admits one of the result, a solution
   of the result restricted to the old unknowns solves the original, and the
   kinds of the old unknowns are untouched ([D] is ordinary).  The fresh
   predicate must take every Boolean universal of the clause: Boolean
   variables standing as nullary predicates are not term variables, and a [D]
   without them would have to satisfy its definition for both of their values
   at once, which can turn a satisfiable constraint unsatisfiable.  And it
   must not be eliminated by resolution afterwards, which would substitute [C]
   back and rebuild the product. *)
let split ?(fewest = false) ?(gain = false) ?(shared_args = false) ~bound ~unknowns
    ~universals ~fresh phi =
  let count = predicted_cnf_clauses unknowns in
  (* [fewest]: in a disjunction over the bound, the disjuncts are named in
     decreasing order of their own counts only until the product of the
     counts left (a named disjunct counting one) is within the bound, instead
     of every disjunct counting more than one; the count of what is left is
     then within the bound, and fewer fresh unknowns are made *)
  let to_name parts =
    if not fewest then List.map parts ~f:(fun c -> count c > 1)
    else
      let counted = List.mapi parts ~f:(fun i c -> (i, count c)) in
      let product l =
        List.fold l ~init:1 ~f:(fun acc (_, n) ->
            if acc = 0 || n = 0 then 0
            else if acc > (1 lsl 40) / n then 1 lsl 40
            else acc * n)
      in
      let rec choose named = function
        | [] -> named
        | (i, n) :: rest as left ->
            if n <= 1 || product left <= bound then named
            else choose (Set.add named i) rest
      in
      let largest_first =
        List.sort counted ~compare:(fun (_, a) (_, b) -> Int.compare b a)
      in
      let named = choose Int.Set.empty largest_first in
      List.mapi parts ~f:(fun i _ -> Set.mem named i)
  in
  let out = ref [] and defs = ref [] in
  let rec go phi =
    if count phi <= bound then out := phi :: !out
    else
      match phi with
      | Formula.BinaryOp (Formula.And, _, _, _) ->
          List.iter (flat Formula.And phi) ~f:go
      | Formula.BinaryOp (Formula.Or, _, _, _) when gain -> (
          let parts = flat Formula.Or phi in
          let named, distribute =
            gain_plan ~bound (List.map parts ~f:count)
          in
          let parts' =
            List.mapi (List.zip_exn parts named) ~f:(fun i (c, named) ->
                if named then
                  define
                    ~others:(lazy (List.filteri parts ~f:(fun j _ -> j <> i)))
                    c
                else c)
          in
          match distribute with
          | Some m -> (
              match List.nth_exn parts' m with
              | Formula.BinaryOp (Formula.And, _, _, _) as c ->
                  let others = List.filteri parts' ~f:(fun j _ -> j <> m) in
                  List.iter (flat Formula.And c) ~f:(fun cj ->
                      go (Formula.or_of (others @ [ cj ])))
              | _ -> out := Formula.or_of parts' :: !out)
          | None -> out := Formula.or_of parts' :: !out)
      | Formula.BinaryOp (Formula.Or, _, _, _) ->
          let parts = flat Formula.Or phi in
          let parts =
            List.mapi (List.zip_exn parts (to_name parts))
              ~f:(fun i (c, named) ->
                if named then
                  define
                    ~others:(lazy (List.filteri parts ~f:(fun j _ -> j <> i)))
                    c
                else c)
          in
          out := Formula.or_of parts :: !out
      | _ -> out := phi :: !out
  and define ~others c =
    let args =
      Set.to_list
      @@ Set.filter
           (Set.union (Formula.term_sort_env_of c)
              (Set.filter universals ~f:(fun (_, s) -> Term.is_bool_sort s)))
           ~f:(fun (x, _) -> not (Set.mem unknowns x))
    in
    (* [shared_args]: only the variables [c] shares with the other disjuncts
       of the formula being split; one free in [c] alone is quantified inside
       the definition, since [forall y. (A \/ c)] is [A \/ forall y. c] when
       [y] is not free in [A].  A Boolean universal is a nullary predicate in
       the formula, so it is looked for among the predicate variables too.
       The same rule as the predicate eliminator's copy of this split. *)
    let args =
      if not shared_args then args
      else
        let others = Lazy.force others in
        let tvs = List.map others ~f:Formula.tvs_of |> Set.Poly.union_list in
        let pvs = List.map others ~f:Formula.pvs_of |> Set.Poly.union_list in
        let c_tvs = Formula.tvs_of c and c_pvs = Formula.pvs_of c in
        List.filter args ~f:(fun (x, s) ->
            (Set.mem tvs x || Set.mem pvs (Ident.tvar_to_pvar x))
            && ((not (Term.is_bool_sort s))
               || Set.mem c_tvs x
               || Set.mem c_pvs (Ident.tvar_to_pvar x)))
    in
    let pvar = fresh () in
    let sorts = List.map args ~f:snd in
    let atom =
      Formula.mk_atom
      @@ Atom.mk_pvar_app pvar sorts
           (List.map args ~f:(fun (x, s) -> Term.mk_var x s))
    in
    defs := (pvar, sorts) :: !defs;
    let guard = Formula.mk_neg atom in
    List.iter (flat Formula.And c) ~f:(fun cj -> go (Formula.mk_or guard cj));
    atom
  in
  go phi;
  (List.rev !out, List.rev !defs)
