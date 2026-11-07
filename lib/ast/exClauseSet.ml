open Core
open Common.Ext
open Common.Combinator
open LogicOld

type t = ExClause.t Set.Poly.t

(* Assuming that all pure formulas are evaluated into T/F. *)
let of_formula exi_senv phi : t =
  Set.Poly.filter_map ~f:(Tuple3.uncurry @@ ExClause.make exi_senv)
  @@ Formula.cnf_of exi_senv phi

let print_log = false

(* the example clauses obtained by applying [map] to the clause [phi]: the
   pipeline shared by [of_model_with_subst] and the witness checker, which
   re-derives an example from its recorded substitution *)
(* [settle_pure]: before the clausal form, ask [discharge] whether the
   disjunction of the clause's disjuncts that apply no predicate is
   unsatisfiable, and drop it if so.  The clausal form distributes such a
   disjunct over the rest, so a conjunction false for every value of an opened
   variable ([0 <= -1 - x /\ x >= 0]) becomes two clauses whose guards are
   each satisfiable, and neither is then discharged; asked whole, it is one
   validity question.  Dropping a disjunct false in every model leaves the
   clause equivalent.  The witness checker re-derives examples without it, so
   an example obtained this way is one it reports unchecked rather than
   re-derived. *)
let settle_pure_disjuncts ?discharge phi =
  match discharge with
  | None -> phi
  | Some discharge -> (
      let pure, rest =
        List.partition_tf (Formula.disjuncts_list_of phi) ~f:(fun d ->
            Set.is_empty (Formula.pvs_of d))
      in
      let pure_phi = Formula.or_of pure in
      if List.is_empty pure || Set.is_empty (Formula.tvs_of pure_phi) then phi
      else
        match discharge (Formula.mk_neg pure_phi) with
        | `Sat -> Formula.or_of rest
        | _ -> phi)

let of_subst ?discharge ?(settle_pure = false) exi_senv phi map : t =
  Formula.subst map phi
  |> Normalizer.normalize_let ~rename:true
  |> Formula.nnf_of |> Formula.instantiate_div0_mod0 |> Evaluator.simplify
  |> Normalizer.normalize
  |> (if settle_pure then settle_pure_disjuncts ?discharge else Fn.id)
  |> Formula.cnf_of (Logic.to_old_sort_env_map exi_senv)
  |> Set.Poly.filter_map ~f:(Tuple3.uncurry @@ ExClause.make ?discharge exi_senv)
  |> Set.Poly.map ~f:(ExClause.normalize_params (Map.key_set exi_senv))

(* Does every example this substitution produces say what it says
   UNCONDITIONALLY?  An example carries a guard when the clause's pure part
   still mentions a variable the substitution left open, and a guarded example
   is a much weaker thing for the loop: it forces nothing until its guard is
   discharged, and a guard mentioning a parameter is never discharged, because
   the discharge is only sound for a ground one.  So this is the test that says
   whether a variable may be left open FOR FREE. *)
let all_unguarded exs =
  Fn.non Set.is_empty exs
  && Set.for_all exs ~f:(fun ex ->
      Set.for_all (ExClause.exatoms_of ex) ~f:(fun atm ->
          let _, cond, _ = ExAtom.to_old_formula_and_cond atm in
          Formula.is_true cond))

(* Keep as little of the model as the clause needs.

   A counterexample is a model [M] with [M |= phi], and the substitution built
   from it fixes every variable [M] mentions -- including the ones the
   constraint never forced, which a model assigns anyway and does not mark.
   Dropping those is not a heuristic about which values look invented: it is the
   question of how much of [M] the clause actually uses, and it has a property
   the guesswork does not.  Where the remaining assignments already settle the
   pure part, the dropped variables are genuinely free, the example holds for
   every value of them, and it holds UNCONDITIONALLY -- no guard, which is the
   form the rest of the loop can act on.  That is the difference from opening a
   variable and letting the residual become a guard: the same generality, and
   the example stays a fact rather than becoming an implication.

   Greedy and one variable at a time, keeping a removal only when every example
   the smaller substitution produces is still unguarded and the set is still
   non-empty.  The order is the map's, so the result is a subset that cannot be
   reduced by removing one more -- irreducible for this oracle, not smallest,
   which is the usual bargain and needs no solver.

   [oracle] is what decides "the pure part is settled without this variable".
   Today it is the evaluator, through the guard the example comes out with,
   which is free and conservative: it keeps a variable whenever simplification
   cannot see that the residual is decided.  A solver asked for validity would
   drop strictly more, and is the next step rather than a different design --
   the loop is the same and only this test changes. *)
let rec shrink_substitution ?discharge ?settle_pure exi_senv phi map = function
  | [] -> map
  | x :: rest ->
      let smaller = Map.Poly.remove map x in
      let map =
        if all_unguarded (of_subst ?discharge ?settle_pure exi_senv phi smaller)
        then smaller
        else map
      in
      shrink_substitution ?discharge ?settle_pure exi_senv phi map rest

(* Open, TOGETHER, variables the model gave one value.

   [shrink_substitution] drops one variable at a time, and a clause that ties
   two variables by an equation -- [(= (mut v1 v0) (mut v53 v52))], the way a
   Rust-derived clause threads a prophecy through its steps -- then keeps both:
   dropping [v0] alone leaves the residual [v0 = v52] as a guard, and so does
   dropping [v52] alone.  Opened together as ONE parameter, the equation is
   [p = p] and is settled.

   The step.  Partition the substitution's variables by their value (the same
   sort and a structurally equal value; a value that is already a variable is
   left out).  For each class of at least two variables, try replacing every
   one of them by one fresh parameter of that sort; if that is refused, try
   instead each subset of the class that the clause's own equations connect (a
   variable-to-variable equation, or an equation between two applications of
   one constructor, pairing their arguments), of at least two variables.  An
   attempt is kept by the test [shrink_substitution] keeps a removal by: the
   examples are non-empty and all UNGUARDED, decided by the evaluator and never
   by satisfiability.  Greedy, in class order.

   Soundness.  The clause is universally quantified over its variables, so
   substituting one fresh parameter for several of them gives an instance of
   its universal closure, valid for every value of the parameter; an unguarded
   example obtained from it is therefore a consequence of the clause.  The
   model's point is an instance (the parameter at the class's common value), so
   the example still excludes the candidate the model refuted.  The equations
   only choose which subsets are tried and carry none of the argument.

   Cost: at most one evaluator pass over the clause per class and per
   component, no solver call.  Returns [map] itself when nothing was merged. *)
(* A trace of [group_equal_values], enabled by [COAR_GROUP_TRACE=1] and
   printed to stderr: per call, the clause kind, the substitution's non-variable
   values, the classes found, each merge tried and whether it was kept, and why
   a refused one was refused.  Otherwise inert. *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let group_trace =
  Lazy.from_val
    (match Sys.getenv "COAR_GROUP_TRACE" with
    | Some ("1" | "true" | "yes") -> true
    | _ -> false)

let group_log msg = if Lazy.force group_trace then prerr_endline ("[grp] " ^ msg)

let clause_kind_of exs =
  if Set.is_empty exs then "empty"
  else if Set.for_all exs ~f:(fun (ex : ExClause.t) -> Set.is_empty ex.positive)
  then "goal"
  else if Set.for_all exs ~f:(fun (ex : ExClause.t) -> Set.is_empty ex.negative)
  then "fact"
  else "step"

let str_of_exs exs =
  String.concat ~sep:" ; " (List.map (Set.to_list exs) ~f:ExClause.str_of)

let group_equal_values ?discharge exi_senv phi map =
  if Lazy.force group_trace then (
    let exs = of_subst ?discharge exi_senv phi map in
    group_log
      (sprintf "call kind=%s exs=[%s]" (clause_kind_of exs) (str_of_exs exs));
    group_log
      ("  subst: "
      ^ String.concat ~sep:", "
          (List.map (Map.Poly.to_alist map) ~f:(fun (x, v) ->
               Ident.name_of_tvar x ^ "=" ^ Term.str_of v))));
  let classes =
    Map.Poly.to_alist map
    |> List.filter ~f:(fun (_, v) -> not (Term.is_var v))
    |> List.map ~f:(fun (x, v) ->
        (Term.str_of_sort (Term.sort_of v) ^ " " ^ Term.str_of v, x))
    |> List.sort_and_group ~compare:(fun (k1, _) (k2, _) -> String.compare k1 k2)
    |> List.filter_map ~f:(function
      | _ :: _ :: _ as cls -> Some (List.map cls ~f:snd)
      | _ -> None)
  in
  group_log
    (sprintf "  classes: %s"
       (String.concat ~sep:" | "
          (List.map classes ~f:(fun cls ->
               String.concat ~sep:","
                 (List.map cls ~f:Ident.name_of_tvar)
               ^ " = "
               ^ Term.str_of (Map.Poly.find_exn map (List.hd_exn cls))))));
  if List.is_empty classes then map
  else
    (* the variable pairs the clause's equations connect *)
    let edges =
      let rec pairs t1 t2 =
        match (t1, t2) with
        | Term.Var (x, _, _), Term.Var (y, _, _) -> [ (x, y) ]
        | ( Term.FunApp (T_dt.DTCons (c1, _, _), a1, _),
            Term.FunApp (T_dt.DTCons (c2, _, _), a2, _) )
          when String.(c1 = c2) && List.length a1 = List.length a2 ->
            List.concat (List.map2_exn a1 a2 ~f:pairs)
        | _ -> []
      in
      let poss, negs = Formula.atoms_of phi in
      Set.to_list (Set.union poss negs)
      |> List.concat_map ~f:(function
        | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) -> pairs t1 t2
        | _ -> [])
    in
    let mem = List.mem ~equal:Stdlib.( = ) in
    (* the subsets of [cls] its members' edges connect, of size >= 2 *)
    let components cls =
      let es = List.filter edges ~f:(fun (x, y) -> mem cls x && mem cls y) in
      let rec reach seen = function
        | [] -> seen
        | x :: todo ->
            let next =
              List.filter_map es ~f:(fun (a, b) ->
                  if Stdlib.(a = x) then Some b
                  else if Stdlib.(b = x) then Some a
                  else None)
              |> List.filter ~f:(fun y -> not (mem seen y))
              |> List.dedup_and_sort ~compare:Stdlib.compare
            in
            reach (seen @ next) (next @ todo)
      in
      List.fold cls ~init:[] ~f:(fun acc x ->
          if List.exists acc ~f:(fun c -> mem c x) then acc
          else acc @ [ reach [ x ] [ x ] ])
      |> List.filter ~f:(fun c -> List.length c >= 2)
    in
    let try_merge map xs =
      let sort = Term.sort_of (Map.Poly.find_exn map (List.hd_exn xs)) in
      let p = Term.mk_var (Ident.mk_fresh_dontcare "grp") sort in
      let map' =
        List.fold xs ~init:map ~f:(fun m x -> Map.Poly.set m ~key:x ~data:p)
      in
      let exs = of_subst ?discharge exi_senv phi map' in
      let ok = all_unguarded exs in
      group_log
        (sprintf "  try {%s}: %s"
           (String.concat ~sep:"," (List.map xs ~f:Ident.name_of_tvar))
           (if ok then "kept -> [" ^ str_of_exs exs ^ "]"
            else if Set.is_empty exs then "refused (examples empty)"
            else "refused (guard remains) -> [" ^ str_of_exs exs ^ "]"));
      if ok then Some map' else None
    in
    List.fold classes ~init:map ~f:(fun map cls ->
        match try_merge map cls with
        | Some map' -> map'
        | None ->
            List.fold (components cls) ~init:map ~f:(fun map comp ->
                Option.value (try_merge map comp) ~default:map))

(* Open the elements of the sequence literals a substitution's values contain,
   one POSITION at a time.

   [shrink_substitution] decides per variable, and a variable whose value is a
   sequence literal -- [seq.++ (seq.unit 0) (seq.unit 7)] -- can then only be
   kept whole or dropped whole, even when the clause reads it at one position
   only and the other element is whatever the solver's model happened to say.
   This tries each element of each maximal sequence literal inside each value
   (inside datatype or tuple values too, not inside an element itself), in
   order, replacing it by a fresh parameter of the element sort and keeping the
   length and every other element.

   Contract.  The test for keeping a replacement is exactly the one
   [shrink_substitution] keeps a removal by: the examples the changed
   substitution produces are non-empty and every one of them is UNGUARDED.  An
   unguarded example's pure part was settled without the opened element, so the
   example is a consequence of the clause for every value of it; nothing is
   decided by satisfiability, and a guard is never produced and then dropped.
   The model's own point is an instance of the result (the parameter at the
   element's old value), so the example still excludes the candidate the model
   refuted.  An element that is already a variable is not tried.  Greedy and in
   position order, so the result cannot be opened at one more position by this
   test; at most [max_tries] positions are tried per call, which bounds the cost
   at that many evaluator passes over the clause (no solver call).  Returns
   [map] itself when nothing was opened. *)
(* Do these examples come from a GOAL clause -- one with no head predicate
   application?  Read off the examples the unopened substitution produces:
   non-empty, and none has a positive atom.  A fact or step clause's example
   always carries its head atom, so it is never taken for a goal. *)
let is_goal exs =
  Fn.non Set.is_empty exs
  && Set.for_all exs ~f:(fun (ex : ExClause.t) -> Set.is_empty ex.positive)

let open_seq_elements ?discharge ?(max_tries = 64) exi_senv phi map =
  let seq_sort_of_literal = function
    | Term.FunApp ((T_seq.SqEmpty se | T_seq.SqUnit se | T_seq.SqConcat se), _, _)
      ->
        Some se
    | _ -> None
  in
  (* the value with its [k]-th literal element (counting top-down through the
     maximal literals) replaced by [f] of it; [k] counts down as elements are
     passed *)
  let rec rewrite k f t =
    match (seq_sort_of_literal t, Evaluator.seq_elems_of t) with
    | Some se, Some es ->
        let n = List.length es in
        if !k >= 0 && !k < n then (
          let es = List.mapi es ~f:(fun i e -> if i = !k then f e se else e) in
          k := -1;
          Evaluator.seq_of_elems se es)
        else (
          if !k >= 0 then k := !k - n;
          t)
    | _ -> (
        match t with
        | Term.FunApp (sym, args, info) when !k >= 0 ->
            let args = List.map args ~f:(rewrite k f) in
            Term.mk_fsym_app ~info sym args
        | _ -> t)
  in
  let rec count t =
    match (seq_sort_of_literal t, Evaluator.seq_elems_of t) with
    | Some _, Some es -> List.length es
    | _ -> (
        match t with
        | Term.FunApp (_, args, _) -> List.sum (module Int) args ~f:count
        | _ -> 0)
  in
  let tries = ref 0 in
  List.fold (Map.Poly.keys map) ~init:map ~f:(fun map x ->
      let n = count (Map.Poly.find_exn map x) in
      List.fold (List.init n ~f:Fn.id) ~init:map ~f:(fun map i ->
          if !tries >= max_tries then map
          else
            let v = Map.Poly.find_exn map x in
            let opened = ref false in
            let v' =
              rewrite (ref i)
                (fun e se ->
                  match e with
                  | Term.Var _ -> e
                  | _ ->
                      opened := true;
                      Term.mk_var (Ident.mk_fresh_dontcare "elem") se)
                v
            in
            if not !opened then map
            else (
              incr tries;
              let map' = Map.Poly.set map ~key:x ~data:v' in
              if all_unguarded (of_subst ?discharge exi_senv phi map') then map'
              else map)))

(* The variables of a clause that are the RESULT of a witness and nothing else:
   [x] such that the clause is one clause of its clausal form, [x] is the
   last argument of exactly one of its atoms, that atom is a negative
   (premise) application of a predicate [is_fn] says is functional, [x]
   appears there as the bare variable and in no other argument of any atom,
   and the pure part is free to mention it.

   Why these may be left open in a counterexample.  A counterexample's model
   gives [x] the candidate's own value, so the example built from it says
   only "this witness does not take that value at these arguments", which a
   candidate meets by moving one witness off one point.  Left open, the
   example is [forall x. phi(x) \/ not F(a, x) \/ ...] at the model's other
   values: an instance of the clause, hence a consequence of the problem, and
   the model's point is one of its instances, so it still excludes the
   candidate the model refuted.  What it adds is read by a synthesizer that
   knows [F]'s template is the graph [x = t(a)]: there the universal over [x]
   is discharged by the one-point rule and the example becomes [phi(t(a))],
   the clause's own demand at these arguments.

   Contract: returns a subset of the clause's free term variables; the empty
   set when the clausal form has more than one clause or no such variable. *)
let fn_result_vars ~is_fn exi_senv phi =
  match
    Set.to_list
      (Formula.cnf_of (Logic.to_old_sort_env_map exi_senv) phi)
  with
  | [ (ps, ns, _pure) ] ->
      let apps polarity atoms =
        List.filter_map (Set.to_list atoms) ~f:(function
          | Atom.App (Predicate.Var (pvar, _), args, _) ->
              Some (polarity, pvar, args)
          | _ -> None)
      in
      let all = apps true ps @ apps false ns in
      let occurrences x =
        List.count all ~f:(fun (_, _, args) ->
            List.exists args ~f:(fun t -> Set.mem (Term.tvs_of t) x))
      in
      Set.Poly.of_list
      @@ List.filter_map all ~f:(fun (polarity, pvar, args) ->
          match List.rev args with
          | Term.Var (x, _, _) :: rest
            when (not polarity) && is_fn pvar
                 && (not
                       (List.exists rest ~f:(fun t ->
                            Set.mem (Term.tvs_of t) x)))
                 && occurrences x = 1 ->
              Some x
          | _ -> None)
  | _ -> Set.Poly.empty

(* also returns the substitution applied to the clause (the countermodel,
   with dummies/don't-cares for the variables it leaves open); the parameters
   of the resulting examples are renamed by [normalize_params], so the
   substitution matches them up to that renaming *)
let of_model_with_subst ?discharge ?(stated_literals = None)
    ?(partial_model = false) ?(partial_seq_elements = false)
    ?(partial_seq_elements_goal_only = false) ?(group_equal = false)
    ?(settle_pure = false) ?(open_vars = Set.Poly.empty) exi_senv pex
    (senv, phi) (* clause*) model :
    LogicOld.TermSubst.t * t =
  (* the values a model invented, opened as parameters -- the rule and its
     soundness argument are with the rewriting in the term language.  The set is
     THE PROBLEM'S, not the clause's, and the difference is not academic: a
     clause-local test opened a variable 416 times on one run and 326 of those
     were the value 10, a slice bound the program states, absent from the clause
     the counterexample came from and present in the problem.  Nor is it unioned
     with the clause's literals, although that reads like the conservative
     choice -- the clause reaching here has the CANDIDATE SOLUTION substituted
     into it, and a candidate is the synthesizer's invention built out of
     earlier examples, so its constants are solver-invented too and protecting
     them protects exactly what is to be opened. *)
  let generalise =
    match stated_literals with
    | Some stated when pex -> LogicOld.make_generaliser ~stated
    | _ -> Fn.id
  in
  let map =
    List.map (Map.Poly.to_alist senv) ~f:(fun (id, sort) ->
        ( (id, sort),
          (* BY NAME AND SORT.  A solver's model describes every symbol its
             context knows, and where the instances are pooled and reused that
             includes the declarations of earlier queries -- so looking an entry
             up by name alone can return a value of a sort this clause never
             asked about, and the substitution below then puts, say, a list
             where a list's element belongs.  The term is well sorted until it
             is, and the run ends in a sort mismatch on a constructor
             application, raised by the conversion far from here.

             No match at the right sort means the model said nothing about this
             variable, which is the case the next branch already handles. *)
          match
            LogicOld.model_find model (id, Logic.ExtTerm.to_old_sort sort)
          with
          | None -> None
          | Some v -> v ))
    |> List.map ~f:(function
      | (x, s), Some v ->
          let v = generalise v in
          let sort = Logic.ExtTerm.to_old_sort s in
          if print_log then
            print_endline
              (Ident.name_of_tvar x ^ " : " ^ Term.str_of_sort sort ^ " |-> "
             ^ Term.str_of v);
          (x, v)
      | (x, s), None ->
          let sort = Logic.ExtTerm.to_old_sort s in
          if print_log then
            print_endline
              (Ident.name_of_tvar x ^ " : " ^ Term.str_of_sort sort ^ " |-> *");
          if pex then
            ( x,
              Term.mk_var (Ident.mk_fresh_dontcare (Ident.name_of_tvar x)) sort
            )
          else (x, Term.mk_dummy sort))
    |> Map.Poly.of_alist_exn
  in
  let map =
    (* Only where the examples are allowed to be parametric at all: with [pex]
       off a variable the model did not mention is filled with a dummy rather
       than left open, so dropping an assignment here would produce a dummy
       instead of a parameter and say something the clause never said. *)
    if partial_model && pex then
      shrink_substitution ?discharge ~settle_pure exi_senv phi map
        (Map.Poly.keys map)
    else map
  in
  let map =
    (* the same restriction to parametric examples, for the same reason; on
       every clause (fact, step, goal), after the shrinking and before the
       element opening *)
    if group_equal && pex then group_equal_values ?discharge exi_senv phi map
    else map
  in
  let map =
    (* the same restriction to parametric examples, for the same reason; with
       [partial_seq_elements_goal_only], only on a goal clause, so that a fact
       or step clause's examples stay as they are without the opening -- a
       positive's parameter would not unify with the literal a step clause's
       body needs, and resolution would stop deriving the positives a
       refutation walks along *)
    if
      partial_seq_elements && pex
      && ((not partial_seq_elements_goal_only)
         || is_goal (of_subst ?discharge exi_senv phi map))
    then open_seq_elements ?discharge exi_senv phi map
    else map
  in
  let exs = of_subst ?discharge ~settle_pure exi_senv phi map in
  (* [open_vars] ([fn_result_vars]): the examples with those variables left
     open are added BESIDE the point's, last, after every step above has
     decided what to keep; only where examples may be parametric, as above.
     Beside and not instead: a reader that does not discharge the open
     results by the one-point rule grounds them at a default value, which
     says less than the point, so replacing the point could only lose.  The
     returned substitution is the point's. *)
  if pex && not (Set.is_empty open_vars) then
    let opened =
      Map.Poly.mapi map ~f:(fun ~key ~data ->
          if Set.mem open_vars key then
            Term.mk_var
              (Ident.mk_fresh_dontcare (Ident.name_of_tvar key))
              (Term.sort_of data)
          else data)
    in
    (map, Set.union exs (of_subst ?discharge ~settle_pure exi_senv phi opened))
  else (map, exs)

(* The maximally partial form of a counterexample, to be kept BESIDE the
   model's point rather than instead of it.

   [map] is the substitution [of_model_with_subst] built from the model (with
   [partial_model] off) and [phi] the clause it was applied to.  Returns
   [Some (smaller, exs)], where [smaller] is [map] shrunk by
   [shrink_substitution] and [exs] the examples [smaller] produces, when the
   shrinking dropped at least one assignment; [None] when it dropped nothing,
   so the caller adds nothing.

   Contract: every example returned is unguarded (the shrinking keeps a
   removal only then), and each is the clause instantiated at [smaller] with
   its pure part settled, hence a consequence of the clause for every value of
   the dropped variables.  Since [map] extends [smaller], the model's own point
   is an instance of each, so an example returned still excludes the candidate
   the model refuted.

   Why beside: an example the candidate refutes is new information only if it
   is not already held.  Where the synthesis phase grounds a parametric
   example at a few instances, a candidate can satisfy those and still violate
   the clause, and the validator then returns the same parametric example every
   round, which teaches nothing; on one input, with the partial form kept
   instead of the point, the same parametric fact positive came back in 35 of
   37 rounds.  The model's point is new each round.  What the parametric form
   adds is a positive the resolver can unify with a body atom at ANY value of
   the dropped positions: a forward step whose predecessor needs a specific
   value there is then provable at once, where a set of ground points proves
   it only if one of them happens to carry that value. *)
let partial_model_beside ?discharge exi_senv phi (map : LogicOld.TermSubst.t) =
  let smaller =
    shrink_substitution ?discharge exi_senv phi map (Map.Poly.keys map)
  in
  if Map.Poly.length smaller = Map.Poly.length map then None
  else Some (smaller, of_subst ?discharge exi_senv phi smaller)

let of_model exi_senv pex clause model : t =
  snd @@ of_model_with_subst exi_senv pex clause model

let pvs_of (clauses : t) : Ident.pvar_set =
  Set.concat_map clauses ~f:ExClause.pvs_of

let exatoms_of = Set.concat_map ~f:ExClause.exatoms_of
let exatoms_of_uclauses = Set.Poly.map ~f:ExClause.exatom_of_uclause

let classify_examples examples =
  let pos, examples' = Set.partition_tf examples ~f:ExClause.is_unit_positive in
  let neg, und = Set.partition_tf examples' ~f:ExClause.is_unit_negative in
  (pos, neg, und)

let to_clause_set exi_senv sample =
  ClauseSet.of_formulas exi_senv @@ Set.Poly.map ~f:ExClause.to_formula sample

let str_of ?(max_display = Some 20) sample =
  (match max_display with
    | None -> Set.to_list sample
    | Some max_display -> List.take (Set.to_list sample) max_display)
  |> String.concat_map_list ~sep:";\n" ~f:ExClause.str_of
  |> fun res ->
  res
  ^
  match max_display with
  | None -> ""
  | Some max_display -> if Set.length sample > max_display then ";.." else ""

let normalize = Set.Poly.map ~f:ExClause.normalize
let instantiate = Set.Poly.map ~f:ExClause.instantiate
let refresh_params senv = Set.Poly.map ~f:(ExClause.refresh_params senv)

let refresh_params_with_src senv =
  Set.Poly.map ~f:(fun (ex, src) -> (ExClause.refresh_params senv ex, src))

(* Do a positive and a negative unit atom conflict?  Only two applications of
   one predicate can, so a caller may pair atoms by predicate variable first. *)
let conflicting_atoms unknowns atm1 atm2 =
  match (ExAtom.to_old_atom atm1, ExAtom.to_old_atom atm2) with
  | ( Some (_, (Atom.App (psym1, _, _) as atm1)),
      Some (_, (Atom.App (psym2, _, _) as atm2)) ) -> (
      if Stdlib.(psym1 <> psym2) then false
      else
        (* Example parameters may be instantiated to find a conflict, but
           existential unknowns are shared choices of the solution. Binding
           a Skolem constant to a negative example's value would refute only
           that choice, not the constraint problem. *)
        try Option.is_some @@ Atom.unify unknowns atm1 atm2
        with exn_ when not (Common.Timer.is_async exn_) -> false)
  | _ -> false

let inter_check ?(enable = true) ?(unknowns = Set.Poly.empty) pos_atoms neg_atoms =
  if not enable then Set.Poly.map ~f:fst @@ Set.inter pos_atoms neg_atoms
  else
    let atm_eq = conflicting_atoms unknowns in
    Set.fold pos_atoms ~init:Set.Poly.empty ~f:(fun confits (atm1, _) ->
        Set.fold neg_atoms ~init:confits ~f:(fun confits (atm2, _) ->
            if atm_eq atm1 atm2 then
              Set.union confits @@ Set.Poly.of_list [ atm1; atm2 ]
            else confits))

(* The reference implementation of [unit_propagation] below: every round
   re-simplifies every undecided clause against every unit and re-checks every
   pair of units.  Kept as the specification the incremental version is tested
   against. *)
let unit_propagation_reference unknowns
    (pos_clauses : (ExClause.t * ExClause.t list) Set.Poly.t)
    (neg_clauses : (ExClause.t * ExClause.t list) Set.Poly.t)
    (undecided : (ExClause.t * ExClause.t list) Set.Poly.t) =
  let rec inner pos neg und =
    let pos_atms =
      Set.Poly.map pos ~f:(fun (ex, srcs) ->
          (ExClause.exatom_of_uclause ex, srcs))
    in
    let neg_atms =
      Set.Poly.map neg ~f:(fun (ex, srcs) ->
          (ExClause.exatom_of_uclause ex, srcs))
    in
    let conflicts = inter_check ~unknowns pos_atms neg_atms in
    if Fn.non Set.is_empty conflicts then `Unsat conflicts
    else
      let und =
        let pos_units = ExClause.prepare_units pos_atms in
        let neg_units = ExClause.prepare_units neg_atms in
        Set.Poly.filter_map und
          ~f:(ExClause.simplify_prepared unknowns pos_units neg_units)
      in
      if Set.exists und ~f:(fst >> ExClause.is_false) then
        `Unsat Set.Poly.empty (* ToDo: recover conflicting literals *)
      else
        let ucs, nucs = Set.partition_tf und ~f:(fst >> ExClause.is_unit) in
        if Set.is_empty ucs then `Result (pos, neg, und)
        else
          let pos', neg' =
            Set.partition_tf ucs ~f:(fst >> ExClause.is_unit_positive)
          in
          inner (Set.union pos pos') (Set.union neg neg') nucs
  in
  (* the sources travel as sets inside the propagation (see
     [ExClause.simplify_prepared]) and leave as duplicate-free lists *)
  let enter =
    Set.Poly.map ~f:(fun (ex, srcs) ->
        (ExClause.normalize ex, Set.Poly.of_list srcs))
  in
  let leave = Set.Poly.map ~f:(fun (ex, srcs) -> (ex, Set.to_list srcs)) in
  match inner (enter pos_clauses) (enter neg_clauses) (enter undecided) with
  | `Unsat conflicts -> `Unsat conflicts
  | `Result (pos, neg, und) -> `Result (leave pos, leave neg, leave und)

(* Unit propagation over example clauses, each paired with the input examples
   it was derived from.  [pos_clauses] and [neg_clauses] are positive and
   negative unit clauses, [undecided] the rest.  Each round (1) answers
   [`Unsat] with every atom of a positive and a negative unit atom that unify
   (the unknowns rigid), if there is such a pair; (2) removes from every
   undecided clause each literal that a unit of the opposite polarity matches,
   adding that unit's sources, and drops a clause that a unit of its own
   polarity subsumes; (3) answers [`Unsat] with no atom if a clause became
   empty; (4) makes the clauses left with one literal units and runs again,
   until no clause does: [`Result (pos, neg, undecided)].

   Contract: the answer of [unit_propagation_reference] -- the same sets, the
   same sources for every example, the same conflicts.  The rounds are the
   same and so is each round's result; only which work is repeated differs:
   - the units are looked up in an index ([ExClause.UnitIndex]) that finds the
     unit the reference's linear scan finds, so a removed literal brings the
     same sources;
   - a pair of units is checked once, in the round the later of the two
     appears: a round is reached only if no earlier pair conflicted;
   - an undecided clause is simplified again only if its last simplification
     changed it or a unit new in this round can match one of its literals.
     Otherwise the last round mapped it to itself against a subset of this
     round's units, no unit matched any of its literals, and none of the new
     ones does, so this round would map it to itself again.  A clause that
     changed is always simplified again, because renaming its parameters
     changes what the subsumption test's printed instantiation compares, so
     the earlier units may match the renamed clause.
   Before this, a chain of d ground examples took d rounds, each matching every
   undecided literal against every unit: one call took 230-290 s on four to
   five thousand examples. *)
let unit_propagation_incremental unknowns
    (pos_clauses : (ExClause.t * ExClause.t list) Set.Poly.t)
    (neg_clauses : (ExClause.t * ExClause.t list) Set.Poly.t)
    (undecided : (ExClause.t * ExClause.t list) Set.Poly.t) =
  let enter =
    Set.Poly.map ~f:(fun (ex, srcs) ->
        (ExClause.normalize ex, Set.Poly.of_list srcs))
  in
  let leave = Set.Poly.map ~f:(fun (ex, srcs) -> (ex, Set.to_list srcs)) in
  let atoms =
    Set.Poly.map ~f:(fun (ex, srcs) -> (ExClause.exatom_of_uclause ex, srcs))
  in
  let pvar_of atm =
    match ExAtom.to_old_atom atm with
    | Some (_, Atom.App (Predicate.Var (pvar, _), _, _)) -> Some pvar
    | _ -> None
  in
  let pos_idx = ExClause.UnitIndex.create () in
  let neg_idx = ExClause.UnitIndex.create () in
  let pos_by_pvar = Hashtbl.Poly.create () in
  let neg_by_pvar = Hashtbl.Poly.create () in
  (* the live undecided clauses by id; [unstable] holds the ids whose last
     simplification changed them, [filed] the ids of the clauses whose
     literals carry each [ExClause.lookup_key] (stale ids are harmless: a
     clause looked up needlessly is simplified to the same result) *)
  let clauses = Hashtbl.Poly.create () in
  let unstable = Hash_set.Poly.create () in
  let filed = Hashtbl.Poly.create () in
  let file id (cl, _) =
    Set.iter (ExClause.exatoms_of cl) ~f:(fun atm ->
        List.iter (ExClause.literal_keys atm) ~f:(fun key ->
            Hashtbl.add_multi filed ~key ~data:id))
  in
  let add_units idx by_pvar =
    Set.iter ~f:(fun ((atm, _) as u) ->
        ExClause.UnitIndex.add idx u;
        Option.iter (pvar_of atm) ~f:(fun key ->
            Hashtbl.add_multi by_pvar ~key ~data:atm))
  in
  let conflicts_with fresh others ~fresh_positive =
    Set.fold fresh ~init:Set.Poly.empty ~f:(fun acc (atm, _) ->
        match pvar_of atm with
        | None -> acc
        | Some pvar ->
            List.fold (Hashtbl.find_multi others pvar) ~init:acc
              ~f:(fun acc atm' ->
                let atm1, atm2 =
                  if fresh_positive then (atm, atm') else (atm', atm)
                in
                if conflicting_atoms unknowns atm1 atm2 then
                  Set.add (Set.add acc atm1) atm2
                else acc))
  in
  let rec round pos neg pos_atms neg_atms new_pos new_neg =
    add_units pos_idx pos_by_pvar new_pos;
    add_units neg_idx neg_by_pvar new_neg;
    let conflicts =
      Set.union
        (conflicts_with new_pos neg_by_pvar ~fresh_positive:true)
        (conflicts_with new_neg pos_by_pvar ~fresh_positive:false)
    in
    if Fn.non Set.is_empty conflicts then `Unsat conflicts
    else
      let touched = Hash_set.Poly.create () in
      Hash_set.iter unstable ~f:(Hash_set.add touched);
      Hash_set.clear unstable;
      Set.iter (Set.union new_pos new_neg) ~f:(fun (atm, _) ->
          List.iter (ExClause.unit_keys atm) ~f:(fun key ->
              List.iter (Hashtbl.find_multi filed key) ~f:(fun id ->
                  if Hashtbl.mem clauses id then Hash_set.add touched id)));
      let falsified = ref false in
      let units = ref [] in
      Hash_set.iter touched ~f:(fun id ->
          let ((cl, _) as ex) = Hashtbl.find_exn clauses id in
          match ExClause.simplify_indexed unknowns pos_idx neg_idx ex with
          | None -> Hashtbl.remove clauses id
          | Some ((cl', _) as ex') ->
              if ExClause.is_false cl' then falsified := true;
              if ExClause.is_unit cl' then (
                Hashtbl.remove clauses id;
                units := ex' :: !units)
              else (
                Hashtbl.set clauses ~key:id ~data:ex';
                if Stdlib.compare ex' ex <> 0 then (
                  Hash_set.add unstable id;
                  if Stdlib.compare cl' cl <> 0 then file id ex')));
      if !falsified then `Unsat Set.Poly.empty
        (* ToDo: recover conflicting literals *)
      else if List.is_empty !units then
        `Result (pos, neg, Set.Poly.of_list (Hashtbl.data clauses))
      else
        let pos', neg' =
          List.partition_tf !units ~f:(fst >> ExClause.is_unit_positive)
        in
        let pos' = Set.Poly.of_list pos' in
        let neg' = Set.Poly.of_list neg' in
        let new_pos = Set.diff (atoms pos') pos_atms in
        let new_neg = Set.diff (atoms neg') neg_atms in
        round (Set.union pos pos') (Set.union neg neg')
          (Set.union pos_atms new_pos) (Set.union neg_atms new_neg) new_pos
          new_neg
  in
  let pos = enter pos_clauses in
  let neg = enter neg_clauses in
  List.iteri (Set.to_list (enter undecided)) ~f:(fun id ex ->
      Hashtbl.set clauses ~key:id ~data:ex;
      Hash_set.add unstable id;
      file id ex);
  let pos_atms = atoms pos in
  let neg_atms = atoms neg in
  match round pos neg pos_atms neg_atms pos_atms neg_atms with
  | `Unsat conflicts -> `Unsat conflicts
  | `Result (pos, neg, und) -> `Result (leave pos, leave neg, leave und)

(* Do two answers of unit propagation agree: the same conflicts, or the same
   positive, negative and undecided examples with the same sources? *)
let same_propagation_result r1 r2 =
  match (r1, r2) with
  | `Unsat c1, `Unsat c2 -> Set.equal c1 c2
  | `Result (p1, n1, u1), `Result (p2, n2, u2) ->
      Set.equal p1 p2 && Set.equal n1 n2 && Set.equal u1 u2
  | _ -> false

(* With COAR_UNITPROP_CHECK set in the environment, every call also runs the
   reference implementation and fails loudly if the answers differ: a check of
   the incremental version on the example sets real runs produce. *)
let unitprop_check = lazy (Option.is_some (Sys.getenv "COAR_UNITPROP_CHECK"))

let unit_propagation unknowns pos_clauses neg_clauses undecided =
  let res =
    unit_propagation_incremental unknowns pos_clauses neg_clauses undecided
  in
  if Lazy.force unitprop_check then (
    let reference =
      unit_propagation_reference unknowns pos_clauses neg_clauses undecided
    in
    if not (same_propagation_result res reference) then
      failwith
        "[unit_propagation] the incremental propagation disagrees with the \
         reference implementation";
    prerr_endline "[unit_propagation] COAR_UNITPROP_CHECK: agrees");
  res

(* let discard_unused_exs pcsp exs =
   let senv = PCSP.Problem.senv_of pcsp in
   Set.filter exs ~f:(fun ex ->
       let pvar_sorts = ExClause.pvar_sorts_of ex in
       not
       @@ Set.exists pvar_sorts ~f:(fun (Ident.Pvar v, sorts) ->
              let tvar = Ident.Tvar v in
              if PCSP.Problem.is_bool_valued_ord_pred pcsp tvar then
                match Map.Poly.find senv tvar with
                | None -> true
                | Some sort ->
                    let sorts' =
                      Logic.Sort.args_of sort
                      |> List.map ~f:Logic.ExtTerm.to_old_sort
                    in
                    Stdlib.(sorts' <> sorts)
              else true)) *)
