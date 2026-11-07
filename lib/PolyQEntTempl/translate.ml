(* From a predicate constraint problem whose unknowns are given templates to
   polynomial quantified entailments (PQEs) over the templates' parameters,
   in the form PolyQEnt reads: each entailment is
   [forall xs. h_1 /\ ... /\ h_m => c_1 \/ ... \/ c_n] with every [h_i] and
   [c_j] a comparison ([<=], [<], [>=], [>], [=]) of polynomials over real
   universals and real parameters.

   A clause [forall xs. phi] (a disjunction) becomes entailments as follows,
   and the conjunction of the entailments is equivalent to the clause with the
   templates substituted (over the reals, which is the clause's own reading
   since every universal must be real):

   - a universal of tuple sort is replaced by a tuple of fresh universals, one
     per component, and a selector applied to a constructed tuple is reduced; a
     comparison of tuples is the comparison of their components, and one of
     values of sort [unit] is decided outright;
   - a disjunct that is a comparison or a negated comparison, and a negated
     unknown application, go to the hypothesis negated; every other disjunct
     goes to the conclusion;
   - an [ite] and an [abs] inside a comparison are split by cases on the
     condition (an equivalence, since the cases are exhaustive and disjoint);
   - the hypothesis is put in disjunctive normal form and the conclusion in
     conjunctive normal form, a disequality becoming [<] or [>], and there is
     one entailment per pair of a hypothesis disjunct and a conclusion
     conjunct.

   Anything else -- a universal or a comparison of another sort (integers
   included: their relaxation to the reals is not done here), a function other
   than [+], [-], [*] and numerals, a quantifier -- is declined with
   [Templates.Decline], and a clause with more than [max] cases with
   [Templates.Too_large]. *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld
open Templates

(* Replace every universal of tuple sort by a tuple of fresh universals, one
   per component (nested tuples are flattened likewise).  Returns the new
   universals with the substitution.  The names are fresh, so the
   substitution captures nothing. *)
let flatten_tuples uni_senv =
  let rec expand x sort =
    match sort with
    | T_tuple.STuple sorts ->
        let parts =
          List.map sorts ~f:(fun s -> expand (Ident.mk_fresh_tvar ()) s)
        in
        ( List.concat_map parts ~f:fst,
          T_tuple.mk_tuple_cons sorts (List.map parts ~f:snd) )
    | _ -> ([ (x, sort) ], Term.mk_var x sort)
  in
  Map.Poly.fold uni_senv ~init:([], Map.Poly.empty)
    ~f:(fun ~key ~data (senv, sub) ->
      match data with
      | T_tuple.STuple _ ->
          let vars, t = expand key data in
          (vars @ senv, Map.Poly.add_exn sub ~key ~data:t)
      | _ -> ((key, data) :: senv, sub))

(* reduce a selector of a constructed tuple, everywhere in [t] *)
let rec norm t =
  match t with
  | Term.Var _ -> t
  | Term.FunApp (T_tuple.TupleSel (sorts, i), [ t' ], info) -> (
      match norm t' with
      | Term.FunApp (T_tuple.TupleCons _, ts, _) -> List.nth_exn ts i
      | t'' -> Term.mk_fsym_app ~info (T_tuple.TupleSel (sorts, i)) [ t'' ])
  | Term.FunApp (T_bool.Formula _, _, _) -> t
  | Term.FunApp (fsym, ts, info) ->
      Term.mk_fsym_app ~info fsym (List.map ts ~f:norm)
  | Term.LetTerm _ -> decline "a let-term %s" (Term.str_of t)

(* the cases of a term: a list of (conditions, ite- and abs-free term), whose
   conditions are exhaustive and pairwise exclusive *)
let rec cases t =
  match t with
  | Term.Var _ -> [ ([], t) ]
  | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) ->
      let phi = Formula.of_bool_term c in
      List.map (cases a) ~f:(fun (cs, t) -> (phi :: cs, t))
      @ List.map (cases b) ~f:(fun (cs, t) -> (Formula.mk_neg phi :: cs, t))
  | Term.FunApp (T_real.RAbs, [ a ], _) ->
      List.concat_map (cases a) ~f:(fun (cs, a) ->
          [
            (Formula.geq a (T_real.rzero ()) :: cs, a);
            (Formula.lt a (T_real.rzero ()) :: cs, T_real.mk_rneg a);
          ])
  | Term.FunApp (fsym, ts, info) ->
      List.fold_right ts ~init:[ ([], []) ] ~f:(fun t acc ->
          List.concat_map (cases t) ~f:(fun (cs1, t) ->
              List.map acc ~f:(fun (cs2, ts) -> (cs1 @ cs2, t :: ts))))
      |> List.map ~f:(fun (cs, ts) -> (cs, Term.mk_fsym_app ~info fsym ts))
  | Term.LetTerm _ -> decline "a let-term %s" (Term.str_of t)

(* a polynomial over real variables: [+], [-], [*], negation and numerals *)
let rec check_poly t =
  match t with
  | Term.Var (_, T_real.SReal, _) -> ()
  | Term.Var (x, s, _) ->
      decline "a variable %s of sort %s" (Ident.name_of_tvar x)
        (Term.str_of_sort s)
  | Term.FunApp (T_real.Real _, [], _) -> ()
  | Term.FunApp (T_real.(RAdd | RSub | RMul), [ t1; t2 ], _) ->
      check_poly t1;
      check_poly t2
  | Term.FunApp (T_real.RNeg, [ t1 ], _) -> check_poly t1
  | _ -> decline "a term outside the polynomials over the reals: %s" (Term.str_of t)

(* literals are comparisons of real polynomials by [<=], [<], [>=], [>] or
   [=] *)
let real_psym = function
  | T_bool.Eq | T_bool.Neq | T_real.RLeq | T_real.RGeq | T_real.RLt
  | T_real.RGt ->
      true
  | _ -> false

let mk psym t1 t2 = Formula.mk_atom @@ Atom.mk_psym_app psym [ t1; t2 ]

(* the negation of a literal, as a disjunction of literals *)
let negate_lit = function
  | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) -> (
      match psym with
      | T_real.RLeq -> [ mk T_real.RGt t1 t2 ]
      | T_real.RGeq -> [ mk T_real.RLt t1 t2 ]
      | T_real.RLt -> [ mk T_real.RGeq t1 t2 ]
      | T_real.RGt -> [ mk T_real.RLeq t1 t2 ]
      | T_bool.Eq -> [ mk T_real.RLt t1 t2; mk T_real.RGt t1 t2 ]
      | _ -> assert false)
  | _ -> assert false

(* [product ~max a b]: the pairwise unions, declined past [max] *)
let product ~max a b =
  if List.length a * List.length b > max then
    too_large "more than %d cases in one clause" max;
  List.concat_map a ~f:(fun x -> List.map b ~f:(fun y -> x @ y))

(* [dnf ~max ~instantiate pos phi]: [phi] (when [pos]) or its negation (when
   not), as a disjunction of conjunctions of literals, with each unknown
   application replaced by [instantiate] *)
let rec dnf ~max ~instantiate pos phi =
  let dnf = dnf ~max ~instantiate in
  match phi with
  | Formula.Atom (Atom.True _, _) -> if pos then [ [] ] else []
  | Formula.Atom (Atom.False _, _) -> if pos then [] else [ [] ]
  | Formula.Atom (Atom.App (Predicate.Var (pvar, _), args, _), _) ->
      dnf pos (instantiate pvar (List.map args ~f:norm))
  | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) ->
      let t1 = norm t1 and t2 = norm t2 in
      let alts =
        List.concat_map (cases t1) ~f:(fun (cs1, t1) ->
            List.map (cases t2) ~f:(fun (cs2, t2) -> (cs1 @ cs2, t1, t2)))
      in
      (match alts with
      | [ ([], t1, t2) ] -> literal ~max ~instantiate pos psym t1 t2
      | _ ->
          (* the cases partition the space, so the comparison (or its
             negation) is the disjunction over the cases of the case's
             conditions with the comparison (or its negation) there *)
          List.concat_map alts ~f:(fun (cs, t1, t2) ->
              product ~max (dnf true (Formula.and_of cs))
                (literal ~max ~instantiate pos psym t1 t2)))
  | Formula.UnaryOp (Not, phi, _) -> dnf (not pos) phi
  | Formula.BinaryOp (And, a, b, _) ->
      if pos then product ~max (dnf true a) (dnf true b)
      else dnf false a @ dnf false b
  | Formula.BinaryOp (Or, a, b, _) ->
      if pos then dnf true a @ dnf true b
      else product ~max (dnf false a) (dnf false b)
  | Formula.BinaryOp (Imply, a, b, _) ->
      dnf pos (Formula.mk_or (Formula.mk_neg a) b)
  | _ -> decline "a formula outside the clause language: %s" (Formula.str_of phi)

and literal ~max ~instantiate pos psym t1 t2 =
  let sort = Term.sort_of t1 in
  match sort with
  | T_tuple.STuple sorts when Stdlib.(psym = T_bool.Eq || psym = T_bool.Neq) ->
      let comps t =
        match t with
        | Term.FunApp (T_tuple.TupleCons _, ts, _) -> ts
        | _ -> List.mapi sorts ~f:(fun i _ -> norm @@ T_tuple.mk_tuple_sel sorts t i)
      in
      let eqs = List.map2_exn (comps t1) (comps t2) ~f:(mk psym) in
      dnf ~max ~instantiate pos
        (if Stdlib.(psym = T_bool.Eq) then Formula.and_of eqs
         else Formula.or_of eqs)
  | s
    when Datatype.is_unit_sort s && Stdlib.(psym = T_bool.Eq || psym = T_bool.Neq)
    ->
      (* [unit] has one value *)
      let holds = Stdlib.(psym = T_bool.Eq) in
      if Bool.equal holds pos then [ [] ] else []
  | T_real.SReal when real_psym psym -> (
      check_poly t1;
      check_poly t2;
      let psym =
        if pos then psym
        else
          match psym with
          | T_real.RLeq -> T_real.RGt
          | T_real.RGeq -> T_real.RLt
          | T_real.RLt -> T_real.RGeq
          | T_real.RGt -> T_real.RLeq
          | T_bool.Eq -> T_bool.Neq
          | _ -> T_bool.Eq
      in
      match psym with
      | T_bool.Neq -> [ [ mk T_real.RLt t1 t2 ]; [ mk T_real.RGt t1 t2 ] ]
      | _ -> [ [ mk psym t1 t2 ] ])
  | s ->
      decline "a comparison %s of sort %s"
        (Formula.str_of (mk psym t1 t2))
        (Term.str_of_sort s)

(* a literal without variables, decided; [None] when it has variables *)
let decide lit =
  if Set.is_empty (Formula.tvs_of lit) then Some (Evaluator.eval lit) else None

(* The entailments of one clause [(uni_senv, phi)] as formulas
   [not h_1 \/ ... \/ not h_m \/ c_1 \/ ... \/ c_n], whose free variables are
   the clause's (flattened) universals and the parameters.  An entailment
   decided by its variable-free literals is left out when it holds; one that
   cannot hold with no hypothesis left is kept, and makes the system
   unsatisfiable, as the clause is under these templates. *)
let pqes_of_clause ~max ~instantiate (uni_senv, phi) =
  let _, sub = flatten_tuples uni_senv in
  let phi = Formula.subst sub phi in
  let hyps, concls =
    List.partition_map (Formula.disjuncts_list_of phi) ~f:(fun d ->
        match d with
        | Formula.Atom (Atom.App (Predicate.Psym _, _, _), _)
        | Formula.UnaryOp (Not, Formula.Atom (Atom.App (Predicate.Psym _, _, _), _), _) ->
            First (Formula.mk_neg d)
        | Formula.UnaryOp (Not, (Formula.Atom (Atom.App (Predicate.Var _, _, _), _) as a), _) ->
            First a
        | _ -> Second d)
  in
  let hyp_dnf = dnf ~max ~instantiate true (Formula.and_of hyps) in
  let concl_cnf =
    List.map
      (dnf ~max ~instantiate false (Formula.or_of concls))
      ~f:(List.concat_map ~f:negate_lit)
  in
  if List.length hyp_dnf * List.length concl_cnf > max then
    too_large "more than %d entailments in one clause" max;
  List.concat_map hyp_dnf ~f:(fun hs ->
      if List.exists hs ~f:(fun h -> Stdlib.(decide h = Some false)) then []
      else
        let hs = List.filter hs ~f:(fun h -> Option.is_none (decide h)) in
        List.filter_map concl_cnf ~f:(fun cs ->
            if List.exists cs ~f:(fun c -> Stdlib.(decide c = Some true)) then
              None
            else
              let cs = List.filter cs ~f:(fun c -> Option.is_none (decide c)) in
              Some (Formula.or_of (List.map hs ~f:Formula.mk_neg @ cs))))
