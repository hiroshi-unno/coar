open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* Finite-membership facts stated under a quantifier, read off formulas so
   that their one-point instances can be offered whole as qualifiers.

   The shape.  A quantified subformula [forall q. D_1 \/ ... \/ D_m] that
   applies no unknown (in any position of any formula given, under any
   polarity) whose disjuncts include
   at least two equations [t(q) = k_1], ..., [t(q) = k_n] of ONE term [t]
   whose only variable is the bound [q] against distinct ground terms [k_i]:
   a precondition [forall q. dl_of(c, q) => ps(q) = 2 \/ ps(q) = 4 \/
   ps(q) = 8], or the same fact with its guard written as a disequation
   [forall q. q <> x \/ ...].  A membership [select S t(q) = true] in a finite
   set literal ([S] a chain of stores of [true] at ground indices over the
   constant-false array) counts as the equations [t(q) = k] for its members.
   An existential [exists q. B] is read as the universal of [not B], so the
   same fact met negated (a premise read inside a clause written as a
   disjunction) gives the same equations.  The other disjuncts (the guard) are
   dropped.

   What it returns.  One [fact] per (quantified subformula, bound variable,
   term [t]): the disjunction [t(q) = k_1 \/ ... \/ t(q) = k_n] with the bound
   variable it is over and that variable's sort.  [instances] puts a
   parameter of the bound's sort in place of [q].

   Contract.  Every formula returned mentions exactly one variable (the one
   named in the fact, or the parameter it is instantiated at).  Nothing here
   claims the instance holds anywhere: the guard is dropped, so an instance
   is a guess, and it is meant only as vocabulary for a candidate that is
   validated against the clauses.  So a caller that only adds it to a
   hypothesis space cannot change the meaning of any verdict.  Syntactic and
   first-order: a fact stated through a [let], or about a term with a second
   variable, is not recognised (and nothing is returned for it).

   Why.  A goal that needs [ps(x) = 2 \/ ps(x) = 4 \/ ps(x) = 8] of an
   unknown's parameter [x] gets from the ordinary extraction only the three
   equations as separate atoms, and a template that starts from conjunctions
   reaches the three-way disjunction only after growing its disjunct count,
   which over about ten unknowns it does not do within the iterations a run
   has.  Offering the disjunction itself as one atom targets this shape
   instead of widening every unknown's template. *)

type fact = {
  var : Ident.tvar;  (** the bound variable the disjunction is over *)
  sort : Sort.t;  (** its sort *)
  disj : Formula.t;  (** [t(var) = k_1 \/ ... \/ t(var) = k_n], [n >= 2] *)
}

(* the members of a finite set literal: [S] a chain of stores of [true] at
   ground indices over the constant-[false] array *)
let rec set_literal_members = function
  | Term.FunApp (T_array.AConst _, [ v ], _) when T_bool.is_false v -> Some []
  | Term.FunApp (T_array.AStore _, [ a; i; v ], _)
    when T_bool.is_true v && Set.is_empty (Term.tvs_of i) ->
      Option.map (set_literal_members a) ~f:(fun ks -> i :: ks)
  | _ -> None

(* the (variable, term, constant) equations a literal states, for terms with
   exactly one variable *)
let equations_of lit =
  let single t =
    let tvs = Term.tvs_of t in
    if Set.length tvs = 1 then Set.choose tvs else None
  in
  let ground k = Set.is_empty (Term.tvs_of k) in
  let oriented t k =
    if ground k then match single t with Some q -> [ (q, t, k) ] | None -> []
    else []
  in
  let eq t1 t2 =
    match oriented t1 t2 @ oriented t2 t1 with
    | _ :: _ as eqs -> eqs
    | [] ->
        (* a membership in a set literal: [select S t = true] *)
        let mem = function
          | Term.FunApp (T_array.ASelect _, [ s; t ], _) -> (
              match (single t, set_literal_members s) with
              | Some q, Some (_ :: _ :: _ as ks) ->
                  List.map ks ~f:(fun k -> (q, t, k))
              | _ -> [])
          | _ -> []
        in
        if T_bool.is_true t2 then mem t1
        else if T_bool.is_true t1 then mem t2
        else []
  in
  match lit with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _),
        _ ) ->
      eq t1 t2
  | _ -> []

(* the facts of one quantified subformula, its body already read as a
   universal's (a disjunction in negation normal form) *)
let facts_of_universal bounds body =
  let eqs =
    List.concat_map ~f:equations_of
      (Formula.disjuncts_list_of (Formula.nnf_of body))
  in
  List.concat_map bounds ~f:(fun (q, sort) ->
      let eqs =
        List.filter_map eqs ~f:(fun (v, t, k) ->
            if Ident.tvar_equal v q then Some (t, k) else None)
      in
      (* grouped by the term, compared by its printed form: two spellings of
         one term that print differently stay apart, which only splits a
         fact *)
      List.filter_map
        (List.Assoc.sort_and_group eqs ~compare:(fun t1 t2 ->
             String.compare (Term.str_of t1) (Term.str_of t2)))
        ~f:(fun (t, ks) ->
          let ks =
            List.dedup_and_sort ks ~compare:(fun k1 k2 ->
                String.compare (Term.str_of k1) (Term.str_of k2))
          in
          if List.length ks < 2 then None
          else
            Some
              {
                var = q;
                sort;
                disj = Formula.or_of (List.map ks ~f:(Formula.eq t));
              }))

(* the facts of every quantified subformula of [phi] that applies no
   unknown: a clause's own binder, which does, quantifies the clause's
   variables, and its disjuncts are the clause's literals rather than a fact
   it is given *)
let rec facts_of acc phi =
  let own bounds body =
    if Set.is_empty (Formula.pvs_of phi) then facts_of_universal bounds body
    else []
  in
  match phi with
  | Formula.Atom _ -> acc
  | Formula.UnaryOp (_, phi, _) -> facts_of acc phi
  | Formula.BinaryOp (_, phi1, phi2, _) -> facts_of (facts_of acc phi1) phi2
  | Formula.LetFormula (_, _, _, phi, _) -> facts_of acc phi
  | Formula.Bind (Formula.Forall, bounds, body, _) ->
      facts_of (own bounds body @ acc) body
  | Formula.Bind (Formula.Exists, bounds, body, _) ->
      facts_of (own bounds (Formula.mk_neg body) @ acc) body
  | Formula.Bind (_, _, body, _) -> facts_of acc body
  | _ -> acc

(** [facts phis]: the facts of every quantified subformula of [phis], each once
    (by its printed disjunction over a canonical variable name, so the same fact
    stated by many clauses with their own bound names is one). *)
let facts (phis : Formula.t list) : fact list =
  let canon f =
    let v = Ident.Tvar "#mf" in
    Formula.str_of
      (Formula.subst (Map.Poly.singleton f.var (Term.mk_var v f.sort)) f.disj)
    ^ " : " ^ Term.str_of_sort f.sort
  in
  List.fold phis ~init:[] ~f:facts_of
  |> List.dedup_and_sort ~compare:(fun f1 f2 ->
      String.compare (canon f1) (canon f2))

(** [instances facts params]: for each fact and each parameter [(x, s)] of
    [params] whose sort is the fact's bound sort, the parameter's position and
    the fact's disjunction with [x] in place of the bound variable. At most
    [List.length facts * List.length params] results, one per (fact, parameter).
*)
let instances (facts : fact list) (params : sort_env_list) :
    (int * Formula.t) list =
  List.concat_map facts ~f:(fun f ->
      List.filter_mapi params ~f:(fun i (x, s) ->
          if Stdlib.( = ) s f.sort then
            Some
              ( i,
                Formula.subst
                  (Map.Poly.singleton f.var (Term.mk_var x s))
                  f.disj )
          else None))
