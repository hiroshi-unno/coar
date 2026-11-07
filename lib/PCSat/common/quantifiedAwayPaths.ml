open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* Components of an unknown's arguments that every clause requiring the
   unknown quantifies away, and a test that keeps a hypothesis-space term or
   qualifier off them.

   A *path* [(i, [s1; ...; sk])] names the component of the [i]-th argument
   reached by the selectors [s1], ..., [sk] in turn, each of a datatype with a
   single constructor (so the component exists in every value); the empty
   selector list names the whole argument.

   Definition.  A path [(i, pi)] of an ordinary predicate [P] is *quantified
   away* when, in every clause of the problem where [P] occurs positively, at
   every such occurrence the component [pi] of the [i]-th argument is a
   universally quantified variable of the clause that occurs nowhere else in
   the clause (or lies inside such a variable).  This is the shape of a
   requirement [forall q. P(..., C(..., q, ...), ...)]: a Rust `requires`
   stated for every final value of a mutable reference.

   Lemma.  If [P] is ordinary and [(i, pi)] is quantified away, then whenever
   the problem has a solution [S], it has one that agrees with [S] except that
   [P] is [P'(x) := forall y. S(P)(x[pi := y])], which does not depend on the
   component [pi].
   Proof.  [P'] implies [S(P)] (instantiate [y] at the component itself), so
   every clause where [P] occurs only negatively still holds.  At a positive
   occurrence the clause holds for every value of the variable [q] at [pi], and
   [q] occurs nowhere else, so its body (which does not mention [q]) implies
   [S(P)] at every value of [q], i.e. [P'] at the occurrence's arguments; a
   negative occurrence of [P] in the same clause is weakened by [P'] => [S(P)]
   in the right direction.  The argument is per model of the background theory,
   so it holds under the forall-models reading of satisfiability.  It needs
   [P] ordinary: a well-founded, functional or other kinded unknown carries a
   condition on its solution that strengthening need not preserve.

   The self-guarded relaxation ([~self_guarded] of [of_problem]) also
   accepts a positive occurrence where the component's variable occurs
   elsewhere only in disjuncts of the pure part that mention no other
   variable: a condition [G] on the component alone, such as the range of a
   machine integer that a frontend states for every integer field of every
   variable.  The lemma then holds with [P'(x) := forall y. G(y) =>
   S(P)(x[pi := y])] for [G] the conjunction of every such condition met,
   PROVIDED every negative occurrence of [P] also has [G] at its component
   (as a disjunct of its clause): at a negative occurrence whose component
   [G] does not cover -- the variable a premise quantifier was skolemised to,
   say -- [P'] need not imply [S(P)], and nothing guarantees a solution
   independent of the component.  That proviso is not checked, so in this
   mode the restriction is a heuristic: it may leave every solution outside
   the space (costing an answer, never soundness).

   So keeping a template's atoms off such components restricts the hypothesis
   space without leaving the problem's solutions behind *semantically*.  It is
   a restriction of the candidates only: every candidate is still validated
   against the original clauses, and refutation does not pass through the
   candidates, so it cannot make a verdict wrong; whether the restricted
   template still expresses [P'] is a separate question, which is why the
   caller keeps it behind a switch.

   What the analysis reads.  Clauses in the first-order language, with each
   disjunct [y != s] of the pure part ([y] a clause variable not in [s]) used
   as the definition [y := s] first, since normalisation may move an argument
   into such an equation.  A positive occurrence whose argument is not read
   this way (a selector application, a function unknown's application, an
   arbitrary term) makes the path *not* quantified away.  A problem given as
   formulas rather than clauses yields nothing. *)

type path = int * string list

let rec is_prefix ~prefix l =
  match (prefix, l) with
  | [], _ -> true
  | a :: prefix', b :: l' -> String.equal a b && is_prefix ~prefix:prefix' l'
  | _ :: _, [] -> false

let max_depth = 6

(* Every path through single-constructor datatypes of [sort], the empty one
   included, at most [max_depth] selectors long; a datatype met again on the
   way stops the descent there. *)
let selector_paths_of_sort sort =
  let rec go depth seen sort =
    match sort with
    | T_dt.SDT dt when depth < max_depth -> (
        let name = Datatype.name_of dt in
        if List.mem seen name ~equal:String.equal then [ [] ]
        else
          match Datatype.conses_of dt with
          | [ cons ] ->
              let sels =
                List.map ~f:Datatype.name_of_sel (Datatype.sels_of_cons cons)
              in
              let sorts = Datatype.sorts_of_cons dt cons in
              []
              :: List.concat
                   (List.map2_exn sels sorts ~f:(fun sel s ->
                        List.map
                          (go (depth + 1) (name :: seen) s)
                          ~f:(fun p -> sel :: p)))
          | _ -> [ [] ])
    | _ -> [ [] ]
  in
  go 0 [] sort

(* The disjunct [y != s] read as a definition of [y], if it is one. *)
let definition_of uni_senv phi =
  let def t1 t2 =
    match (t1, t2) with
    | Term.Var (y, _, _), s
      when Map.Poly.mem uni_senv y && not (Set.mem (Term.tvs_of s) y) ->
        Some (y, s)
    | s, Term.Var (y, _, _)
      when Map.Poly.mem uni_senv y && not (Set.mem (Term.tvs_of s) y) ->
        Some (y, s)
    | _ -> None
  in
  match phi with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _) ->
      def t1 t2
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
        _ ) ->
      def t1 t2
  | _ -> None

(* Substitutes every definition among the pure part's disjuncts, one at a
   time, until none is left.  The result denotes the same universal closure:
   [forall y. y != s \/ R(y)] is [R(s)]. *)
let eliminate_definitions (uni_senv, ps, ns, phi) =
  let rec go ps ns disjs =
    match
      List.find_mapi disjs ~f:(fun k d ->
          Option.map (definition_of uni_senv d) ~f:(fun def -> (k, def)))
    with
    | None -> (ps, ns, disjs)
    | Some (k, (y, s)) ->
        let sub = Map.Poly.singleton y s in
        go
          (List.map ps ~f:(Atom.subst sub))
          (List.map ns ~f:(Atom.subst sub))
          (List.filteri disjs ~f:(fun k' _ -> k' <> k)
          |> List.map ~f:(Formula.subst sub))
  in
  go (Set.to_list ps) (Set.to_list ns) (Formula.disjuncts_list_of phi)

(* The term reached from [t] along [pi], through constructor applications:
   [`At (t', rebuild)] when the whole path was consumed, [`Inside (y,
   rebuild)] when a variable [y] was met first, where [rebuild u] is [t] with
   the reached subterm (the variable, in the second case) replaced by [u];
   [`Stuck] otherwise. *)
let rec descend t pi =
  match pi with
  | [] -> `At (t, Fn.id)
  | sel :: rest -> (
      match t with
      | Term.Var (y, _, _) -> `Inside (y, Fn.id)
      | Term.FunApp ((T_dt.DTCons (cname, _, dt) as fsym), args, info) -> (
          match Datatype.look_up_cons dt cname with
          | None -> `Stuck
          | Some cons -> (
              let sels =
                List.map ~f:Datatype.name_of_sel (Datatype.sels_of_cons cons)
              in
              match List.findi sels ~f:(fun _ s -> String.equal s sel) with
              | None -> `Stuck
              | Some (k, _) -> (
                  let wrap rebuild u =
                    Term.mk_fsym_app ~info fsym
                      (List.mapi args ~f:(fun k' a ->
                           if k' = k then rebuild u else a))
                  in
                  match descend (List.nth_exn args k) rest with
                  | `At (t', rebuild) -> `At (t', wrap rebuild)
                  | `Inside (y, rebuild) -> `Inside (y, wrap rebuild)
                  | `Stuck -> `Stuck)))
      | _ -> `Stuck)

let tvs_of_clause (ps, ns, disjs) =
  Set.Poly.union_list
    (List.map ps ~f:Atom.tvs_of @ List.map ns ~f:Atom.tvs_of
    @ List.map disjs ~f:Formula.tvs_of)

(* How the component [pi] of argument [i] stands in the clause [(uni_senv,
   (ps, ns, disjs))] whose [k]-th positive atom has arguments [args]:
   [`Free] when it is a clause variable (or inside one) that occurs nowhere
   else in the clause; [`Self_guarded] when its other occurrences are all in
   disjuncts of the pure part that mention no other variable (a condition on
   the component alone, such as a machine-integer range on each of its
   fields); [`Bound] otherwise. *)
let status_at uni_senv (ps, ns, disjs) k args i pi =
  let check y rebuild =
    if not (Map.Poly.mem uni_senv y) then `Bound
    else
      let marker = Term.mk_var (Ident.mk_fresh_tvar ()) T_int.SInt in
      let args' =
        List.mapi args ~f:(fun i' a -> if i' = i then rebuild marker else a)
      in
      let ps' =
        List.mapi ps ~f:(fun k' atm ->
            if k' = k then
              let pvar, sorts, _, info = Atom.let_pvar_app atm in
              Atom.mk_app ~info (Predicate.Var (pvar, sorts)) args'
            else atm)
      in
      if not (Set.mem (tvs_of_clause (ps', ns, disjs)) y) then `Free
      else
        let guards, rest =
          List.partition_tf disjs ~f:(fun d ->
              Set.equal (Formula.tvs_of d) (Set.Poly.singleton y))
        in
        if List.is_empty guards then `Bound
        else if Set.mem (tvs_of_clause (ps', ns, rest)) y then `Bound
        else `Self_guarded
  in
  match descend (List.nth_exn args i) pi with
  | `At (Term.Var (q, _, _), rebuild) -> check q rebuild
  | `Inside (y, rebuild) ->
      (* every component of [y] is reached only through this position *)
      check y rebuild
  | _ -> `Bound

(* The quantified-away paths (self-guarded ones too when [self_guarded]) of
   every ordinary predicate of [pcsp] that occurs positively somewhere,
   prefix-minimal (a path below a listed one is not
   listed).  Keys are the predicates' names as type variables. *)
let of_problem ~self_guarded pcsp : (Ident.tvar, path list) Map.Poly.t =
  match PCSP.Problem.clauses_of_opt pcsp with
  | None -> Map.Poly.empty
  | Some cls ->
      let exi_senv = PCSP.Problem.senv_of pcsp in
      let clauses =
        List.map
          (Set.to_list (ClauseSet.to_old_clause_set exi_senv cls))
          ~f:(fun ((uni_senv, _, _, _) as c) ->
            (uni_senv, eliminate_definitions c))
      in
      Map.Poly.filter_mapi exi_senv ~f:(fun ~key:tvar ~data:sort ->
          let ordinary =
            try Kind.is_ord (PCSP.Problem.kind_of pcsp tvar)
            with exn_ when not (Common.Timer.is_async exn_) -> false
          in
          if not ordinary then None
          else
            let pvar = Ident.tvar_to_pvar tvar in
            let occurrences =
              List.concat_map clauses ~f:(fun (uni_senv, ((ps, _, _) as c)) ->
                  List.filter_mapi ps ~f:(fun k atm ->
                      match atm with
                      | Atom.App (Predicate.Var (pv, _), args, _)
                        when Ident.pvar_equal pv pvar ->
                          Some (uni_senv, c, k, args)
                      | _ -> None))
            in
            if List.is_empty occurrences then None
            else
              let sorts =
                List.map ~f:Logic.ExtTerm.to_old_sort @@ Logic.Sort.args_of sort
              in
              let candidates =
                List.concat_mapi sorts ~f:(fun i s ->
                    List.map (selector_paths_of_sort s) ~f:(fun p -> (i, p)))
              in
              let away =
                List.filter candidates ~f:(fun (i, pi) ->
                    List.for_all occurrences ~f:(fun (uni_senv, c, k, args) ->
                        List.length args > i
                        &&
                        match status_at uni_senv c k args i pi with
                        | `Free -> true
                        | `Self_guarded -> self_guarded
                        | `Bound -> false))
              in
              let minimal =
                List.filter away ~f:(fun (i, q) ->
                    not
                    @@ List.exists away ~f:(fun (i', p) ->
                        i = i'
                        && List.length p < List.length q
                        && is_prefix ~prefix:p q))
              in
              if List.is_empty minimal then None else Some minimal)

(* The selector chain [t] is, read root-first from a variable. *)
let rec chain_of = function
  | Term.Var (x, _, _) -> Some (x, [])
  | Term.FunApp (T_dt.DTSel (sel, _, _), [ t ], _) ->
      Option.map (chain_of t) ~f:(fun (x, p) -> (x, p @ [ sel ]))
  | _ -> None

(* Whether [t] reads a quantified-away component: some occurrence of a
   parameter [params.(i)] sits under a selector chain [p] that is a prefix of,
   or extends, a listed path of argument [i].  A chain that stops above a
   listed path (the whole argument, say) counts, since an atom over the
   whole value constrains the component too. *)
let term_touches params (paths : path list) t =
  let index x =
    List.findi params ~f:(fun _ (y, _) -> Ident.tvar_equal x y)
    |> Option.map ~f:fst
  in
  let touches i p =
    List.exists paths ~f:(fun (i', q) ->
        i = i' && (is_prefix ~prefix:p q || is_prefix ~prefix:q p))
  in
  let rec go t =
    match chain_of t with
    | Some (x, p) -> (
        match index x with Some i -> touches i p | None -> false)
    | None -> (
        match t with
        | Term.FunApp (T_bool.Formula phi, _, _) ->
            Set.exists (Formula.terms_of phi) ~f:go
        | Term.FunApp (_, args, _) -> List.exists args ~f:go
        | _ ->
            (* a term this walk does not take apart: read by its variables *)
            Set.exists (Term.tvs_of t) ~f:(fun x ->
                match index x with Some i -> touches i [] | None -> false))
  in
  go t

let formula_touches params paths phi =
  Set.exists (Formula.terms_of phi) ~f:(term_touches params paths)
