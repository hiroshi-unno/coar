open Core
open Common.Ext
open LogicOld

(* Which argument positions of an unknown the clauses RELATE, read off the
   clauses alone, and the filter that offers a generated qualifier only over
   positions so related.

   The relation.  Let [P] be an unknown and [i <> j] two of its positions.
   In a clause [C], call a variable a TERMINAL when it occurs in an argument of
   an application of an unknown in [C], and LOCAL otherwise (a variable of the
   pure part alone, or a name a binder or a let of the pure part introduces).
   The EDGES of [C] are variable sets:

     (a) the variables of one atom of the pure part -- under any quantifier or
         connective, the binders' variables included, so that a premise
         [forall q. s[q] = t[q]] is one edge over [s], [q], [t] -- where an
         atom comparing a Boolean term with a constant ([b = true], [b] a
         let-bound name or an embedded formula) is read as the formula [b]
         denotes, so its atoms are the edges, and a let-bound name inside an
         atom stands for its definition's variables; a let binding itself is
         no edge, so a let that names a large conjunction joins nothing;
     (b) the variables of one argument term [s_k] of an application
         [Q(s1, ..., sm)] in [C];
     (c) the variables of two argument terms [s_k], [s_l] of such an
         application with [(Q, k) ~ (Q, l)] already; [Q] may be [P] itself,
         and the application may be the very one the rule is applied to;

   and, with [~whole_clause], also
     (d) the variables of the pure part as a whole.

   Two terminals [v], [w] are LINKED in [C] when one edge holds both, or two
   edges hold them that are joined by a path of edges through LOCAL variables
   only.  A path never passes through a terminal: a variable passed to an
   unknown and read in many atoms (a relation handed unchanged to every
   unknown, a counter compared with everything) would otherwise link every
   two positions it meets, and does not here.  [(P, i) ~ (P, j)] is the least
   relation such that, for an application [P(t1, ..., tn)] in a clause [C], a
   variable of [t_i] and a variable of [t_j] are linked in [C] (a variable
   both terms share is linked with itself).  A position whose argument is
   ground at an application is related to nothing through that application.
   Bound names are not renamed apart, so two quantifiers of one clause that
   reuse a name join through it: that can only relate more.

   The filter.  A qualifier generated over a predicate's parameters [x1 ...
   xn] mentions a set [S] of them (through the terms reached from each by
   selectors, reads, lengths and suffixes).  It is KEPT when [|S| <= 1], or
   when the graph on [S] whose edges are the related pairs is connected; it is
   dropped otherwise.  The filter is applied by its callers to the families
   that are built over every combination of parameters (equalities between
   datatype, sequence, array and opaque-sort terms, testers of reached terms,
   guarded payload and selector-path comparisons, sequence suffix equations),
   never to qualifiers extracted from the clauses.

   What this is and is not.  Dropping a qualifier only narrows the hypothesis
   space, so no verdict changes from wrong to right or right to wrong because
   of it; what can change is that a solution is no longer expressible.  That
   can happen: a relation the clauses never state through one atom
   can still be needed.  Two positions linked only through a third argument
   ([x <= w] and [w <= y], with [w] passed to an unknown too) are not
   related, although a qualifier over all three is kept when each pair on a
   path is.  Two counters moved in lock step ([x' = x + 1] and
   [y' = y + 1], two atoms) and a goal [x >= 10 /\ y < 10] (two atoms) need
   [x = y], and no atom relates [x] and [y]; with [~whole_clause] rule (d)
   relates them through the step's pure part.  Neither form relates two
   positions that meet only in the disjunction of applications of unknowns:
   with [P(x, y) <- A(x) /\ B(y)], [P(x, y) <- C(x) /\ D(y)] and a goal
   [P(x, y) /\ E(x) /\ F(y) -> false], a solution of [P] can need a relation
   between [x] and [y] that no rule here derives.  The integer part of a
   template is not filtered, so integer relations between positions are
   unaffected. *)

type t = (Ident.pvar, (int * int) Set.Poly.t) Map.Poly.t

(* a union-find over variable names, per clause *)
module UF = struct
  type t = (Ident.tvar, Ident.tvar) Hashtbl.t

  let create () : t = Hashtbl.Poly.create ()

  let rec find (uf : t) x =
    match Hashtbl.find uf x with
    | None -> x
    | Some y when Ident.tvar_equal x y -> x
    | Some y ->
        let r = find uf y in
        Hashtbl.set uf ~key:x ~data:r;
        r

  let union uf x y =
    let rx = find uf x and ry = find uf y in
    if not (Ident.tvar_equal rx ry) then Hashtbl.set uf ~key:rx ~data:ry

  let link uf vs =
    match Set.to_list vs with
    | [] -> ()
    | v :: rest -> List.iter rest ~f:(union uf v)
end

(* the edges of rule (a): one per atom, with every let-bound name
   standing for its definition (see the header).  [lets] maps a let-bound name
   to the variables its definition mentions, names bound by enclosing lets
   expanded, and to the edges of the definition read as a formula. *)
let expand_lets lets vs =
  Set.fold vs ~init:Set.Poly.empty ~f:(fun acc v ->
      match Map.Poly.find lets v with
      | Some (vs', _) -> Set.union acc vs'
      | None -> Set.add acc v)

let rec pure_edges ?(lets = Map.Poly.empty) acc phi =
  let expand = expand_lets lets in
  match phi with
  | Formula.Atom (Atom.App (Predicate.Var (Ident.Pvar n, []), [], _), _)
    when Map.Poly.mem lets (Ident.Tvar n) ->
      let _, edges = Map.Poly.find_exn lets (Ident.Tvar n) in
      Lazy.force edges @ acc
  | Formula.Atom
      (Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ t1; t2 ], _), _)
    when Term.is_bool_sort (Term.sort_of t1)
         && (Set.is_empty (Term.tvs_of t1) || Set.is_empty (Term.tvs_of t2)) ->
      (* a Boolean term compared with a constant, [b = true]: the edges of
         the formula [b] stands for *)
      let t = if Set.is_empty (Term.tvs_of t1) then t2 else t1 in
      bool_term_edges ~lets t @ acc
  | Formula.Atom (atom, _) -> expand (Atom.tvs_of atom) :: acc
  | Formula.UnaryOp (_, phi, _) -> pure_edges ~lets acc phi
  | Formula.BinaryOp (_, phi1, phi2, _) ->
      pure_edges ~lets (pure_edges ~lets acc phi1) phi2
  | Formula.Bind (_, senv, phi, _) ->
      let lets =
        Map.Poly.filter_keys lets ~f:(fun v ->
            not (List.Assoc.mem senv ~equal:Ident.tvar_equal v))
      in
      pure_edges ~lets acc phi
  | Formula.LetRec (funcs, phi, _) ->
      List.fold funcs ~init:(pure_edges ~lets acc phi) ~f:(fun acc def ->
          pure_edges ~lets acc def.body)
  | Formula.LetFormula (x, sort, def, body, _) ->
      let vs = expand (Term.tvs_of def) in
      let edges =
        lazy
          (if Term.is_bool_sort sort then
             pure_edges ~lets [] (Formula.of_bool_term def)
           else [ vs ])
      in
      pure_edges ~lets:(Map.Poly.set lets ~key:x ~data:(vs, edges)) acc body

(* the edges of a Boolean term read as a formula: a let-bound name is its
   definition's edges, an embedded formula its own, anything else one edge *)
and bool_term_edges ~lets = function
  | Term.Var (x, _, _) when Map.Poly.mem lets x ->
      Lazy.force (snd (Map.Poly.find_exn lets x))
  | Term.FunApp (T_bool.Formula phi, [], _) -> pure_edges ~lets [] phi
  | t -> [ expand_lets lets (Term.tvs_of t) ]

let pure_vars phi =
  List.fold (pure_edges [] phi) ~init:Set.Poly.empty ~f:Set.union

(* the applications of unknowns in a clause, with their argument variables *)
let apps_of ((_, ps, ns, _) : ClauseOld.t) =
  List.filter_map
    (Set.to_list (Set.union ps ns))
    ~f:(function
      | Atom.App (Predicate.Var (p, _), ts, _) ->
          Some (p, Array.of_list (List.map ts ~f:Term.tvs_of))
      | _ -> None)

let related_of (rel : t) p =
  match Map.Poly.find rel p with Some s -> s | None -> Set.Poly.empty

let compute ?(whole_clause = false) (clauses : ClauseOld.t list) : t =
  let prepared =
    List.map clauses ~f:(fun ((_, _, _, phi) as c) ->
        let edges = pure_edges [] phi in
        let edges =
          if whole_clause then
            List.fold edges ~init:Set.Poly.empty ~f:Set.union :: edges
          else edges
        in
        let apps = apps_of c in
        let terminals =
          List.fold apps ~init:Set.Poly.empty ~f:(fun acc (_, args) ->
              Array.fold args ~init:acc ~f:Set.union)
        in
        (* the local variables of each pure edge, unioned: an edge's group is
           the component of its locals, or its own when it has none *)
        let uf = UF.create () in
        List.iter edges ~f:(fun e -> UF.link uf (Set.diff e terminals));
        let next = ref 0 in
        let groups = Hashtbl.Poly.create () in
        let add_group e =
          let locals = Set.diff e terminals in
          let g =
            match Set.choose locals with
            | Some v -> `Local (UF.find uf v)
            | None ->
                incr next;
                `Own !next
          in
          Set.iter (Set.inter e terminals) ~f:(fun v ->
              Hashtbl.update groups v ~f:(function
                | None -> Set.Poly.singleton g
                | Some gs -> Set.add gs g))
        in
        List.iter edges ~f:add_group;
        (* rule (b): each argument term is an edge of terminals only *)
        List.iter apps ~f:(fun (_, args) -> Array.iter args ~f:add_group);
        (Hashtbl.copy groups, !next, apps))
  in
  let rec loop rel =
    let changed = ref false in
    let rel =
      List.fold prepared ~init:rel ~f:(fun rel (groups0, next0, apps) ->
          let groups = Hashtbl.copy groups0 in
          let next = ref next0 in
          let add_own e =
            incr next;
            let g = `Own !next in
            Set.iter e ~f:(fun v ->
                Hashtbl.update groups v ~f:(function
                  | None -> Set.Poly.singleton g
                  | Some gs -> Set.add gs g))
          in
          (* rule (c), with the relation as it stands *)
          List.iter apps ~f:(fun (q, args) ->
              Set.iter (related_of rel q) ~f:(fun (k, l) ->
                  if k < Array.length args && l < Array.length args then
                    add_own (Set.union args.(k) args.(l))));
          let groups_of vs =
            Set.fold vs ~init:Set.Poly.empty ~f:(fun acc v ->
                match Hashtbl.find groups v with
                | None -> acc
                | Some gs -> Set.union acc gs)
          in
          List.fold apps ~init:rel ~f:(fun rel (p, args) ->
              let gs = Array.map args ~f:groups_of in
              let n = Array.length args in
              let old = related_of rel p in
              let fresh = ref old in
              for i = 0 to n - 1 do
                for j = i + 1 to n - 1 do
                  if
                    (not (Set.mem !fresh (i, j)))
                    && not (Set.are_disjoint gs.(i) gs.(j))
                  then fresh := Set.add !fresh (i, j)
                done
              done;
              if Set.length !fresh > Set.length old then (
                changed := true;
                Map.Poly.set rel ~key:p ~data:!fresh)
              else rel))
    in
    if !changed then loop rel else rel
  in
  loop Map.Poly.empty

(* the computed relation, kept for the last clause list it was asked about
   (compared physically: every template of a problem forces one shared lazy
   list), so that the templates of one problem compute it once *)
let cache : (ClauseOld.t list * bool * t) option Atomic.t = Atomic.make None

let compute_cached ?(whole_clause = false) clauses =
  match Atomic.get cache with
  | Some (cs, w, rel) when phys_equal cs clauses && Bool.equal w whole_clause ->
      rel
  | _ ->
      let rel = compute ~whole_clause clauses in
      Atomic.set cache (Some (clauses, whole_clause, rel));
      rel

let related (rel : t) p i j =
  i = j || Set.mem (related_of rel p) (Int.min i j, Int.max i j)

(* the positions of [params] a formula mentions *)
let positions_of ~(params : sort_env_list) tvs =
  List.filter_mapi params ~f:(fun i (x, _) ->
      if Set.mem tvs x then Some i else None)

(* [S] connected under the related pairs (see the header) *)
let connected ~related = function
  | [] | [ _ ] -> true
  | p0 :: _ as ps ->
      let rec grow seen = function
        | [] -> seen
        | i :: todo ->
            let next =
              List.filter ps ~f:(fun j ->
                  (not (List.mem seen j ~equal:Int.equal)) && related i j)
            in
            grow (next @ seen) (next @ todo)
      in
      List.length (grow [ p0 ] [ p0 ]) = List.length ps

let keep_qual (rel : t) (p : Ident.pvar) ~(params : sort_env_list) phi =
  connected ~related:(related rel p) (positions_of ~params (Formula.tvs_of phi))

let keep_term (rel : t) (p : Ident.pvar) ~(params : sort_env_list) t =
  connected ~related:(related rel p) (positions_of ~params (Term.tvs_of t))

(* The units a formula over [params] is built from, for judging a solution
   against the filter: each atom outside every binder, and each maximal
   quantified subformula as a whole (a quantified qualifier is offered or
   dropped whole). *)
let rec units_of acc = function
  | Formula.Atom (atom, _) as phi -> (
      match atom with Atom.True _ | Atom.False _ -> acc | _ -> phi :: acc)
  | Formula.UnaryOp (_, phi, _) -> units_of acc phi
  | Formula.BinaryOp (_, phi1, phi2, _) -> units_of (units_of acc phi1) phi2
  | Formula.Bind _ as phi -> phi :: acc
  | Formula.LetRec (_, phi, _) -> units_of acc phi
  | Formula.LetFormula _ as phi -> phi :: acc

(* For a solution [binds] (each unknown with its parameters and its body),
   the units of each body whose parameter positions the relation does not
   connect -- those a generated qualifier could not have supplied with the
   filter on.  A unit can also have come from an extracted qualifier or the
   integer part of a template, which the filter leaves alone, so the list is
   an upper bound on what the filter removes from this solution. *)
let unrelated_units (rel : t)
    (binds : (Ident.pvar * (sort_env_list * Formula.t)) list) =
  List.map binds ~f:(fun (p, (params, phi)) ->
      let units = List.rev (units_of [] phi) in
      ( p,
        List.length units,
        List.filter units ~f:(fun u -> not (keep_qual rel p ~params u)) ))
