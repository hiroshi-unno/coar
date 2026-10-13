open Core
open Common.Ext
open Ast.LogicOld

(* Two exact rewrites over integer linear arithmetic, used where a formula is
   handed to an SMT solver that decides it faster once an integer's range or
   value is visible at the top level.

   [norm_term t] rewrites every integer arithmetic subterm of [t] into a flat
   sum [a_1 x_1 + ... + a_k x_k + b_1 u_1 + ... + c], where the [x_i] are
   variables, the [u_i] the maximal subterms that are not integer arithmetic
   (normalised in turn) and [c] a literal.  It uses only the ring laws of the
   integers, so [t] and [norm_term t] have the same value in every model.  Its
   purpose is size: substituting [x := x - 1] into a term that already reads
   [x - 1] gives [x - 2] rather than a term one level deeper, so a chain of
   such substitutions stays linear in size.

   [implied_bounds ~pos phi] maps free integer variables to an interval
   [(lo, hi)] (each end optional, both inclusive) that every model of [phi]
   (with [pos], or of [not phi] without) puts the variable in.  It is read off
   the formula structurally: a literal comparing [x + c] with a literal (one
   variable, coefficient 1 or -1) bounds [x]; a conjunction bounds by the
   intersection of its sides' intervals; a disjunction by the hull of both
   sides', and only a variable both sides bound; a quantifier keeps what its
   body implies of the variables it does not bind.  Each rule is sound, so
   [phi] implies the conjunction [bounds_formula] of what is returned, and
   [phi] is equivalent to [bounds_formula /\ phi]: that is [hoist], which
   puts what every disjunct of a deep disjunction implies at the top, where a
   preprocessing step that reads only top-level conjuncts sees it. *)

(** an integer term as [(vars, opaque, c)]: the sum of [a * x] over [vars], of
    [b * u] over [opaque] (in order of first occurrence, unmerged) and [c] *)
let rec lin_of (t : Term.t) =
  match t with
  | Term.Var (x, T_int.SInt, _) -> (Map.Poly.singleton x Z.one, [], Z.zero)
  | Term.FunApp (T_int.Int c, [], _) -> (Map.Poly.empty, [], c)
  | Term.FunApp (T_int.Add, [ t1; t2 ], _) -> comb Z.one t1 Z.one t2
  | Term.FunApp (T_int.Sub, [ t1; t2 ], _) -> comb Z.one t1 Z.minus_one t2
  | Term.FunApp (T_int.Neg, [ t1 ], _) -> scale Z.minus_one (lin_of t1)
  | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int a, [], _); t1 ], _)
  | Term.FunApp (T_int.Mul, [ t1; Term.FunApp (T_int.Int a, [], _) ], _) ->
      scale a (lin_of t1)
  | t -> (Map.Poly.empty, [ (Z.one, norm_term t) ], Z.zero)

and scale a (m, us, c) =
  ( Map.Poly.map m ~f:(Z.mul a),
    List.map us ~f:(fun (b, u) -> (Z.mul a b, u)),
    Z.mul a c )

and comb a1 t1 a2 t2 =
  let m1, us1, c1 = scale a1 (lin_of t1) in
  let m2, us2, c2 = scale a2 (lin_of t2) in
  ( Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
      | `Left a | `Right a -> Some a | `Both (a, b) -> Some (Z.add a b)),
    us1 @ us2,
    Z.add c1 c2 )

and rebuild (m, us, c) =
  let mono a t =
    if Z.equal a Z.one then t
    else if Z.equal a Z.minus_one then T_int.mk_neg t
    else T_int.mk_mul (T_int.mk_int a) t
  in
  let parts =
    List.filter_map (Map.Poly.to_alist m) ~f:(fun (x, a) ->
        if Z.equal a Z.zero then None
        else Some (mono a (Term.mk_var x T_int.SInt)))
    @ List.filter_map us ~f:(fun (b, u) ->
        if Z.equal b Z.zero then None else Some (mono b u))
  in
  match parts with
  | [] -> T_int.mk_int c
  | p :: ps ->
      let s = T_int.mk_sum p ps in
      if Z.equal c Z.zero then s else T_int.mk_add s (T_int.mk_int c)

(** [t] with each integer arithmetic subterm a flat sum; see the head *)
and norm_term (t : Term.t) =
  match t with
  | Term.FunApp ((T_int.Add | T_int.Sub | T_int.Neg), _, _)
  | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int _, [], _); _ ], _)
  | Term.FunApp (T_int.Mul, [ _; Term.FunApp (T_int.Int _, [], _) ], _) ->
      rebuild (lin_of t)
  | Term.FunApp (T_bool.Formula _, _, _) -> t
  | Term.FunApp (sym, args, info) ->
      Term.mk_fsym_app ~info sym (List.map args ~f:norm_term)
  | Term.Var _ | Term.LetTerm _ -> t

let norm_atom (a : Atom.t) =
  match a with
  | Atom.App (pred, args, info) -> Atom.mk_app ~info pred (List.map args ~f:norm_term)
  | Atom.True _ | Atom.False _ -> a

(** [phi] with [norm_term] applied to every atom's arguments *)
let rec norm_formula (phi : Formula.t) =
  match phi with
  | Formula.Atom (a, info) -> Formula.mk_atom ~info (norm_atom a)
  | Formula.UnaryOp (op, p, info) -> Formula.mk_unop ~info op (norm_formula p)
  | Formula.BinaryOp (op, p1, p2, info) ->
      Formula.mk_binop ~info op (norm_formula p1) (norm_formula p2)
  | Formula.Bind (b, bounds, p, info) -> Formula.mk_bind ~info b bounds (norm_formula p)
  | Formula.LetRec _ | Formula.LetFormula _ -> phi

(* intervals: [(lo, hi)], both inclusive, [None] for unbounded *)
let meet (l1, h1) (l2, h2) =
  ( (match (l1, l2) with
    | Some a, Some b -> Some (Z.max a b)
    | Some a, None | None, Some a -> Some a
    | None, None -> None),
    match (h1, h2) with
    | Some a, Some b -> Some (Z.min a b)
    | Some a, None | None, Some a -> Some a
    | None, None -> None )

let hull (l1, h1) (l2, h2) =
  ( (match (l1, l2) with Some a, Some b -> Some (Z.min a b) | _ -> None),
    match (h1, h2) with Some a, Some b -> Some (Z.max a b) | _ -> None )

let meet_maps m1 m2 =
  Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
    | `Left i | `Right i -> Some i | `Both (i, j) -> Some (meet i j))

let hull_maps m1 m2 =
  Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
    | `Left _ | `Right _ -> None
    | `Both (i, j) -> (
        match hull i j with None, None -> None | iv -> Some iv))

(** the interval a literal ([pos] for its polarity) puts a single variable in *)
let literal_bound pos (atm : Atom.t) =
  match atm with
  | Atom.App (Predicate.Psym psym, [ t1; t2 ], _) -> (
      (* the difference [t1 - t2] as [a x + c] with [a] = 1 or -1 *)
      let m, us, c = comb Z.one t1 Z.minus_one t2 in
      let m = Map.Poly.filter m ~f:(fun a -> not (Z.equal a Z.zero)) in
      match (Map.Poly.to_alist m, us) with
      | [ (x, a) ], [] when Z.equal (Z.abs a) Z.one -> (
          (* [e = a x + c]; the literal says [e op 0] *)
          let ge0 = (Some (Z.neg c), None) (* a x >= -c *) in
          let le0 = (None, Some (Z.neg c)) (* a x <= -c *) in
          let rel =
            match (psym, pos) with
            | T_int.Geq, true | T_int.Lt, false -> Some ge0
            | T_int.Leq, true | T_int.Gt, false -> Some le0
            | T_int.Gt, true | T_int.Leq, false ->
                Some (Some Z.(succ (neg c)), None)
            | T_int.Lt, true | T_int.Geq, false ->
                Some (None, Some Z.(pred (neg c)))
            | T_bool.Eq, true -> Some (meet ge0 le0)
            | T_bool.Neq, false -> Some (meet ge0 le0)
            | _ -> None
          in
          (* [rel] bounds [a x]; for [a = -1] flip it onto [x] *)
          Option.map rel ~f:(fun (lo, hi) ->
              let iv =
                if Z.equal a Z.one then (lo, hi)
                else (Option.map hi ~f:Z.neg, Option.map lo ~f:Z.neg)
              in
              Map.Poly.singleton x iv))
      | _ -> None)
  | _ -> None

(** see the head; [pos = false] reads [not phi] *)
let rec implied_bounds ~pos (phi : Formula.t) =
  match phi with
  | Formula.Atom (atm, _) ->
      Option.value ~default:Map.Poly.empty (literal_bound pos atm)
  | Formula.UnaryOp (Formula.Not, p, _) -> implied_bounds ~pos:(not pos) p
  | Formula.BinaryOp (Formula.And, p1, p2, _) ->
      let b1 = implied_bounds ~pos p1 and b2 = implied_bounds ~pos p2 in
      if pos then meet_maps b1 b2 else hull_maps b1 b2
  | Formula.BinaryOp (Formula.Or, p1, p2, _) ->
      let b1 = implied_bounds ~pos p1 and b2 = implied_bounds ~pos p2 in
      if pos then hull_maps b1 b2 else meet_maps b1 b2
  | Formula.Bind (_, bounds, p, _) ->
      let bound = Set.Poly.of_list (List.map bounds ~f:fst) in
      Map.Poly.filter_keys (implied_bounds ~pos p) ~f:(fun x ->
          not (Set.mem bound x))
  | _ -> Map.Poly.empty

(** the bounds as atoms [lo <= x], [x <= hi] *)
let bounds_atoms m =
  List.concat_map (Map.Poly.to_alist m) ~f:(fun (x, (lo, hi)) ->
      let v = Term.mk_var x T_int.SInt in
      Option.to_list
        (Option.map lo ~f:(fun l -> Formula.leq (T_int.mk_int l) v))
      @ Option.to_list
          (Option.map hi ~f:(fun h -> Formula.leq v (T_int.mk_int h))))

(** [hoist phi] is [B /\ phi] for [B] the conjunction of [implied_bounds ~pos:true
    phi], hence equivalent to [phi]; and the list of atoms of [B] *)
let hoist phi =
  let atoms = bounds_atoms (implied_bounds ~pos:true phi) in
  (Formula.and_of (atoms @ [ phi ]), atoms)

(** [hoist_valid phi] is [not B \/ phi] for [B] what [not phi] implies: valid
    exactly when [phi] is, and its negation has [B]'s atoms as top-level
    conjuncts *)
let hoist_valid phi =
  let atoms = bounds_atoms (implied_bounds ~pos:false phi) in
  (Formula.or_of (List.map atoms ~f:Formula.mk_neg @ [ phi ]), atoms)
