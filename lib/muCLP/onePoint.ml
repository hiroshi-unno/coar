(* The one-point rule on the quantifiers of a muCLP problem.

   For an integer variable [x] bound by a universal whose body has a disjunct
   [l <> r] (or [not (l = r)]) that solves as [x = e], with [x] at coefficient
   1 or -1 and [e] free of [x],

     forall x. (l <> r) \/ phi   <=>   phi[e/x]

   and dually, for an existential whose body has a conjunct [l = r] solving as
   [x = e],

     exists x. (l = r) /\ phi    <=>   phi[e/x].

   Both are equivalences of first-order logic over the integers that hold at
   every interpretation of the predicate variables (an [e] with coefficient
   +-1 is an integer whenever its free variables are), so replacing a body by
   the rewritten one leaves each predicate's body operator, and hence every
   least and greatest fixpoint and the query's validity, unchanged.

   Why it is wanted.  The transition-system translation writes a deterministic
   update [x' = x + 1] as [forall x'. x' <> x + 1 \/ P(.., x', ..)].  A
   validity checker that unfolds the body into clauses removes such a
   variable by its own equality elimination, but a strategy-based solver reads
   every universal of a least-fixpoint body as an opponent's decision and
   Skolemises it into an unknown function it then has to synthesise and
   refine, although the function is determined.

   CONTRACT.  [formula phi] is equivalent to [phi]; it removes only bound
   variables of sort [Int], keeps every other binder where it was, and
   substitutes with [Formula.subst], which is capture-avoiding.  It
   terminates: each rewrite removes one bound variable.  [problem m] applies
   [formula] to every predicate body and to the query.  [count] is the number
   of variables removed in this process so far (read by a census only). *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

let count = Atomic.make 0

(* [x = e] for an integer (dis)equation [l ~ r] in which [x] has coefficient 1
   or -1, [None] otherwise (the linear reading is [ArrayPointwise.solve_for]) *)
let solve x l r =
  if Set.mem (Term.tvs_of l) x || Set.mem (Term.tvs_of r) x then
    ArrayPointwise.solve_for x l r
  else None

(* the equation a literal states when it is false ([`Neq]) or true ([`Eq]) *)
let equation_of polarity = function
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ l; r ], _), _)
    when Stdlib.( = ) polarity `Neq ->
      Some (l, r)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ l; r ], _), _),
        _ )
    when Stdlib.( = ) polarity `Neq ->
      Some (l, r)
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ l; r ], _), _)
    when Stdlib.( = ) polarity `Eq ->
      Some (l, r)
  | _ -> None

(* one rewrite of [bounds], [parts] (the disjuncts of a universal's body or
   the conjuncts of an existential's): a bound integer variable and the part
   that fixes it, or [None] *)
let find_fixed polarity bounds parts =
  List.find_map bounds ~f:(fun (x, s) ->
      if not (Term.is_int_sort s) then None
      else
        List.find_mapi parts ~f:(fun i part ->
            match equation_of polarity part with
            | None -> None
            | Some (l, r) -> (
                match solve x l r with
                | Some e when not (Set.mem (Term.tvs_of e) x) -> Some (x, i, e)
                | _ -> None)))

let rec eliminate polarity bounds parts =
  match find_fixed polarity bounds parts with
  | None -> (bounds, parts)
  | Some (x, i, e) ->
      Atomic.incr count;
      let sub = Map.Poly.singleton x e in
      let parts =
        List.filteri parts ~f:(fun j _ -> j <> i)
        |> List.map ~f:(Formula.subst sub)
      in
      let bounds =
        List.filter bounds ~f:(fun (y, _) -> not (Stdlib.( = ) x y))
      in
      eliminate polarity bounds parts

let rec formula phi =
  match phi with
  | Formula.Atom _ -> phi
  | Formula.UnaryOp (op, phi1, info) -> Formula.mk_unop ~info op (formula phi1)
  | Formula.BinaryOp (op, phi1, phi2, info) ->
      Formula.mk_binop ~info op (formula phi1) (formula phi2)
  | Formula.Bind (Formula.Forall, bounds, body, info) ->
      let bounds, parts =
        eliminate `Neq bounds (Formula.disjuncts_list_of (formula body))
      in
      Formula.mk_forall_if_bounded ~info bounds (Formula.or_of parts)
  | Formula.Bind (Formula.Exists, bounds, body, info) ->
      let bounds, parts =
        eliminate `Eq bounds (Formula.conjuncts_list_of (formula body))
      in
      Formula.mk_exists_if_bounded ~info bounds (Formula.and_of parts)
  | Formula.Bind (binder, bounds, body, info) ->
      Formula.mk_bind ~info binder bounds (formula body)
  | Formula.LetFormula (v, s, def, body, info) ->
      Formula.mk_let_formula ~info v s def (formula body)
  | Formula.LetRec _ -> phi

let problem muclp = Problem.map_formula formula muclp
