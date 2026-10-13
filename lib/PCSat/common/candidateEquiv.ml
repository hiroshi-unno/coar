(* Equality of candidate solutions up to the names of their bound variables.

   The synthesizer's non-progress test asks whether this round's candidate is
   the one it proposed last round.  A candidate read back from a template with
   quantifiers carries binders whose names are drawn fresh at every read-back
   ([forall #tvar14791. ...] one round, [forall #tvar14861. ...] the next), so a
   comparison that renames only the outer lambda parameters never sees two
   such candidates as equal, and a round that proposes the same quantified
   candidate again is taken for progress.  [alpha_equal] compares terms with
   every binder (lambda, quantifier, fixpoint, let) identified by its position
   rather than its name.

   Contract: [alpha_equal t1 t2] holds exactly when [t1] and [t2] differ only by
   a consistent renaming of bound term variables: binders of the same kind and
   sort at the same places, a bound occurrence in one bound by the binder at the
   same place in the other, and free variables, constants, sorts and type
   applications equal.  Sorts and constants are compared structurally (as the
   test this one refines did); the [info] fields are ignored.  A sort variable
   bound by [TyLam] is compared by name. *)

open Core
open Common.Ext
open Ast
open Ast.Logic

let alpha_equal (t1 : term) (t2 : term) : bool =
  (* [env1]/[env2] map a bound variable to the depth of its binder *)
  let rec go env1 env2 depth t1 t2 =
    match (t1, t2) with
    | Var (x1, _), Var (x2, _) -> (
        match (Map.Poly.find env1 x1, Map.Poly.find env2 x2) with
        | Some d1, Some d2 -> d1 = d2
        | None, None -> Ident.tvar_equal x1 x2
        | _ -> false)
    | Con (s1, _), Con (s2, _) -> Stdlib.(s1 = s2)
    | App (f1, a1, _), App (f2, a2, _) ->
        go env1 env2 depth f1 f2 && go env1 env2 depth a1 a2
    | Bin (b1, x1, s1, body1, _), Bin (b2, x2, s2, body2, _) ->
        Stdlib.(b1 = b2)
        && Stdlib.(s1 = s2)
        && go
             (Map.Poly.set env1 ~key:x1 ~data:depth)
             (Map.Poly.set env2 ~key:x2 ~data:depth)
             (depth + 1) body1 body2
    | Let (x1, s1, d1, body1, _), Let (x2, s2, d2, body2, _) ->
        Stdlib.(s1 = s2)
        && go env1 env2 depth d1 d2
        && go
             (Map.Poly.set env1 ~key:x1 ~data:depth)
             (Map.Poly.set env2 ~key:x2 ~data:depth)
             (depth + 1) body1 body2
    | TyApp (u1, s1, _), TyApp (u2, s2, _) ->
        Stdlib.(s1 = s2) && go env1 env2 depth u1 u2
    | TyLam (v1, u1, _), TyLam (v2, u2, _) ->
        Stdlib.(v1 = v2) && go env1 env2 depth u1 u2
    | _ -> false
  in
  go Map.Poly.empty Map.Poly.empty 0 t1 t2

(* Two candidate maps propose the same solution: the same predicates, each with
   an [alpha_equal] definition.  Sorts are not compared, as in the test this
   refines; a predicate's sort does not change between rounds. *)
let same_candidates (c1 : cand_map) (c2 : cand_map) : bool =
  Map.Poly.equal (fun (_, t1) (_, t2) -> alpha_equal t1 t2) c1 c2
