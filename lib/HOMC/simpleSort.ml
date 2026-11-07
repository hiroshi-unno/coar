(* Simple sorts of the terms of a recursion scheme, inferred by first-order
   unification: [O] for trees, [D] for a finite-data value, [Arr] for a
   function, and [V] a sort variable, which [unify] binds.  A recursion
   scheme is simply sorted when unifying every application's function sort
   with an arrow from its argument's sort succeeds.  [unify] raises
   [Failure] on a clash or a cyclic sort; [arity] reads an unconstrained
   result as [O]. *)
open Core

type sort = O | D | Arr of sort * sort | V of sort option ref

let fresh () = V (ref None)
let rec repr = function V { contents = Some s } -> repr s | s -> s

let rec occurs r s =
  match repr s with
  | V r' -> phys_equal r r'
  | Arr (s1, s2) -> occurs r s1 || occurs r s2
  | O | D -> false

let rec unify s1 s2 =
  match (repr s1, repr s2) with
  | V r1, V r2 when phys_equal r1 r2 -> ()
  | V r, s | s, V r ->
      if occurs r s then
        failwith "the rules are not simply sorted (cyclic sort)"
      else r := Some s
  | O, O | D, D -> ()
  | Arr (a1, b1), Arr (a2, b2) ->
      unify a1 a2;
      unify b1 b2
  | _ -> failwith "the rules are not simply sorted"

(* the number of arguments of a sort, an unconstrained result read as [o] *)
let rec arity s = match repr s with Arr (_, s) -> 1 + arity s | _ -> 0
let rec tree_sort k = if k = 0 then O else Arr (O, tree_sort (k - 1))
