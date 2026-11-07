(* Negation pushed to the atoms, for the readers of formulas with [not], [=>]
   and [<=>].  An HFL formula has no negation constructor: predicate variables
   occur only positively, which the fixpoints need to be monotone.  So the
   negation of a predicate-variable application (or of a lambda) cannot be
   pushed and is refused; the negation of a closed fixpoint formula would need
   its dual equations, which a reader cannot introduce. *)

open HflSyntax

exception Refused of string

let rec neg = function
  | Bool b -> Bool (not b)
  | Pred (p, a, b) -> Pred (negate_pred p, a, b)
  | And (a, b) -> Or (neg a, neg b)
  | Or (a, b) -> And (neg a, neg b)
  | Forall (x, a) -> Exists (x, neg a)
  | Exists (x, a) -> Forall (x, neg a)
  | Var _ | App _ | Abs _ ->
      raise
        (Refused
           "negation of a predicate-variable application (predicate \
            variables must occur positively)")
  | Int _ | Op _ | Neg _ -> raise (Refused "negation of an integer term")
