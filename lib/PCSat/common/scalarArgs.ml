open Core
open Ast

(* Whether every unknown of a problem takes only SCALAR arguments: integers,
   reals, Booleans and bit-vectors.

   A shape test on the problem's signature, decided once and asking no solver,
   for the mechanisms of the learning loop whose gain lives in the structure of
   an unknown's arguments and whose cost is paid everywhere:

   - finding a conflict between a positive and a negative example by asking
     whether their arguments can be made equal, where intersecting their ground
     instances finds none: the conflicts that only this finds pair two examples
     whose parameters sit inside constructor terms, arrays or elements of an
     uninterpreted sort, where the one instance the instantiation picks per
     example never coincides with the other's;
   - resolving decided examples one step against the problem's own clauses,
     whose refutations come from a parametric example instantiated at the
     standard dummy of a structured sort -- a constant array, an arbitrary
     constructor term -- meeting a goal clause.

   On a scalar problem both still act (an integer parameter unifies, a ground
   point resolves) but add solver calls per labeling and examples per round,
   which is where they were seen to cost answers on linear-arithmetic inputs.

   Contract: [true] exactly when each unknown of [senv_of pcsp] -- predicate or
   function -- has a curried sort whose argument sorts are all [Int], [Real],
   [Bool] or a bit-vector sort.  A polymorphic unknown ([SForAll]) counts as
   non-scalar, and so does every sort this match does not name (a datatype, an
   uninterpreted sort, a sort variable, an array, a sequence, a tuple, a
   string), which is the direction that keeps a guarded mechanism on: [Sort.t]
   is an extensible variant, and a sort added elsewhere then switches nothing
   off silently.  A problem with no unknown is scalar. *)

let is_scalar_sort = function
  | Logic.IntTerm.SInt | Logic.RealTerm.SReal | Logic.BoolTerm.SBool
  | Logic.BVTerm.SBV _ ->
      true
  | _ -> false

let unknown_is_scalar = function
  | Logic.Sort.SForAll _ -> false
  | sort -> List.for_all (Logic.Sort.args_of sort) ~f:is_scalar_sort

let unknowns_take_only_scalars pcsp =
  Map.Poly.for_all (PCSP.Problem.senv_of pcsp) ~f:unknown_is_scalar
