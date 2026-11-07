(* The condition under which two atoms are the same atom, shared by the
   resolvers. *)

open Core
open Common.Ext
open Ast.LogicOld

exception Mismatch

(** [matching_condition_of (a1, a2)] is [Some c] when the two atoms have
    compatible shapes -- both [true], both [false], or applications of one
    predicate at one arity -- with [c] the conjunction of the argument equations
    under which they are the same atom, and [None] otherwise.

    Two argument positions are compared only when both are literals of one kind
    (integer, real, or the boolean constants): equal literals add nothing to
    [c], different ones make the result [None]. Any other pair, including two
    terms under a constructor, contributes the equation [t1 = t2] UNCHECKED, so
    [Some c] does NOT say the atoms can be made to agree: [c] may be
    unsatisfiable ([seq.unit 6 = seq.unit 8]). A caller that acts on [Some] as a
    verdict has to decide [c] itself. *)
let matching_condition_of = function
  | Atom.True _, Atom.True _ | False _, False _ -> Some (Formula.mk_true ())
  | App (pred, terms, _), App (pred', terms', _)
    when Stdlib.( = ) pred pred' && List.length terms = List.length terms' -> (
      try
        Some
          (Formula.and_of
          @@ List.filter_map (List.zip_exn terms terms') ~f:(function
            | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                if Z.Compare.( = ) n1 n2 then None else raise Mismatch
            | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _) ->
                if Q.( = ) r1 r2 then None else raise Mismatch
            | ( FunApp (T_bool.Formula (Formula.Atom (atm1, _)), [], _),
                FunApp (T_bool.Formula (Formula.Atom (atm2, _)), [], _) )
              when (Atom.is_true atm1 || Atom.is_false atm1)
                   && (Atom.is_true atm2 || Atom.is_false atm2) ->
                if
                  (Atom.is_true atm1 && Atom.is_true atm2)
                  || (Atom.is_false atm1 && Atom.is_false atm2)
                then None
                else raise Mismatch
            | t1, t2 -> Some (Formula.eq t1 t2)))
      with Mismatch -> None)
  | _ -> None
