(* The learner for FUNCTIONAL predicates: two decided positive atoms that agree
   on a predicate's arguments and disagree on its result cannot both hold.

   A functional predicate stands for a witness -- skolemising an existentially
   quantified term variable introduces one, its argument tuple being the
   variables the witness may depend on and its last argument the value chosen.
   Being functional is a semantic condition on the solution, not something any
   clause states, so the sample is where a violation of it becomes visible: if
   the labeling has decided both [P(a, r1)] and [P(a, r2)] with [r1 <> r2],
   the two are inconsistent and the clause saying so is learned.

   The learned clause is all-negative and binary, which is weaker than
   forbidding either atom on its own and is the most that follows: the sample
   says one of the two must go, not which.

   It sits beside the loop detectors rather than inside the labeling functor
   because it is the fourth of four learners and the other three already do --
   and because that is what lets it be tested. Neither this kind nor the
   non-well-founded and parity ones have any input syntax, so a sample that
   exercises them has to be built through the API. *)

open Core
open Common.Ext
open Common.Combinator
open Ast

(** [learn pos res svpvs] adds to [res] one all-negative binary clause for each
    pair of decided positives of a single-valued predicate in [svpvs] that agree
    everywhere except at its single-valued position [j] and differ there.

    Only single-valuedness is used, never totality, so the learner serves both a
    functional predicate ([FN], position its last argument) and a [Uniq] one.

    [pos] is the decided positive atoms as (predicate, argument tuple) pairs --
    the whole sample, filtered here per predicate.  Requires [0 <= j] and every
    tuple of a predicate in [svpvs] to be longer than [j]; guarantees the result
    mentions only atoms of [pos]. *)

(* the tuple without position [j], and the element at [j] *)
let split_at j args = (List.take args j @ List.drop args (j + 1), List.nth_exn args j)
let insert_at j rest x = List.take rest j @ (x :: List.drop rest j)

let rec learn pos res = function
  | [] -> res
  | (pvar, sorts, j) :: svpvs ->
      let sample = Set.filter pos ~f:(fst >> fst >> Stdlib.( = ) pvar) in
      if Set.is_empty sample then learn pos res svpvs
      else
        Set.Poly.map sample ~f:(snd >> split_at j)
        |> Set.to_list |> Map.Poly.of_alist_multi
        |> Map.Poly.fold ~init:res ~f:(fun ~key:args ~data:rets res ->
               Set.fold_distinct_pairs (Set.Poly.of_list rets) ~init:res
                 ~f:(fun acc r1 r2 ->
                   (* CANONICALISE.  A [Set.Poly] orders by the shape of the
                      tree it was built as, not by its elements, so the two
                      orderings this fold visits -- (r1, r2) and (r2, r1) --
                      produce two values that are [Set.equal], print
                      identically and are DIFFERENT elements of the enclosing
                      set.  Every conflict was therefore learned twice. *)
                   Set.add acc @@ ExClause.canon
                   @@ ExClause.
                        {
                          positive = Set.Poly.empty;
                          negative =
                            Set.Poly.of_list
                              [
                                ExAtom.PApp ((pvar, sorts), insert_at j args r1);
                                ExAtom.PApp ((pvar, sorts), insert_at j args r2);
                              ];
                        }))
        |> Fn.flip (learn pos) svpvs
