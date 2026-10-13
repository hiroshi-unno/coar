open Core
open Common.Ext
open Ast

type info = {
  num_cegis_iters : int;
  unsat_witness : UnsatWitness.t option;
      (* the evidence behind an [Unsat] answer, if a component recorded it *)
  kind_certificates : (Ident.tvar, KindCert.t) Map.Poly.t;
      (* for a [Sat] answer: the kind certificates of the accepted candidate *)
}

type output = PCSP.Problem.solution * info

let merge_infos infos =
  {
    num_cegis_iters =
      List.fold ~init:0 ~f:( + )
        (List.map infos ~f:(fun info -> info.num_cegis_iters));
    unsat_witness = List.find_map infos ~f:(fun info -> info.unsat_witness);
    kind_certificates =
      List.fold infos ~init:Map.Poly.empty ~f:(fun acc info ->
          Map.Poly.merge acc info.kind_certificates ~f:(fun ~key:_ -> function
            | `Left v | `Right v -> Some v
            | `Both (v, _) -> Some v));
  }

type _ t =
  | Sat of CandSol.t
  | Unsat
  | Timeout
  | OutSpace of Ident.tvar list
  (* The solver could not decide whether a candidate violates a clause, so the
     candidate is neither confirmed nor refuted and the round learnt nothing.
     Before this existed the validator returned a VACUOUS counterexample
     instead -- non-empty, so the caller rejected the candidate, and saying
     nothing, so the example set did not grow -- and the next round proposed the
     same candidate, forever: a correct invariant was rejected on 45 consecutive
     iterations that way.  Reported as [unknown], which is an ordinary answer
     here, rather than as a loop that cannot end. *)
  | Undecided
  | Continue : VersionSpace.t * 'a -> (VersionSpace.t * 'a) t

(* with solution *)
type s = (VersionSpace.t * (CandSol.t * CandSol.tag) list) t

(* without solution *)
type u = (VersionSpace.t * unit) t

let lift : u -> s = function
  | Continue (vs, ()) -> Continue (vs, [])
  | Sat cand_sol -> Sat cand_sol
  | Unsat -> Unsat
  | OutSpace ps -> OutSpace ps
  | Timeout -> Timeout
  | Undecided -> Undecided

let discard : s -> u = function
  | Continue (vs, _) -> Continue (vs, ())
  | Sat cand_sol -> Sat cand_sol
  | Unsat -> Unsat
  | OutSpace ps -> OutSpace ps
  | Timeout -> Timeout
  | Undecided -> Undecided

let is_end = function Continue _ -> false | _ -> true

let map ~f = function
  | Continue (vs, a) -> Continue (VersionSpace.map ~f vs, a)
  | Sat cand_sol -> Sat cand_sol
  | Unsat -> Unsat
  | OutSpace ps -> OutSpace ps
  | Timeout -> Timeout
  | Undecided -> Undecided

let bind x f =
  match x with
  | Continue (vs, a) -> f vs a
  | Sat sol -> Sat sol
  | Unsat -> Unsat
  | OutSpace ps -> OutSpace ps
  | Timeout -> Timeout
  | Undecided -> Undecided

let bind_may_err x f =
  let open Or_error in
  x >>= function
  | Continue (vs, a) -> f vs a >>= fun res -> Ok res
  | Sat sol -> Ok (Sat sol)
  | Unsat -> Ok Unsat
  | OutSpace ps -> Ok (OutSpace ps)
  | Timeout -> Ok Timeout
  | Undecided -> Ok Undecided

module Monad_infix = struct
  let ( >>= ) = bind
  let ( >>=? ) = bind_may_err
end

(*let init ?(oracle = None) = Continue (VersionSpace.init oracle, ())*)

let examples_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ | Undecided -> assert false
  | Continue (vs, _) -> VersionSpace.examples_of vs

let pos_neg_und_examples_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ | Undecided -> assert false
  | Continue (vs, _) -> VersionSpace.pos_neg_und_examples_of vs

let labelings_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ | Undecided -> assert false
  | Continue (vs, _) -> vs.labelings

let candidates_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ | Undecided -> assert false
  | Continue (_, cs) -> cs

let version_space_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ | Undecided -> assert false
  | Continue (vs, _) -> vs

let of_version_space vs = Continue (vs, ())

let of_pos_neg_und_examples vs examples =
  let vs' =
    vs
    |> VersionSpace.set_pos_neg_und_examples examples
    |> VersionSpace.set_labelings [ (Map.Poly.empty (*ToDo*), false (*ToDo*)) ]
  in
  Continue (vs', ())

let of_examples vs examples =
  VersionSpace.add_examples vs examples;
  let vs' =
    VersionSpace.set_labelings [ (Map.Poly.empty (*ToDo*), false (*ToDo*)) ] vs
  in
  Continue (vs', ())
