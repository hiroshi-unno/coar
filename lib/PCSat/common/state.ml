open Core
open Common.Ext
open Ast

type info = { num_cegis_iters : int }
type output = PCSP.Problem.solution * info

let merge_infos infos =
  { num_cegis_iters = List.fold ~init:0 ~f:(+) (List.map infos ~f:(fun info -> info.num_cegis_iters)) }

type _ t =
  | Sat of CandSol.t
  | Unsat
  | Timeout
  | OutSpace of Ident.tvar list
  | Continue : VersionSpace.t * 'a -> (VersionSpace.t * 'a) t

(** with solution *)
type s = (VersionSpace.t * (CandSol.t * CandSol.tag) list) t
(** without solution *)
type u = (VersionSpace.t * unit) t

let lift : u -> s = function
  | Continue (vs, ()) -> Continue (vs, [])
  | Sat cand_sol -> Sat cand_sol
  | Unsat -> Unsat
  | OutSpace ps -> OutSpace ps
  | Timeout -> Timeout
let discard : s -> u = function
  | Continue (vs, _) -> Continue (vs, ())
  | Sat cand_sol -> Sat cand_sol
  | Unsat -> Unsat
  | OutSpace ps -> OutSpace ps
  | Timeout -> Timeout
let is_end = function
  | Continue _ -> false
  | _ -> true

let map ~f = function
  | Continue (vs, a) -> Continue (VersionSpace.map ~f vs, a)
  | Sat cand_sol -> Sat cand_sol
  | Unsat -> Unsat
  | OutSpace ps -> OutSpace ps
  | Timeout -> Timeout
let bind x f =
  match x with
  | Continue (vs, a) -> f vs a
  | Sat sol -> Sat sol
  | Unsat -> Unsat
  | OutSpace ps -> OutSpace ps
  | Timeout -> Timeout
let bind_may_err x f =
  let open Or_error in
  x >>= function
  | Continue (vs, a) -> f vs a >>= fun res -> Ok res
  | Sat sol -> Ok (Sat sol)
  | Unsat -> Ok (Unsat)
  | OutSpace ps -> Ok (OutSpace ps)
  | Timeout -> Ok Timeout
module Monad_infix = struct
  let (>>=) = bind
  let (>>=?) = bind_may_err
end

(*let init ?(oracle = None) = Continue (VersionSpace.init oracle, ())*)

let examples_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ -> assert false
  | Continue (vs, _) -> VersionSpace.examples_of vs

let pos_neg_und_examples_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ -> assert false
  | Continue (vs, _) -> VersionSpace.pos_neg_und_examples_of vs

let labelings_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ -> assert false
  | Continue (vs, _) -> VersionSpace.labelings_of vs

let candidates_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ -> assert false
  | Continue (_, cs) -> cs

let version_space_of = function
  | Sat _ | Unsat | Timeout | OutSpace _ -> assert false
  | Continue (vs, _) -> vs

let of_version_space vs = Continue (vs, ())

let of_pos_neg_und_examples vs examples =
  let vs' =
    vs |> VersionSpace.set_pos_neg_und_examples examples
    |> VersionSpace.set_labelings [Map.Poly.empty(*ToDo*), false(*ToDo*)] in
  Continue (vs', ())

let of_examples vs examples =
  VersionSpace.add_examples vs examples;
  let vs' = VersionSpace.set_labelings [Map.Poly.empty(*ToDo*), false(*ToDo*)] vs in
  Continue (vs', ())

