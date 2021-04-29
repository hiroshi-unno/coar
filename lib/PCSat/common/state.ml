open Core
open Common.Util
open Ast

type _ t =
  | Sat of CandSol.t
  | Unsat
  | Continue : (VersionSpace.t) * 'a -> ((VersionSpace.t) * 'a) t

(** with solution *)
type s = ((VersionSpace.t) * (CandSol.t list)) t
(** without solution *)
type u = ((VersionSpace.t) * unit) t

let lift : u -> s = function
  | Continue (vs, ()) -> Continue (vs, [])
  | Sat cand_sol -> Sat cand_sol
  | Unsat -> Unsat
let discard : s -> u = function
  | Continue (vs, _) -> Continue (vs, ())
  | Sat cand_sol -> Sat cand_sol
  | Unsat -> Unsat
let is_end = function
  | Continue _ -> false
  | _ -> true

let map ~f = function
  | Continue ((vs), a) -> Continue (VersionSpace.map ~f vs, a)
  | Sat cand_sol -> Sat cand_sol
  | Unsat -> Unsat
let bind x f =
  match x with
  | Continue (vs, a) -> f vs a
  | Sat sol -> Sat sol
  | Unsat -> Unsat
let bind_may_err x f =
  let open Or_error in
  x >>= function
  | Continue (vs, a) -> f vs a >>= fun res -> Ok res
  | Sat sol -> Ok (Sat sol)
  | Unsat -> Ok (Unsat)
module Monad_infix = struct
  let (>>=) = bind
  let (>>=?) = bind_may_err
end

let init () = Continue ((VersionSpace.init ()), ())

let example_instances_of = function
  | Sat _ | Unsat -> assert false
  | Continue (vs, _) -> VersionSpace.examples_of vs

let labelings_of = function
  | Sat _ | Unsat -> assert false
  | Continue (vs, _) -> VersionSpace.labelings_of vs

let candidates_of = function
  | Sat _ | Unsat -> assert false
  | Continue (_, cs) -> cs

let version_space_of = function
  | Sat _ | Unsat -> assert false
  | Continue (vs, _) -> vs

let of_version_space vs = Continue(vs, ())

let of_examples vs examples =
  let vs' =
    vs |> VersionSpace.set_examples examples
    |> VersionSpace.set_labelings [Map.Poly.empty]  in
  Continue (vs', ())

let put_undecided e undecided' =
  let open Monad_infix in
  e >>= fun vs a -> 
  let (pos, neg, undecided) = VersionSpace.examples_of vs in
  Continue(VersionSpace.set_examples (pos, neg, Set.Poly.union undecided undecided') vs, a)

(*let normalize = function
  | Sat sol -> Sat sol | Unsat -> Unsat
  | Continue (vs, a) ->
    let (pos, neg, undecided) = VersionSpace.examples_of vs in
    let pos', neg', undecided' =
      ExClauseSet.(normalize pos, normalize neg, normalize undecided) in
    Continue(VersionSpace.set_examples (pos', neg', undecided') vs, a)*)
