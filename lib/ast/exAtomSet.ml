(* Sets of example atoms ([ExAtom.t]) and their per-predicate projections.
   [reduce bvs] keeps, of atoms that are instances of one another (by
   [Atom.pattern_match], the variables [bvs] held fixed), only the most
   general: an atom an existing member generalises is not added, and an atom
   that generalises members replaces them.  The result depends on the order
   the set is folded in only through which of two mutually matching atoms is
   kept.  [reduce_with_source] does the same with a source carried beside
   each atom. *)
open Core
open LogicOld

type t = ExAtom.t Set.Poly.t

let papps_of atms pvar =
  Set.Poly.filter_map atms ~f:(function
    | ExAtom.PApp (((pvar', _), _) as papp) ->
        if Stdlib.(pvar' = pvar) then Some papp else None
    | _ -> None)

let ppapps_of atms pvar =
  Set.Poly.filter_map atms ~f:(function
    | ExAtom.PPApp (cond, (((pvar', _), _) as papp)) ->
        if Stdlib.(pvar' = pvar) then Some (cond, papp) else None
    | _ -> None)

let str_of (sample : t) =
  sample
  |> Set.Poly.map ~f:ExAtom.str_of
  |> Set.to_list
  |> (fun ls -> List.take ls 5)
  |> String.concat ~sep:", "
  |> sprintf (if Set.length sample > 5 then "[%s, ..]" else "[%s]")

let str_of_papps papps =
  papps |> Set.Poly.map ~f:(fun papp -> ExAtom.PApp papp) |> str_of

let str_of_ppapps ppapps =
  ppapps
  |> Set.Poly.map ~f:(fun (cond, papp) -> ExAtom.PPApp (cond, papp))
  |> str_of

let reduce bvs =
  Set.fold ~init:Set.Poly.empty ~f:(fun atms (param_senv, atm) ->
      try
        Set.add
          (Set.filter atms ~f:(fun (_, atm') ->
               match Atom.pattern_match bvs atm atm' with
               | None -> (
                   match Atom.pattern_match bvs atm' atm with
                   | None -> true
                   | Some _ -> raise Stdlib.Not_found)
               | Some _ -> false))
          (param_senv, atm)
      with Stdlib.Not_found -> atms)

let reduce_with_source bvs =
  Set.fold ~init:Set.Poly.empty ~f:(fun atms ((param_senv, atm), source) ->
      try
        Set.add
          (Set.filter atms ~f:(fun ((_, atm'), _) ->
               match Atom.pattern_match bvs atm atm' with
               | None -> (
                   match Atom.pattern_match bvs atm' atm with
                   | None -> true
                   | Some _ -> raise Stdlib.Not_found)
               | Some _ -> false))
          ((param_senv, atm), source)
      with Stdlib.Not_found -> atms)
