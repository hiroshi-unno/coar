open Core
open Common.Util
open Ast

type t = ExAtom.t Set.Poly.t

let papps_of atms pvar =
  Set.Poly.filter_map atms ~f:(function
      | ExAtom.PApp(((pvar', _), _) as papp) -> if Stdlib.(=) pvar' pvar then Some papp else None
      | _ -> None)
let ppapps_of atms pvar =
  Set.Poly.filter_map atms ~f:(function
      | ExAtom.PPApp(cond, (((pvar', _), _) as papp)) -> if Stdlib.(=) pvar' pvar then Some (cond, papp) else None
      | _ -> None)
let str_of (sample: t) =
  sample
  |> Set.Poly.map ~f:ExAtom.str_of
  |> Set.Poly.to_list
  |> (fun ls -> List.take ls 5)
  |> String.concat ~sep:", "
  |> Printf.sprintf (if Set.Poly.length sample > 5 then "[%s, ..]" else "[%s]")
let str_of_papps papps = papps |> Set.Poly.map ~f:(fun papp -> ExAtom.PApp papp) |> str_of
let str_of_ppapps ppapps = ppapps |> Set.Poly.map ~f:(fun (cond, papp) -> ExAtom.PPApp (cond, papp)) |> str_of

let reduce bvs =
  Set.Poly.fold ~init:Set.Poly.empty ~f:(fun atms (param_senv, atm) ->
      try
        Set.Poly.add
          (Set.Poly.filter atms ~f:(fun (_, atm') ->
               match LogicOld.Atom.pattern_match bvs atm atm' with
               | None -> (match LogicOld.Atom.pattern_match bvs atm' atm with None -> true | Some _ -> raise Caml.Not_found)
               | Some _ -> false))
          (param_senv, atm)
      with Caml.Not_found -> atms)
