open Core
open Common.Ext
open Ast

type space_flag = | NC  | ND  | Depth
type t = (Ident.tvar, (space_flag, int option) Map.Poly.t) Map.Poly.t
type constr = (Ident.tvar * space_flag * int)

let space_flag_of = function
  | "upb_nc" -> (NC)
  | "upb_nd" -> (ND)
  | "upb_depth" -> (Depth)
  | str -> failwith @@ sprintf "[space_flag_of] unknown flag [%s]" str
let str_of t =
  Map.Poly.map t ~f:(Map.Poly.to_alist)
  |> Map.Poly.to_alist
  |> String.concat_map_list ~sep:"\n" ~f:(fun (Ident.Tvar v, constrs) ->
      v ^ ".(" ^ String.concat_map_list ~sep:"," constrs ~f:(fun (flag, i) ->
          match i with
          | Some i ->
            sprintf "%s = %d"
              begin match flag with
                | Depth -> "maxdepth"
                | ND -> "maxnd"
                | NC -> "maxnd"
              end i
          | None -> "") ^ ")")

let in_space tvar flag i space =
  match Map.Poly.find space tvar with
  | Some (space) ->
    begin match Map.Poly.find space flag with
      | Some (Some c) -> i <= c
      | _ -> true
    end
  | _ -> true
let str_of_tvar_and_flag tvar flag space =
  match Map.Poly.find space tvar with
  | Some space ->
    begin match Map.Poly.find space flag with
      | Some (Some c) -> sprintf "%d" c
      | _ -> "inf"
    end
  | _ -> "inf"

let of_space_constrs (space_constrs:constr list) : t =
  List.fold space_constrs ~init:Map.Poly.empty ~f:(fun acc (tvar, flag, i) ->
      match Map.Poly.find acc tvar with
      | Some (space) ->
        Map.Poly.set acc ~key:tvar ~data:(Map.Poly.set space ~key:flag ~data:(Some i))
      | None -> Map.Poly.set acc ~key:tvar ~data:(Map.Poly.singleton flag (Some i))
    )