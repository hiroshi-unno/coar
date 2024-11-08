open Core
open Common.Ext

type space_flag = Depth | ND | NC | NP | NDC | NL
type t = (Ident.tvar, (space_flag, int option) Map.Poly.t) Map.Poly.t
type constr = Ident.tvar * space_flag * int

let space_flag_of = function
  | "upb_depth" -> Depth
  | "upb_nd" -> ND
  | "upb_nc" -> NC
  | "upb_np" -> NP
  | "upb_ndc" -> NDC
  | "upb_nl" -> NL
  | str -> failwith @@ sprintf "[space_flag_of] unknown flag [%s]" str

let str_of_flag = function
  | Depth -> "maxdepth"
  | ND -> "maxnd"
  | NC -> "maxnd"
  | NP -> "maxnp"
  | NDC -> "maxndc"
  | NL -> "maxnl"

let str_of t =
  Map.Poly.map t ~f:Map.Poly.to_alist
  |> Map.Poly.to_alist
  |> String.concat_map_list ~sep:"\n" ~f:(fun (Ident.Tvar v, constrs) ->
         v ^ ".("
         ^ String.concat_map_list ~sep:"," constrs ~f:(function
             | flag, Some i -> sprintf "%s = %d" (str_of_flag flag) i
             | _, None -> "")
         ^ ")")

let in_space tvar flag i space =
  match Map.Poly.find space tvar with
  | Some space -> (
      match Map.Poly.find space flag with Some (Some c) -> i <= c | _ -> true)
  | _ -> true

let str_of_tvar_and_flag tvar flag space =
  match Map.Poly.find space tvar with
  | Some space -> (
      match Map.Poly.find space flag with
      | Some (Some c) -> sprintf "%d" c
      | _ -> "inf")
  | None -> "inf"

let of_space_constrs (space_constrs : constr list) : t =
  List.fold space_constrs ~init:Map.Poly.empty ~f:(fun acc (tvar, flag, i) ->
      Map.Poly.set acc ~key:tvar
        ~data:
          (match Map.Poly.find acc tvar with
          | Some space -> Map.Poly.set space ~key:flag ~data:(Some i)
          | None -> Map.Poly.singleton flag (Some i)))
