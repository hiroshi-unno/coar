open Core
open Common.Ext
open LogicOld

let rank_of phi =
  let max_const =
    Set.max_elt
    @@ Set.Poly.filter_map ~f:(function
         | T_int.Int i -> Some (Z.abs i)
         | _ -> None)
    @@ Formula.funsyms_of phi
  in
  let num_vars = Set.length @@ Formula.tvs_of phi in
  let size = Formula.ast_size phi in
  (max_const, num_vars, size)

let compare_aux x y =
  match (x, y) with
  | None, None -> 0
  | None, Some _ -> -1
  | Some _, None -> 1
  | Some x, Some y ->
      if Z.Compare.(x < y) then -1 else if Z.Compare.(x > y) then 1 else 0

let compare ((x1, x2, x3) : Z.t option * int * int) (y1, y2, y3) =
  let c = compare_aux x1 y1 in
  if c <> 0 then c
  else if x2 < y2 then -1
  else if x2 > y2 then 1
  else if x3 < y3 then -1
  else if x3 > y3 then 1
  else 0

let sort_quals quals =
  Set.Poly.map quals ~f:(fun ((_, phi) as qual) -> (rank_of phi, qual))
  |> Set.to_list
  |> List.sort ~compare:(fun (r1, _) (r2, _) -> compare r1 r2)
  |> List.map ~f:snd

let sort_indices qarr qlist =
  Set.Poly.map qlist ~f:(fun idx -> (rank_of qarr.(idx), idx))
  |> Set.to_list
  |> List.sort ~compare:(fun (r1, _) (r2, _) -> compare r1 r2)
  |> List.map ~f:snd

let str_of (x1, x2, x3) =
  match x1 with
  | Some x1 -> String.paren @@ sprintf "%s, %d, %d" (Z.to_string x1) x2 x3
  | None -> String.paren @@ sprintf "_, %d, %d" x2 x3
