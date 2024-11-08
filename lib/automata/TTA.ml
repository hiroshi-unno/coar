(* Trivial Tree Automata *)

open Core
open Common.Ext

type dest = string list

let pr_dest ppf (dest : dest) =
  Format.fprintf ppf "%s" @@ String.concat ~sep:" " dest
(*List.pr pr_id " "*)

type pre_trs = (string * (string * dest)) list

let pr_pre ppf (trs : pre_trs) =
  (*List.sort ~compare:(fun (q1, _) (q2, _) -> String.compare q1 q2)*)
  List.iter trs ~f:(fun (q, (a, qs)) ->
      Format.fprintf ppf "%s %s -> %a.@\n" q a pr_dest qs)

let states (trs : pre_trs) =
  List.unique @@ List.concat_map trs ~f:(fun (q, (_a, qs)) -> q :: qs)

let br_symbol = "br"

let add_br_transitions (trs : pre_trs) =
  trs @ List.map (states trs) ~f:(fun q -> (q, (br_symbol, [ q; q ])))

let success_symbol = "success__"

let add_success_transitions (trs : pre_trs) =
  trs @ List.map (states trs) ~f:(fun q -> (q, (success_symbol, [])))

let add_check_transitions (trs : pre_trs) cs =
  trs
  @ List.concat_map (states trs) ~f:(fun q ->
        List.map cs ~f:(fun q' -> (q, ("check__" ^ q', [ q' ]))))

type body = (string, dest) Base.List.Assoc.t

let next_ids_body (body : body) = List.concat_map body ~f:snd

type trs = (string, body) Base.List.Assoc.t

let rec make (trs : pre_trs) : trs =
  match trs with
  | [] -> []
  | (id, x) :: xs' ->
      let t, f =
        List.partition_map xs' ~f:(fun (id', x') ->
            if Stdlib.(id = id') then First x' else Second (id', x'))
      in
      (id, x :: t) :: make f

let pr pr_id ppf (trs : trs) =
  List.iter trs ~f:(fun (q, xs) ->
      List.iter xs ~f:(fun (a, qs) ->
          Format.fprintf ppf "%a %a -> %a.@\n" pr_id q pr_id a pr_dest qs))
