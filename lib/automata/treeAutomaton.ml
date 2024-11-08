open Core
open Common.Ext
open Common.Combinator

type t =
  | TTA of TTA.trs
  | ATA of ATA.arity * ATA.trs
  | RTA of (string, string) RTA.trs

let assoc id trs =
  match List.Assoc.find ~equal:Stdlib.( = ) trs id with
  | Some r -> r
  | None -> failwith ("state " ^ id ^ " not found")

let reachable_set_of ids next =
  let diff l1 l2 = List.filter l1 ~f:(List.mem ~equal:Stdlib.( = ) l2 >> not) in
  let rec loop ids nids =
    let ids' = ids @ nids in
    let nids' = diff (List.unique (List.concat_map ~f:next nids)) ids' in
    if List.is_empty nids' then ids' else loop ids' nids'
  in
  loop [] ids

(* without changing order*)
let remove_unreachable ~next_ids_body ids trs =
  let reachable_ids =
    reachable_set_of (List.unique ids) (fun id -> next_ids_body (assoc id trs))
  in
  List.filter trs ~f:(fst >> List.mem ~equal:Stdlib.( = ) reachable_ids)

let reachable ~next_ids_body id trs =
  let reachable_ids =
    reachable_set_of [ id ] (fun id -> next_ids_body (assoc id trs))
  in
  List.map reachable_ids ~f:(fun id -> (id, assoc id trs))

let number_of_states_trs trs = List.length @@ List.unique @@ List.map ~f:fst trs

let number_of_states = function
  | TTA trs -> number_of_states_trs trs
  | ATA (_, trs) -> number_of_states_trs trs
  | RTA trs -> number_of_states_trs trs

let init_state_of_trs trs = fst @@ List.hd_exn trs

let init_state_of = function
  | TTA trs -> init_state_of_trs trs
  | ATA (_, trs) -> init_state_of_trs trs
  | RTA trs -> init_state_of_trs trs

let pr ppf = function
  | TTA trs ->
      Format.fprintf ppf "%%BEGINA@\n";
      if List.is_empty trs then Format.fprintf ppf "\n"
      else TTA.pr String.pr ppf trs;
      Format.fprintf ppf "%%ENDA@,"
  | ATA (arity, trs) ->
      Format.fprintf ppf "%%BEGINR@\n";
      if List.is_empty arity then Format.fprintf ppf "\n"
      else ATA.pr_arity String.pr ppf arity;
      Format.fprintf ppf "%%ENDR@,@,";
      Format.fprintf ppf "%%BEGINATA@\n";
      if List.is_empty trs then Format.fprintf ppf "\n"
      else ATA.pr String.pr ppf trs;
      Format.fprintf ppf "%%ENDATA@,"
  | RTA _trs -> failwith "not implemented"
