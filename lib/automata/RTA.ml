(* Regular Tree Automata *)

open Core
open Common.Ext

(** Tree automata *)

type ('lab, 'sym) body =
  | Leaf
  | Label of 'sym * 'lab * 'lab
  | Alter of ('lab, 'sym) body * ('lab, 'sym) body
  | Emp

let rec pr_body pr_id ppf = function
  | Leaf -> Format.fprintf ppf "()"
  | Label (id1, id2, id3) ->
      Format.fprintf ppf "%a(%a, %a)" pr_id id1 pr_id id2 pr_id id3
  | Alter (u1, u2) ->
      Format.fprintf ppf "(%a | %a)" (pr_body pr_id) u1 (pr_body pr_id) u2
  | Emp -> ()

let rec rename_body rn = function
  | Leaf -> Leaf
  | Label (id1, id2, id3) ->
      Label
        ( id1,
          (match List.Assoc.find ~equal:Stdlib.( = ) rn id2 with
          | Some r -> r
          | None -> id2),
          match List.Assoc.find ~equal:Stdlib.( = ) rn id3 with
          | Some r -> r
          | None -> id3 )
  | Alter (u1, u2) -> Alter (rename_body rn u1, rename_body rn u2)
  | Emp -> Emp

let canonize_body u =
  let rec aux = function
    | Leaf | Label (_, _, _) -> [ u ]
    | Alter (u1, u2) ->
        let x = aux u1 @ aux u2 in
        let x' = List.unique x in
        (*let _ = assert (x = x') in*)
        x'
    | Emp -> []
  in
  match List.sort ~compare:Stdlib.compare @@ aux u with
  | [] -> failwith "canonize_body"
  | [ x ] -> x
  | x :: xs -> List.fold_left ~init:x xs ~f:(fun x y -> Alter (x, y))

let rec next_ids_body = function
  | Leaf -> []
  | Label (_id1, id2, id3) -> [ id2; id3 ]
  | Alter (u1, u2) -> (*List.unique*) next_ids_body u1 @ next_ids_body u2
  | Emp -> []

let rec tta_body_of (body : ('lab, 'sym) body) : TTA.body =
  match body with
  | Leaf -> [ ("leaf", []) ]
  | Label (id1, id2, id3) -> [ (id1, [ id2; id3 ]) ]
  | Alter (u1, u2) -> tta_body_of u1 @ tta_body_of u2
  | Emp -> failwith "RTA.table_of_body"

type ('lab, 'sym) trs = ('lab, ('lab, 'sym) body) List.Assoc.t

let pr pr_id ppf (trs : ('lab, 'sym) trs) =
  List.iter trs ~f:(fun (id, u) ->
      Format.fprintf ppf "%a -> %a.@\n" pr_id id (pr_body pr_id) u)

let rec minimize (trs : ('lab, 'sym) trs) =
  let rec f nece = function
    | [] -> nece
    | (id, u) :: rs -> (
        try
          let id', _ =
            List.find_exn nece ~f:(fun (id', u') ->
                Stdlib.(
                  rename_body [ (id, id') ] u = rename_body [ (id, id') ] u'))
          in
          (* Format.printf "=  %a@," pr u; *)
          let rn = [ (id, id') ] in
          f
            (List.map nece ~f:(fun (id, u) -> (id, rename_body rn u)))
            (List.map rs ~f:(fun (id, u) -> (id, rename_body rn u)))
        with Not_found_s _ ->
          (* Format.printf "<> %a@," pr u; *)
          f ((id, u) :: nece) rs)
  in
  let trs' = List.rev (f [] trs) in
  if List.length trs' < List.length trs then minimize trs' else trs'

let tta_of (trs : ('lab, 'sym) trs) : TTA.trs =
  List.map trs ~f:(fun (id, u) -> (id, tta_body_of u))
