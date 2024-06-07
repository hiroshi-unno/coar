open Core
open Common.Ext

(** Tree automata *)

type ('sym, 'lab) t =
  | Leaf
  | Label of 'sym * 'lab * 'lab
  | Alter of ('sym, 'lab) t * ('sym, 'lab) t
  | Emp

let rec pr ppf = function
  | Leaf -> Format.fprintf ppf "()"
  | Label (id1, id2, id3) ->
      Format.fprintf ppf "%a(%a, %a)" String.pr id1 String.pr id2 String.pr id3
  | Alter (u1, u2) -> Format.fprintf ppf "(%a | %a)" pr u1 pr u2
  | Emp -> ()

let rec rename rn = function
  | Leaf -> Leaf
  | Label (id1, id2, id3) ->
      Label
        ( id1,
          (try List.Assoc.find_exn ~equal:String.equal rn id2
           with Not_found_s _ -> id2),
          try List.Assoc.find_exn ~equal:String.equal rn id3
          with Not_found_s _ -> id3 )
  | Alter (u1, u2) -> Alter (rename rn u1, rename rn u2)
  | Emp -> Emp

let rec next_ids = function
  | Leaf -> []
  | Label (_id1, id2, id3) -> [ id2; id3 ]
  | Alter (u1, u2) -> (*List.unique*) next_ids u1 @ next_ids u2
  | Emp -> []

let set_reachable ids next =
  let diff l1 l2 =
    List.filter ~f:(fun x -> not @@ List.mem ~equal:Stdlib.( = ) l2 x) l1
  in
  let rec loop ids nids =
    let ids' = ids @ nids in
    let nids' = diff (List.unique (List.concat_map ~f:next nids)) ids' in
    if List.is_empty nids' then ids' else loop ids' nids'
  in
  loop [] ids

let assoc id rs =
  try List.Assoc.find_exn ~equal:String.equal rs id
  with Not_found_s _ -> failwith ("state " ^ id ^ " not found")

(* without changing order*)
let remove_unreachable ids rs =
  let reachable_ids =
    set_reachable (List.unique ids) (fun id -> next_ids (assoc id rs))
  in
  List.filter
    ~f:(fun (id, _) -> List.mem ~equal:String.equal reachable_ids id)
    rs

let reachable id rs =
  List.map
    ~f:(fun id -> (id, assoc id rs))
    (set_reachable [ id ] (fun id -> next_ids (assoc id rs)))

let rec minimize rs =
  let rec f rs nece =
    match rs with
    | [] -> nece
    | (id, u) :: rs -> (
        try
          let id', _ =
            List.find_exn
              ~f:(fun (id', u') ->
                Stdlib.(rename [ (id, id') ] u = rename [ (id, id') ] u'))
              nece
          in
          (* Format.printf "=  %a@," pr u; *)
          let rn = [ (id, id') ] in
          f
            (List.map ~f:(fun (id, u) -> (id, rename rn u)) rs)
            (List.map ~f:(fun (id, u) -> (id, rename rn u)) nece)
        with Not_found_s _ ->
          (* Format.printf "<> %a@," pr u; *)
          f rs ((id, u) :: nece))
  in
  let rs' = List.rev (f rs []) in
  if List.length rs' < List.length rs then minimize rs' else rs'

let canonize u =
  let rec aux u =
    match u with
    | Leaf | Label (_, _, _) -> [ u ]
    | Alter (u1, u2) ->
        let x = aux u1 @ aux u2 in
        let x' = List.unique x in
        (*let _ = assert (x = x') in*)
        x'
    | Emp -> []
  in
  let xs = List.sort ~compare:Stdlib.compare @@ aux u in
  match xs with
  | [] -> failwith "canonize"
  | [ x ] -> x
  | x :: xs -> List.fold_left ~init:x xs ~f:(fun x y -> Alter (x, y))

let rec of_table_aux = function
  | Leaf -> [ ("leaf", []) ]
  | Label (id1, id2, id3) -> [ (id1, [ id2; id3 ]) ]
  | Alter (u1, u2) -> of_table_aux u1 @ of_table_aux u2
  | Emp -> failwith "TreeAutomaton.of_table_aux"

let of_table rs = List.map ~f:(fun (id, u) -> (id, of_table_aux u)) rs
let make_table xs = List.classify xs

let pr_table ppf trs =
  List.iter trs ~f:(fun (id1, xs) ->
      List.iter xs ~f:(fun (id2, ids) ->
          Format.fprintf ppf "%a %a -> %a.@\n" String.pr id1 String.pr id2
            (List.pr String.pr " ") ids))

let next_ids_table = List.concat_map ~f:snd

(* without changing order*)
let remove_unreachable_table ids trs =
  let reachable_ids =
    set_reachable (List.unique ids) (fun id -> next_ids_table (assoc id trs))
  in
  List.filter
    ~f:(fun (id, _) -> List.mem ~equal:String.equal reachable_ids id)
    trs

let reachable_table id trs =
  List.map
    ~f:(fun id -> (id, assoc id trs))
    (set_reachable [ id ] (fun id -> next_ids_table (assoc id trs)))

let number_of_states trs = List.length @@ List.unique @@ List.map ~f:fst trs

(*
let parse_file filename =
  let inchan = open_in filename in
  let lb = Lexing.from_channel inchan in
  let _ = lb.Lexing.lex_curr_p <-
    { Lexing.pos_fname = Filename.basename filename; Lexing.pos_lnum = 1; Lexing.pos_cnum = 0; Lexing.pos_bol = 0 } in
  let tl = Parser.xmltypedefs Lexer.token lb in
  let _ = close_in inchan in
  tl

let parse_string str =
  let lb = Lexing.from_string str in
  let _ = lb.Lexing.lex_curr_p <-
    { Lexing.pos_fname = ""; Lexing.pos_lnum = 1; Lexing.pos_cnum = 0; Lexing.pos_bol = 0 } in
  Parser.xmltypedefs Lexer.token lb

let _ =
  let filename =
    if Array.length Sys.argv = 2 then
      Sys.argv.(1)
    else
      failwith "invalid arguments"
  in
  let env = parse_file filename in
  Format.printf "@[<v>";
  let env = RegTreeExp.elim_kleene_env env in
  let env = RegTreeExp.elim_option_env env in
(*
  List.iter (fun (id, t) -> Format.printf "type %s = %a@," id RegTreeExp.pr t) env;
  Format.printf "@,";
*)
  let rs = RegTreeExp.to_ta_env env env [] [] in
  let rs = List.map (fun (id, u) -> id, TreeAutomaton.canonize u) rs in
  let (id, _) = List.hd rs in
  let rs = TreeAutomaton.remove_unreachable [id] rs in
(*
  List.iter (fun (id, u) -> Format.printf "%s -> %a@," id TreeAutomaton.pr u) rs;
*)
  let rs = TreeAutomaton.minimize rs in
  let rn = List.mapi (fun i (id, _) -> id, "q" ^ (string_of_int i)) rs in
  let rs = List.map (fun (id, u) -> List.assoc id rn, TreeAutomaton.rename rn u) rs in
(*
  List.iter (fun (id, u) -> Format.printf "%s -> %a@," id TreeAutomaton.pr u) rs;
*)
  let trs = TreeAutomaton.of_table rs in
  let trs_out = trs in
  Format.printf "%%BEGINA@,";
  Format.printf "%a" TreeAutomaton.pr_table trs_out;
  Format.printf "%%ENDA@,";
  Format.printf "@]"
 *)
