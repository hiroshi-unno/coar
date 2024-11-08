open Core
open Common.Ext
open Automata

(** Regular tree expressions *)

type ('sym, 'lab) t =
  | Nil
  | Symbol of 'sym
  | Label of 'lab * ('sym, 'lab) t
  | Concat of ('sym, 'lab) t * ('sym, 'lab) t
  | Alter of ('sym, 'lab) t * ('sym, 'lab) t
  | Kleene of ('sym, 'lab) t
  | Option of ('sym, 'lab) t

let canonize t =
  let rec aux = function
    | Nil | Symbol _ | Label (_, _) | Concat (_, _) | Kleene _ | Option _ ->
        [ t ]
    | Alter (t1, t2) ->
        let x = aux t1 @ aux t2 in
        let x' = List.unique x in
        (*let _ = assert (x = x') in*)
        x'
  in
  match List.sort ~compare:Stdlib.compare @@ aux t with
  | [] -> failwith "canonize"
  | [ x ] -> x
  | x :: xs -> List.fold_left ~init:x xs ~f:(fun x y -> Alter (x, y))

let rec pr ppf = function
  | Nil -> Format.fprintf ppf "()"
  | Symbol id -> String.pr ppf id
  | Label (id, t) -> Format.fprintf ppf "%a[%a]" String.pr id pr t
  | Concat (t1, t2) -> Format.fprintf ppf "(%a, %a)" pr t1 pr t2
  | Alter (t1, t2) -> Format.fprintf ppf "(%a | %a)" pr t1 pr t2
  | Kleene t -> Format.fprintf ppf "%a*" pr t
  | Option t -> Format.fprintf ppf "%a?" pr t

let gen_nt =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    "%N" ^ string_of_int !cnt

let rec elim_kleene t sub =
  match t with
  | Nil -> (Nil, sub)
  | Symbol id -> (Symbol id, sub)
  | Label (id, t) ->
      let t, sub = elim_kleene t sub in
      (Label (id, t), sub)
  | Concat (t1, t2) ->
      let t1, sub = elim_kleene t1 sub in
      let t2, sub = elim_kleene t2 sub in
      (Concat (t1, t2), sub)
  | Alter (t1, t2) ->
      let t1, sub = elim_kleene t1 sub in
      let t2, sub = elim_kleene t2 sub in
      (Alter (t1, t2), sub)
  | Kleene t -> (
      let t, sub = elim_kleene t sub in
      try (Symbol (List.Assoc.find_exn ~equal:Stdlib.( = ) sub t), sub)
      with Not_found_s _ ->
        let id = gen_nt () in
        (Symbol id, sub @ [ (t, id) ]))
  | Option t ->
      let t, sub = elim_kleene t sub in
      (Option t, sub)

let elim_kleene_env env =
  let sub, env =
    List.fold_left ~init:([], []) env ~f:(fun (sub, env) (id, t) ->
        let t, sub = elim_kleene t sub in
        (sub, env @ [ (id, t) ]))
  in
  env
  @ List.map ~f:(fun (t, id) -> (id, Alter (Concat (t, Symbol id), Nil))) sub

let rec elim_option t sub =
  match t with
  | Nil -> (Nil, sub)
  | Symbol id -> (Symbol id, sub)
  | Label (id, t) ->
      let t, sub = elim_option t sub in
      (Label (id, t), sub)
  | Concat (t1, t2) ->
      let t1, sub = elim_option t1 sub in
      let t2, sub = elim_option t2 sub in
      (Concat (t1, t2), sub)
  | Alter (t1, t2) ->
      let t1, sub = elim_option t1 sub in
      let t2, sub = elim_option t2 sub in
      (Alter (t1, t2), sub)
  | Kleene t ->
      let t, sub = elim_option t sub in
      (Kleene t, sub)
  | Option t -> (
      let t, sub = elim_option t sub in
      try (Symbol (List.Assoc.find_exn ~equal:Stdlib.( = ) sub t), sub)
      with Not_found_s _ ->
        let id = gen_nt () in
        (Symbol id, sub @ [ (t, id) ]))

let elim_option_env env =
  let sub, env =
    List.fold_left ~init:([], []) env ~f:(fun (sub, env) (id, t) ->
        let t, sub = elim_option t sub in
        (sub, env @ [ (id, t) ]))
  in
  env @ List.map sub ~f:(fun (t, id) -> (id, Alter (t, Nil)))

let add wl wl' t =
  match canonize t with
  | Symbol id -> (id, wl)
  | _ -> (
      try
        let id, _ =
          List.find_exn (wl @ wl') ~f:(fun (_id, t') -> Stdlib.(t = t'))
        in
        (id, wl)
      with Not_found_s _ ->
        let id = gen_nt () in
        (id, wl @ [ (id, t) ]))

let rec to_ta env t wl wl' rho =
  match t with
  | Nil -> (RTA.Leaf, wl, wl')
  | Symbol id ->
      if List.mem ~equal:Stdlib.( = ) rho t then (RTA.Emp, wl, wl')
      else
        to_ta env
          (List.Assoc.find_exn ~equal:Stdlib.( = ) env id)
          wl wl' (t :: rho)
  | Label (id1, t) ->
      let id3, wl = add wl wl' Nil in
      let id2, wl = add wl wl' t in
      (RTA.Label (id1, id2, id3), wl, wl')
  | Concat (Nil, t) -> to_ta env t wl wl' rho
  | Concat (Symbol id, t1) ->
      if List.mem ~equal:Stdlib.( = ) rho t then (RTA.Emp, wl, wl')
      else
        to_ta env
          (Concat (List.Assoc.find_exn ~equal:Stdlib.( = ) env id, t1))
          wl wl' (t :: rho)
  | Concat (Label (id1, t1), t2) ->
      let id3, wl = add wl wl' t2 in
      let id2, wl = add wl wl' t1 in
      (RTA.Label (id1, id2, id3), wl, wl')
  | Concat (Concat (t1, t2), t3) ->
      to_ta env (Concat (t1, Concat (t2, t3))) wl wl' rho
  | Concat (Alter (t1, t2), t3) ->
      let u1, wl, wl' = to_ta env (Concat (t1, t3)) wl wl' rho in
      let u2, wl, wl' = to_ta env (Concat (t2, t3)) wl wl' rho in
      (RTA.Alter (u1, u2), wl, wl')
  | Concat (Kleene _, _) -> failwith ""
  | Concat (Option _, _) -> failwith ""
  | Option _ -> failwith ""
  | Alter (t1, t2) ->
      let u1, wl, wl' = to_ta env t1 wl wl' rho in
      let u2, wl, wl' = to_ta env t2 wl wl' rho in
      (RTA.Alter (u1, u2), wl, wl')
  | Kleene _t -> failwith ""

let rec to_ta_env env wl wl' rs =
  if false then (
    List.iter rs ~f:(fun (id, u) ->
        Format.printf "%s -> %a@," id (RTA.pr_body String.pr) u);
    List.iter wl ~f:(fun (id, t) -> Format.printf "%s -> %a@," id pr t);
    Format.printf "@,");
  match wl with
  | [] -> rs
  | (id, t) :: wl ->
      let u, wl, wl' = to_ta env t wl ((id, t) :: wl') [] in
      to_ta_env env wl wl' (rs @ [ (id, u) ])

let tta_of env =
  let env = elim_kleene_env env in
  let env = elim_option_env env in
  if false then (
    List.iter env ~f:(fun (id, t) -> Format.printf "type %s = %a@," id pr t);
    Format.printf "@,");
  let trs = to_ta_env env env [] [] in
  let trs = List.map trs ~f:(fun (id, u) -> (id, RTA.canonize_body u)) in
  let trs =
    TreeAutomaton.remove_unreachable ~next_ids_body:RTA.next_ids_body
      [ fst @@ List.hd_exn trs ]
      trs
  in
  if false then RTA.pr String.pr Format.std_formatter trs;
  let trs = RTA.minimize trs in
  let rn = List.mapi trs ~f:(fun i (id, _) -> (id, "q" ^ string_of_int i)) in
  let trs =
    List.map trs ~f:(fun (id, u) ->
        (List.Assoc.find_exn ~equal:Stdlib.( = ) rn id, RTA.rename_body rn u))
  in
  if false then RTA.pr String.pr Format.std_formatter trs;
  RTA.tta_of trs

(*
let parse_file filename =
  let inchan = In_channel.create filename in
  let lb = Lexing.from_channel inchan in
  lb.Lexing.lex_curr_p <-
    {
      Lexing.pos_fname = Filename.basename filename;
      Lexing.pos_lnum = 1;
      Lexing.pos_cnum = 0;
      Lexing.pos_bol = 0;
    };
  let tl = RegTreeExpParser.regtreeexpdefs RegTreeExpLexer.token lb in
  In_channel.close inchan;
  tl

let parse_string str =
  let lb = Lexing.from_string str in
  lb.Lexing.lex_curr_p <-
    {
      Lexing.pos_fname = "";
      Lexing.pos_lnum = 1;
      Lexing.pos_cnum = 0;
      Lexing.pos_bol = 0;
    };
  RegTreeExpParser.regtreeexpdefs RegTreeExpLexer.token lb

let main filename =
  let env = parse_file filename in
  Format.printf "@[<v>";
  let trs = tta_of env in
  Format.printf "%%BEGINA@,";
  TTA.pr_map String.pr Format.std_formatter trs;
  Format.printf "%%ENDA@,";
  Format.printf "@]"
*)
