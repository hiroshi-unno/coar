open Core
open Common.Ext
open Automaton

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
  let rec aux t =
    match t with
    | Nil | Symbol _ | Label (_, _) | Concat (_, _) | Kleene _ | Option _ -> [t]
    | Alter (t1, t2) ->
      let x = (aux t1) @ (aux t2) in
      let x' = List.unique x in
      (*let _ = assert (x = x') in*)
      x'
  in
  match List.sort ~compare:Stdlib.compare @@ aux t with
    [] -> failwith "canonize"
  | [x] -> x
  | x :: xs -> List.fold_left ~init:x xs ~f:(fun x y -> Alter (x, y))

let rec pr ppf = function
  | Nil ->
    Format.fprintf ppf "()"
  | Symbol id ->
    Format.fprintf ppf "%a" String.pr id
  | Label (id, t) ->
    Format.fprintf ppf "%a[%a]" String.pr id pr t
  | Concat (t1, t2) ->
    Format.fprintf ppf "(%a, %a)" pr t1 pr t2
  | Alter (t1, t2) ->
    Format.fprintf ppf "(%a | %a)" pr t1 pr t2
  | Kleene t ->
    Format.fprintf ppf "%a*" pr t
  | Option t ->
    Format.fprintf ppf "%a?" pr t

let gen_nt =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    "%N" ^ string_of_int !cnt

let rec elim_kleene t sub =
  match t with
  | Nil ->
    Nil, sub
  | Symbol id ->
    Symbol id, sub
  | Label (id, t) ->
    let t, sub = elim_kleene t sub in
    Label (id, t), sub
  | Concat (t1, t2) ->
    let t1, sub = elim_kleene t1 sub in
    let t2, sub = elim_kleene t2 sub in
    Concat (t1, t2), sub
  | Alter (t1, t2) ->
    let t1, sub = elim_kleene t1 sub in
    let t2, sub = elim_kleene t2 sub in
    Alter (t1, t2), sub
  | Kleene t ->
    let t, sub = elim_kleene t sub in
    (try
       Symbol (List.Assoc.find_exn ~equal:Stdlib.(=) sub t), sub
     with Not_found_s _ ->
       let id = gen_nt () in
       Symbol id, sub @ [t, id])
  | Option t ->
    let t, sub = elim_kleene t sub in
    Option t, sub

let elim_kleene_env env =
  let sub, env =
    List.fold_left ~init:([], []) env ~f:(fun (sub, env) (id, t) ->
        let t, sub = elim_kleene t sub in
        sub, env @ [id, t])
  in
  env @ List.map ~f:(fun (t, id) -> id, Alter (Concat (t, Symbol id), Nil)) sub

let rec elim_option t sub =
  match t with
  | Nil ->
    Nil, sub
  | Symbol id ->
    Symbol id, sub
  | Label (id, t) ->
    let t, sub = elim_option t sub in
    Label (id, t), sub
  | Concat (t1, t2) ->
    let t1, sub = elim_option t1 sub in
    let t2, sub = elim_option t2 sub in
    Concat (t1, t2), sub
  | Alter (t1, t2) ->
    let t1, sub = elim_option t1 sub in
    let t2, sub = elim_option t2 sub in
    Alter (t1, t2), sub
  | Kleene t ->
    let t, sub = elim_option t sub in
    Kleene t, sub
  | Option t ->
    let t, sub = elim_option t sub in
    (try
       Symbol (List.Assoc.find_exn ~equal:Stdlib.(=) sub t), sub
     with Not_found_s _ ->
       let id = gen_nt () in
       Symbol id, sub @ [t, id])

let elim_option_env env =
  let sub, env =
    List.fold_left ~init:([], []) env ~f:(fun (sub, env) (id, t) ->
        let t, sub = elim_option t sub in
        sub, env @ [id, t])
  in
  env @ List.map ~f:(fun (t, id) -> id, Alter (t, Nil)) sub



let add wl wl' t =
  let t = canonize t in
  match t with
  | Symbol id ->
    id, wl
  | _ ->
    (try
       let id, _ = List.find_exn ~f:(fun (_id, t') -> Stdlib.(t = t')) (wl @ wl') in
       id, wl
     with Not_found_s _ ->
       let id = gen_nt () in
       id, wl @ [id, t])

let rec to_ta env t wl wl' rho =
  match t with
  | Nil ->
    TreeAutomaton.Leaf, wl, wl'
  | Symbol id ->
    if List.mem ~equal:Stdlib.(=) rho t then
      TreeAutomaton.Emp, wl, wl'
    else
      to_ta env (List.Assoc.find_exn ~equal:Stdlib.(=) env id) wl wl' (t::rho)
  | Label (id1, t) ->
    let id3, wl = add wl wl' Nil in
    let id2, wl = add wl wl' t in
    TreeAutomaton.Label (id1, id2, id3), wl, wl'
  | Concat (Nil, t) ->
    to_ta env t wl wl' rho
  | Concat (Symbol id, t1) ->
    if List.mem ~equal:Stdlib.(=) rho t then
      TreeAutomaton.Emp, wl, wl'
    else
      to_ta env (Concat (List.Assoc.find_exn ~equal:Stdlib.(=) env id, t1)) wl wl' (t::rho)
  | Concat (Label (id1, t1), t2) ->
    let id3, wl = add wl wl' t2 in
    let id2, wl = add wl wl' t1 in
    TreeAutomaton.Label (id1, id2, id3), wl, wl'
  | Concat (Concat (t1, t2), t3) ->
    to_ta env (Concat (t1, Concat (t2, t3))) wl wl' rho
  | Concat (Alter (t1, t2), t3) ->
    let u1, wl, wl' = to_ta env (Concat (t1, t3)) wl wl' rho in
    let u2, wl, wl' = to_ta env (Concat (t2, t3)) wl wl' rho in
    TreeAutomaton.Alter (u1, u2), wl, wl'
  | Concat (Kleene _, _) -> failwith ""
  | Concat (Option _, _) -> failwith ""
  | Option _ -> failwith ""
  | Alter (t1, t2) ->
    let u1, wl, wl' = to_ta env t1 wl wl' rho in
    let u2, wl, wl' = to_ta env t2 wl wl' rho in
    TreeAutomaton.Alter (u1, u2), wl, wl'
  | Kleene _t -> failwith ""

let rec to_ta_env env wl wl' rs =
(*
  List.iter (fun (id, u) -> Format.printf "%s -> %a@," id TreeAutomaton.pr u) rs;
  List.iter (fun (id, t) -> Format.printf "%s -> %a@," id pr t) wl;
  Format.printf "@,";
*)
  match wl with
  | [] -> rs
  | (id, t) :: wl ->
    let u, wl, wl' = to_ta env t wl ((id, t) :: wl') [] in
    to_ta_env env wl wl' (rs @ [id, u])
