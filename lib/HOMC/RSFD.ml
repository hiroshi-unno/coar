open Core
open Ast
open Common.Ext
open Common.Combinator
open Automata

type term =
  | Fd of (Ident.tvar, int) Either.t
  | Nonterm of Ident.tvar
  | Var of Ident.tvar
  | Term of Ident.tvar
  | App of term * term
  | Case of Ident.tvar * term list
  | CaseFd of (Ident.tvar, int) Either.t * term list

type t = (Ident.tvar * (Ident.tvar list * term)) list

let app t1 t2 = App (t1, t2)
let apps t ts = List.fold_left ~init:t ts ~f:app

let rec sizeof_term = function
  | Fd _ -> 1
  | Nonterm _ -> 1
  | Var _ -> 1
  | Term _ -> 1
  | App (t1, t2) -> sizeof_term t1 + sizeof_term t2
  | Case (_, ts) | CaseFd (_, ts) ->
      1 + Integer.sum_list (List.map ~f:sizeof_term ts)

let rec subst sub = function
  | Fd id -> Fd id
  | Nonterm id -> Nonterm id
  | Var id -> (
      match List.Assoc.find ~equal:Ident.tvar_equal sub id with
      | Some r -> r
      | None -> Var id)
  | Term id -> Term id
  | App (t1, t2) -> App (subst sub t1, subst sub t2)
  | Case (id, ts) -> (
      let id' =
        match List.Assoc.find ~equal:Ident.tvar_equal sub id with
        | Some r -> r
        | None -> Var id
      in
      match id' with
      | Fd x -> CaseFd (x, List.map ~f:(subst sub) ts)
      | Var x -> Case (x, List.map ~f:(subst sub) ts)
      | _ -> failwith "RSFD.subst")
  | CaseFd (id, ts) -> CaseFd (id, List.map ~f:(subst sub) ts)

let sizeof (rules : t) =
  Integer.sum_list @@ List.map rules ~f:(snd >> snd >> sizeof_term)

let reachable id (rs : t) =
  let assoc id rs =
    match List.Assoc.find ~equal:Ident.tvar_equal rs id with
    | Some r -> r
    | None -> failwith ("non-terminal " ^ Ident.name_of_tvar id ^ " not found")
  in
  let next_nts (_, t) =
    let rec next_nts' = function
      | Fd _ -> []
      | Nonterm id -> [ id ]
      | Var _ | Term _ -> []
      | App (t1, t2) -> next_nts' t1 @ next_nts' t2
      | Case (_, ts) -> List.concat_map ~f:next_nts' ts
      | CaseFd (_, ts) -> List.concat_map ~f:next_nts' ts
    in
    next_nts' t
  in
  List.map ~f:(fun id -> (id, assoc id rs))
  @@ List.reachable [ id ] (fun id -> next_nts (assoc id rs))

let rec reduce (trs : TTA.trs) = function
  | (Fd _ | Nonterm _ | Var _ | Term _) as t -> t
  | App (t1, t2) -> App (reduce trs t1, reduce trs t2)
  | Case (id, ts) -> Case (id, List.map ~f:(reduce trs) ts)
  | CaseFd (id, ts) ->
      let idx =
        match id with
        | Second idx -> idx
        | First id -> (
            match
              List.find_mapi trs ~f:(fun i (s, _) ->
                  if String.(Ident.name_of_tvar id = s) then Some i else None)
            with
            | Some idx -> idx
            | None -> failwith "RSFD.reduce")
      in
      reduce trs @@ List.nth_exn ts idx

let rec fv bvs = function
  | Fd _id -> []
  | Nonterm _id -> []
  | Var id -> if List.mem ~equal:Ident.tvar_equal bvs id then [] else [ id ]
  | Term _id -> []
  | App (t1, t2) -> List.unique (fv bvs t1 @ fv bvs t2)
  | Case (id, ts) -> List.unique (id :: List.concat_map ~f:(fv bvs) ts)
  | CaseFd (_id, ts) -> List.unique @@ List.concat_map ~f:(fv bvs) ts

let case_size_th = ref 64 (* ad hoc threshold *)
let case_id = ref 1

let new_case_nt () =
  let i = !case_id in
  case_id := i + 1;
  "CASE" ^ string_of_int i

(* Note: this function must be applied after the "reduce" function *)
let rec externalize_large_cases = function
  | (Fd _ | Nonterm _ | Var _ | Term _) as t -> (t, [])
  | App (t1, t2) ->
      let t1', f1 = externalize_large_cases t1 in
      let t2', f2 = externalize_large_cases t2 in
      (App (t1', t2'), f1 @ f2)
  | Case (id, ts) as t ->
      if sizeof_term t >= !case_size_th then
        let ts, fs = List.unzip @@ List.map ~f:externalize_large_cases ts in
        let fs = List.concat fs in
        let _n = List.length ts in
        let externalize t =
          if sizeof_term t >= !case_size_th then
            let fvs = fv [] t in
            let vars = List.map ~f:(fun x -> Var x) fvs in
            let nt = new_case_nt () in
            let t' = apps (Nonterm (Ident.Tvar nt)) vars in
            (t', [ (Ident.Tvar nt, (fvs, t)) ])
          else (t, [])
        in
        let ts', fs' = List.unzip @@ List.map ~f:externalize ts in
        (Case (id, ts'), List.concat fs' @ fs)
      else (t, [])
  | CaseFd (_id, _ts) -> failwith "externalize_large_cases"

let optimize_case (rules : t) =
  let rules, fs =
    List.unzip
    @@ List.map rules ~f:(fun (id, (ids, t)) ->
           let t', fs = externalize_large_cases t in
           ((id, (ids, t')), fs))
  in
  rules @ List.concat fs

let pr_id ppf id = Format.fprintf ppf "%s" (Ident.name_of_tvar id)

let rec pr_aux b (trs : TTA.trs) ppf = function
  | Fd id ->
      let idx =
        match id with
        | Second idx -> idx
        | First id -> (
            match
              List.find_mapi trs ~f:(fun i (s, _) ->
                  if String.(Ident.name_of_tvar id = s) then Some i else None)
            with
            | Some idx -> idx
            | None -> failwith "RSFD.pr_aux")
      in
      Format.fprintf ppf "%d" idx
  | Nonterm id | Var id | Term id -> pr_id ppf id
  | App (t1, t2) ->
      if b then Format.fprintf ppf "(";
      Format.fprintf ppf "%a %a" (pr_aux false trs) t1 (pr_aux true trs) t2;
      if b then Format.fprintf ppf ")"
  | Case (id, ts) ->
      if b then Format.fprintf ppf "(";
      Format.fprintf ppf "_case %d %s %a" (List.length trs)
        (Ident.name_of_tvar id)
        (List.pr (pr_aux true trs) " ")
        ts;
      if b then Format.fprintf ppf ")"
  | CaseFd (id, ts) ->
      if b then Format.fprintf ppf "(";
      Format.fprintf ppf "_case %d %a %a" (List.length trs) (pr_aux b trs)
        (Fd id)
        (List.pr (pr_aux true trs) " ")
        ts;
      if b then Format.fprintf ppf ")"

let pr_rules (trs : TTA.trs) ppf (rules : t) =
  if List.is_empty rules then Format.fprintf ppf "\n"
  else
    List.iter rules ~f:(fun (id, (ids, t)) ->
        Format.fprintf ppf "%s -> %a.@,"
          (String.concat ~sep:" "
             (List.map ~f:Ident.name_of_tvar @@ (id :: ids)))
          (pr_aux false trs) t)

let verbose_fail = ref false

let fail id =
  if !verbose_fail then Term (Ident.Tvar ("fail_" ^ Ident.name_of_tvar id))
  else Term (Ident.Tvar "fail")
