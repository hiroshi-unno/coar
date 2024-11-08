open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.Ident
open Ast.Logic
open Ast.Assertion

type t = (dir_map * priority * fronts) * PCSP.Problem.t

type solution =
  | Unknown
  | Unsat
  | Sat of (tvar, term) Map.Poly.t
  | OptSat of (tvar, term) Map.Poly.t
  | OptSatInSpace of (tvar, term) Map.Poly.t
  | Skip
  | Timeout

let is_dup = function DUp -> true | _ -> false
let is_ddown = function DDown -> true | _ -> false
let reverse_direction = function DUp -> DDown | DDown -> DUp
let str_of_direction = function DUp -> "u'" | DDown -> "d'"
let pretty_str_of_direction = function DUp -> "⬆" | DDown -> "⬇"

let str_of_dir_map dir_map =
  Map.Poly.to_alist dir_map
  |> String.concat_map_list ~sep:", " ~f:(fun (p, d) ->
         sprintf "%s -> %s" (name_of_tvar p) (pretty_str_of_direction d))
  |> sprintf "{%s}"

let str_of_priority priority =
  String.concat_map_list ~sep:" ⊏ " priority ~f:name_of_tvar

let topological_sort (ps : 'a list) (priority_pairs : ('a * 'a) list) =
  let rec inner indegrees ret =
    if Map.Poly.for_all indegrees ~f:(fun d -> d < 0) then List.rev ret
    else
      match Map.find_with indegrees ~f:(fun d -> d = 0) with
      | [] -> failwith "topological_sort: there is a loop"
      | (p, _) :: _ ->
          let indegrees = Map.Poly.set indegrees ~key:p ~data:(-1) in
          let indegrees =
            List.fold priority_pairs ~init:indegrees ~f:(fun acc (a, b) ->
                (* L.debug ~pre:"indegree--" @@ name_of_tvar b; *)
                if Stdlib.(a = p) then
                  Map.Poly.set acc ~key:b ~data:(Map.Poly.find_exn acc b - 1)
                else acc)
          in
          inner indegrees @@ (p :: ret)
  in
  let indegrees =
    Map.Poly.of_alist_exn
    @@ List.map ps ~f:(fun p ->
           (* L.debug ~pre:"indegree 0" @@ name_of_tvar p;  *)
           (p, 0))
  in
  let indegrees =
    List.fold priority_pairs ~init:indegrees ~f:(fun acc (_, b) ->
        (* a --> b*)
        (* L.debug ~pre:"indegree++" @@ name_of_tvar b; *)
        Map.Poly.set acc ~key:b ~data:(Map.Poly.find_exn acc b + 1))
  in
  inner indegrees []

(* For tvar symbol *)
let direction_tvar d = function Tvar ident -> Tvar (str_of_direction d ^ ident)

let tvar_is_up = function
  | Tvar ident -> String.is_prefix ident ~prefix:(str_of_direction DUp)

let tvar_is_down = function
  | Tvar ident -> String.is_prefix ident ~prefix:(str_of_direction DDown)

let direction_of_tvar tvar =
  if tvar_is_up tvar then Some DUp
  else if tvar_is_down tvar then Some DDown
  else None

let direction_of_tvar_exn = function Some d -> d | None -> assert false

let extract_tvar tvar =
  if tvar_is_up tvar || tvar_is_down tvar then tvar else tvar

let str_of_fronts fronts =
  Map.Poly.to_alist fronts
  |> String.concat_map_list ~sep:"\n" ~f:(fun (p, term) ->
         sprintf "  %s -> %s" (name_of_tvar p) (ExtTerm.str_of term))
  |> sprintf "{\n%s\n}"

let of_pcsp pcsp =
  let delta = PCSP.Problem.senv_of @@ PCSP.Problem.remove_unused_params pcsp in
  let dir_map =
    Map.Poly.filter_map delta ~f:(fun s ->
        if Sort.is_arrow s then Some DUp else None)
  in
  let fronts = Map.Poly.empty in
  let priority = topological_sort (Map.Poly.keys dir_map) [] in
  ((dir_map, priority, fronts), pcsp)

let of_dir_map_priorpair_pcsp dir_map prior pcsp =
  let fronts = Map.Poly.empty in
  let priority = topological_sort (Map.Poly.keys dir_map) prior in
  ((dir_map, priority, fronts), pcsp)

(* for improve *)

let mk_fresh_args sort =
  let sorts = Sort.args_of sort in
  let senv = mk_fresh_sort_env_list sorts in
  let args = List.map senv ~f:(fst >> ExtTerm.mk_var) in
  (args, senv)

let genc ~is_pos d (fronts : fronts * fronts) delta theta (tvar, sort) : term =
  let args, senv = mk_fresh_args sort in
  (* L.debug ~pre:("genc:sort_of " ^ name_of_tvar tvar) @@ ExtTerm.str_of_sort sort; *)
  (* L.debug ~pre:"genc:delta" @@ str_of_sort_env_map delta; *)
  let simplify body =
    (* L.debug ~pre:"simplify" @@ ExtTerm.str_of body; *)
    ExtTerm.simplify_formula delta (Map.Poly.of_alist_exn senv) body
  in
  let pf =
    match Map.Poly.find ((if is_pos then fst else snd) @@ fronts) tvar with
    | Some term -> ExtTerm.beta_reduction (Term.mk_apps term args)
    | None -> ExtTerm.mk_bool true
  in
  let sol =
    match Map.Poly.find theta tvar with
    | Some sol -> sol
    | None -> ExtTerm.mk_lambda senv @@ ExtTerm.mk_bool true
  in
  let ps =
    ExtTerm.simplify_formula delta (Map.Poly.of_alist_exn senv)
    @@ ExtTerm.beta_reduction (Term.mk_apps sol args)
  in
  let p = ExtTerm.mk_var_app tvar args in
  let body, head =
    let body, head =
      match d with
      | DUp -> (ExtTerm.and_of [ pf; ps ], p)
      | DDown -> (ExtTerm.and_of [ pf; p ], ps)
    in
    (simplify body, simplify head)
  in
  ExtTerm.mk_lambda senv
  @@
  if is_pos then ExtTerm.imply_of body head
  else simplify @@ ExtTerm.neg_of @@ ExtTerm.imply_of body head

let is_unknown = function Unknown -> true | _ -> false
let is_unsat = function Unsat -> true | _ -> false
let is_sat = function Sat _ -> true | _ -> false
let is_maxsat = function OptSat _ -> true | _ -> false
let is_maxsat_inspace = function OptSatInSpace _ -> true | _ -> false
let is_skip = function Skip -> true | _ -> false
let filter_sol delta sol = Map.Poly.filter_keys ~f:(Map.Poly.mem delta) sol

let str_of_solution delta iter = function
  | Unknown -> sprintf "Unknown, %d" iter
  | Unsat -> sprintf "Unsat, %d" iter
  | Skip -> sprintf "Skip, %d" iter
  | Sat sol ->
      let sol = filter_sol delta sol in
      sprintf "Sat, %d\n%s" iter @@ CandSol.str_of @@ CandSol.of_subst delta sol
  | OptSat sol ->
      let sol = filter_sol delta sol in
      sprintf "Maxsat, %d\n%s" iter
      @@ CandSol.str_of @@ CandSol.of_subst delta sol
  | OptSatInSpace sol ->
      let sol = filter_sol delta sol in
      sprintf "MaxsatInSpace, %d\n%s" iter
      @@ CandSol.str_of @@ CandSol.of_subst delta sol
  | Timeout -> sprintf "Timeout, %d" iter

let equal_sol sol1 sol2 =
  match (sol1, sol2) with
  | Unknown, Unknown | Unsat, Unsat | Skip, Skip | Timeout, Timeout -> true
  | Sat sol1, Sat sol2
  | OptSat sol1, OptSat sol2
  | OptSatInSpace sol1, OptSatInSpace sol2 ->
      Map.Poly.equal Stdlib.( = ) sol1 sol2
  | _ -> false
