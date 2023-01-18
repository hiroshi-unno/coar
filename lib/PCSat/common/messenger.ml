open Core
open Common.Ext
open Ast

type Common.Messenger.info += Examples of ExClauseSet.t

let send_examples messenger id exs =
  match messenger with
  | None -> ()
  | Some messenger -> Common.Messenger.send_boardcast messenger id @@ Examples exs
let send_cand_sol messenger id sol =
  match messenger with
  | None -> ()
  | Some messenger -> Common.Messenger.send_boardcast messenger id @@ PCSP.Problem.CandidateSolution sol

let send_candidate_partial_solution ?(print=(fun _ -> ())) messenger id (pfwcsp, counterexamples, cand, cand_tag, lbs_opt, cls) =
  let query_clauses = PCSP.Problem.unpreprocessable_clauses_of pfwcsp in
  if Set.Poly.is_empty query_clauses then ()(*ToDo*)
  else
    let partial_sol_targets = PCSP.Problem.partial_sol_targets_of pfwcsp in
    let partial_sol_cand_of target_pvar sol =
      let pvars =
        Set.Poly.map ~f:(fun ri -> ri.PCSP.Params.name) @@
        Map.Poly.find_exn partial_sol_targets target_pvar
      in
      Map.Poly.filteri sol ~f:(fun ~key ~data:_ -> Set.Poly.mem pvars key)
    in
    let violated_non_query_clauses =
      Set.concat_map counterexamples ~f:(fun (_, sources) ->
          (* filter out query clauses *)
          Set.Poly.of_list @@ List.filter_map sources ~f:(function
              | ClauseGraph.Clause c, _ when not @@ Set.Poly.mem query_clauses c -> Some c
              | _ -> None))
    in
    let full_non_query_clauses = Set.Poly.diff cls query_clauses in
    let sol = PCSP.Problem.sol_of_candidate pfwcsp cand in
    let sol_before_red = CandSol.to_subst cand in
    match cand_tag with
    | CandSol.Partial target_pvar ->
      let sol = partial_sol_cand_of target_pvar sol in
      let sol_before_red = partial_sol_cand_of target_pvar sol_before_red in
      print @@ lazy (sprintf "cast a candidate partial solution to messenger for [%s]" @@ Ident.name_of_tvar target_pvar);
      send_cand_sol messenger id (sol, sol_before_red, violated_non_query_clauses, full_non_query_clauses, lbs_opt)
    | Total _with_sample ->
      let dep_graph = PCSP.Problem.dep_graph_of pfwcsp in
      let target_pvars = Map.key_set partial_sol_targets in
      if Set.Poly.is_empty target_pvars then begin
        (*ToDo: this case is necessary because [partial_sol_targets] is empty if [gen_extra_partial_sols] is false*)
        print @@ lazy ("cast a candidate partial solution to messenger");
        send_cand_sol messenger id (sol, sol_before_red, violated_non_query_clauses, full_non_query_clauses, lbs_opt)
      end else if (match lbs_opt with Some _ -> true | None -> false) ||
                  (* if [check_part_sol_with_lbs] is false, necessary to satisfy [is_qualified_partial_solution] for some target pvar *)
                  Set.Poly.exists target_pvars ~f:(fun target_pvar ->
                      let pvars_the_target_pvar_depends_on = Map.Poly.find_exn dep_graph target_pvar in
                      PCSP.Problem.is_qualified_partial_solution
                        pvars_the_target_pvar_depends_on target_pvars violated_non_query_clauses)
      then begin
        print @@ lazy ("cast a candidate partial solution to messenger");
        send_cand_sol messenger id (sol, sol_before_red, violated_non_query_clauses, full_non_query_clauses, lbs_opt)
      end

let receive_request messenger id =
  match messenger with
  | None -> ()
  | Some messenger ->
    match Common.Messenger.receive_request messenger id with
    | None -> ()
    | Some request -> Common.Messenger.exec_request messenger request
let receive_all_examples messenger id =
  match messenger with
  | None -> Set.Poly.empty
  | Some messenger ->
    Common.Messenger.receive_all_infos_with messenger id
      ~filter:(function Examples _ -> true | _ -> false)
    |> List.map ~f:(function (_, Examples exs) -> exs | _ -> Set.Poly.empty)
    |> Set.Poly.union_list
let receive_bounds messenger id pfwcsp vs =
  match messenger with
  | None -> ()
  | Some messenger ->
    Common.Messenger.receive_all_infos_with messenger id ~filter:(function (PCSP.Problem.LowerBounds _ | PCSP.Problem.UpperBounds _) -> true | _ -> false)
    |> List.iter ~f:(function
        | (_, PCSP.Problem.LowerBounds bounds) ->
          Map.Poly.iteri bounds ~f:(fun ~key ~data ->
              VersionSpace.add_bound_as_learned_clause id pfwcsp vs key data false)
        | (_, PCSP.Problem.UpperBounds bounds) ->
          Map.Poly.iteri bounds ~f:(fun ~key ~data ->
              VersionSpace.add_bound_as_learned_clause id pfwcsp vs key data true)
        | _ -> failwith "receive_partial_solutions")
