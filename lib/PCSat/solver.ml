open Core
open Common.Util
open Coordination

module type SolverType = sig
  val solve: ?bpvs:(Ast.Ident.tvar Set.Poly.t) -> ?print_sol:bool ->
    PCSP.Problem.t -> (PCSP.Problem.solution * int(*#iterations*)) Core.Or_error.t
end

module Make (Config: Config.ConfigType): SolverType = struct
  let config = Config.config

  let pvar_eliminator =
    let open Or_error in
    ExtFile.unwrap config.pvar_eliminator >>= fun cfg ->
    Ok (PvarEliminator.make cfg)

  let coordinator =
    let open Or_error in
    ExtFile.unwrap config.coordinator >>= fun cfg ->
    Ok (Coordinator.make cfg)

  let solve_each ?(bpvs=Set.Poly.empty) pcsp =
    let open Or_error in
    pvar_eliminator >>= fun pvar_eliminator ->
    let (module PvarEliminator : PvarEliminator.PvarEliminatorType) = pvar_eliminator in
    coordinator >>= fun coordinator ->
    let (module Coordinator : Coordinator.CoordinatorType) = coordinator in
    PvarEliminator.elim ~bpvs Coordinator.solve pcsp

  let solve ?(bpvs=Set.Poly.empty) ?(print_sol=false) pcsp =
    let open Or_error in
    let pcsps = if config.solve_each_query then PCSP.Problem.divide pcsp else [pcsp] in
    List.map pcsps ~f:(solve_each ~bpvs) |> Or_error.combine_errors >>= (fun sols ->
        let (solution, iteration) = PCSP.Problem.merge_sol pcsp sols in
        if print_sol then begin
          Out_channel.print_endline @@
          if config.sygus_comp then
            PCSP.Problem.str_of_sygus_solution solution
          else if config.output_iteration then
            Printf.sprintf "%s,%d" (PCSP.Problem.str_of_solution solution) iteration
          else
            PCSP.Problem.str_of_solution solution;
          Out_channel.flush stdout
        end;
        Or_error.return (solution, iteration))
end
