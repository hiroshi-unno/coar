open Core

module type SolverType = sig
  val solve: ?bpvs:(Ast.Ident.tvar Set.Poly.t) -> ?print_sol:bool ->
    PCSP.Problem.t -> (PCSP.Problem.solution * int(*#iterations*)) Or_error.t
end

module Make (Cfg: Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  let solve = 
    let open Or_error in
    match config with
    | Config.PCSat cfg ->
      let module Cfg = struct let config = cfg end in
      let module PCSat = PCSat.Solver.Make(Cfg) in
      fun ?(bpvs=Set.Poly.empty) ?(print_sol=false) pcsp -> PCSat.solve ~bpvs ~print_sol pcsp
    | Config.SPACER cfg ->
      let module Cfg = struct let config = cfg end in
      let module SPACER = SPACER.Solver.Make(Cfg) in
      fun ?bpvs ?(print_sol=false) pcsp ->
        ignore bpvs;
        SPACER.solve ~print_sol pcsp >>= fun sol -> Ok (sol, -1)
    | Hoice cfg ->
      let module Cfg = struct let config = cfg end in
      let module Hoice = Hoice.Solver.Make(Cfg) in
      fun ?bpvs ?(print_sol=false) pcsp ->
        ignore bpvs;
        Hoice.solve ~print_sol pcsp >>= fun sol -> Ok (sol, -1)
    | Forward ->
      fun ?bpvs ?(print_sol=false) pcsp ->
        ignore bpvs;
        PCSP.ForwardPropagate.solve pcsp >>= fun sol ->
        if print_sol then begin
          Out_channel.print_endline @@ Printf.sprintf "%s" (PCSP.Problem.str_of_solution sol);
          Out_channel.flush stdout
        end;
        Ok (sol, -1)
end
