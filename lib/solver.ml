open Core
open Async

module Config = struct

  type t =
    (* SAT solvers *)
    | Z3Sat of Z3Sat.Config.t (** configuration of Z3Sat *)
    | Minisat of MINISAT.Config.t (** configuration of Minisat *)
    (* SMT solvers *)
    | Z3Smt of Z3Smt.Config.t (** configuration of Z3Smt *)
    (* pfwCSP/CHC solvers *)
    | PCSat of PCSat.Config.t (** configuration of PCSat *)
    | SPACER of SPACER.Config.t (** configuration of SPACER *)
    | Hoice of Hoice.Config.t (** configuration of Hoice *)
    (* muCLP solvers *)
    | MuVal of MuVal.Config.t (** configuration of MuVal *)
    (* printer *)
    | Printer of Printer.Config.t
  [@@deriving yojson]

  module type ConfigType = sig val config : t end

  let instantiate_ext_files = let open Or_error in
    function
    | Z3Sat cfg ->
      Z3Sat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Z3Sat cfg)
    | Minisat cfg ->
      MINISAT.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Minisat cfg)

    | Z3Smt cfg ->
      Z3Smt.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Z3Smt cfg)
    | PCSat cfg ->
      PCSat.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (PCSat cfg)
    | SPACER cfg ->
      SPACER.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (SPACER cfg)
    | Hoice cfg ->
      Hoice.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Hoice cfg)

    | MuVal cfg ->
      MuVal.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (MuVal cfg)

    | Printer cfg ->
      Printer.Config.instantiate_ext_files cfg >>= fun cfg -> Ok (Printer cfg)

  let load_config filename =
    let open Or_error in
    try_with (fun () -> Yojson.Safe.from_file filename)
    >>= fun raw_json ->
    match of_yojson raw_json with
    | Ok x -> instantiate_ext_files x
    | Error msg ->
      error_string
      @@ Printf.sprintf
        "Invalid Solver Configuration format (%s): %s"
        filename msg
end

module type SolverType = sig
  val solve_sat: SAT.Problem.t -> unit Deferred.Or_error.t
  val solve_smt: SMT.Problem.t -> unit Deferred.Or_error.t
  val solve_pcsp: ?bpvs:(Ast.Ident.tvar Set.Poly.t) -> PCSP.Problem.t -> unit Deferred.Or_error.t
  val solve_muclp: MuCLP.Problem.t -> unit Deferred.Or_error.t
  val solve_sygus: SyGuS.Problem.Make(SyGuS.Problem.ExtTerm).t -> unit Deferred.Or_error.t
  val solve_lts: LTS.Problem.t -> unit Deferred.Or_error.t
end

module Make (Config: Config.ConfigType): SolverType = struct
  let solve_sat cnf =
    match Config.config with
    | Z3Sat cfg ->
      let module Cfg = struct let config = cfg end in
      let module Z3Sat = Z3Sat.Solver.Make(Cfg) in
      Deferred.return (Z3Sat.solve ~print_sol:true cnf) >>=? fun _ -> Deferred.Or_error.ok_unit
    | Minisat cfg ->
      let module Cfg = struct let config = cfg end in
      let module MINISAT = MINISAT.Solver.Make(Cfg) in
      Deferred.return (MINISAT.solve ~print_sol:true cnf) >>=? fun _ -> Deferred.Or_error.ok_unit
    | _ -> Deferred.Or_error.unimplemented "Solver.solve_sat"
  let solve_smt phi =
    match Config.config with
    | Z3Smt cfg ->
      let module Cfg = struct let config = cfg end in
      let module Z3Smt = Z3Smt.Solver.Make(Cfg) in
      Deferred.return (Z3Smt.solve ~print_sol:true phi) >>=? fun _ -> Deferred.Or_error.ok_unit
    | _ -> Deferred.Or_error.unimplemented "Solver.solve_smt"
  let solve_pcsp ?(bpvs=Set.Poly.empty) pcsp =
    match Config.config with
    | PCSat cfg ->
      let module Cfg = struct let config = cfg end in
      let module PCSat = PCSat.Solver.Make(Cfg) in
      Deferred.return (PCSat.solve ~bpvs ~print_sol:true pcsp) >>=? fun _ -> Deferred.Or_error.ok_unit
    | SPACER cfg ->
      let module Cfg = struct let config = cfg end in
      let module SPACER = SPACER.Solver.Make(Cfg) in
      Deferred.return (SPACER.solve ~print_sol:true pcsp) >>=? fun _ -> Deferred.Or_error.ok_unit
    | Hoice cfg ->
      let module Cfg = struct let config = cfg end in
      let module Hoice = Hoice.Solver.Make(Cfg) in
      Deferred.return (Hoice.solve ~print_sol:true pcsp) >>=? fun _ -> Deferred.Or_error.ok_unit
    | MuVal cfg ->
      let module Cfg = struct let config = cfg end in
      let module MuVal = MuVal.Solver.Make(Cfg) in
      MuVal.solve_pcsp ~print_sol:true pcsp >>=? fun _ -> Deferred.Or_error.ok_unit
    | Printer cfg ->
      let module Cfg = struct let config = cfg end in
      let module Printer = Printer.Solver.Make(Cfg) in
      Printer.print_pcsp pcsp; Deferred.Or_error.ok_unit
    | _ -> Deferred.Or_error.unimplemented "Solve.solve_pcsp"
  let solve_muclp muclp =
    let config = Config.config in
    match config with
    | MuVal cfg ->
      let module Cfg = struct let config = cfg end in
      let module MuVal = MuVal.Solver.Make(Cfg) in
      MuVal.solve muclp ~print_sol:true >>=? fun _ -> Deferred.Or_error.ok_unit
    | Printer cfg ->
      let module Cfg = struct let config = cfg end in
      let module Printer = Printer.Solver.Make(Cfg) in
      Printer.print_muclp muclp; Deferred.Or_error.ok_unit
    | _ -> Deferred.Or_error.unimplemented "Solver.solve_muclp"
  let solve_lts lts =
    match Config.config with
    | PCSat cfg ->
      let module Cfg = struct let config = cfg end in
      let module PCSat = PCSat.Solver.Make(Cfg) in
      Deferred.return (PCSat.solve ~print_sol:true (PCSP.Problem.of_lts lts)) >>=? fun _ -> Deferred.Or_error.ok_unit
    | MuVal cfg ->
      let module Cfg = struct let config = cfg end in
      let module MuVal = MuVal.Solver.Make(Cfg) in
      MuVal.solve_lts ~print_sol:true lts >>=? fun _ -> Deferred.Or_error.ok_unit
    | Printer cfg ->
      let module Cfg = struct let config = cfg end in
      let module Printer = Printer.Solver.Make(Cfg) in
      Printer.print_lts lts; Deferred.Or_error.ok_unit
    | _ -> Deferred.Or_error.unimplemented "Solve.solve_lts"
  let solve_sygus sygus =
    let pcsp = PCSP.Problem.of_sygus sygus in
    match Config.config with
    | PCSat cfg ->
      let module Cfg = struct let config = cfg end in
      let module PCSat = PCSat.Solver.Make(Cfg) in
      Deferred.return (PCSat.solve ~print_sol:true pcsp) >>=? fun _ -> Deferred.Or_error.ok_unit
    | SPACER cfg ->
      let module Cfg = struct let config = cfg end in
      let module SPACER = SPACER.Solver.Make(Cfg) in
      Deferred.return (SPACER.solve pcsp) >>=? fun solution ->
      Out_channel.print_endline (PCSP.Problem.str_of_solution solution);
      Out_channel.flush stdout;
      Deferred.Or_error.ok_unit
    | Hoice cfg ->
      let module Cfg = struct let config = cfg end in
      let module Hoice = Hoice.Solver.Make(Cfg) in
      Deferred.return (Hoice.solve pcsp) >>=? fun solution ->
      Out_channel.print_endline (PCSP.Problem.str_of_solution solution);
      Out_channel.flush stdout;
      Deferred.Or_error.ok_unit
    | Printer cfg ->
      let module Cfg = struct let config = cfg end in
      let module Printer = Printer.Solver.Make(Cfg) in
      Printer.print_pcsp pcsp; Deferred.Or_error.ok_unit
    | _ -> Deferred.Or_error.unimplemented "Solver.solve_sygus"
end            