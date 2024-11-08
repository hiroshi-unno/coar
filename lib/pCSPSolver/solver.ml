open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld

module type SolverType = sig
  val solve :
    ?timeout:int option ->
    ?bpvs:Ast.Ident.tvar Set.Poly.t ->
    ?print_sol:bool ->
    ?preds:(Ident.pvar, sort_env_list * Formula.t) Map.Poly.t ->
    ?copreds:(Ident.pvar, sort_env_list * Formula.t) Map.Poly.t ->
    PCSP.Problem.t ->
    (PCSP.Problem.solution * int) Or_error.t

  val preprocess :
    ?bpvs:Ast.Ident.tvar Set.Poly.t ->
    PCSP.Problem.t ->
    PCSP.Problem.t Or_error.t

  val reset : unit -> unit
  val push : unit -> unit
  val pop : unit -> unit
  val print : PCSP.Problem.t -> string
end

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  type solver =
    | SPCSat of (module PCSat.Solver.SolverType)
    | SSPACER of SPACER.Config.t
    | SHoice of (module Hoice.Solver.SolverType)
    | SForward
    | SPrinter of (module Printer.Solver.SolverType)

  let solver =
    match config with
    | Config.SPACER cfg -> SSPACER cfg
    | Config.PCSat cfg -> SPCSat (PCSat.Solver.make cfg)
    | Config.Forward -> SForward
    | Config.Hoice cfg -> SHoice (Hoice.Solver.make cfg)
    | Config.Printer cfg -> SPrinter (Printer.Solver.make cfg)

  let solve ?(timeout = None) ~preds ~copreds =
    if Map.Poly.is_empty preds && Map.Poly.is_empty copreds then (
      let open Or_error in
      match solver with
      | SPCSat (module PCSat) ->
          fun ?(bpvs = Set.Poly.empty) ?(print_sol = false) pcsp ->
            PCSat.solve ~bpvs ~print_sol pcsp >>= fun (sol, info) ->
            Ok (sol, info.PCSatCommon.State.num_cegis_iters)
      | SSPACER cfg ->
          let module Cfg = struct
            let config = cfg
          end in
          let module SPACER = SPACER.Solver.Make (Cfg) in
          fun ?bpvs ?(print_sol = false) pcsp ->
            ignore bpvs;
            SPACER.solve ~timeout ~print_sol pcsp >>= fun sol -> Ok (sol, -1)
      | SHoice (module Hoice) ->
          fun ?bpvs ?(print_sol = false) pcsp ->
            ignore bpvs;
            Hoice.solve ~print_sol pcsp >>= fun sol -> Ok (sol, -1)
      | SForward ->
          fun ?bpvs ?(print_sol = false) pcsp ->
            ignore bpvs;
            PCSP.ForwardPropagate.solve pcsp >>= fun sol ->
            if print_sol then (
              Out_channel.print_endline
              @@ sprintf "%s" (PCSP.Problem.str_of_solution sol);
              Out_channel.flush stdout);
            Ok (sol, -1)
      | SPrinter _ ->
          fun ?bpvs ?(print_sol = false) _ ->
            ignore print_sol;
            ignore bpvs;
            error_string "config printer need to call print function")
    else fun ?bpvs ?(print_sol = false) pcsp ->
      ignore bpvs;
      ignore print_sol;
      print_endline "";
      print_endline "*** inductive predicates:";
      print_endline "";
      Map.Poly.iteri preds ~f:(fun ~key:pvar ~data:(senv, phi) ->
          let sub =
            Map.Poly.of_alist_exn
            @@ List.mapi senv ~f:(fun i (x, _) ->
                   (x, Ident.Tvar (sprintf "x%d" i)))
          in
          let senv =
            List.map senv ~f:(fun (x, s) -> (Map.Poly.find_exn sub x, s))
          in
          let phi = LogicOld.Formula.rename sub phi in
          print_endline
            (sprintf "%s(%s) =mu\n  %s\n" (Ident.name_of_pvar pvar)
               (LogicOld.str_of_sort_env_list LogicOld.Term.str_of_sort senv)
               (LogicOld.Formula.str_of phi)));
      print_endline "*** coinductive predicates:";
      print_endline "";
      Map.Poly.iteri copreds ~f:(fun ~key:pvar ~data:(senv, phi) ->
          let sub =
            Map.Poly.of_alist_exn
            @@ List.mapi senv ~f:(fun i (x, _) ->
                   (x, Ident.Tvar (sprintf "x%d" i)))
          in
          let senv =
            List.map senv ~f:(fun (x, s) -> (Map.Poly.find_exn sub x, s))
          in
          let phi = LogicOld.Formula.rename sub phi in
          print_endline
            (sprintf "%s(%s) =nu\n  %s\n" (Ident.name_of_pvar pvar)
               (LogicOld.str_of_sort_env_list LogicOld.Term.str_of_sort senv)
               (LogicOld.Formula.str_of phi)));
      print_endline "*** predicate constraints:";
      print_endline "";
      print_endline @@ PCSP.Problem.str_of
      @@ PCSP.Problem.normalize_uni_senv pcsp;
      print_endline "";
      print_endline "constraint solving not supported";
      print_endline "";
      Ok (PCSP.Problem.Unknown, -1)
  (*Or_error.error_string "(co)inductive predicates not supported by the constraint solver"*)

  let solve ?(timeout = None) ?(bpvs = Set.Poly.empty) ?(print_sol = false)
      ?(preds = Map.Poly.empty) ?(copreds = Map.Poly.empty) pcsp =
    match timeout with
    | Some tm when tm > 0 ->
        Timer.enable_timeout tm Fn.id ignore
          (fun () -> solve ~timeout ~bpvs ~print_sol ~preds ~copreds pcsp)
          (fun _ res -> res)
          (fun _ -> function
            | Timer.Timeout -> Ok (PCSP.Problem.Timeout, -1)
            | e -> raise e)
    | _ -> solve ~bpvs ~print_sol ~preds ~copreds pcsp

  let preprocess =
    match solver with
    | SPCSat (module PCSat) ->
        fun ?(bpvs = Set.Poly.empty) pcsp -> PCSat.preprocess ~bpvs pcsp
    | _ ->
        fun ?bpvs _ ->
          ignore bpvs;
          failwith "preprocess unsupported (need apply pcsat)"

  let print =
    match solver with
    | SPrinter (module Printer) -> fun pcsp -> Printer.string_of_pcsp pcsp
    | _ -> fun _ -> failwith "print function expects printer config"

  let reset () =
    match solver with SPCSat (module PCSat) -> PCSat.reset () | _ -> ()

  let push () =
    match solver with SPCSat (module PCSat) -> PCSat.push () | _ -> ()

  let pop () =
    match solver with SPCSat (module PCSat) -> PCSat.pop () | _ -> ()
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : SolverType)
