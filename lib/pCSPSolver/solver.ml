(* The constraint-solver interface that mid-level solvers (the fixpoint-logic
   solvers, OptPCSat, RCaml) call, so that they need not depend on the
   top-level dispatcher.  [solve] forwards a pfwCSP
   problem to the configured backend and returns its answer with the number of
   CEGIS iterations (-1 for a backend that has none), under an optional
   timeout that becomes the [Timeout] verdict.  A backend's refusal of an
   unsupported problem becomes [Unknown] here.  Problems carrying inductive or
   coinductive predicate definitions are not solved: they are printed and
   answered [Unknown].  [preprocess], [reset], [push] and [pop] act on PCSat
   only. *)
open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld

module type SolverType = sig
  val solve :
    ?timeout:int option ->
    ?bpvs:Ast.Ident.tvar_set ->
    ?print_sol:bool ->
    ?preds:(Ident.pvar, sort_env_list * Formula.t) Map.Poly.t ->
    ?copreds:(Ident.pvar, sort_env_list * Formula.t) Map.Poly.t ->
    PCSP.Problem.t ->
    (PCSP.Problem.solution * int) Or_error.t

  (* [solve] that also returns the kind certificates PCSat's template recorded
     for a [Sat] answer (the ranking behind each WF/DWF solution), so that a
     caller can have them re-checked.  Contract: the answer and the iteration
     count are exactly those [solve] returns on the same problem; the map is
     empty for a backend other than PCSat and for any answer but [Sat]. *)
  val solve_with_kind_certificates :
    ?timeout:int option ->
    ?bpvs:Ast.Ident.tvar_set ->
    PCSP.Problem.t ->
    (PCSP.Problem.solution
    * int
    * (Ident.tvar, PCSatCommon.KindCert.t) Map.Poly.t)
    Or_error.t

  val preprocess :
    ?bpvs:Ast.Ident.tvar_set -> PCSP.Problem.t -> PCSP.Problem.t Or_error.t

  val reset : unit -> unit
  val push : unit -> unit
  val pop : unit -> unit
  (*val print : PCSP.Problem.t -> string*)
end

module Make (Cfg : Config.ConfigType) : SolverType = struct
  let config = Cfg.config

  type solver =
    | SPCSat of (module PCSat.Solver.SolverType)
    | SSPACER of (module SPACER.Solver.SolverType)
    | SHoice of (module Hoice.Solver.SolverType)
    | SPolyQEnt of (module PolyQEnt.Solver.SolverType)
    | SForward
    | SPrinter of (module Printer.Solver.SolverType)

  let solver =
    match config with
    | Config.SPACER cfg -> SSPACER (SPACER.Solver.make cfg)
    | Config.PCSat cfg -> SPCSat (PCSat.Solver.make cfg)
    | Config.Hoice cfg -> SHoice (Hoice.Solver.make cfg)
    | Config.PolyQEnt cfg -> SPolyQEnt (PolyQEnt.Solver.make cfg)
    | Config.Forward -> SForward
    | Config.Printer cfg -> SPrinter (Printer.Solver.make cfg)

  (* A backend reached through here refuses a problem whose predicate kinds it
     cannot carry, and this path bypasses the top-level dispatcher that turns
     such a refusal into a verdict -- a mid-level solver calls these backends
     directly, which is what this module exists for.  So the refusal is given
     the same treatment here: an ordinary [Unknown], which is what an undecided
     sub-query is, with the reason on the diagnostic stream.  Left to escape it
     would reach the user as a backtrace from inside another solver's run.

     [Unknown] is safe for every caller: all six that consume this answer match
     it explicitly and none reads it as a refutation -- the distinction that
     matters, since reading "could not decide" as "no counterexample" would turn
     an undecided sub-query into a proof.  It is checked rather than assumed,
     because the shape has produced a defect here before.

     Whether a kinded problem can actually reach this path is NOT established:
     eight shipped configurations put one of these backends under a
     kind-producing one, so it is configured, and on the inputs tried the
     refusal did not fire -- consistent with that backend's refinement being
     unfinished. This is therefore insurance at a boundary, not a cure for an
     observed failure. *)
  let rec solve ?(timeout = None) ~preds ~copreds =
    let dispatch = solve_aux ~timeout ~preds ~copreds in
    fun ?bpvs ?print_sol pcsp ->
      try dispatch ?bpvs ?print_sol pcsp
      with PCSP.Problem.NoTemplate reason ->
        prerr_endline ("unsupported input: " ^ reason);
        Ok (PCSP.Problem.Unknown, -1)

  and solve_aux ?(timeout = None) ~preds ~copreds =
    if Map.Poly.is_empty preds && Map.Poly.is_empty copreds then (
      let open Or_error in
      match solver with
      | SPCSat (module PCSat) ->
          fun ?(bpvs = Set.Poly.empty) ?(print_sol = false) pcsp ->
            PCSat.solve ~bpvs ~print_sol pcsp >>= fun (sol, info) ->
            Ok (sol, info.PCSatCommon.State.num_cegis_iters)
      | SSPACER (module SPACER) ->
          fun ?bpvs ?(print_sol = false) pcsp ->
            ignore bpvs;
            SPACER.solve ~timeout ~print_sol pcsp >>= fun sol -> Ok (sol, -1)
      | SHoice (module Hoice) ->
          fun ?bpvs ?(print_sol = false) pcsp ->
            ignore bpvs;
            Hoice.solve ~print_sol pcsp >>= fun sol -> Ok (sol, -1)
      | SPolyQEnt (module PolyQEnt) ->
          fun ?bpvs ?(print_sol = false) pcsp ->
            ignore bpvs;
            PolyQEnt.solve ~timeout ~print_sol pcsp >>= fun sol -> Ok (sol, -1)
      | SForward ->
          fun ?bpvs ?(print_sol = false) pcsp ->
            ignore bpvs;
            PCSP.ForwardPropagate.solve pcsp >>= fun sol ->
            if print_sol then (
              Out_channel.print_endline
              @@ sprintf "%s" (PCSP.Problem.str_of_solution sol);
              Out_channel.flush stdout);
            Ok (sol, -1)
      | SPrinter (module Printer) ->
          fun ?bpvs ?(print_sol = false) pcsp ->
            ignore print_sol;
            ignore bpvs;
            Printer.print_pcsp pcsp >>= fun _ -> Ok (PCSP.Problem.Unknown, -1))
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
            | Timer.Timeout -> Ok (PCSP.Problem.Timeout, -1) | e -> raise e)
    | _ -> solve ~bpvs ~print_sol ~preds ~copreds pcsp

  let solve_with_kind_certificates ?(timeout = None) ?(bpvs = Set.Poly.empty)
      pcsp =
    match solver with
    | SPCSat (module PCSat) -> (
        (* the same call, refusal handling and budget as [solve]'s PCSat arm,
           keeping the [info] that arm discards *)
        let run () =
          try
            PCSat.solve ~bpvs ~print_sol:false pcsp
            |> Or_error.map ~f:(fun (sol, info) ->
                ( sol,
                  info.PCSatCommon.State.num_cegis_iters,
                  info.PCSatCommon.State.kind_certificates ))
          with PCSP.Problem.NoTemplate reason ->
            prerr_endline ("unsupported input: " ^ reason);
            Ok (PCSP.Problem.Unknown, -1, Map.Poly.empty)
        in
        match timeout with
        | Some tm when tm > 0 ->
            Timer.enable_timeout tm Fn.id ignore run
              (fun _ res -> res)
              (fun _ -> function
                | Timer.Timeout ->
                    Ok (PCSP.Problem.Timeout, -1, Map.Poly.empty)
                | e -> raise e)
        | _ -> run ())
    | _ ->
        solve ~timeout ~bpvs pcsp
        |> Or_error.map ~f:(fun (sol, n) -> (sol, n, Map.Poly.empty))

  let preprocess =
    match solver with
    | SPCSat (module PCSat) ->
        fun ?(bpvs = Set.Poly.empty) pcsp -> PCSat.preprocess ~bpvs pcsp
    | _ ->
        fun ?bpvs _ ->
          ignore bpvs;
          failwith "preprocess unsupported (need apply pcsat)"

  (*let print =
    match solver with
    | SPrinter (module Printer) -> fun pcsp -> Printer.string_of_pcsp pcsp
    | _ -> fun _ -> failwith "print function expects printer config"*)

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
