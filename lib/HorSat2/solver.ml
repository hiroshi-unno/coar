(* Backend that decides a higher-order model checking problem with the external
   HorSat2 model checker, run as a separate process on a per-process input
   file.  It reads alternating tree automata only; a trivial-automaton input
   is refused with an [Error] naming TRecS.  The verdict is read positionally
   from HorSat2's output (satisfied, or not satisfied with a counterexample
   unless [-noce] is set).  An EHMTT problem is reduced to HORS problems and
   is satisfied when every one of them is.  A parse error or output in an
   unexpected shape becomes an [Error], never a verdict. *)
open Core
open Common
open Automata

module type SolverType = sig
  val solve :
    ?print_sol:bool -> HOMC.Problem.t -> HOMC.Problem.solution Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let rec solve ?(print_sol = false) homc =
    match homc with
    | HOMC.Problem.RSFD _ when not (HOMC.Problem.reads_alternating homc) ->
        Or_error.error_string
        @@ sprintf
             "HorSat2 cannot read this input: it specifies %s, and HorSat2's \
              converter requires an alternating one. Run it with TRecS instead \
              (-c config/solver/trecs.json)."
             (HOMC.Problem.dialect_str_of homc)
    | HOMC.Problem.RSFD (trs_in, rules, trs_out) ->
        let filename =
          (* the process id keeps two concurrent runs in one directory from
             writing, reading and overwriting the same file *)
          sprintf "temp_horsat2_p%d.hors" (Pid.to_int @@ Core_unix.getpid ())
        in
        Debug.print
        @@ lazy
             (sprintf "Size of HORS: %d (%d rules)" (HOMC.RSFD.sizeof rules)
                (List.length rules));
        Debug.print
        @@ lazy
             (sprintf "Number of states of input automaton: %d"
             @@ TreeAutomaton.number_of_states_trs trs_in);
        Debug.print
        @@ lazy
             (sprintf "Number of states of output automaton: %d"
             @@ TreeAutomaton.number_of_states trs_out);
        (* output generated RSFD *)
        Out_channel.with_file filename ~f:(fun channel ->
            HOMC.Problem.pr (Format.formatter_of_out_channel channel) homc);
        let res =
          (* HorSat2 0.9.5 *)
          let cmd = "./horsat2 " in
          let cmd = if config.noce then cmd ^ "-noce " else cmd in
          let cmd = if config.merge then cmd ^ "-merge " else cmd in
          let cmd = if config.gfp then cmd ^ "-gfp " else cmd in
          let cmd = cmd ^ filename in
          let (s0, s1, s2), status =
            Common.Util.Command.read_process cmd ~f:(fun cin ->
              let s0 =
                ignore (In_channel.input_line cin);
                ignore (In_channel.input_line cin);
                In_channel.input_line cin
              in
              let s1 =
                ignore (In_channel.input_line cin);
                ignore (In_channel.input_line cin);
                ignore (In_channel.input_line cin);
                In_channel.input_line cin
              in
              let s2 =
                ignore (In_channel.input_line cin);
                In_channel.input_line cin
              in
              (s0, s1, s2))
          in
          match (status, s0, s1, s2) with
          | Error err, Some "Parse error", _, _ ->
              Debug.print
              @@ lazy (Core_unix.Exit_or_signal.to_string_hum (Error err));
              Debug.print @@ lazy "Parse error";
              None
          | Ok _, Some _, Some "The property is NOT satisfied.", Some s2
            when not config.noce ->
              Some (Second (Some s2))
          | Ok _, Some _, Some "The property is NOT satisfied.", None
            when config.noce ->
              Some (Second None)
          | Ok _, Some _, Some "The property is satisfied.", None ->
              Some (First ())
          | _, _, _, _ -> None
        in
        let open Or_error in
        (match res with
        | None -> Or_error.error_string "HORS verification failed"
        | Some (First ()) ->
            Debug.print @@ lazy "verified";
            Ok HOMC.Problem.Sat
        | Some (Second None) ->
            Debug.print @@ lazy "refuted";
            Ok HOMC.Problem.Unsat
        | Some (Second (Some cex)) ->
            Debug.print @@ lazy "refuted with a counterexample:";
            Debug.print @@ lazy cex;
            Ok HOMC.Problem.Unsat)
        >>= fun sol ->
        if print_sol then print_endline (HOMC.Problem.str_of_solution sol);
        Ok sol
    | HOMC.Problem.EHMTT (ehmtt, trs, (main, typ)) -> (
        try
          let start_t = Common.Clock.time_s () in
          let rsfds =
            HOMC.Reducer.rsfds_of_ehmtt ~print:Debug.print ehmtt trs (main, typ)
          in
          let res =
            List.for_all rsfds ~f:(fun (name, rsfd) ->
                Debug.print
                @@ lazy (sprintf "\nHigher-Order Model Checking: %s" name);
                match solve ~print_sol:false (*ToDo*) rsfd with
                | Ok HOMC.Problem.Sat -> true
                | Ok HOMC.Problem.Unsat -> false
                | _ -> failwith "failed")
          in
          let elapsed_t = Common.Clock.time_s () -. start_t in
          Debug.print @@ lazy (sprintf "\nElapsed Time: %f sec" elapsed_t);
          let sol = if res then HOMC.Problem.Sat else HOMC.Problem.Unsat in
          if print_sol then print_endline (HOMC.Problem.str_of_solution sol);
          Ok sol
        with exn_ when not (Common.Timer.is_async exn_) ->
          Or_error.error_string "EHMTT verification failed")
end
