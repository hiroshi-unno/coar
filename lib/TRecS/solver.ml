(* Backend that decides a higher-order model checking problem with the external
   TRecS model checker, run as a separate process.  A HORS with a trivial tree
   automaton is printed into a per-process scratch directory and TRecS is run
   there; the verdict is read positionally from its output (verified, or
   refuted with a counterexample trace).  An EHMTT problem is first reduced to
   a list of HORS model checking problems and is satisfied when every one of
   them is.  An alternating-automaton input, a parse error, or output in an
   unexpected shape becomes an [Error], never a verdict. *)
open Core
open Common
open Automata
open HOMC

module type SolverType = sig
  val solve : ?print_sol:bool -> Problem.t -> Problem.solution Or_error.t
end

module Make (Config : Config.ConfigType) : SolverType = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  exception E of Error.t
  exception U

  let rec solve ?(print_sol = false) homc =
    match homc with
    | Problem.RSFD _ when Problem.reads_alternating homc ->
        Or_error.error_string
        @@ sprintf
             "TRecS cannot read this input: it specifies %s, and TRecS reads \
              only a trivial tree automaton. Run it with HorSat2 instead \
              (-c config/solver/horsat2.json)."
             (Problem.dialect_str_of homc)
    | Problem.RSFD (trs_in, rules, trs_out) ->
        let dir =
          (* TRecS creates its own scratch files in the current directory under
             fixed names ("log<n>.hrs", numbered by an internal counter that
             carries no process id) and unlinks them when it is done, so two
             concurrent runs in one directory delete each other's files and
             TRecS aborts with ENOENT on the unlink.  Its stdout is then short,
             the positional parsing below reads the wrong lines, and the run is
             reported as "HORS verification failed" -- intermittently, only
             under concurrency.  Give every run a directory of its own; that
             also keeps two runs from overwriting the same input file. *)
          sprintf "temp_trecs_p%d" (Pid.to_int @@ Core_unix.getpid ())
        in
        Core_unix.mkdir_p dir;
        let filename = Filename.concat dir "input.hors" in
        Debug.print
        @@ lazy
             (sprintf "Size of HORS: %d (%d rules)" (RSFD.sizeof rules)
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
          (* TRecS 1.2.1 and 1.2.2 *)
          let cmd =
            (* run TRecS inside that directory, so its fixed-name scratch files
               land there too; the executable itself is at the repository root,
               which is where the tool must be started from *)
            sprintf "cd %s && %s input.hors" (Filename.quote dir)
              (Filename.quote (Filename.concat (Core_unix.getcwd ()) "trecs"))
          in
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
                In_channel.input_line cin
              in
              let s2 =
                ignore (In_channel.input_line cin);
                In_channel.input_line cin
              in
              (s0, s1, s2))
          in
          match (status, s0, s1, s2) with
          | _ (*ToDo*), Some "Parse error", _, _ ->
              Debug.print @@ lazy "Parse error";
              None
          | Ok _, Some _, Some "The property is not satisfied.", Some s2 ->
              Some (Second s2)
          | Ok _, Some _, Some s1, Some _
            when String.is_suffix s1 ~suffix:" : " ->
              Some (First ())
          | _, _, _, _ -> None
        in
        let open Or_error in
        (match res with
        | None -> Or_error.error_string "HORS verification failed"
        | Some (First ()) ->
            Debug.print @@ lazy "verified";
            Ok Problem.Sat
        | Some (Second cex) ->
            Debug.print @@ lazy "refuted with a counterexample:";
            Debug.print @@ lazy cex;
            Ok Problem.Unsat)
        >>= fun sol ->
        if print_sol then print_endline (HOMC.Problem.str_of_solution sol);
        Ok sol
    | Problem.EHMTT (ehmtt, trs, (main, typ)) -> (
        try
          let start_t = Common.Clock.time_s () in
          let rsfds =
            Reducer.rsfds_of_ehmtt ~print:Debug.print ehmtt trs (main, typ)
          in
          let res =
            List.for_all rsfds ~f:(fun (name, rsfd) ->
                Debug.print
                @@ lazy (sprintf "\nHigher-Order Model Checking: %s" name);
                match solve ~print_sol:false (*ToDo*) rsfd with
                | Ok Problem.Sat -> true
                | Ok Problem.Unsat -> false
                | Ok Problem.Unknown -> raise U
                | Error err -> raise (E err))
          in
          let elapsed_t = Common.Clock.time_s () -. start_t in
          Debug.print @@ lazy (sprintf "\nElapsed Time: %f sec" elapsed_t);
          let sol = if res then Problem.Sat else Problem.Unsat in
          if print_sol then print_endline (HOMC.Problem.str_of_solution sol);
          Ok sol
        with
        | E err -> Error err
        | U -> Or_error.error_string "EHMTT verification failed")
end
