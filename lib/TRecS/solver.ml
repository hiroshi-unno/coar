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
    | Problem.RSFD (trs_in, rules, trs_out) ->
        let filename = "temp_trecs.hors" in
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
        let ppf =
          Format.formatter_of_out_channel
          @@ if true then Stdlib.open_out filename else Out_channel.stdout
        in
        HOMC.Problem.pr ppf homc;
        let res =
          (* TRecS 1.2.1 and 1.2.2 *)
          let cin = Core_unix.open_process_in ("./trecs " ^ filename) in
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
          In_channel.close cin;
          match (Core_unix.close_process_in cin, s0, s1, s2) with
          | _ (*ToDo*), Some "Parse error", _, _ ->
              Debug.print @@ lazy "Parse error";
              None
          | Ok _, Some _, Some "The property is not satisfied.", Some s2 ->
              Some (Second s2)
          | Ok _, Some _, Some s1, Some _ ->
              assert (
                String.(
                  String.sub s1 ~pos:(String.length s1 - 3) ~len:3 = " : "));
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
          let start_t = Core_unix.time () in
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
          let elapsed_t = Core_unix.time () -. start_t in
          Debug.print @@ lazy (sprintf "\nElapsed Time: %f sec" elapsed_t);
          let sol = if res then Problem.Sat else Problem.Unsat in
          if print_sol then print_endline (HOMC.Problem.str_of_solution sol);
          Ok sol
        with
        | E err -> Error err
        | U -> Or_error.error_string "EHMTT verification failed")
end
