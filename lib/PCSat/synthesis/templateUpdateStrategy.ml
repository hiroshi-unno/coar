open Core
open Common
open Common.Util
open Ast
open PCSatCommon
open Template.Function

module Config = struct
  type t = Disable | UnsatCore | RL | CBSynth of CBSynthesizer.Config.t
  [@@deriving yojson]

  let instantiate_ext_files = function
    | Disable -> Ok Disable
    | UnsatCore -> Ok UnsatCore
    | RL -> Ok RL
    | CBSynth cfg ->
        let open Or_error in
        CBSynthesizer.Config.instantiate_ext_files cfg >>= fun cfg ->
        Ok (CBSynth cfg)

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid TemplateUpdateStrategy Configuration (%s): %s"
                 filename msg)

  module type ConfigType = sig
    val config : t
  end
end

module type TemplateUpdateStrategyType = sig
  val update :
    (Ident.tvar, (module Template.Function.Type)) Map.Poly.t ->
    int ->
    State.u ->
    (Ident.tvar, parameter_update_type Set.Poly.t) Map.Poly.t option ->
    unit
end

module Make
    (RLCfg : RLConfig.ConfigType)
    (Cfg : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : TemplateUpdateStrategyType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make
      ((val Debug.Config.((*if config.verbose then*) enable (*else disable*))))

  let _ = Debug.set_id id

  module S =
    (val match config with
         | Config.Disable ->
             (module struct
               let update _ _ _ _ = failwith "template update is disabled"
             end : TemplateUpdateStrategyType)
         | Config.UnsatCore ->
             (module struct
               let update template_modules _ _ = function
                 | None ->
                     Map.Poly.iter template_modules
                       ~f:(fun (module FT : Template.Function.Type) ->
                         FT.restart ())
                 | Some pvar_labels_map ->
                     (* ToDo: output -> boolean value *)
                     Map.Poly.iteri template_modules
                       ~f:(fun
                           ~key:pvar
                           ~data:(module FT : Template.Function.Type)
                         ->
                         match Map.Poly.find pvar_labels_map pvar with
                         | None -> ()
                         | Some labels -> FT.update_with_labels labels)
             end : TemplateUpdateStrategyType)
         | Config.RL ->
             (module struct
               let update template_modules num_iters _ pvar_labels_map_opt =
                 RLConfig.lock ();
                 if RLCfg.config.show_num_iters then
                   Debug.print_stdout @@ lazy (sprintf "#iters: %d" num_iters);
                 if RLCfg.config.show_user_time then
                   Debug.print_stdout
                   @@ lazy
                        (sprintf "user time: %s"
                           (string_of_float @@ Timer.get_user_time ()));
                 Map.Poly.iteri template_modules
                   ~f:(fun
                       ~key:pvar ~data:(module FT : Template.Function.Type) ->
                     Debug.print_stdout
                     @@ lazy
                          ("### information about " ^ Ident.name_of_tvar
                         @@ FT.name_of ());
                     if RLCfg.config.show_kind then
                       Debug.print_stdout
                       @@ lazy (sprintf "kind: %s" (FT.kind_of ()));
                     if RLCfg.config.show_sort then
                       Debug.print_stdout
                       @@ lazy
                            (sprintf "sort: %s"
                               (LogicOld.Term.str_of_sort @@ FT.sort_of ()));
                     if RLCfg.config.show_num_args then
                       Debug.print_stdout
                       @@ lazy
                            (sprintf "#args: %d" @@ List.length
                           @@ LogicOld.Sort.args_of @@ FT.sort_of ());
                     (match pvar_labels_map_opt with
                     | None -> ()
                     | Some pvar_labels_map ->
                         if RLCfg.config.show_relevance then
                           Debug.print_stdout
                           @@ lazy
                                (sprintf "occurs in unsat core?: %B"
                                @@ Map.Poly.mem pvar_labels_map pvar));
                     FT.show_state ~config:RLCfg.config
                     @@
                     match
                       Option.(
                         pvar_labels_map_opt >>= Fn.flip Map.Poly.find pvar)
                     with
                     | None -> Set.Poly.empty
                     | Some labels -> labels);
                 Debug.print_stdout @@ lazy "end of states";
                 Out_channel.flush Out_channel.stdout;
                 RLConfig.unlock ();
                 Map.Poly.iteri template_modules
                   ~f:(fun
                       ~key:pvar ~data:(module FT : Template.Function.Type) ->
                     match pvar_labels_map_opt with
                     | None ->
                         RLConfig.lock ();
                         if RLCfg.config.show_pcsat_actions then
                           Debug.print_stdout
                           @@ lazy
                                (sprintf "PCSat actions for restarting %s:\n%s"
                                   (Ident.name_of_tvar pvar)
                                   (String.concat ~sep:"\n" [ "restart"; "end" ]));
                         Debug.print_stdout
                         @@ lazy
                              (sprintf "input actions for restarting %s"
                                 (Ident.name_of_tvar pvar));
                         Out_channel.flush Out_channel.stdout;
                         FT.rl_action Set.Poly.empty;
                         RLConfig.unlock ()
                     | Some pvar_labels_map -> (
                         match Map.Poly.find pvar_labels_map pvar with
                         | None ->
                             RLConfig.lock ();
                             if RLCfg.config.show_pcsat_actions then
                               Debug.print_stdout
                               @@ lazy
                                    (sprintf
                                       "PCSat actions for updating unrelated %s:\n\
                                        %s"
                                       (Ident.name_of_tvar pvar)
                                       (String.concat ~sep:"\n" [ "end" ]));
                             Debug.print_stdout
                             @@ lazy
                                  (sprintf
                                     "input actions for updating unrelated %s"
                                     (Ident.name_of_tvar pvar));
                             Out_channel.flush Out_channel.stdout;
                             FT.rl_action Set.Poly.empty;
                             RLConfig.unlock ()
                         | Some labels ->
                             RLConfig.lock ();
                             if RLCfg.config.show_pcsat_actions then
                               Debug.print_stdout
                               @@ lazy
                                    (sprintf
                                       "PCSat actions for updating related %s:\n\
                                        %s"
                                       (Ident.name_of_tvar pvar)
                                       (String.concat ~sep:"\n"
                                      @@ FT.actions_of labels));
                             Debug.print_stdout
                             @@ lazy
                                  (sprintf
                                     "input actions for updating related %s"
                                     (Ident.name_of_tvar pvar));
                             Out_channel.flush Out_channel.stdout;
                             FT.rl_action labels;
                             RLConfig.unlock ()))
             end : TemplateUpdateStrategyType)
         | Config.CBSynth cfg ->
             (module CBSynthTemplateUpdateStrategy.Make
                       (struct
                         let config = cfg
                       end)
                       (APCSP) : TemplateUpdateStrategyType))

  let update = S.update
end
