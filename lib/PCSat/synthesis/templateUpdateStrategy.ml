open Core
open Common.Util
open Ast
open PCSatCommon
open Template.Function

module Config = struct
  type t =
    | Default
    | UnsatCore
    | RL
    | CBSynth of CBSynthesizer.Config.t
    | Disable [@@deriving yojson]

  let instantiate_ext_files = function
    | Default -> Ok Default
    | UnsatCore -> Ok UnsatCore
    | RL -> Ok RL
    | CBSynth cfg ->
      let open Or_error in
      CBSynthesizer.Config.instantiate_ext_files cfg >>= fun cfg ->
      Ok (CBSynth cfg)
    | Disable -> Ok Disable

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x ->
          instantiate_ext_files x >>= fun x ->
          Ok (ExtFile.Instance x)
        | Error msg ->
          error_string
          @@ Printf.sprintf
            "Invalid TemplateUpdateStrategy Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (ExtFile.Instance x)

  module type ConfigType = sig val config : t end
end

module type TemplateUpdateStrategyType = sig
  val update: (Ident.tvar, (module Template.Function.Type)) Map.Poly.t
    -> State.u
    -> (Ident.tvar, parameter_update_type Set.Poly.t) Map.Poly.t
    -> unit
end

module Make (Cfg: Config.ConfigType) (PCSP: PCSP.Problem.ProblemType) : TemplateUpdateStrategyType = struct
  let config = Cfg.config

  module S =
    (val (match config with
         | Config.Default ->
           (module struct
             let update template_modules _example _ =
               Map.Poly.iter template_modules ~f:(fun ft ->
                   let (module FunTemplate : Template.Function.Type) = ft in
                   FunTemplate.next ())
           end : TemplateUpdateStrategyType)
         | Config.UnsatCore ->
           (module struct
             let update template_modules _example pvar_labels_map = (*ToDo: output -> boolean value *)
               Map.Poly.iteri template_modules ~f:(fun ~key:pvar ~data:ft ->
                   match Map.Poly.find pvar_labels_map pvar with
                   | None -> ()
                   | Some labels ->
                     let (module FunTemplate : Template.Function.Type) = ft in
                     FunTemplate.update_with_labels labels)
           end : TemplateUpdateStrategyType)
         | Config.RL ->
           (module struct
             let update template_modules _example pvar_labels_map =
               Map.Poly.iteri template_modules ~f:(fun ~key:pvar ~data:ft ->
                   let (module FunTemplate : Template.Function.Type) = ft in
                   let labels =
                     match Map.Poly.find pvar_labels_map pvar with
                     | None -> Set.Poly.empty (*ToDo: is this OK?*)
                     | Some labels -> labels
                   in
                   FunTemplate.rl_action labels)
           end : TemplateUpdateStrategyType)
         | Config.CBSynth cfg ->
           (module CBSynthTemplateUpdateStrategy.Make (struct let config = cfg end) (PCSP) : TemplateUpdateStrategyType)
         | Config.Disable ->
           (module struct
             let update _template_modules _example _ =
               assert false (* TODO : the solution must be unknown *)
           end : TemplateUpdateStrategyType)))

  let update = S.update
end