open Core
open Common
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon
open Regression

module Config = struct
  type t = {
    verbose: bool;
    qualifier_generator: Qualifier.Generator.Config.t ext_file;
    regressor: Regressor.Config.t ext_file;
  } [@@deriving yojson]

  module type ConfigType = sig val config: t end

  let instantiate_ext_files cfg =
    let open Or_error in
    Qualifier.Generator.Config.load_ext_file cfg.qualifier_generator >>= fun qualifier_generator ->
    Regressor.Config.load_ext_file cfg.regressor >>= fun regressor ->
    Ok { cfg with qualifier_generator = qualifier_generator;
                  regressor = regressor }
end

module Make (Cfg: Config.ConfigType) (PCSP: PCSP.Problem.ProblemType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  type classifier = SortMap.t * (Ident.pvar * (SortEnv.t * Formula.t))

  let qualifier_generator =
    let open Or_error in
    ExtFile.unwrap config.qualifier_generator >>= fun cfg ->
    Ok (module Qualifier.Generator.Make (struct let config = cfg end) (PCSP)
        : Qualifier.Generator.GeneratorType)

  let regressor =
    let open Or_error in
    ExtFile.unwrap config.regressor >>= fun cfg ->
    Ok (module Regressor.Make (struct let config = cfg end)
        : Regressor.RegressorType)

  let mk_classifier pvar params table labeling _examples =
    let open Or_error in
    qualifier_generator >>= fun qualifier_generator ->
    let (module G : Qualifier.Generator.GeneratorType) = qualifier_generator in
    regressor >>= fun regressor ->
    let (module R : Regressor.RegressorType) = regressor in
    let args, ret = List.take (SortEnv.list_of params) (SortEnv.length params - 1), List.last_exn (SortEnv.list_of params) in
    let labeled_atoms =
      let tt = TruthTable.get_table table pvar in
      let tt = TruthTable.set_alist tt labeling in
      Debug.print @@ lazy (sprintf "    labeled atoms (%d):" (Map.Poly.length labeling));
      Debug.print @@ lazy (TruthTable.str_of_atoms tt);
      TruthTable.labeled_atoms_of tt in
    R.mk_regressor (SortEnv.of_list args) labeled_atoms
    >>= (fun (ps, t) ->
        let phi = Formula.eq (uncurry Term.mk_var ret) t in
        Ok (ps(* parameters of parametric candidate*), (pvar, (params, phi))))
end