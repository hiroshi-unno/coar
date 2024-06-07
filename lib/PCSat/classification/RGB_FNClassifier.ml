open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open PCSatCommon
open Regression

module Config = struct
  type t = {
    verbose : bool;
    qualifier_generator : Qualifier.Generator.Config.t ext_file;
    regressor : Regressor.Config.t ext_file;
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg =
    let open Or_error in
    Qualifier.Generator.Config.load_ext_file cfg.qualifier_generator
    >>= fun qualifier_generator ->
    Regressor.Config.load_ext_file cfg.regressor >>= fun regressor ->
    Ok { cfg with qualifier_generator; regressor }
end

module Make (Cfg : Config.ConfigType) (APCSP : PCSP.Problem.ProblemType) =
struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  type classifier = sort_env_map * (Ident.pvar * (sort_env_list * Formula.t))

  let qualifier_generator =
    let open Or_error in
    ExtFile.unwrap config.qualifier_generator >>= fun cfg ->
    Ok
      (module Qualifier.Generator.Make
                (struct
                  let config = cfg
                end)
                (APCSP) : Qualifier.Generator.GeneratorType)

  let regressor =
    let open Or_error in
    ExtFile.unwrap config.regressor >>= fun cfg ->
    Ok
      (module Regressor.Make (struct
        let config = cfg
      end) : Regressor.RegressorType)

  let mk_classifier pvar params table labeling _examples =
    let open Or_error in
    qualifier_generator >>= fun qualifier_generator ->
    let (module G : Qualifier.Generator.GeneratorType) = qualifier_generator in
    regressor >>= fun regressor ->
    let (module R : Regressor.RegressorType) = regressor in
    let args, ret = List.rest_last params in
    let labeled_atoms =
      let alist = labeling in
      let tt = TruthTable.get_table table pvar in
      Debug.print
      @@ lazy (sprintf "    labeled atoms (%d):" (TruthTable.num_atoms alist));
      Debug.print @@ lazy (TruthTable.str_of_atoms tt alist);
      TruthTable.labeled_atoms_of tt alist
    in
    R.mk_regressor args labeled_atoms >>= fun (ps, t) ->
    let phi = Formula.eq (uncurry Term.mk_var ret) t in
    Ok [ (ps (* parameters of parametric candidate*), (pvar, (params, phi))) ]
end
