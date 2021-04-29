open Core
open Common
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon
open Bf_synthesis

module Config = struct
  type strategy =
    | Single
    | MultHeight of int
    | MultSize of int
    | SeqHeight of int
    | SeqSize of int [@@ deriving yojson]
  type t = {
    verbose: bool;
    qualifier_generator: Qualifier.Generator.Config.t ext_file;
    strategy: strategy;
    bfsynth: BFSynthesizer.Config.t ext_file;
  } [@@deriving yojson]

  module type ConfigType = sig val config: t end

  let instantiate_ext_files cfg =
    let open Or_error in
    Qualifier.Generator.Config.load_ext_file cfg.qualifier_generator >>= fun qualifier_generator ->
    BFSynthesizer.Config.load_ext_file cfg.bfsynth >>= fun bfsynth ->
    Ok { cfg with qualifier_generator = qualifier_generator; bfsynth = bfsynth }
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

  let bfsynth =
    let open Or_error in
    ExtFile.unwrap config.bfsynth >>= fun cfg ->
    Ok (module BFSynthesizer.Make (struct let config = cfg end)
        : BFSynthesizer.BFSynthesizerType)

  let fenv = Set.Poly.empty (*TODO : generate fenv*)

  (*val needs_to_refine_bf: PropLogic.Formula.t -> bool*)
  let needs_to_refine_bf =
    match config.strategy with
    | MultHeight th -> fun phi -> PropLogic.Formula.height phi >= th
    | MultSize th -> fun phi -> PropLogic.Formula.size phi >= th
    | SeqHeight th -> fun phi -> PropLogic.Formula.height phi >= th
    | SeqSize th -> fun phi -> PropLogic.Formula.size phi >= th
    | _ -> fun _ -> false
  let find_small_classifier pvar params table labeling examples =
    let open Or_error in
    qualifier_generator >>= fun qualifier_generator ->
    let (module G : Qualifier.Generator.GeneratorType) = qualifier_generator in
    bfsynth >>= fun bfsynth ->
    let (module B : BFSynthesizer.BFSynthesizerType) = bfsynth in
    let labeled_atoms =
      let tt = TruthTable.get_table table pvar in
      let tt = TruthTable.set_alist tt labeling in
      Debug.print @@ lazy (sprintf "    labeled atoms (%d):" (Map.Poly.length labeling));
      Debug.print @@ lazy (TruthTable.str_of_atoms tt);
      TruthTable.labeled_atoms_of tt in
    let generate n =
      let quals = G.generate pvar params labeled_atoms examples n in
      Debug.print @@ lazy
        (Format.sprintf
           "    @[<2>%s set of qualifiers (%d) generated from the domain %s:@ %s@]"
           (Ordinal.string_of n)
           (List.length quals)
           (G.str_of_domain n)
           (String.concat ~sep:", " (List.map quals ~f:(fun (_, phi) -> Formula.str_of phi))));
      TruthTable.update_map_with_qualifiers table fenv pvar (params, (Set.Poly.of_list @@ List.map ~f:snd quals));
      let tt =
        let tt = TruthTable.get_table table pvar in
        let alist = labeling in
        let qlist = List.map quals ~f:(fun (_, phi) -> TruthTable.index_of_qual tt fenv phi) in
        TruthTable.set_qlist (TruthTable.set_alist tt alist) qlist in
      Debug.print @@ lazy (sprintf "    created truth table ((%d + %d) x %d)"
                             (TruthTable.num_pos_labeled_atoms tt)
                             (TruthTable.num_neg_labeled_atoms tt)
                             (TruthTable.num_quals tt));
      Debug.print @@ lazy (TruthTable.str_of_table_transposed tt);
      let tt = TruthTable.reduce_qualifiers tt in
      Debug.print @@ lazy (sprintf "    qualifiers reduced ((%d + %d) x %d)"
                             (TruthTable.num_pos_labeled_atoms tt)
                             (TruthTable.num_neg_labeled_atoms tt)
                             (TruthTable.num_quals tt));
      let tt = TruthTable.reduce_atoms tt in
      Debug.print @@ lazy (sprintf "    atoms reduced ((%d + %d) x %d)"
                             (TruthTable.num_pos_labeled_atoms tt)
                             (TruthTable.num_neg_labeled_atoms tt)
                             (TruthTable.num_quals tt));
      B.synthesize tt
    in
    let rec inner n =
      match generate n with
      | Ok boolean_formula ->
        Debug.print @@ lazy "    succeeded";
        if n + 1 < G.num_of_domains && needs_to_refine_bf boolean_formula then
          boolean_formula :: inner (n + 1)
        else [boolean_formula]
      | Error _ ->
        Debug.print @@ lazy "    failed";
        assert (n + 1 < G.num_of_domains); inner (n + 1)
    in
    let qbs = inner 0 in
    List.iteri qbs ~f:(fun i bf ->
        Debug.print @@ lazy (Format.sprintf "    @[<2>%s synthesized boolean function:@ %s@]" (Ordinal.string_of i) (PropLogic.Formula.str_of bf)));
    match config.strategy with
    | MultHeight _ ->
      qbs
      |> argmin ~f:PropLogic.Formula.height
      |> fun bf -> Ok (TruthTable.concretize_bf (TruthTable.get_table table pvar).qarr bf)
    | MultSize _ ->
      qbs
      |> argmin ~f:PropLogic.Formula.size
      |> fun bf -> Ok (TruthTable.concretize_bf (TruthTable.get_table table pvar).qarr bf)
    | Single | SeqHeight _ | SeqSize _ ->
      Ok (TruthTable.concretize_bf (TruthTable.get_table table pvar).qarr (List.last_exn qbs))

  let mk_classifier pvar params table labeling examples =
    let open Or_error in
    find_small_classifier pvar params table labeling examples
    >>= fun phi -> Ok (SortMap.empty(* parameters of parametric candidate*),
                       (pvar, (params, phi)))
end