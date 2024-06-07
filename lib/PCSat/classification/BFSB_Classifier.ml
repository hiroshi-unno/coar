open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon
open Bf_synthesis

module Config = struct
  type strategy =
    | First
    | All
    | MinHeightSize of int option
    | MinSizeHeight of int option
  [@@deriving yojson]

  type order = Rank | Shuffle [@@deriving yojson]

  type t = {
    verbose : bool;
    qualifier_generator : Qualifier.Generator.Config.t ext_file;
    qual_order : order;  (** priority order for qualifiers *)
    strategy : strategy;
    bfsynth : BFSynthesizer.Config.t ext_file;
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg =
    let open Or_error in
    Qualifier.Generator.Config.load_ext_file cfg.qualifier_generator
    >>= fun qualifier_generator ->
    BFSynthesizer.Config.load_ext_file cfg.bfsynth >>= fun bfsynth ->
    Ok { cfg with qualifier_generator; bfsynth }
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

  let bfsynth =
    let open Or_error in
    ExtFile.unwrap config.bfsynth >>= fun cfg ->
    Ok
      (module BFSynthesizer.Make (struct
        let config = cfg
      end) : BFSynthesizer.BFSynthesizerType)

  let qdeps = Map.Poly.empty (* TODO: generate qdeps *)
  let fenv = Map.Poly.empty (*TODO : generate fenv*)

  let compare (x1, x2) (y1, y2) =
    if x1 < y1 then -1
    else if x1 > y1 then 1
    else if x2 < y2 then -1
    else if x2 > y2 then 1
    else 0

  (*val needs_to_refine_bf: BoolFunction.t -> bool*)
  let needs_to_refine_bf =
    match config.strategy with
    | First -> fun _ -> false
    | All -> fun _ -> true
    | MinHeightSize None -> fun _ -> true
    | MinHeightSize (Some th) -> fun phi -> BoolFunction.height phi >= th
    | MinSizeHeight None -> fun _ -> true
    | MinSizeHeight (Some th) -> fun phi -> BoolFunction.size phi >= th

  let select =
    match config.strategy with
    | First -> fun qbs -> [ List.hd_exn qbs ]
    | All -> fun qbs -> qbs
    | MinHeightSize _ ->
        fun qbs ->
          List.map qbs ~f:(fun qb ->
              ((BoolFunction.height qb, BoolFunction.size qb), qb))
          |> List.sort ~compare:(fun (r1, _) (r2, _) -> compare r1 r2)
          |> List.map ~f:snd
    | MinSizeHeight _ ->
        fun qbs ->
          List.map qbs ~f:(fun qb ->
              ((BoolFunction.size qb, BoolFunction.height qb), qb))
          |> List.sort ~compare:(fun (r1, _) (r2, _) -> compare r1 r2)
          |> List.map ~f:snd

  let find_small_classifier pvar params table labeling examples =
    let open Or_error in
    qualifier_generator >>= fun qualifier_generator ->
    let (module G : Qualifier.Generator.GeneratorType) = qualifier_generator in
    bfsynth >>= fun bfsynth ->
    let (module B : BFSynthesizer.BFSynthesizerType) = bfsynth in
    let alist = labeling in
    let labeled_atoms =
      let tt = TruthTable.get_table table pvar in
      Debug.print
      @@ lazy (sprintf "    labeled atoms (%d):" (TruthTable.num_atoms alist));
      Debug.print @@ lazy (TruthTable.str_of_atoms tt alist);
      TruthTable.labeled_atoms_of tt alist
    in
    let generate n =
      let quals = G.generate pvar params labeled_atoms examples n in
      Debug.print
      @@ lazy
           (sprintf
              "    @[<2>%s set of qualifiers (%d) generated from the domain \
               %s:@ %s@]"
              (Ordinal.string_of @@ Ordinal.make n)
              (Set.length quals) (G.str_of_domain n)
              (String.concat_set ~sep:", "
              @@ Set.Poly.map quals ~f:(fun (_, phi) -> Formula.str_of phi)));
      TruthTable.update_map_with_qualifiers ~id table fenv qdeps pvar
        (params, Set.Poly.map ~f:snd quals);
      let tt = TruthTable.get_table table pvar in
      let qlist =
        Set.Poly.map quals ~f:(fun (_, phi) ->
            TruthTable.index_of_qual ~id tt fenv qdeps phi)
        |>
        match config.qual_order with
        | Rank -> Rank.sort_indices tt.TruthTable.qarr
        | Shuffle -> fun indices -> List.shuffle @@ Set.to_list indices
      in
      Debug.print
      @@ lazy
           (sprintf "    created truth table ((%d + %d) x %d)"
              (TruthTable.num_pos_labeled_atoms alist)
              (TruthTable.num_neg_labeled_atoms alist)
              (TruthTable.num_quals qlist));
      Debug.print @@ lazy (TruthTable.str_of_table_transposed tt (qlist, alist));
      let qlist' = TruthTable.reduced_qlist_of tt (qlist, alist) in
      let alist' = TruthTable.reduced_alist_of tt (qlist', alist) in
      Debug.print
      @@ lazy
           (sprintf "    qualifiers and atoms reduced ((%d + %d) x %d)"
              (TruthTable.num_pos_labeled_atoms alist')
              (TruthTable.num_neg_labeled_atoms alist')
              (TruthTable.num_quals qlist'));
      B.synthesize tt (qlist', alist')
    in
    let rec inner n =
      match generate n with
      | Ok boolean_formula ->
          Debug.print @@ lazy "    succeeded";
          if n + 1 < G.num_of_domains && needs_to_refine_bf boolean_formula then
            boolean_formula :: inner (n + 1)
          else [ boolean_formula ]
      | Error _ ->
          Debug.print @@ lazy "    failed";
          assert (n + 1 < G.num_of_domains);
          inner (n + 1)
    in
    let qbs = inner 0 in
    List.iteri qbs ~f:(fun i bf ->
        Debug.print
        @@ lazy
             (sprintf "    @[<2>%s synthesized boolean function:@ %s@]"
                (Ordinal.string_of @@ Ordinal.make i)
                (BoolFunction.str_of bf)));
    Ok
      (List.map
         ~f:(BoolFunction.concretize (TruthTable.get_table table pvar).qarr)
         (select qbs))

  let mk_classifier pvar params table labeling examples =
    let open Or_error in
    find_small_classifier pvar params table labeling examples >>= fun phis ->
    Ok
      (List.map phis ~f:(fun phi ->
           ( Map.Poly.empty (* parameters of parametric candidate*),
             (pvar, (params, phi)) )))
end
