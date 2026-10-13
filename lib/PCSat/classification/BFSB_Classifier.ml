(* Classification-based candidate synthesis for an ordinary predicate: learn
   a Boolean combination of qualifiers that separates its labelled examples.

   [mk_classifier pvar params table labeling examples] walks the qualifier
   generator's domains in order; for each it adds the domain's qualifiers to
   the predicate's truth table, reduces the table, and asks the configured
   Boolean-function learner for a formula over the qualifiers.  The strategy
   decides whether a later domain is also tried after a success and which of
   the formulas found are returned.  Each candidate is closed (no template
   parameters).  When no domain separates the examples the result is an
   error rather than a failed assertion; the abstract-domain qualifiers are
   integer-only, so predicates over other sorts reach that error. *)
open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
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
    verbose : bool; [@default false]
    qualifier_generator : Qualifier.Generator.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/qualifier/polyhedron012.json"]
    qual_order : order; [@default Rank]  (** priority order for qualifiers *)
    strategy : strategy; [@default All]
    bfsynth : BFSynthesizer.Config.t ext_file; [@default Common.Util.config_default (Common.Util.ext_file_of_yojson BFSynthesizer.Config.of_yojson) {|["Instance", ["DTBF", {"verbose": false}]]|}]
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

  let print_log = false

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
              (String.concat_map_set ~sep:", " quals ~f:(snd >> Formula.str_of)));
      TruthTable.update_map_with_qualifiers
        ~print:(if print_log then Debug.print ~id else fun _ -> ())
        ~id table fenv qdeps pvar
        (params, Set.Poly.map ~f:snd quals);
      let tt = TruthTable.get_table table pvar in
      let qlist =
        Set.Poly.map quals
          ~f:
            (snd
            >> TruthTable.index_of_qual
                 ~print:(if print_log then Debug.print ~id else fun _ -> ())
                 ~id tt fenv qdeps)
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
            inner (n + 1) >>| fun rest -> boolean_formula :: rest
          else Ok [ boolean_formula ]
      | Error e ->
          Debug.print @@ lazy "    failed";
          if n + 1 < G.num_of_domains then inner (n + 1)
          else
            (* no qualifier domain separates the examples: report it instead
               of asserting.  The abstract-domain qualifiers (interval,
               octagon, octahedron, polyhedron) are integer-only, so this is
               what a predicate over bit-vector, real or datatype arguments
               reaches under a decision-tree configuration. *)
            Or_error.error_string
              (sprintf
                 "no qualifier domain separates the examples of %s (%d \
                  domain(s) tried, last error: %s); the abstract-domain \
                  qualifiers are integer-only, so a predicate over bit-vector, \
                  real or datatype arguments needs a template-based \
                  configuration"
                 (Ident.name_of_pvar pvar) (n + 1) (Error.to_string_hum e))
    in
    inner 0 >>= fun qbs ->
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
