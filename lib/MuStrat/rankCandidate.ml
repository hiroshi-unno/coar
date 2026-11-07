(* The ranking candidates a refinement offers a key from its chain pairs and
   regions, built by linear programming over Farkas certificates before the
   constraint solver is asked: a nested (multiphase) ranking per region, and a
   lexicographic one over every region and pair at once, the latter memoised
   per key.  [Make] takes what the strategy check holds: its configuration
   (only the [chain_pair_lex_candidate_*] fields are read), its trace and its
   one-line repair log. *)

open Core
open Common.Ext
open Ast

(* Whether the region [(vars, region)] holds at the ground pair [(a, b)]:
   true only when substituting the pair decides it true. *)
let region_holds_at (vars, region) (a, b) =
  let open LogicOld in
  let point = a @ b in
  List.length point = List.length vars
  &&
  try
    Evaluator.eval @@ Evaluator.simplify
    @@ Formula.subst
         (Map.Poly.of_alist_exn
         @@ List.map2_exn vars point ~f:(fun (v, _) t -> (v, t)))
         region
  with exn_ when not (Common.Timer.is_async exn_) -> false

module Make (A : sig
  val config : Config.t
  val print : ?id:int option -> string Lazy.t -> unit
  val repair_log : string -> unit

  val literal_bound : unit -> Z.t
  (** the largest absolute integer literal of the game being solved, at
      least 1; read only under a literal rung
      ([chain_pair_lex_candidate_const_ladder]) *)
end) =
struct
  let config = A.config
  let repair_log = A.repair_log

  (* [chain_pair_lex_candidate_const_first] and
     [chain_pair_lex_candidate_const_ladder]: the rungs on a component's
     constant, as [RankingCheck.lex_ranking ~const_first] takes them, for
     the unit-coefficient construction ([unit_const_rungs]) and for the
     other [lex_ranking] constructions ([other_const_rungs]); [None] asks
     the construction without rungs.  Rungs never change which questions
     are decided, only which components are returned. *)
  let const_rungs () =
    Option.map config.chain_pair_lex_candidate_const_first ~f:(fun b ->
        let first = Z.of_int b in
        match config.chain_pair_lex_candidate_const_ladder with
        | Config.Fixed_rung -> [ first ]
        | Literal_rung | Literal_rung_everywhere ->
            RankingCheck.const_ladder ~first ~literal:(A.literal_bound ()) ())

  let unit_const_rungs () = const_rungs ()

  let other_const_rungs () =
    match config.chain_pair_lex_candidate_const_ladder with
    | Config.Literal_rung_everywhere -> const_rungs ()
    | Fixed_rung | Literal_rung -> None

  module Debug = struct
    let print = A.print
  end

  (* [order_covers ~args order regions pairs]: whether the relation
     [order vars] (a formula over the two states [vars], the copy's
     positions followed by the state's) contains every ground pair of
     [pairs] (decided by evaluation over [args]) and every region of
     [regions] (each [region => order vars] proved valid by Z3 within 1000
     ms, over the region's own variables).  A check that raises, times out,
     is undecided, or is about a region of another arity answers false, so
     [true] is a proof of every containment and [false] claims nothing. *)
  let order_covers ~args order regions pairs =
    let open LogicOld in
    let n = List.length args / 2 in
    let old_args =
      List.map args ~f:(fun (x, s) -> (x, Logic.ExtTerm.to_old_sort s))
    in
    let guarded f x =
      try f x with exn_ when not (Common.Timer.is_async exn_) -> false
    in
    let covers_region =
      guarded (fun (vars, region, _) ->
          List.length vars = 2 * n
          &&
          let phi = Formula.mk_imply region (order vars) in
          (not (Z3Smt.Z3interface.may_not_return phi))
          &&
          match
            Z3Smt.Z3interface.check_valid ~timeout:(Some 1000) ~id:None
              (get_fenv ()) phi
          with
          | `Valid -> true
          | _ -> false)
    in
    let covers_pair =
      guarded (fun pair -> region_holds_at (old_args, order old_args) pair)
    in
    List.for_all pairs ~f:covers_pair && List.for_all regions ~f:covers_region

  (* [order_of_vars ~n build vars]: [build xs ys] over the terms of [vars]
     split into the first [n] (the copy) and the rest (the state). *)
  let order_of_vars ~n build vars =
    let xs, ys =
      List.split_n
        (List.map vars ~f:(fun (v, s) -> LogicOld.Term.mk_var v s))
        n
    in
    build xs ys

  (* [multiphase_candidate ~key ~args regions pairs]: under
     [chain_pair_region_multiphase_depth], a ranking for the key [key] (whose
     parameters [args] are the copy's state followed by the state) built from
     the certificates of [regions] (see [chain_regions_of]), tried in the order
     of their segments' lengths, shortest first: the first relation
     [RankingCheck.template_order] builds from a certificate that contains
     every ground pair of [pairs] and every region of [regions], certified or
     not ([order_covers]).  [None] when no region holds a certificate or no
     candidate passes.

     Why one certificate is tried against every region rather than one
     ranking fitted to all of them jointly: nested rankings are not closed
     under composition, so the regions of segments of two, three, ... steps
     of one loop need coefficients growing with the length, and no single
     nested ranking fits them all; but the order a certificate builds is
     transitive, so the certificate of the one-step region contains every
     composition of that step.

     Post: a [Some (fs, lam)] answer is [lam], the lambda over [args] of
     [template_order] on [fs], which is an instance of the ranking template
     with one piece and a trivially true discriminator, so well-founded
     whatever [fs] is.  The containment checks decide only whether the
     candidate is offered; a wrong check can cost a refinement, never
     soundness, since an answer still comes from a won strategy check. *)
  let multiphase_candidate ~key ~args regions pairs =
    let n = List.length args / 2 in
    let certs =
      List.filter_map regions ~f:(fun (_, _, cert) -> cert)
      |> List.stable_sort ~compare:(fun (l1, _) (l2, _) -> Int.compare l1 l2)
      |> List.map ~f:snd
      |> List.fold ~init:[] ~f:(fun acc fs ->
          if List.mem acc fs ~equal:Stdlib.( = ) then acc else acc @ [ fs ])
    in
    let old_args =
      List.map args ~f:(fun (x, s) -> (x, Logic.ExtTerm.to_old_sort s))
    in
    let order_over vars fs =
      order_of_vars ~n (fun xs ys -> RankingCheck.template_order xs ys fs) vars
    in
    if List.length args <> 2 * n || List.is_empty certs then None
    else
      List.find_map certs ~f:(fun fs ->
          match order_covers ~args (fun vars -> order_over vars fs) regions pairs with
          | true ->
              Debug.print
              @@ lazy
                   (sprintf
                      "## %s: multiphase candidate %s covers %d region(s) and \
                       %d pair(s)"
                      key
                      (RankingCheck.str_of_components fs)
                      (List.length regions) (List.length pairs));
              Some
                ( fs,
                  Logic.Term.mk_lambda args
                    (Logic.ExtTerm.of_old_formula (order_over old_args fs)) )
          | false ->
              Debug.print
              @@ lazy
                   (sprintf "## %s: multiphase candidate %s rejected" key
                      (RankingCheck.str_of_components fs));
              None)

  (* Counts of the LP candidate's questions without a coefficient bound by
     arithmetic ([chain_pair_lex_candidate_arith]), printed to stderr at exit
     when COAR_LEX_ARITH_COUNT is set: constructions asked over the rationals,
     then over the integers.  They are what proves a run read the field. *)
  let lex_arith_counts = [| 0; 0 |]

  let () =
    match Sys.getenv "COAR_LEX_ARITH_COUNT" with
    | None | Some "" -> ()
    | Some _ ->
        Stdlib.at_exit (fun () ->
            Stdlib.prerr_endline
            @@ sprintf "lex-arith: unbounded constructions rational %d, integer %d"
                 lex_arith_counts.(0) lex_arith_counts.(1))

  (* Counts of [chain_pair_lex_candidate_sign_cells]' constructions, printed
     to stderr at exit when COAR_SIGN_CELLS_COUNT is set: tried, built (a
     split's query answered), accepted (proved to contain every region and
     pair).  They are what proves a run read the field. *)
  let sign_cell_counts = [| 0; 0; 0 |]

  let () =
    match Sys.getenv "COAR_SIGN_CELLS_COUNT" with
    | None | Some "" -> ()
    | Some _ ->
        Stdlib.at_exit (fun () ->
            Stdlib.prerr_endline
            @@ sprintf "sign-cells: tried %d, built %d, accepted %d"
                 sign_cell_counts.(0) sign_cell_counts.(1) sign_cell_counts.(2))

  (* [lex_candidate ~key ~args regions pairs]: under
     [chain_pair_lex_candidate_depth] at [d >= 1], a ranking for the key [key]
     (parameters [args]: the copy's state, then the state) that contains every
     region of [regions] and every ground pair of [pairs], built by linear
     programming over all of them together rather than fitted point by point:
     first [RankingCheck.lex_ranking] of depth at most [d] over the regions'
     rows and the pairs read as point regions, offered only when it needs at
     least two components (a single linear ranking is the constraint
     solver's own first shape, so offering it would only replace one fit by
     another); then, when that finds nothing, [RankingCheck.piecewise_ranking]
     on the integer positions (also not when a single linear function ranks
     everything, which the lexicographic construction finds first).  A
     candidate is accepted only when
     [order_covers] proves it contains every region and pair; [None] when
     nothing is built or nothing passes, and then the caller asks the
     constraint solver exactly as without the field.  A region or pair whose
     rows cannot be read ([RankingCheck.region_rows]) takes no part in the
     construction but is still checked.

     Post: a [Some (descr, lam)] answer is [lam], the lambda over [args] of
     [RankingCheck.template_order] (one piece, the components as its
     lexicographic components, a trivially true discriminator) or of
     [RankingCheck.template_order_pieces] on two pieces with one component
     each and affine discriminators -- both instances of the ranking
     template, so well-founded whatever the linear programs answered; the
     containment checks decide only whether the candidate is offered.
     [descr] is the candidate for a trace.

     Under [chain_pair_lex_candidate_arith = Rational_unbounded] the
     questions without a coefficient bound are linear programs over the
     rationals with scaled components; they decide the same questions as the
     integer ones, so the steps of the construction are the same and only the
     components found may differ. *)
  let lex_candidate_build ~key ~args regions pairs =
    (if config.chain_pair_lex_candidate_conjunct_memo then
       Z3Smt.Z3interface.with_conjunct_memo
     else fun f -> f ())
    @@ fun () ->
    let open LogicOld in
    let depth = config.chain_pair_lex_candidate_depth in
    let direct_points = config.chain_pair_lex_candidate_direct_points in
    let base_session = config.chain_pair_lex_candidate_base_session in
    (* [chain_pair_lex_candidate_arith]: whether the questions without a
       coefficient bound are linear programs over the rationals; the
       unit-coefficient construction is an integer program either way *)
    let rational =
      match config.chain_pair_lex_candidate_arith with
      | Config.Integer -> false
      | Config.Rational_unbounded -> true
    in
    let count_unbounded () =
      let i = if rational then 0 else 1 in
      lex_arith_counts.(i) <- lex_arith_counts.(i) + 1
    in
    let n = List.length args / 2 in
    let old_args =
      List.map args ~f:(fun (x, s) -> (x, Logic.ExtTerm.to_old_sort s))
    in
    if depth < 1 || List.length args <> 2 * n || n = 0 then None
    else
      let rows_of vars phi =
        let xs, ys = List.split_n vars n in
        RankingCheck.region_rows xs ys phi
      in
      let region_rows =
        List.filter_map regions ~f:(fun (vars, region, _) ->
            if List.length vars <> 2 * n then None else rows_of vars region)
      in
      (* [chain_pair_lex_candidate_skip_covered_pairs]: a pair some region
         holds at adds no linear question the region's own do not imply *)
      let row_pairs =
        if config.chain_pair_lex_candidate_skip_covered_pairs then
          List.filter pairs ~f:(fun pair ->
              not
                (List.exists regions ~f:(fun (vars, r, _) ->
                     region_holds_at (vars, r) pair)))
        else pairs
      in
      let pair_rows =
        List.filter_map row_pairs ~f:(fun (a, b) ->
            let point = a @ b in
            if List.length point <> 2 * n then None
            else
              rows_of old_args
                (Formula.and_of
                   (List.map2_exn old_args point ~f:(fun (v, s) t ->
                        Formula.eq (Term.mk_var v s) t))))
      in
      let all_rows = region_rows @ pair_rows in
      (* [chain_pair_lex_candidate_dedup_rows]: each list of rows once, in
         the order of its first occurrence.  The rows are positional (column
         [j] is the [j]-th state variable of either visit), so the regions of
         one loop step read at different points of a long play are often the
         same rows; a repeated list adds the same constraints to every
         question, and the greedy pass below asks once per list (a list
         equal to one already ranked is feasible with it, one equal to a
         rejected one stays infeasible as the ranked set only grows), so the
         same lists are ranked at each level, up to questions undecided in
         their budget and the models returned.  Off, one question per region
         and pair: a play of 5,050 visits asked 5,050 growing linear programs
         at a level, about 0.6 s each. *)
      let n_rows = List.length all_rows in
      let all_rows =
        if config.chain_pair_lex_candidate_dedup_rows then
          let seen = Hash_set.Poly.create () in
          List.filter all_rows ~f:(fun rows ->
              let k =
                List.map rows ~f:(fun (ks, k0) ->
                    (List.map ks ~f:Z.to_string, Z.to_string k0))
              in
              if Hash_set.mem seen k then false
              else (
                Hash_set.add seen k;
                true))
        else all_rows
      in
      ChainPairs.log
        (sprintf "lexrows key=%s regions=%d pairs=%d rows=%d distinct=%s" key
           (List.length region_rows) (List.length pair_rows) n_rows
           (if config.chain_pair_lex_candidate_dedup_rows then
              string_of_int (List.length all_rows)
            else "-"));
      if List.is_empty all_rows then None
      else
        let accept descr build =
          let order vars = order_of_vars ~n build vars in
          if order_covers ~args order regions pairs then (
            Debug.print
            @@ lazy
                 (sprintf
                    "## %s: LP candidate %s covers %d region(s) and %d pair(s)"
                    key descr (List.length regions) (List.length pairs));
            Some
              ( descr,
                Logic.Term.mk_lambda args
                  (Logic.ExtTerm.of_old_formula (order old_args)) ))
          else (
            Debug.print
            @@ lazy (sprintf "## %s: LP candidate %s rejected" key descr);
            None)
        in
        (* whether a single linear ranking found without a coefficient bound
           is offered ([chain_pair_lex_candidate_linear], or past the
           template's bound under [chain_pair_lex_candidate_linear_above]) *)
        let offer_single fs =
          config.chain_pair_lex_candidate_linear
          (* [refine_rankings = Joint_guided] and [Joint_steered] select the
             terms against a ranking fixed before them, so the one linear
             ranking is offered rather than left to the constraint solver *)
          || Config.ranking_fixed_first config.refine_rankings
          || Option.exists config.chain_pair_lex_candidate_linear_above
               ~f:(fun b -> RankingCheck.exceeds_bound (Z.of_int b) fs)
        in
        let no_candidate_single fs =
          (* one linear function ranks everything: the constraint solver's
             own first shape, left to it *)
          Debug.print
          @@ lazy
               (sprintf
                  "## %s: one linear ranking %s ranks the %d region(s) and \
                   pair(s) read; no LP candidate"
                  key
                  (RankingCheck.str_of_components [ fs ])
                  (List.length all_rows));
          None
        in
        (* [chain_pair_lex_candidate_single_first]: the unbounded question
           for one component, asked before anything else; [`Not_asked]
           without the field *)
        let single =
          if config.chain_pair_lex_candidate_single_first then
            match
              count_unbounded ();
              RankingCheck.lex_ranking ~direct_points ~base_session ~rational
                ?const_first:(other_const_rungs ()) ~first_ask_only:true ~depth ~n
                all_rows
            with
            | Some [ fs ] -> `Single fs
            | _ -> `None
          else `Not_asked
        in
        match single with
        | `Single fs when not (offer_single fs) -> no_candidate_single fs
        | _ -> (
        (* first with unit coefficients, which prefers a lexicographic
           order over few positions to a single function with large
           coefficients; then unbounded *)
        let unit_raw =
          RankingCheck.lex_ranking ~direct_points ~base_session ~coef_bound:Z.one
            ?const_first:(unit_const_rungs ())
            ~depth ~n all_rows
        in
        let bounded =
          match unit_raw with
          | Some fs
            when List.length fs >= 2 || config.chain_pair_lex_candidate_linear
            ->
              accept
                ("lexicographic (unit coefficients) "
                ^ RankingCheck.str_of_components fs)
                (fun xs ys -> RankingCheck.template_order xs ys fs)
          | _ -> None
        in
        if Option.is_some bounded then bounded
        else
        let unbounded () =
          match single with
          | `Single fs -> Some [ fs ]
          | `None ->
              count_unbounded ();
              RankingCheck.lex_ranking ~direct_points ~base_session ~rational
                ?const_first:(other_const_rungs ()) ~skip_first_ask:true ~depth ~n
                all_rows
          | `Not_asked ->
              count_unbounded ();
              RankingCheck.lex_ranking ~direct_points ~base_session ~rational
                ?const_first:(other_const_rungs ()) ~depth ~n all_rows
        in
        (* [chain_pair_lex_candidate_small_first]: coefficient bounds 1, 2, 3
           before none, each with integer coefficients and rational Farkas
           multipliers (the unit-bound construction above has integer
           multipliers, which miss implications needing a fractional one).
           That construction's answer is reused at bound 1 when it is a
           single function (offered or not, it is an answer the bound allows),
           and a lexicographic answer of it that was not accepted counts as
           none at bound 1, so that the larger bounds and the unbounded
           construction can still offer something else. *)
        let unbounded =
          if config.chain_pair_lex_candidate_small_first then
            match
              RankingCheck.lex_ranking_small_first ~direct_points
                ~bounded:(fun b ->
                  match unit_raw with
                  | Some [ fs ] when b = 1 -> Some [ fs ]
                  | Some _ when b = 1 -> None
                  | _ ->
                      RankingCheck.lex_ranking ~direct_points ~base_session ~rational:true
                        ~integral:true ~coef_bound:(Z.of_int b)
                        ?const_first:(other_const_rungs ()) ~depth ~n
                        all_rows)
                ~bounds:[ 1; 2; 3 ] ~unbounded ~depth ~n all_rows
            with
            | Some (b, fs) ->
                repair_log
                  (sprintf "small-first %s %s at bound %s" key
                     (RankingCheck.str_of_components fs)
                     (match b with Some b -> string_of_int b | None -> "none"));
                Debug.print
                @@ lazy
                     (sprintf "## %s: LP components %s at coefficient bound %s"
                        key
                        (RankingCheck.str_of_components fs)
                        (match b with
                        | Some b -> string_of_int b
                        | None -> "none"));
                Some fs
            | None -> None
          else unbounded ()
        in
        match unbounded with
        | Some [ fs ] when offer_single fs ->
            accept
              ("linear " ^ RankingCheck.str_of_components [ fs ])
              (fun xs ys -> RankingCheck.template_order xs ys [ fs ])
        | Some [ fs ] -> no_candidate_single fs
        | Some fs ->
            accept
              ("lexicographic " ^ RankingCheck.str_of_components fs)
              (fun xs ys -> RankingCheck.template_order xs ys fs)
        | None -> (
            let is_int p =
              Term.is_int_sort (snd (List.nth_exn old_args p))
              && Term.is_int_sort (snd (List.nth_exn old_args (n + p)))
            in
            match RankingCheck.piecewise_ranking ~direct_points ~n ~is_int all_rows with
            | Some pw ->
                accept
                  ("two-piece " ^ RankingCheck.str_of_two_pieces pw)
                  (fun xs ys ->
                    RankingCheck.template_order_pieces xs ys
                      (RankingCheck.two_pieces ~n pw))
            | None -> (
                (* [chain_pair_lex_candidate_sign_cells]: pieces split on the
                   signs of one or two discriminators the rows state *)
                let sign_cells =
                  if config.chain_pair_lex_candidate_sign_cells then (
                    sign_cell_counts.(0) <- sign_cell_counts.(0) + 1;
                    RankingCheck.sign_cell_ranking ~direct_points ~rational
                      ~prune_empty:
                        config.chain_pair_lex_candidate_sign_cells_prune
                      ~n ~is_int all_rows)
                  else None
                in
                match sign_cells with
                | Some pieces ->
                    sign_cell_counts.(1) <- sign_cell_counts.(1) + 1;
                    let r =
                      accept
                        ("sign-cell " ^ RankingCheck.str_of_sign_cells pieces)
                        (fun xs ys ->
                          RankingCheck.template_order_pieces xs ys pieces)
                    in
                    if Option.is_some r then
                      sign_cell_counts.(2) <- sign_cell_counts.(2) + 1;
                    r
                | None ->
                Debug.print
                @@ lazy
                     (sprintf
                        "## %s: no LP candidate for the %d region(s) and \
                         pair(s) read"
                        key (List.length all_rows));
                None)))

  (* [chain_pair_lex_candidate_memo]: the outcomes of [lex_candidate_build]
     over ground pairs alone (no region), keyed by the key's name, its
     parameters, the pairs and the constant rungs (which read the game's
     literals), compared structurally as the pairs are everywhere else
     here.  The build reads nothing but these and the configuration, so a
     kept outcome is one a rebuild could give. *)
  let lex_candidate_memo = Hashtbl.Poly.create ()

  let lex_candidate ~key ~args regions pairs =
    if config.chain_pair_lex_candidate_memo && List.is_empty regions then (
      let k = (key, args, pairs, const_rungs ()) in
      match Hashtbl.find lex_candidate_memo k with
      | Some r ->
          Debug.print
          @@ lazy (sprintf "## %s: LP candidate over the pairs kept" key);
          r
      | None ->
          let r = lex_candidate_build ~key ~args regions pairs in
          Hashtbl.set lex_candidate_memo ~key:k ~data:r;
          r)
    else lex_candidate_build ~key ~args regions pairs
end
