open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open PCSatCommon

module Config = struct
  type perturbation =
    | None
    | Trans of int (* max_iters *)
    | Uniform of float (* bound *)
    | Gaussian of float (* standard deviation *)
  [@@deriving yojson]

  type strategy =
    | SAT (* SAT solving *)
    | ORACLE_SAT of strategy
    | POS_BIASED_SAT (* Positively biased SAT solving *)
    | NEG_BIASED_SAT (* Negatively biased SAT solving *)
    | RAND_MAX_SAT of
        (* Randomly weighted MAX-SAT solving *)
        float
        (* cut-off lower-bound *)
        * float (* cut-off upper-bound *)
    | BMI_MAX_SAT of
        (* BMI weighted MAX-SAT solving *)
        int
        (* num *)
        * int (* bound *)
        * float (* ratio *)
        * perturbation
        * float (* cut-off lower-bound *)
        * float (* cut-off upper-bound *)
        * float (* enc_bool_to_float *)
        * bool (* ignore_bool_args_variance *)
    | ORACLE_MAX_SAT of strategy
    | POS_BIASED_MAX_SAT of
        (* Positively biased MAX-SAT solving *)
        bool
        (* use examples *)
        * float (* weight *)
    | NEG_BIASED_MAX_SAT of
        (* Negatively biased MAX-SAT solving *)
        bool
        (* use examples *)
        * float (* weight *)
    | Mixed of (strategy * bool (* enable sampling *)) list
    | CBandit (* Contextual bandit *)
    | Bandit_BDD (* Bandit with BDDs *)
  [@@deriving yojson]

  type t = {
    verbose : bool; [@default false]
    num_labelings : int; [@default 1]
    strategy : strategy; [@default SAT]
    sat_solver : SATSolver.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/solver/z3_sat_dim_red.json"]
    discharge_cardinality_guards : bool; [@default false]
        (** NOT SOUND AS IT STANDS -- kept off, and kept because the measurement
            it produced is worth reproducing, not because the step is licensed.

            It treats a guard that constrains only the size of a quantified sort
            as a fact rather than a hypothesis. The reasoning was: a solution
            holds in every model of the theory, a quantified sort is every
            non-empty type, so a satisfiable such guard holds in some model and
            the model-independent solution must satisfy the atom there. Carrying
            that from *that* model to every value of the guard's parameters is
            the step that fails.

            The guard says the sort is a singleton. In a model where it holds,
            any two arguments of that sort are necessarily equal; in a model
            with two elements they need not be. So a candidate that tests two
            such arguments for equality -- which this hypothesis space can
            express -- satisfies the guarded example and violates the discharged
            one, and dropping the guard rejects a candidate the problem admits.
            That is a wrong refutation, not a lost answer. Invariance under
            permutations of the sort does not rescue it: permutations act inside
            one model, and the direction needed here identifies distinct
            elements, which creates equalities that did not hold.

            What would be sound is to instantiate the sort at the size the guard
            describes rather than to drop the guard, which is what the
            preprocessing pass that fixes a quantified sort at a finite size
            already does. *)
    conflict_by_unification : bool; [@default true]
        (** find a conflict between a positive and a negative example by asking
            whether their argument lists can be made equal, instead of by
            intersecting the sets of ground instances. Two parametric examples
            conflict at any COMMON instance, and the instantiation builds each
            example's instances from its own parameters alone, so a common
            instance needing coordinated choices across the two is never
            produced however many instances are taken *)
    pex_instances : int; [@default 1]
        (** how many ground instances a parametric example contributes to the
            satisfiability check and the labeling; [1] is one per example, the
            instance [ExClause.instantiate] picks *)
    smt_refutation : bool; [@default false]
        (** when the propositional labeling finds an assignment -- that is, when
            it has failed to refute -- ask an SMT solver whether the example set
            is satisfiable at all, with the unknowns as uninterpreted predicates
            over the atoms' actual arguments and with the guards kept. The
            propositional query can only refute through a collision of identical
            atoms; this one sees the arguments, so it reaches refutations that
            one cannot. Sound in the refutation direction only: the query asks
            whether some interpretation of the unknowns *and* of the theory
            satisfies the examples, which is weaker than what a solution must
            do, so its `unsat` refutes and its `sat` and `unknown` say nothing.
        *)
    truth_table_valid_timeout : int; [@default 0]
        (** a budget in milliseconds for each validity question the truth
            tables ask while this phase runs (a new atom evaluated against
            every qualifier of its predicate).  [0] (or less) asks without
            one, as before; an [int] rather than an option only because this
            module's own [None] constructor shadows the option's.  A question not decided in time leaves its cell undecided
            and is not recorded as "not valid", so a later question can still
            decide it; answers can be lost, never decided wrongly.  Without
            it one labeling phase was observed asking for minutes, most
            questions answering undecided after about a second. *)
    discharge_guards_globally : bool; [@default true]
        (** ask once whether the guards of *all* the parametric example atoms
            hold together, and if they do, drop every one of them for this
            labeling. A solution must work for every interpretation of a
            universally quantified sort, so a refutation may choose one, and in
            one where every guard holds a guarded atom is its bare application.
            Two atoms that differ only in their guards then collide, which is
            the one thing the propositional abstraction can refute with. *)
    fn_totality_drop : bool; [@default false]
        (** in an undecided example clause, drop a body atom of a functional
            unknown whose result is a parameter occurring nowhere else in the
            clause -- not among the atom's inputs, not in another atom, not in a
            head, not in a guard ([ExClause.simplify_totpvs] with
            [~with_positives:true], over the functional unknowns' input
            positions as well as the total ones').  [forall v. not P(t, v) \/ R]
            with [v] not in [R] says [R], since [P] is total.  Without it such
            an atom is a fresh propositional variable at every value a model
            gives the witness, so the labeling escapes the head by labeling
            the atom false, one value at a time.  [false]: only clauses
            without heads over total unknowns are so simplified *)
  }
  [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    SATSolver.Config.load_ext_file cfg.sat_solver >>= fun sat ->
    Ok { cfg with sat_solver = sat }

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Labeler"
    let instantiate = instantiate_ext_files
  end)

  let str_of_perturbation = function
    | None -> "None"
    | Trans max_iters -> sprintf "Trans(%d)" max_iters
    | Uniform bound -> sprintf "Uniform(%f)" bound
    | Gaussian sigma -> sprintf "Gaussian(%f)" sigma

  let rec str_of_strategy = function
    | SAT -> "SAT solving"
    | ORACLE_SAT s -> sprintf "Oracle SAT solving [%s]" @@ str_of_strategy s
    | POS_BIASED_SAT -> "Positively biased SAT solving"
    | NEG_BIASED_SAT -> "Negatively biased SAT solving"
    | RAND_MAX_SAT (cut_off_lb, cut_off_ub) ->
        sprintf "Randomly weighted MAX-SAT solving (%f, %f)" cut_off_lb
          cut_off_ub
    | BMI_MAX_SAT
        ( num,
          bound,
          ratio,
          perturbation,
          cut_off_lb,
          cut_off_ub,
          enc_bool_to_float,
          ignore_bool_args_variance ) ->
        sprintf "BMI weighted MAX-SAT solving (%d, %d, %f, %s, %f, %f, %f, %b)"
          num bound ratio
          (str_of_perturbation perturbation)
          cut_off_lb cut_off_ub enc_bool_to_float ignore_bool_args_variance
    | ORACLE_MAX_SAT s ->
        sprintf "Oracle MAX-SAT solving [%s]" (str_of_strategy s)
    | POS_BIASED_MAX_SAT (b, w) ->
        sprintf "Positively biased MAX-SAT solving (%b, %s)" b
          (string_of_float w)
    | NEG_BIASED_MAX_SAT (b, w) ->
        sprintf "Negatively biased MAX-SAT solving (%b, %s)" b
          (string_of_float w)
    | Mixed ss ->
        String.bracket
        @@ String.concat_map_list ~sep:", " ss ~f:(fun (s, b) ->
            (if b then "!" else "") ^ str_of_strategy s)
    | CBandit -> "Contextual bandit"
    | Bandit_BDD -> "Bandit with BDDs"

  module type ConfigType = sig
    val config : t
  end
end

module type ClassifierType = sig
  val run_phase : int -> State.u -> State.u Or_error.t
end

module Make
    (RLCfg : RLConfig.ConfigType)
    (Cfg : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : ClassifierType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  (* the input positions of each functional unknown (all but the result), in
     the form [ExClause.simplify_totpvs] takes for a total unknown *)
  let fn_input_positions =
    lazy
      (Map.Poly.filter_mapi (PCSP.Problem.senv_of APCSP.problem)
         ~f:(fun ~key ~data ->
           if PCSP.Problem.is_fn_pred APCSP.problem key then
             let n = List.length (Logic.Sort.args_of data) in
             if n >= 1 then Some (List.init (n - 1) ~f:Fn.id) else None
           else None))

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  let sat_solver =
    let open Or_error in
    ExtFile.unwrap config.sat_solver >>= fun cfg ->
    Ok
      (module SATSolver.Solver.Make (struct
        let config = cfg
      end) : SATSolver.Solver.SolverType)


  (* A disjunctively well-founded relation is one contained in a finite union
     of well-founded relations, and such a relation may contain a cycle of
     length two or more ({(a,b),(b,a)} is {(a,b)} u {(b,a)}), so a sample
     refutes it only by a self-loop, which no well-founded relation contains.
     Refuting every cycle, as for WF, is sound only where the clauses force
     the self-loop too, as the fixpoint reduction's encoding does by carrying
     the remembered state, and not for a declared DWF predicate. *)
  let learn_clauses_for_dwf_self_loops pos res dwfpvs =
    List.fold dwfpvs ~init:res ~f:(fun res (pvar, _sorts) ->
        Set.fold pos ~init:res ~f:(fun res ((pv, terms) as _papp) ->
            if Stdlib.(fst pv = pvar) && ExClause.has_self_loop terms then
              Set.add res (ExClause.mk_unit_neg (ExAtom.PApp (pv, terms)))
            else res))

  (* the return value may contain a unit clause*)
  let rec learn_clauses_for_wf_cycles pos res = function
    | [] -> res
    | (pvar, sorts) :: wfpvs -> (
        Fn.flip (learn_clauses_for_wf_cycles pos) wfpvs
        @@
        let sample = Set.filter pos ~f:(fst >> fst >> Stdlib.( = ) pvar) in
        if Set.is_empty sample then res
        else
          (* ToDo: Better add all? *)
          match Set.find sample ~f:(snd >> ExClause.has_self_loop) with
          | Some (pv, terms) ->
              Set.add res (ExClause.mk_unit_neg (ExAtom.PApp (pv, terms)))
          | None ->
              let open Graph in
              let open Pack.Digraph in
              let graph, node_map_rev = LoopDetector.gen_graph sample in
              LoopDetector.detect ~print:Debug.print pvar sorts
                (graph, Components.scc_list graph, node_map_rev)
                res)

  let rec learn_clauses_for_nwf_cycles pos res = function
    | [] -> res
    | (name, m) :: nwfpvs -> (
        Fn.flip (learn_clauses_for_nwf_cycles pos) nwfpvs
        @@
        let sample =
          Set.Poly.filter_map pos ~f:(fun (pv, terms) ->
              match
                PCSP.Problem.kind_of APCSP.problem (Ident.pvar_to_tvar @@ fst pv)
              with
              | Kind.NWF (nwf, (idl, idr))
                when Ident.tvar_equal name nwf.Kind.name ->
                  Some (pv, (idl, idr), terms)
              | _ -> None)
        in
        if Set.is_empty sample then res
        else
          (* ToDo: Better add all? *)
          match NWFLoopDetector.nwf_self_loop m sample with
          | Some lemma -> Set.add res lemma
          | None ->
              let open Graph in
              let open Pack.Digraph in
              let graph, node_map_rev = NWFLoopDetector.gen_graph m sample in
              NWFLoopDetector.detect_nwf ~print:Debug.print name m
                (graph, Components.scc_list graph, node_map_rev)
                res)

  let rec learn_clauses_for_parity_functions pos res = function
    | [] -> res
    | (name, m) :: parpvs -> (
        Fn.flip (learn_clauses_for_parity_functions pos) parpvs
        @@
        let sample =
          Set.Poly.filter_map pos ~f:(fun (pv, terms) ->
              match
                PCSP.Problem.kind_of APCSP.problem (Ident.pvar_to_tvar @@ fst pv)
              with
              | Kind.Parity (nwf, (idl, idr))
                when Ident.tvar_equal name nwf.Kind.name ->
                  Some (pv, (idl, idr), terms)
              | _ -> None)
        in
        if Set.is_empty sample then res
        else
          (* ToDo: Better add all? *)
          match NWFLoopDetector.parity_self_loop m sample with
          | Some lemma -> Set.add res lemma
          | None ->
              let open Graph in
              let open Pack.Digraph in
              let graph, node_map_rev = NWFLoopDetector.gen_graph m sample in
              NWFLoopDetector.detect_parity ~print:Debug.print m
                (graph, Components.scc_list graph, node_map_rev)
                res)

  let abstract_exatom map atm =
    match Map.Poly.find map atm with
    | None -> failwith @@ sprintf "Not found: %s" (ExAtom.str_of atm)
    | Some p -> p

  let abstract_clause map clause =
    let ps = Set.Poly.map clause.ExClause.positive ~f:(abstract_exatom map) in
    let ns =
      Set.Poly.map clause.ExClause.negative
        ~f:(abstract_exatom map >> PropLogic.Formula.mk_neg)
    in
    PropLogic.Formula.or_of @@ Set.to_list @@ Set.union ps ns

  let abstract map cls =
    PropLogic.Formula.and_of @@ Set.to_list
    @@ Set.Poly.map cls ~f:(abstract_clause map)

  let gen_fresh_prop =
    let prop_count = ref 0 in
    fun () ->
      prop_count := !prop_count + 1;
      PropLogic.Formula.mk_atom ("A" ^ string_of_int !prop_count)

  let mk_labels pos neg und =
    assert (Set.are_disjoint pos neg);
    Map.of_set_exn
    @@ Set.Poly.union_list
         [
           Set.Poly.filter_map und ~f:(fun atm ->
               if Set.mem pos atm || Set.mem neg atm then
                 (*ToDo: reachable?*)
                 None
               else Some (atm, gen_fresh_prop ()));
           Set.Poly.map pos ~f:(fun atm -> (atm, PropLogic.Formula.mk_true ()));
           Set.Poly.map neg ~f:(fun atm -> (atm, PropLogic.Formula.mk_false ()));
         ]

  let of_assignment map assign =
    Map.Poly.fold map ~init:(Set.Poly.empty, Set.Poly.empty)
      ~f:(fun ~key:app ~data:prop (pos, neg) ->
        match prop with
        | PropLogic.Formula.Atom (bvar, _) -> (
            match List.Assoc.find assign bvar ~equal:Stdlib.( = ) with
            | None (*ignore don't care*) -> (pos, neg)
            | Some true -> (Set.add pos app, neg)
            | Some false -> (pos, Set.add neg app))
        | True _ -> (Set.add pos app, neg)
        | False _ -> (pos, Set.add neg app)
        | _ -> (pos, neg))

  let scaler = 10000.0
  let print_log = false

  (* how many example clauses the previous labeling round held; the SMT
     refutation below is asked only when this round holds the same number *)
  let prev_example_count = ref (-1)

  (* the SAT solver gave up (Z3 [UNKNOWN]); must not be read as "no labeling
     exists", which would make the verdict [unsat] *)
  exception Sat_solver_unknown

  let search_labeling_with iters vs _wfpvs _dwfpvs map cls =
    let open Or_error.Monad_infix in
    if print_log then
      Set.iter cls ~f:(fun cl ->
          Debug.print
          @@ lazy ("[search_labeling_with] clause: " ^ ExClause.str_of cl));
    let constr = abstract map cls in
    if print_log then
      Debug.print
      @@ lazy
           ("[search_labeling_with] constr: " ^ PropLogic.Formula.str_of constr);
    let rec aux iters strategy =
      sat_solver >>= fun (module SatSolver : SATSolver.Solver.SolverType) ->
      match strategy with
      | Config.SAT -> (
          SatSolver.solve (SAT.Problem.of_prop_formula constr) >>= function
          | SAT.Problem.Unsat -> Ok None
          | SAT.Problem.Unknown -> raise Sat_solver_unknown
          | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
      | Config.ORACLE_SAT s -> (
          match vs.VersionSpace.oracle with
          | None -> aux iters s
          | Some oracle -> (
              constr
              :: List.filter_map (Map.Poly.to_alist map) ~f:(fun (atom, prop) ->
                  let open Option in
                  ExAtom.pvar_of atom >>= fun pvar ->
                  let qdep = VersionSpace.qdeps_of pvar vs in
                  Map.Poly.find (Map.of_set_exn @@ snd oracle) pvar
                  >>= fun pred ->
                  match
                    TruthTable.eval_pred
                      ~print:
                        (if print_log then Debug.print ~id else fun _ -> ())
                      ~id vs.fenv qdep pred atom
                  with
                  | Some true -> Some prop
                  | Some false -> Some (PropLogic.Formula.mk_neg prop)
                  | None -> assert false)
              |> PropLogic.Formula.and_of |> SAT.Problem.of_prop_formula
              |> SatSolver.solve
              >>= function
              | SAT.Problem.Unsat -> Ok None
              | SAT.Problem.Unknown -> raise Sat_solver_unknown
              | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true))))
      | Config.POS_BIASED_SAT | Config.NEG_BIASED_SAT -> (
          let pos_bias = Stdlib.(strategy = Config.POS_BIASED_SAT) in
          constr
          :: List.filter_map (Map.Poly.to_alist map) ~f:(fun (atm, prop) ->
              match (ExAtom.pvar_of atm, prop) with
              | Some _, PropLogic.Formula.Atom (_, _) ->
                  if pos_bias then Some prop
                  else Some (PropLogic.Formula.mk_neg prop)
              | _ -> None)
          |> PropLogic.Formula.and_of |> SAT.Problem.of_prop_formula
          |> SatSolver.solve
          >>= function
          | SAT.Problem.Unsat | SAT.Problem.Unknown (*ToDo*) -> (
              Debug.print @@ lazy "biased labeling not found";
              SatSolver.solve (SAT.Problem.of_prop_formula constr) >>= function
              | SAT.Problem.Unsat -> Ok None
              | SAT.Problem.Unknown -> raise Sat_solver_unknown
              | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
          | SAT.Problem.Sat sol ->
              Debug.print @@ lazy "biased labeling found";
              Ok (Some (of_assignment map sol, true)))
      | RAND_MAX_SAT (cut_off_lb, _cut_off_ub) -> (
          let soft =
            assert (Float.(cut_off_lb >= 0.));
            List.filter_map (Map.Poly.to_alist map) ~f:(fun (atom, prop) ->
                let heat = Random.float_range (-1.) 1. in
                Debug.print
                @@ lazy (sprintf "%s has value %f" (ExAtom.str_of atom) heat);
                let scaled_heat = int_of_float (scaler *. heat) in
                let scaled_cut_off_lb = int_of_float (scaler *. cut_off_lb) in
                if scaled_heat > scaled_cut_off_lb then
                  Some (SAT.Problem.of_prop_formula prop, scaled_heat)
                else if scaled_heat < -scaled_cut_off_lb then
                  Some
                    ( SAT.Problem.of_prop_formula (PropLogic.Formula.mk_neg prop),
                      -scaled_heat )
                else None)
          in
          SatSolver.opt_solve soft (SAT.Problem.of_prop_formula constr)
          >>= function
          | SAT.Problem.Unsat -> Ok None
          | SAT.Problem.Unknown -> raise Sat_solver_unknown
          | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
      | BMI_MAX_SAT
          ( num,
            bound,
            ratio,
            perturbation,
            cut_off_lb,
            _cut_off_ub,
            enc_bool_to_float,
            ignore_bool_args_variance ) -> (
          let soft =
            assert (Float.(cut_off_lb >= 0.));
            Debug.print @@ lazy ">>> heat map generation";
            let tm = Timer.make () in
            let exs1 =
              let dw =
                1.0
                (* default weight for counterexamples *)
              in
              Set.to_list
              @@ Set.Poly.map ~f:(fun cl -> (cl, dw))
              @@ VersionSpace.examples_of vs
            in
            let exs2 =
              let clauses =
                Set.elements @@ PCSP.Problem.clauses_of APCSP.problem
              in
              let rand_samp =
                List.init num ~f:(fun _ ->
                    let clause =
                      List.nth_exn clauses (Random.int (List.length clauses))
                    in
                    let sub =
                      Map.Poly.mapi (Clause.sort_env_of clause)
                        ~f:(fun ~key:_ ~data ->
                          match data with
                          | Logic.IntTerm.SInt ->
                              Logic.ExtTerm.mk_int
                                (Z.of_int
                                   (Random.int ((2 * bound) + 1) - bound))
                          | Logic.RealTerm.SReal ->
                              let fb = float_of_int bound in
                              Logic.ExtTerm.mk_real
                                (Q.of_float @@ Random.float_range (-.fb) fb)
                          | Logic.BoolTerm.SBool ->
                              Logic.BoolTerm.mk_bool @@ Random.bool ()
                          | _ (*ToDo*) -> Logic.ExtTerm.mk_dummy data)
                    in
                    Clause.reduce_sort_map
                    @@ Clause.subst
                         (PCSP.Problem.senv_of APCSP.problem)
                         sub clause)
              in
              let weight =
                if num = 0 then 0.0
                else
                  ratio
                  *. (float_of_int @@ List.length exs1)
                  /. float_of_int num
              in
              let unknowns =
                Map.key_set @@ PCSP.Problem.senv_of APCSP.problem
              in
              List.filter_map rand_samp ~f:(fun cl ->
                  let uni_senv, pos_atms, neg_atms, phi =
                    Clause.to_old_clause (PCSP.Problem.senv_of APCSP.problem) cl
                  in
                  assert (Map.Poly.is_empty uni_senv);
                  match
                    ExClause.make
                      (PCSP.Problem.senv_of APCSP.problem)
                      pos_atms neg_atms phi
                  with
                  | None -> None
                  | Some cl ->
                      Some (ExClause.normalize_params unknowns cl, weight))
            in
            VersionSpace.update_heat_map ~enc_bool_to_float
              ~ignore_bool_args_variance
              (PCSP.Problem.senv_of APCSP.problem)
              (exs1 @ exs2) vs;
            Debug.print @@ lazy (sprintf "<<< heat map generation: %f" (tm ()));
            (*Out_channel.print_endline @@ string_of_int iters_mod;*)
            List.filter_map (Map.Poly.to_alist map) ~f:(fun (atom, prop) ->
                let heat = VersionSpace.get_heat vs atom in
                let heat =
                  match perturbation with
                  | None -> heat
                  | Trans max_iters ->
                      let alpha =
                        float_of_int (min iters max_iters)
                        /. float_of_int max_iters
                      in
                      ((1.0 -. alpha) *. heat)
                      +. (alpha *. Random.float_range (-1.) 1.)
                  | Uniform bound ->
                      heat
                      +. Random.float_range (-.bound) bound
                         *. float_of_int iters
                  | Gaussian sigma ->
                      Float.rand_gaussian heat (sigma *. float_of_int iters)
                in
                Debug.print
                @@ lazy (sprintf "%s has value %f" (ExAtom.str_of atom) heat);
                let scaled_heat = int_of_float (scaler *. heat) in
                let scaled_cut_off_lb = int_of_float (scaler *. cut_off_lb) in
                if scaled_heat > scaled_cut_off_lb then
                  Some (SAT.Problem.of_prop_formula prop, scaled_heat)
                else if scaled_heat < -scaled_cut_off_lb then
                  Some
                    ( SAT.Problem.of_prop_formula (PropLogic.Formula.mk_neg prop),
                      -scaled_heat )
                else None)
          in
          SatSolver.opt_solve soft (SAT.Problem.of_prop_formula constr)
          >>= function
          | SAT.Problem.Unsat -> Ok None
          | SAT.Problem.Unknown -> raise Sat_solver_unknown
          | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
      | Config.ORACLE_MAX_SAT s -> (
          match vs.oracle with
          | None -> aux iters s
          | Some oracle -> (
              let soft =
                List.filter_map (Map.Poly.to_alist map) ~f:(fun (atom, prop) ->
                    let open Option in
                    ExAtom.pvar_of atom >>= fun pvar ->
                    Map.Poly.find (Map.of_set_exn @@ snd oracle) pvar
                    >>= fun pred ->
                    match
                      TruthTable.eval_pred
                        ~print:
                          (if print_log then Debug.print ~id else fun _ -> ())
                        ~id vs.fenv Map.Poly.empty pred atom
                    with
                    | Some true -> Some (SAT.Problem.of_prop_formula prop, 1)
                    | Some false ->
                        Some
                          ( SAT.Problem.of_prop_formula
                              (PropLogic.Formula.mk_neg prop),
                            1 )
                    | None -> assert false)
              in
              SatSolver.opt_solve soft (SAT.Problem.of_prop_formula constr)
              >>= function
              | SAT.Problem.Unsat -> Ok None
              | SAT.Problem.Unknown -> raise Sat_solver_unknown
              | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true))))
      | Config.POS_BIASED_MAX_SAT (strengthen_bias, w)
      | Config.NEG_BIASED_MAX_SAT (strengthen_bias, w) -> (
          let pos_bias =
            match strategy with
            | Config.POS_BIASED_MAX_SAT _ -> true
            | _ -> false
          in
          let weights =
            List.filter_map (Map.Poly.to_alist map) ~f:(fun (atm, prop) ->
                match (ExAtom.pvar_of atm, prop) with
                | Some _, PropLogic.Formula.Atom (_, _) -> Some (atm, 1.)
                | _ -> None)
          in
          let weights =
            if strengthen_bias then
              Set.fold ~init:weights cls ~f:(fun weights clause ->
                  List.map weights ~f:(fun (atm, weight) ->
                      let size =
                        Set.length clause.ExClause.positive
                        + Set.length clause.ExClause.negative
                      in
                      ( atm,
                        if
                          (pos_bias && Set.mem clause.ExClause.positive atm)
                          || (not pos_bias)
                             && Set.mem clause.ExClause.negative atm
                        then weight +. (w /. float_of_int size)
                        else weight )))
            else weights
          in
          let soft =
            List.map weights ~f:(fun (atm, weight) ->
                let prop = Map.Poly.find_exn map atm in
                if pos_bias then
                  ( SAT.Problem.of_prop_formula prop,
                    int_of_float (scaler *. weight) )
                else
                  ( SAT.Problem.of_prop_formula (PropLogic.Formula.mk_neg prop),
                    int_of_float (scaler *. weight) ))
          in
          SatSolver.opt_solve soft (SAT.Problem.of_prop_formula constr)
          >>= function
          | SAT.Problem.Unsat -> Ok None
          | SAT.Problem.Unknown -> raise Sat_solver_unknown
          | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
      | Config.Mixed ss -> (
          let strategy, sample_examples =
            List.nth_exn ss (iters mod List.length ss)
          in
          aux (iters / List.length ss) strategy >>= function
          | None -> Ok None
          | Some (labeling, sample_examples') ->
              Ok (Some (labeling, sample_examples && sample_examples')))
      | CBandit | Bandit_BDD -> failwith "not implemented"
    in
    aux iters

  (** ToDo: extend to support the case where [undecided] contains function
      variables *)
  let search_labeling_main iters vs wfpvs dwfpvs nwfpvs parpvs fnpvs pos_atms
      neg_atms undecided =
    let und_atms = ExClauseSet.exatoms_of undecided in
    let map = mk_labels pos_atms neg_atms und_atms in
    if print_log then
      Debug.print
      @@ lazy
           ("[search_labeling_main] map:\n"
           ^ String.concat_map_list (Map.Poly.to_alist map) ~sep:"\n"
               ~f:(fun (atm, prop) ->
                 sprintf "%s -> %s" (ExAtom.str_of atm)
                   (PropLogic.Formula.str_of prop)));
    let rec outer_loop ps_ns_list cls n =
      let open Or_error.Monad_infix in
      let rec inner_loop lcls (* learned clauses *) sample =
        let block_prev_assignments =
          (* constraints to block previous assignments *)
          Set.Poly.map (Set.Poly.of_list ps_ns_list) ~f:(fun (ps, ns, _) ->
              ExClause.canon { positive = ns; negative = ps })
        in
        if print_log then (
          Debug.print
          @@ lazy
               ("[search_labeling_main] learned clauses:\n"
               ^ ExClauseSet.str_of ~max_display:None lcls);
          Debug.print
          @@ lazy
               ("[search_labeling_main] example instances:\n"
               ^ ExClauseSet.str_of ~max_display:None sample);
          Debug.print
          @@ lazy
               ("[search_labeling_main] block_prev_assignments:\n"
               ^ ExClauseSet.str_of ~max_display:None block_prev_assignments));
        search_labeling_with iters vs wfpvs dwfpvs map
          (Set.Poly.union_list [ lcls; sample; block_prev_assignments ])
          config.strategy
        >>= function
        | None -> Ok (None, lcls)
        | Some ((pos, neg), sample_examples) ->
            let lcls' =
              let papps =
                Set.Poly.filter_map pos ~f:(function
                  | PApp papp ->
                      if print_log then
                        Debug.print
                        @@ lazy
                             ("[search_labeling_main] pos: "
                             ^ ExAtom.str_of (ExAtom.PApp papp));
                      Some papp
                  | _ -> (*ToDo: is it OK to ignore parametric examples?*) None)
              in
              Set.Poly.union_list
                [
                  learn_clauses_for_wf_cycles papps Set.Poly.empty wfpvs;
                  learn_clauses_for_dwf_self_loops papps Set.Poly.empty dwfpvs;
                  learn_clauses_for_nwf_cycles papps Set.Poly.empty nwfpvs;
                  learn_clauses_for_parity_functions papps Set.Poly.empty parpvs;
                  FnConflict.learn papps Set.Poly.empty fnpvs;
                ]
            in
            if Set.is_empty lcls' then
              (*sat*)
              Ok (Some (pos, neg, sample_examples), lcls)
            else inner_loop (Set.union lcls lcls') sample
      in
      if n <= 0 then Ok (ps_ns_list, cls)
      else
        inner_loop cls undecided >>= function
        | None, lcls ->
            (* the lemmas learned so far are part of the evidence when this
               is the first attempt (an unsat verdict) *)
            Ok (ps_ns_list, Set.union cls lcls)
        | Some (pos, neg, sample_examples), lcls ->
            outer_loop
              ((pos, neg, sample_examples) :: ps_ns_list)
              (Set.union cls lcls) (n - 1)
    in
    assert (config.num_labelings > 0);
    outer_loop [] Set.Poly.empty config.num_labelings

  (* [ExClause.instantiate] sends each parameter [$k] of a sort variable to its
     own constant [dummy_<sort>_$k] ([T_dt.mk_dummy_for]), so the distinctions a
     counterexample drew between the parameters of *one* example survive.  The
     constant is chosen by the parameter's canonical position, though, so every
     example is instantiated at the same points: two examples that conflict only
     when one's [$1] is the other's [$2], or only when two parameters denote the
     same element, are never seen.  With
     [pex_instances = k > 1] such an example contributes up to [k] instances --
     the one above first, then other maps of its parameters into the pool
     [$1 .. $k] described below, the ones that keep the parameters apart
     first.  Each is a substitution of universally
     quantified dummy constants for the parameters, hence an instance the
     example denotes; the option only adds material. *)
  let param_instance_subs k params =
    let svars =
      List.filter (Map.Poly.to_alist params) ~f:(function
        | _, LogicOld.Sort.SVar _ -> true
        | _ -> false)
    in
    if k <= 1 || List.is_empty svars || List.length svars > 4 (* k^n maps *)
    then []
    else
      (* The pool of a sort variable is the constants of the canonical
         parameter names [$1 .. $k], whether or not *this* example has that
         many parameters.  Both directions matter: sending two parameters of
         one example to the same constant reaches a one-element carrier, and
         sending one example's [$1] to [$2] separates it from another example's
         [$1], which is what makes a carrier with more than one element
         reachable at all -- by the canonical naming every example is otherwise
         instantiated at exactly the same points.  The choice is consistent
         across examples (one interpretation of the sort, which is what a
         refutation may pick, a forall-sort denoting every non-empty type). *)
      let pool s =
        List.init k ~f:(fun i ->
            let x = Ident.mk_dontcare (string_of_int (i + 1)) in
            let tvar = Option.value_exn (LogicOld.T_dt.dummy_name_for x s) in
            LogicOld.add_dummy_term tvar s;
            LogicOld.Term.mk_var tvar s)
      in
      let key = LogicOld.Term.str_of in
      let ident (x, s) =
        LogicOld.Term.mk_var
          (Option.value_exn (LogicOld.T_dt.dummy_name_for x s))
          s
      in
      let maps =
        List.fold svars ~init:[ Map.Poly.empty ] ~f:(fun acc (x, s) ->
            List.concat_map acc ~f:(fun sub ->
                List.map (pool s) ~f:(fun t -> Map.Poly.set sub ~key:x ~data:t)))
        |> List.filter ~f:(fun sub ->
            (* the identity map is [ExClause.instantiate]'s own instance *)
            not
            @@ List.for_all svars ~f:(fun (x, s) ->
                match Map.Poly.find sub x with
                | Some t -> String.equal (key t) (key (ident (x, s)))
                | None -> false))
        |> List.sort ~compare:(fun s1 s2 ->
            (* *More* distinct images first.  A map that sends two parameters
               to one constant is a one-element carrier, on which a guard
               saying [$1 != $2] is unsatisfiable, so the instance says
               nothing: ranking those first (the first version did) produced
               exactly the two vacuous instances on the two-element-carrier
               witness, and the guard below -- which discards a conflict whose
               combined condition is unsatisfiable -- threw them away.  What
               earns a place is a map that *permutes* -- it puts this
               example's atoms on another example's constants, where they can
               collide, and a collision is the only way the propositional
               abstraction refutes. *)
            let card sub =
              Set.length @@ Set.Poly.of_list @@ List.map ~f:key
              @@ Map.Poly.data sub
            in
            match Int.compare (card s2) (card s1) with
            | 0 ->
                String.compare
                  (String.concat_map_list ~f:key @@ Map.Poly.data s1)
                  (String.concat_map_list ~f:key @@ Map.Poly.data s2)
            | c -> c)
      in
      List.take maps (k - 1)

  let instantiate_examples cls =
    if config.pex_instances <= 1 then ExClauseSet.instantiate cls
    else
      let insts =
        Set.concat_map cls ~f:(fun cl ->
            let subs =
              param_instance_subs config.pex_instances @@ ExClause.params_of cl
            in
            (* the guard is part of the atom, hence part of the key the
               labeling matches on, and [ExAtom.instantiate] only simplifies it
               -- [$1 != $2] under the identity and under the swap come out as
               [d1 != d2] and [d2 != d1], two keys, and the instances that
               should collide do not.  [normalize] is what orients them (it is
               the commented-out step at the three call sites below); it is
               applied only on this path, so [pex_instances = 1] keeps the
               keys it always had. *)
            Set.Poly.of_list
            @@ List.map ~f:ExClause.normalize
            @@ ExClause.instantiate cl
               :: List.map subs ~f:(fun sub ->
                   ExClause.instantiate (ExClause.subst sub cl)))
      in
      Debug.print
      @@ lazy
           (sprintf "[instantiate_examples] %d example(s) -> %d instance(s)"
              (Set.length cls) (Set.length insts));
      insts

  let str_of_conflicts conflicts =
    "********* conflicts *********\n"
    ^ String.concat_map_set ~sep:", " ~f:ExAtom.str_of conflicts

  (* A COUNT, NOT A PASS: how many samples in the undecided clauses would a
     fact or goal clause of the problem decide outright, instantiated at the
     sample's own arguments?  Enabled by [COAR_FACTGOAL_COUNT=1] and otherwise
     inert -- no query, no fresh name, nothing beyond the environment read.  It
     decides nothing: the sets the labeling works on are untouched, so the only
     effect of switching it on is the solver time it spends (and whatever that
     does to a run near its budget).

     The rule it counts is the published one -- a fact clause
     [forall x. Phi(x) => pi(a(x))] forces [pi(v)] true wherever [Phi /\ a = v]
     has a witness, and a goal clause [forall x. Phi /\ pi(a) => false] forces
     it false -- with one change that is not optional here.  Satisfiability
     licenses the conclusion only when the query is closed and every term in it
     is fixed by the theory: then satisfiable and valid coincide.  An atom that
     is guarded or parametric means [forall params. cond => pi(args)], and a
     term the theory leaves open (a selector on the wrong constructor, a
     division by zero, an uninterpreted symbol) has a value that varies with
     the model; in both cases the conclusion has to hold in every model and at
     every admitted instantiation, so the query asked is the validity of
     [cond => exists x. Phi /\ a = args].  An answer that is neither yes nor
     no -- unknown, timeout, a formula the solver may not return on, an
     exception -- leaves the atom undecided and is counted as such, never as
     decided. *)
  (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
  let factgoal_enabled =
    Lazy.from_val
      (match Sys.getenv "COAR_FACTGOAL_COUNT" with
      | Some ("1" | "2" | "true" | "yes") -> true
      | _ -> false)

  (* [2] also prints every atom with its answer, for checking the count *)
  (* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
  let factgoal_detail =
    Lazy.from_val
      (match Sys.getenv "COAR_FACTGOAL_COUNT" with
      | Some "2" -> true
      | _ -> false)

  let factgoal_round = ref 0

  (* per predicate, the fact clauses and the goal clauses of the problem the
     loop solves -- the preprocessed one, since that is where the undecided
     atoms' predicates live -- each as [(binders, Phi, atom arguments)] *)
  let factgoal_clauses =
    lazy
      (let exi_senv = PCSP.Problem.senv_of APCSP.problem in
       let facts = Hashtbl.Poly.create () and goals = Hashtbl.Poly.create () in
       (match PCSP.Problem.clauses_of_opt APCSP.problem with
       | None -> ()
       | Some cls ->
           Set.iter cls ~f:(fun cl ->
               try
                 let uni_senv, ps, ns, phi = Clause.to_old_clause exi_senv cl in
                 let binders =
                   Map.Poly.to_alist
                   @@ Map.Poly.map uni_senv ~f:Logic.ExtTerm.to_old_sort
                 in
                 (* a clause is [phi \/ ps \/ not ns], so its body's pure part
                    is the negation of [phi] *)
                 let body = LogicOld.Formula.mk_neg phi in
                 let one = function
                   | LogicOld.Atom.App (LogicOld.Predicate.Var (pv, _), args, _)
                     ->
                       Some (pv, args)
                   | _ -> None
                 in
                 match (Set.to_list ps, Set.to_list ns) with
                 | [ a ], [] -> (
                     match one a with
                     | Some (pv, args) ->
                         Hashtbl.Poly.add_multi facts ~key:pv
                           ~data:(binders, body, args)
                     | None -> ())
                 | [], [ a ] -> (
                     match one a with
                     | Some (pv, args) ->
                         Hashtbl.Poly.add_multi goals ~key:pv
                           ~data:(binders, body, args)
                     | None -> ())
                 | _ -> ()
               with exn when not (Timer.is_async exn) -> ()));
       (* once per labeler instance, so that a zero in the per-call line can be
          told apart from a problem that has no fact or goal clause at all *)
       eprintf "[factgoal] clauses fact=%d goal=%d\n%!"
         (Hashtbl.fold facts ~init:0 ~f:(fun ~key:_ ~data n ->
              n + List.length data))
         (Hashtbl.fold goals ~init:0 ~f:(fun ~key:_ ~data n ->
              n + List.length data));
       (facts, goals))

  (* atom -> (decided by a fact, decided by a goal, some query undecided);
     cached because the version space keeps its examples across rounds and the
     answer depends on the atom alone *)
  let factgoal_cache : (string, bool * bool * bool) Hashtbl.t =
    Hashtbl.create (module String)

  let factgoal_query fenv (args, params, cond) (binders, body, cargs) =
    (* the clause's variables are renamed apart from the atom's by a prefix
       rather than by a fresh name, so the global fresh-name counter -- which
       steers CEGIS trajectories -- is not moved by the count *)
    let ren =
      List.map binders ~f:(fun (x, s) ->
          (x, (Ident.Tvar ("fg__" ^ Ident.name_of_tvar x), s)))
    in
    let sub =
      Map.Poly.of_alist_exn
      @@ List.map ren ~f:(fun (x, (y, s)) -> (x, LogicOld.Term.mk_var y s))
    in
    let binders' = List.map ren ~f:snd in
    match List.zip cargs args with
    | Unequal_lengths -> `Undecided
    | Ok pairs -> (
        try
          let eqs =
            List.map pairs ~f:(fun (ca, a) ->
                LogicOld.Formula.eq (LogicOld.Term.subst sub ca) a)
          in
          let core =
            LogicOld.Formula.and_of (LogicOld.Formula.subst sub body :: eqs)
          in
          let ground =
            Map.Poly.is_empty params
            && LogicOld.Formula.is_true cond
            && List.for_all args ~f:(fun t ->
                Set.is_empty (LogicOld.Term.tvs_of t))
          in
          if ground && not (ClauseOld.interpretation_dependent core) then
            if Z3Smt.Z3interface.may_not_return core then `Undecided
            else
              match
                Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 2000) fenv
                  [ core ]
              with
              | `Sat _ -> `Decided
              | `Unsat -> `No
              | _ -> `Undecided
          else
            let phi =
              LogicOld.Formula.mk_imply cond
                (LogicOld.Formula.exists binders' core)
            in
            if Z3Smt.Z3interface.may_not_return phi then `Undecided
            else
              match
                Z3Smt.Z3interface.check_valid ~id ~timeout:(Some 2000) fenv phi
              with
              | `Valid -> `Decided
              | `Invalid _ -> `No
              | _ -> `Undecided
        with exn when not (Timer.is_async exn) -> `Undecided)

  let factgoal_count vs dpos dneg undecided =
    if Lazy.force factgoal_enabled then begin
      incr factgoal_round;
      let facts, goals = Lazy.force factgoal_clauses in
      let decided =
        Set.union (ExClauseSet.exatoms_of dpos) (ExClauseSet.exatoms_of dneg)
      in
      let atoms =
        Set.filter (ExClauseSet.exatoms_of undecided) ~f:(fun a ->
            (ExAtom.is_papp a || ExAtom.is_ppapp a) && not (Set.mem decided a))
      in
      let n = ref 0 and p = ref 0 and q = ref 0 and u = ref 0 and c = ref 0 in
      Set.iter atoms ~f:(fun atm ->
          match atm with
          | ExAtom.PApp ((pv, _), args)
          | ExAtom.PPApp (_, ((pv, _), args)) ->
              let params, cond =
                match atm with
                | ExAtom.PPApp ((params, cond), _) -> (params, cond)
                | _ -> (Map.Poly.empty, LogicOld.Formula.mk_true ())
              in
              let key = ExAtom.str_of atm in
              let pos, neg, und =
                match Hashtbl.find factgoal_cache key with
                | Some r -> r
                | None ->
                    let decide tbl =
                      List.fold (Hashtbl.Poly.find_multi tbl pv)
                        ~init:(false, false) ~f:(fun (d, un) cl ->
                          if d then (d, un)
                          else
                            match
                              factgoal_query vs.VersionSpace.fenv
                                (args, params, cond) cl
                            with
                            | `Decided -> (true, un)
                            | `No -> (false, un)
                            | `Undecided -> (false, true))
                    in
                    let pos, u1 = decide facts in
                    let neg, u2 = decide goals in
                    let r = (pos, neg, u1 || u2) in
                    Hashtbl.set factgoal_cache ~key ~data:r;
                    r
              in
              if Lazy.force factgoal_detail then
                eprintf "[factgoal] atom %s facts=%d goals=%d pos=%b neg=%b und=%b\n%!"
                  key
                  (List.length (Hashtbl.Poly.find_multi facts pv))
                  (List.length (Hashtbl.Poly.find_multi goals pv))
                  pos neg und;
              incr n;
              if pos then incr p;
              if neg then incr q;
              if pos && neg then incr c;
              if (not pos) && (not neg) && und then incr u
          | _ -> ());
      eprintf
        "[factgoal] round=%d undecided_atoms=%d pos_by_fact=%d neg_by_goal=%d \
         undecided_query=%d conflicting=%d\n\
         %!"
        !factgoal_round !n !p !q !u !c
    end

  let search_labeling_body iters vs () =
    let dpos, dneg, undecided = VersionSpace.pos_neg_und_examples_of vs in
    factgoal_count vs dpos dneg undecided;
    (*Debug.print @@ lazy ("undecided:\n" ^ ExClauseSet.str_of ~max_display:None undecided);*)
    Debug.print
    @@ lazy ("*** labeling with " ^ Config.str_of_strategy config.strategy);
    let wfpvs =
      List.map ~f:(fun (x, sort) ->
          ( Ident.tvar_to_pvar x,
            List.map (Logic.Sort.args_of sort) ~f:Logic.ExtTerm.to_old_sort ))
      @@ Map.Poly.to_alist
      @@ PCSP.Problem.wfpvs_senv_of APCSP.problem
    in
    let dwfpvs =
      List.map ~f:(fun (x, sort) ->
          ( Ident.tvar_to_pvar x,
            List.map (Logic.Sort.args_of sort) ~f:Logic.ExtTerm.to_old_sort ))
      @@ Map.Poly.to_alist
      @@ PCSP.Problem.dwfpvs_senv_of APCSP.problem
    in
    let nwfpvs =
      List.map ~f:(fun ls ->
          (fst @@ List.hd_exn ls, Map.Poly.of_alist_exn @@ List.map ls ~f:snd))
      @@ List.classify (fun (n1, _) (n2, _) -> Ident.tvar_equal n1 n2)
      @@ List.map ~f:(fun (name, sorts, idl, sorts_x, idr, sorts_y) ->
          ( name,
            ( (idl, idr),
              ( (* A placeholder, and safe as one: on the NWF path the record's
                   fields are never read.  [learn_clauses_for_nwf_cycles] takes
                   only the *sorts* out of this tuple, and the [nwf] it matches
                   against comes from the problem's own [kind_map], not from
                   here; [NWFLoopDetector.detect_nwf], [nwf_self_loop] and
                   [get_papps_nwf] use the sorts too.  The functions that do
                   read the record -- [is_sat_parity_cond] and
                   [parity_self_loop], through [nwf.sigma] and [nwf.acc_set] --
                   are reached only from the Parity learner, and the Parity list
                   built just below passes the real record.  Were that ever to
                   change, [dummy_nwf.sigma] is empty and the [find_exn] there
                   would raise. *)
                Kind.dummy_nwf,
                List.map ~f:Logic.ExtTerm.to_old_sort sorts,
                List.map ~f:Logic.ExtTerm.to_old_sort sorts_x,
                List.map ~f:Logic.ExtTerm.to_old_sort sorts_y ) ) ))
      @@ Map.Poly.data
      @@ PCSP.Problem.nwfpvs_senv_of APCSP.problem
    in
    let parpvs =
      List.map ~f:(fun ls ->
          (fst @@ List.hd_exn ls, Map.Poly.of_alist_exn @@ List.map ls ~f:snd))
      @@ List.classify (fun (n1, _) (n2, _) -> Ident.tvar_equal n1 n2)
      @@ List.map ~f:(fun (nwf, idl, sorts_x, idr, sorts_y) ->
          ( nwf.Kind.name,
            ( (idl, idr),
              ( nwf,
                List.map ~f:Logic.ExtTerm.to_old_sort nwf.sorts_shared,
                List.map ~f:Logic.ExtTerm.to_old_sort sorts_x,
                List.map ~f:Logic.ExtTerm.to_old_sort sorts_y ) ) ))
      @@ Map.Poly.data
      @@ PCSP.Problem.paritypvs_senv_of APCSP.problem
    in
    (* the single-valued predicates with their positions: FN at its last
       argument, Uniq at its declared one; the conflict learner uses only
       single-valuedness, so both reach it *)
    let fnpvs =
      List.map ~f:(fun (x, (sort, j)) ->
          ( Ident.tvar_to_pvar x,
            List.map (Logic.Sort.args_of sort) ~f:Logic.ExtTerm.to_old_sort,
            j ))
      @@ Map.Poly.to_alist
      @@ PCSP.Problem.single_valued_pvs_of APCSP.problem
    in
    let open Or_error in
    (* What reaches this phase, and what the next line does to it.  The two are
       counted together because they are the same examples before and after:
       [instantiate_examples] replaces a parametric atom's parameters by
       concrete values, so whatever generality a producer put into [dpos] and
       [dneg] stops here unless a consumer below reads it from the uninstantiated
       sets.  Reporting arrival without this loss would credit the phase with
       generality it immediately spends. *)
    PCSatCommon.GeneralityMonitor.(
      if on () then begin
        let classify exs =
          Set.fold (ExClauseSet.exatoms_of exs) ~init:(0, 0, 0)
            ~f:(fun (g, p, c) atm ->
              let _, cond, _ = ExAtom.to_old_formula_and_cond atm in
              let guarded = if LogicOld.Formula.is_true cond then 0 else 1 in
              if ExAtom.is_ppapp atm then (g, p + 1, c + guarded)
              else (g + 1, p, c + guarded))
        in
        let g1, p1, c1 = classify dpos and g2, p2, c2 = classify dneg in
        arrive ~site:"decided-examples" Labeling ~ground:(g1 + g2)
          ~parametric:(p1 + p2) ~guarded:(c1 + c2);
        (* NOT a loss of generality by itself, and saying so was wrong.  Two
           consumers read these examples and only one of them is fed from here:
           the propositional search below keys on atoms and needs them ground,
           while the conflict-by-unification search reads [dpos] and [dneg]
           directly, parameters and all.  So this counts what the PROPOSITIONAL
           path gives up, and the parametric path sees the generality whatever
           this number is. *)
        lose Labeling "grounded-for-the-propositional-path" (p1 + p2)
      end);
    let pos_atms, neg_atms, undecided_inst =
      (*ToDo: extend satisfiability checker to support parametric examples;
        [instantiate_examples] only widens the set of ground instances it sees
        ([pex_instances]) *)
      ( ExClauseSet.exatoms_of_uclauses
        @@
        (*ExClauseSet.normalize @@*)
        instantiate_examples dpos,
        ExClauseSet.exatoms_of_uclauses
        @@
        (*ExClauseSet.normalize @@*)
        instantiate_examples dneg,
        (*ExClauseSet.normalize @@*) instantiate_examples undecided )
    in
    (* An instance whose guard became [false] says nothing, and must not reach
       the propositional encoding below: that encoding gives each atom -- guard
       included -- one variable, so [false => P(t)] from one example and
       [false => not P(t)] from another share a variable and contradict each
       other although neither applies anywhere.  The instantiation makes such
       atoms whenever a guard constrains a parameter that the default point
       does not satisfy ([$1 >= 1] at [$1 = 0]), and a model-independent
       labeling problem built from them was refuted, with the refutation
       certified by a check replaying the same encoding, on a satisfiable
       input.  Removing an atom or a clause only weakens the problem, so a
       refutation of what is left is still one. *)
    let pos_atms = Set.filter pos_atms ~f:(Fn.non ExAtom.guard_is_false)
    and neg_atms = Set.filter neg_atms ~f:(Fn.non ExAtom.guard_is_false)
    and undecided_inst =
      Set.filter undecided_inst ~f:(Fn.non ExClause.has_false_guard)
    in
    (* Stage 1 of the labeling redesign: the guards the instantiation could not
       discharge one at a time may still hold *together*, and a refutation is
       entitled to pick an interpretation in which they do -- a solution has to
       work for every interpretation of a universally quantified sort.  One Z3
       call over the whole accumulated set decides it; the set is accumulated
       because the version space keeps its examples across rounds, and once the
       conjunction is unsatisfiable the transformation stops for good. *)
    let cond_of atm =
      let _, cond, _ = ExAtom.to_old_formula_and_cond atm in
      if LogicOld.Formula.is_true cond then None else Some cond
    in
    let pos_atms, neg_atms, undecided_inst =
      if not config.discharge_guards_globally then
        (pos_atms, neg_atms, undecided_inst)
      else
        let conds =
          Set.to_list
          @@ Set.union
               (Set.Poly.filter_map (Set.union pos_atms neg_atms) ~f:cond_of)
          @@ Set.concat_map undecided_inst ~f:(fun cl ->
              Set.Poly.filter_map
                (Set.union cl.ExClause.positive cl.ExClause.negative)
                ~f:cond_of)
        in
        (* what is handed to the check, not what the examples print: an
           example prints its guard over the parameters, while the check sees
           the guard after instantiation, and the two differ whenever the
           instantiation collapses parameters onto one dummy.  Printing only
           the former hides a guard that has become [false] -- which is a
           labeling that decides nothing, from examples that look fine. *)
        Debug.print
        @@ lazy
             (sprintf "*** guards handed to the satisfiability check:\n%s"
             @@ String.concat_map_list ~sep:"\n" conds
                  ~f:LogicOld.Formula.str_of);
        if List.is_empty conds then (pos_atms, neg_atms, undecided_inst)
        else
          let phi = LogicOld.Formula.and_of conds in
          match
            (* a binder of certain sorts makes the call not return at all, and
               the 5 s below is handed to the solver as a tactic's budget and
               does not hold there, so the shape is checked before asking.  The
               answer when it cannot be asked is the one this site already gives
               when the solver gives up: the guards are KEPT, which is the safe
               direction -- discharging a guard that was never shown to hold is
               what turns examples that apply nowhere into a refutation *)
            if Z3Smt.Z3interface.may_not_return phi then
              `Unknown "a sort the query may not return on (a binder, or an occurrence)"
            else
              Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 5000) vs.fenv
                [ phi ]
          with
          | `Sat _ ->
              Debug.print
              @@ lazy
                   (sprintf
                      "*** the %d guards hold together; dropped for this \
                       labeling"
                      (List.length conds));
              ( Set.Poly.map pos_atms ~f:ExAtom.discharge_guard,
                Set.Poly.map neg_atms ~f:ExAtom.discharge_guard,
                Set.Poly.map undecided_inst ~f:ExClause.discharge_guards )
          | ans ->
              Debug.print
              @@ lazy
                   (sprintf "*** the %d guards are %s together; kept"
                      (List.length conds)
                      (match ans with
                      | `Unsat -> "unsatisfiable"
                      | _ -> "undecided"));
              (pos_atms, neg_atms, undecided_inst)
    in
    (* Two examples parametric in their own variables conflict wherever their
       arguments can be made equal, and the intersection above cannot find that:
       [instantiate_examples] builds each example's instances from that
       example's parameters, so a common instance requiring a coordinated choice
       across the two -- one example's parameter matching a term built from the
       other's -- is never produced, at any number of instances. Asking the
       solver instead is exact and needs no unifier: rename the two parameter
       sets apart, conjoin both guards with the equations between corresponding
       arguments, and ask whether that is satisfiable. A model of it is a point
       at which one example demands the predicate hold and the other demands it
       not, which is a refutation. Unsatisfiable means the two never meet, and
       undecided is not a refutation -- the same safe direction the guard check
       below takes, for the same reason. *)
    let paired = ref 0
    and declined = ref 0
    and unsat_pairs = ref 0
    and undecided_pairs = ref 0
    and guard_only = ref 0 in
    let unification_conflicts =
      if not config.conflict_by_unification then Set.Poly.empty
      else
        (* Is this guard a statement about the SIZE of a forall-sort alone?
           Then it is a fact rather than a hypothesis: it holds in some model of
           the theory -- a forall-sort is every non-empty type -- and a solution
           is one formula for all models, so it must satisfy the atom there.
           Parametricity carries that from the element the guard names to every
           value of its parameters.

           The two conditions are what keep it narrow. Every free variable must
           be of a *sort variable*: a guard over an [Int] constrains a sort the
           theory fixes and parametricity says nothing about it. And the guard
           must contain no application of a universal function -- a universal
           reaches this tree as an array-sorted variable applied by [select], and
           a constraint on what it RETURNS is not a constraint on how many
           elements the sort has, so discharging it would assert something the
           example never said. *)
        let cardinality_guard_only cond =
          config.discharge_cardinality_guards
          && (not (LogicOld.Formula.is_true cond))
          && Set.for_all (LogicOld.Formula.term_sort_env_of cond)
               ~f:(fun (_, srt) ->
                 match srt with LogicOld.Sort.SVar _ -> true | _ -> false)
          && Set.is_empty
               (LogicOld.Formula.filtered_terms_of cond ~f:(function
                 | LogicOld.Term.FunApp (LogicOld.T_array.ASelect _, _, _) ->
                     true
                 | _ -> false))
          && (not (Z3Smt.Z3interface.may_not_return cond))
          &&
          match
            Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 5000) vs.fenv
              [ cond ]
          with
          | `Sat _ ->
              Debug.print
              @@ lazy
                   (sprintf
                      "[search_labeling] discharging a guard about the size of \
                       a quantified sort: %s"
                      (LogicOld.Formula.str_of cond));
              true
          | _ -> false
        in
        let drop_if_cardinality cond =
          if cardinality_guard_only cond then LogicOld.Formula.mk_true ()
          else cond
        in
        (* Where do the two atoms agree?  Returns the condition under which they
           are the same atom, together with the renamed parameters of the second,
           or [None] when they cannot agree at all.

           Satisfiability, not validity, and the difference decided this: a
           decided negative that is MORE SPECIFIC than a clause's head -- it
           carries a concrete term where the head carries a parameter -- does not
           settle that head at every value, and asking validity correctly says
           no.  But a conflict does not need every value, only a common
           instance, and the head being universally quantified over its own
           parameters includes the one the negative fixes.  What keeps that sound
           is that the condition travels: the literal is not removed, an example
           GUARDED by the condition is derived, which says exactly "where these
           two are the same atom, the body is false" and nothing more. *)
        let matching (pv1, a1, c1, prm1) (pv2, a2, c2, prm2) =
          if not (Ident.pvar_equal pv1 pv2 && List.length a1 = List.length a2)
          then None
          else
            (* the two atoms name their parameters independently -- both count
             from [$1] -- so the equations must be built after renaming one side
             apart. Without this the query mentions one name at two sorts and
             the conversion fails with "assigned inconsistent types", which is
             what happens the first time a head and an example of different
             sorts meet. *)
            let ren =
              Map.Poly.mapi prm2 ~f:(fun ~key ~data ->
                  LogicOld.Term.mk_var
                    (Ident.mk_fresh_tvar
                       ~prefix:(Some (Ident.name_of_tvar key ^ "%"))
                       ())
                    data)
            in
            let a2 = List.map a2 ~f:(LogicOld.Term.subst ren) in
            let c2 = LogicOld.Formula.subst ren c2 in
            let ex_names =
              Set.Poly.of_list
              @@ List.filter_map (Map.Poly.data ren) ~f:(function
                | LogicOld.Term.Var (x, _, _) -> Some x
                | _ -> None)
            in
            let eqs =
              LogicOld.Formula.and_of
                (c1 :: c2 :: List.map2_exn a1 a2 ~f:LogicOld.Formula.eq)
            in
            let ex_params =
              Set.to_list
              @@ Set.filter (LogicOld.Formula.term_sort_env_of eqs)
                   ~f:(fun (x, _) -> Set.mem ex_names x)
            in
            ignore ex_params;
            let query = eqs in
            let ren_params =
              Map.Poly.of_alist_exn
              @@ List.filter_map (Map.Poly.to_alist ren) ~f:(function
                | _, LogicOld.Term.Var (x, srt, _) -> Some (x, srt)
                | _ -> None)
            in
            ignore prm1;
            if Z3Smt.Z3interface.may_not_return query then None
            else if ExAtom.args_never_meet a1 a2 then
              (* different literals at one position: the two atoms are never
                 the same atom, which is the solver's [Unsat] below, without
                 the call; this search tests every (head, decided negative)
                 pair of a predicate at every labeling *)
              None
            else
              match
                Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 5000) vs.fenv
                  [ query ]
              with
              | `Sat _ -> Some (query, ren_params)
              | _ -> None
        in
        let parts atm =
          match (ExAtom.pvar_of atm, ExAtom.args_of atm) with
          | Some pvar, Some args ->
              let _, cond, _ = ExAtom.to_old_formula_and_cond atm in
              Some (pvar, args, cond, ExAtom.params_of atm)
          | _ -> None
        in
        let freshen (pvar, args, cond, params) =
          let sub =
            Map.Poly.mapi params ~f:(fun ~key ~data ->
                LogicOld.Term.mk_var
                  (Ident.mk_fresh_tvar
                     ~prefix:(Some (Ident.name_of_tvar key ^ "#"))
                     ())
                  data)
          in
          ( pvar,
            List.map args ~f:(LogicOld.Term.subst sub),
            LogicOld.Formula.subst sub cond )
        in
        (* the PARAMETRIC atoms, not [pos_atms]/[neg_atms]: those come from
           [instantiate_examples], which has already replaced the parameters by
           concrete values, so equations between them are equations between
           ground terms and this test would be the intersection again with a
           solver call bolted on. The whole point is to compare the examples
           before either of them has been committed to an instance. *)
        let pos_par = ExClauseSet.exatoms_of_uclauses dpos in
        let neg_par0 = ExClauseSet.exatoms_of_uclauses dneg in
        (* what the unification search actually receives, uninstantiated.  This
           is the arrival number that matters for a generalisation mechanism:
           the one above is what the propositional path is handed. *)
        PCSatCommon.GeneralityMonitor.(
          if on () then begin
            let count s = Set.count s ~f:ExAtom.is_ppapp in
            arrive ~site:"unification-search" Labeling
              ~ground:
                (Set.length pos_par + Set.length neg_par0
                - count pos_par - count neg_par0)
              ~parametric:(count pos_par + count neg_par0)
              ~guarded:0
          end);
        (* An undecided clause [body => head] whose head a decided negative
           settles at EVERY value of the clause's parameters has a body that
           must be false, so it is a negative example the loop has not drawn.
           Validity, not satisfiability: the head is being settled for the whole
           clause, and an overlap would let a body be called false where the
           examples never refuted its head, which is a wrong refutation. Only
           the two-literal shape is taken, because that is the one whose
           simplification leaves a unit. *)
        let shaped = ref 0 and tried = ref 0 and renamed = ref 0 in
        let derived_neg =
          Set.concat_map undecided ~f:(fun cl ->
              match
                ( Set.to_list cl.ExClause.positive,
                  Set.to_list cl.ExClause.negative )
              with
              | [ head ], [ body ] -> (
                  incr shaped;
                  match parts head with
                  | None -> Set.Poly.empty
                  | Some hp ->
                      Set.Poly.filter_map neg_par0 ~f:(fun n ->
                          match parts n with
                          | None -> None
                          | Some np ->
                              let pv1, _, _, _ = hp and pv2, _, _, _ = np in
                              if Ident.pvar_equal pv1 pv2 then (
                                incr tried;
                                (* DIAGNOSTIC: do the two agree up to a
                                     bijection on their parameters once the
                                     guards are set aside?  That is what
                                     [canon_key] decides, exactly and without a
                                     solver, and it separates "the atoms are
                                     different" from "they are the same and the
                                     query could not be proved" -- a validity
                                     question with a forall-exists alternation
                                     over uninterpreted sorts and datatypes is
                                     one a solver may simply not answer, and
                                     anything but [Valid] is read here as no. *)
                                (* compared as strings: an example atom holds
                                     a [Map.Poly], whose comparator is a closure
                                     the runtime reaches, so [Stdlib.( = )] on
                                     one raises rather than answering *)
                                let bare a =
                                  ExAtom.str_of
                                  @@
                                  match a with
                                  | ExAtom.PPApp ((prm, _), papp) ->
                                      ExAtom.canon_key
                                        (ExAtom.PPApp
                                           ( (prm, LogicOld.Formula.mk_true ()),
                                             papp ))
                                  | x -> ExAtom.canon_key x
                                in
                                (* a count for the trace only, and the
                                   canonical keys and their printing are
                                   rebuilt for every pair at every
                                   labeling, so it is taken only when the
                                   trace is on *)
                                if
                                  Atomic.get Debug.enable
                                  && String.(bare head = bare n)
                                then incr renamed);
                              Option.map (matching hp np) ~f:(fun (cond, prm) ->
                                  (* the body, guarded by the condition under
                                     which the head and the decided negative are
                                     the same atom: where that holds the head is
                                     false, so the body must be *)
                                  let guarded =
                                    match body with
                                    | ExAtom.PPApp ((bprm, bcond), bpapp) ->
                                        ExAtom.PPApp
                                          ( ( Map.force_merge bprm prm,
                                              LogicOld.Formula.and_of
                                                [ bcond; cond ] ),
                                            bpapp )
                                    | ExAtom.PApp bpapp ->
                                        ExAtom.PPApp ((prm, cond), bpapp)
                                    | x -> x
                                  in
                                  Debug.print
                                  @@ lazy
                                       (sprintf
                                          "[search_labeling] the head of %s \
                                           meets a decided negative, so its \
                                           body is negative under a guard"
                                          (ExClause.str_of cl));
                                  guarded)))
              | _ -> Set.Poly.empty)
        in
        let neg_par = Set.union neg_par0 derived_neg in
        Debug.print
        @@ lazy
             (sprintf
                "[search_labeling] %d undecided clause(s), %d of the \
                 two-literal shape, %d same-predicate (head, decided negative) \
                 pair(s) tested, %d equal up to a renaming with the guards set \
                 aside, %d body atom(s) derived negative"
                (Set.length undecided) !shaped !tried !renamed
                (Set.length derived_neg));
        Debug.print
        @@ lazy
             (sprintf
                "[search_labeling] conflict by unification: %d positive x %d \
                 negative parametric atom(s)"
                (Set.length pos_par) (Set.length neg_par));
        Set.concat_map
          (Set.Poly.filter_map pos_par ~f:(fun pa ->
               Option.map (parts pa) ~f:(fun x -> (pa, x))))
          ~f:(fun (pos_atom, p) ->
            Set.Poly.filter_map
              (Set.Poly.filter_map neg_par ~f:(fun na ->
                   Option.map (parts na) ~f:(fun x -> (na, x))))
              ~f:(fun (neg_atom, n) ->
                let pv1, a1, c1 = freshen p and pv2, a2, c2 = freshen n in
                if
                  (not (Ident.pvar_equal pv1 pv2))
                  || List.length a1 <> List.length a2
                then None
                else
                  let eqs = List.map2_exn a1 a2 ~f:LogicOld.Formula.eq in
                  let query =
                    LogicOld.Formula.and_of
                      (drop_if_cardinality c1 :: drop_if_cardinality c2 :: eqs)
                  in
                  incr paired;
                  if Z3Smt.Z3interface.may_not_return query then (
                    incr declined;
                    None)
                  else if PCSatCommon.SolveDeadline.expired_strict () then (
                    (* past a strict deadline of the solve this labeling
                       belongs to: the pairs are quadratic in the parametric
                       atoms and each is a solver call, so the rest are not
                       asked; a pair not asked is no conflict, which can only
                       lose a refutation *)
                    incr undecided_pairs;
                    None)
                  else if ExAtom.args_never_meet a1 a2 then (
                    (* the two atoms hold different literals at one position,
                       so the equations are false in every model: the answer
                       the solver would give is [Unsat], and the diagnostic
                       question below, which keeps every equation, would be
                       unsatisfiable too.  On inputs whose examples are mostly
                       ground this is most pairs, and each was a solver call per
                       labeling. *)
                    incr unsat_pairs;
                    None)
                  else
                    match
                      Z3Smt.Z3interface.check_sat ~id
                        ~timeout:
                          (PCSatCommon.SolveDeadline.cap_ms_strict (Some 5000))
                        vs.fenv [ query ]
                    with
                    | `Sat _ ->
                        Debug.print
                        @@ lazy
                             (sprintf
                                "[search_labeling] a positive and a negative \
                                 example of %s meet: %s"
                                (Ident.name_of_pvar pv1)
                                (LogicOld.Formula.str_of query));
                        (* Keep the two atoms that actually met.  Reporting
                           an arbitrary atom of the same predicate instead --
                           which is what this did -- loses the only evidence
                           the refutation has: the witness is then built by
                           filtering the examples for THAT atom, the negative
                           example holds a different one by construction (a
                           different atom is why matching was needed rather
                           than intersection), and the positive is parametric
                           while the filter compares against instantiated
                           atoms, so both example lists come out empty and the
                           checker reports that it was given nothing to
                           compare. *)
                        Some (pos_atom, neg_atom)
                    | `Unsat ->
                        incr unsat_pairs;
                        (* DIAGNOSTIC, no effect on the answer: ask the same
                           question without the negative's guard. Satisfiable
                           there means the two atoms do meet and the guard is
                           what forbids saying so -- a semantic question about
                           discharging a guard, not a matching failure. *)
                        (let bare = LogicOld.Formula.and_of (c1 :: eqs) in
                         (* its only effects are a trace line and the count
                            printed with the trace, so it is asked only when
                            the trace is on: it doubled the solver calls of
                            this search *)
                         if
                           Atomic.get Debug.enable
                           && (not (Z3Smt.Z3interface.may_not_return bare))
                           && not (PCSatCommon.SolveDeadline.expired_strict ())
                         then
                           match
                             Z3Smt.Z3interface.check_sat ~id
                               ~timeout:
                                 (PCSatCommon.SolveDeadline.cap_ms_strict
                                    (Some 5000))
                               vs.fenv [ bare ]
                           with
                           | `Sat _ ->
                               incr guard_only;
                               Debug.print
                               @@ lazy
                                    (sprintf
                                       "[search_labeling] %s: the atoms MEET \
                                        and only the guard blocks it: %s"
                                       (Ident.name_of_pvar pv1)
                                       (LogicOld.Formula.str_of c2))
                           | _ -> ());
                        None
                    | _ ->
                        incr undecided_pairs;
                        None))
    in
    Debug.print
    @@ lazy
         (sprintf
            "[search_labeling] conflict pairs: %d same-predicate, %d declined \
             (query may not return), %d unsatisfiable (%d of them only because \
             of the negative's guard), %d undecided"
            !paired !declined !unsat_pairs !guard_only !undecided_pairs);
    let conflicts =
      (* an example atom carries a guard: it says [cond => P(t̄)]
         ([ExAtom.to_old_formula]), so where the instance falsifies [cond] the
         two sides do not really conflict.  Instantiation can falsify one -- an
         integer parameter is instantiated at [0] whatever the condition says,
         and two examples whose conditions both become [false] instantiate to
         the *same* atom -- and a conflict is a refutation, so the guard is
         checked rather than assumed.  Z3 undecided is not a refutation
         either: treating a give-up as one is how the verdict becomes a wrong
         [unsat]. *)
      Set.filter (Set.inter pos_atms neg_atms) ~f:(fun atm ->
          let _, cond, _ = ExAtom.to_old_formula_and_cond atm in
          LogicOld.Formula.is_true cond
          ||
          match
            (* same question, same place it is answered; and the same safe
               direction -- a conflict is a refutation, so one whose guard
               cannot be asked about is dropped rather than counted *)
            if Z3Smt.Z3interface.may_not_return cond then
              `Unknown "a sort the query may not return on (a binder, or an occurrence)"
            else
              Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 5000) vs.fenv
                [ cond ]
          with
          | `Sat _ -> true
          | ans ->
              Debug.print
              @@ lazy
                   (sprintf
                      "[search_labeling] a conflict on %s is dropped: its \
                       guard %s                        is %s"
                      (ExAtom.str_of atm)
                      (LogicOld.Formula.str_of cond)
                      (match ans with
                      | `Unsat -> "unsatisfiable"
                      | _ -> "undecided"));
              false)
    in
    (* [unification_conflicts] now holds the PAIRS that met.  The propositional
       side below wants a set of atoms, so take the positive of each pair; the
       pair itself is what the witness needs, and is looked up by that atom. *)
    let unification_pair_of =
      Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
      @@ List.map (Set.to_list unification_conflicts) ~f:(fun (p, n) -> (p, n))
    in
    let unification_atoms = Set.Poly.map unification_conflicts ~f:fst in
    (* THE DISCRIMINATING COUNT.  A mechanism that makes examples more general
       is easy to measure where it produces them and that measurement says
       nothing: what decides whether the generality was worth producing is how
       many conflicts it found that comparing atoms for equality could not have
       found.  Those are exactly the ones the unification search contributes and
       the intersection does not, so the difference is taken rather than the
       total -- a unification conflict on two identical atoms is not evidence of
       anything, since the cheap test finds it too. *)
    PCSatCommon.GeneralityMonitor.(
      use Labeling "conflicts-only-by-unification"
        (Set.length (Set.diff unification_atoms conflicts));
      use Labeling "conflicts-by-identical-atoms" (Set.length conflicts));
    let conflicts = Set.union conflicts unification_atoms in
    let senv = PCSP.Problem.senv_of APCSP.problem in
    let examples_with atom exs =
      VersionSpace.witness_examples vs
      @@ Set.filter exs ~f:(fun ex ->
          Set.mem
            (ExClauseSet.exatoms_of_uclauses
            @@ instantiate_examples (Set.Poly.singleton ex))
            atom)
    in
    (* The same search without instantiating first.  A conflict found by
       unification names the atoms as the examples carry them -- parametric,
       with their own [$1], [$2] -- and [instantiate_examples] has already
       replaced those by concrete values, so comparing against the instantiated
       set finds nothing.  Matching the example's own atoms is what the atom
       came from and is what finds it. *)
    let examples_holding atom exs =
      VersionSpace.witness_examples vs
      @@ Set.filter exs ~f:(fun ex ->
          Set.mem
            (ExClauseSet.exatoms_of_uclauses (Set.Poly.singleton ex))
            atom)
    in
    if Fn.non Set.is_empty conflicts then (
      Debug.print @@ lazy (str_of_conflicts conflicts);
      let atom = Set.choose_exn conflicts in
      let positives, negatives =
        match Map.Poly.find unification_pair_of atom with
        | Some neg_atom ->
            (* found by unification: the two sides are different atoms, so each
               list is built from the atom that side actually contributed *)
            (examples_holding atom dpos, examples_holding neg_atom dneg)
        | None -> (examples_with atom dpos, examples_with atom dneg)
      in
      VersionSpace.set_unsat_witness vs
      @@ UnsatWitness.make senv
           (UnsatWitness.Conflict { atom; positives; negatives });
      Ok State.Unsat)
    else
      (* Stage 2 of the labeling redesign, refutation direction only.  The
         propositional query refutes only through a collision of identical
         atoms; this one hands the whole example set to an SMT solver with the
         unknowns as uninterpreted predicates, so it sees the atoms' arguments
         and their guards.  It is asked *before* the propositional search
         because the answer that matters is its [unsat], and that answer is a
         verdict on its own.
         Soundness is one-directional and that is what makes it safe.  The
         query is "does some interpretation of the unknowns and of the theory
         satisfy these examples", which is weaker than what a solution must do
         (an interpretation of the unknowns that works in *every* model of the
         theory), so if even that fails there is no solution and [unsat] is
         justified; [sat] and [unknown] establish nothing and the round goes on
         exactly as before. *)
      let smt_refutes =
        let cls = Set.union dpos @@ Set.union dneg undecided in
        let n = Set.length cls in
        (* Only on a round that made no progress.  The examples only grow, so
           the query grows with them, and a file converging in three hundred
           rounds would pay three hundred increasingly expensive calls for an
           answer the last one could have given -- measured on
           [flip_exit_eq_sat.smt2], which answers in [sat,152] and [sat,285]
           and, asked every round, loses the answer at 200 s altogether.  A
           round that added no example is one the propositional abstraction has
           already failed to refute with exactly this set, which is the only
           place the extra reach can change anything. *)
        let no_progress = n > 0 && n = !prev_example_count in
        prev_example_count := n;
        config.smt_refutation && no_progress
        &&
        let param_senv, phis =
          Set.fold cls ~init:(Map.Poly.empty, []) ~f:(fun (senv, acc) cl ->
              let senv', phi = ExClause.to_old_formula cl in
              (Map.force_merge senv senv', phi :: acc))
        in
        let phi =
          LogicOld.Formula.forall (Map.Poly.to_alist param_senv)
          @@ LogicOld.Formula.and_of phis
        in
        match
          Z3Smt.Z3interface.check_sat ~id ~timeout:(Some 10000) vs.fenv [ phi ]
        with
        | `Unsat ->
            Debug.print
            @@ lazy
                 (sprintf
                    "*** the %d example clauses are unsatisfiable as a \
                     formula:                      refuted"
                    (Set.length cls));
            true
        | _ -> false
      in
      if smt_refutes then (
        VersionSpace.set_unsat_witness vs
        @@ UnsatWitness.make senv
             (UnsatWitness.Labeling
                {
                  positives = VersionSpace.witness_examples vs dpos;
                  negatives = VersionSpace.witness_examples vs dneg;
                  undecided = VersionSpace.witness_examples vs undecided;
                  lemmas = [];
                });
        Ok State.Unsat)
      else
        search_labeling_main iters vs wfpvs dwfpvs nwfpvs parpvs fnpvs pos_atms
          neg_atms undecided_inst
        >>= function
        | [], lemmas ->
            VersionSpace.set_unsat_witness vs
            @@ UnsatWitness.make senv
                 (UnsatWitness.Labeling
                    {
                      positives = VersionSpace.witness_examples vs dpos;
                      negatives = VersionSpace.witness_examples vs dneg;
                      undecided = VersionSpace.witness_examples vs undecided;
                      lemmas = Set.to_list lemmas;
                    });
            Ok State.Unsat
        | pos_neg_list, loop_cls ->
            let _ =
              if true then ()
              else
                (* ToDo: adding determinacy and acyclicity constraints are useless? *)
                let new_undecided = Set.diff loop_cls undecided in
                VersionSpace.add_examples vs
                @@ Set.Poly.map new_undecided ~f:(fun ex ->
                    (ex, Set.Poly.singleton (ClauseGraph.Dummy, false)))
              (*TODO: add sources for new_undecided *)
            in
            let vs' =
              let labeling_list =
                List.map pos_neg_list ~f:(fun (pos, neg, sample_examples) ->
                    let labeling =
                      Set.fold pos ~init:Map.Poly.empty ~f:(fun l atm ->
                          VersionSpace.set_label
                            ~print:
                              (if print_log then Debug.print ~id
                               else fun _ -> ())
                            ~id vs TruthTable.label_pos l
                          @@ ExAtom.normalize_params atm)
                    in
                    let labeling =
                      Set.fold neg ~init:labeling ~f:(fun l atm ->
                          VersionSpace.set_label
                            ~print:
                              (if print_log then Debug.print ~id
                               else fun _ -> ())
                            ~id vs TruthTable.label_neg l
                          @@ ExAtom.normalize_params atm)
                    in
                    (labeling, sample_examples))
              in
              VersionSpace.set_labelings labeling_list vs
            in
            Ok (State.Continue (vs', ()))

  let search_labeling iters vs () =
    try search_labeling_body iters vs ()
    with Sat_solver_unknown ->
      Debug.print
      @@ lazy
           "[search_labeling] the SAT solver gave up (Z3 unknown); the phase \
            reports a timeout";
      Ok State.Timeout

  let unit_propagation vs () =
    Debug.print @@ lazy ">>> unit propagation";
    let dpos, dneg, undecided = VersionSpace.pos_neg_und_examples_of vs in
    let simplify =
      if true (*ToDo*) then Fn.id
      else ExClause.simplify_wfpvs (PCSP.Problem.wfpvs_of APCSP.problem)
    in
    let dpos = Set.Poly.map dpos ~f:simplify in
    let dneg = Set.Poly.map dneg ~f:simplify in
    let undecided =
      Set.Poly.map undecided
        ~f:
          (simplify
          >> ExClause.simplify_totpvs (PCSP.Problem.tot_positions_of APCSP.problem)
          >> fun cl ->
          if not config.fn_totality_drop then cl
          else
            ExClause.simplify_totpvs ~with_positives:true
              (Lazy.force fn_input_positions) cl)
    in
    let res =
      ExClauseSet.unit_propagation
        (Map.key_set @@ PCSP.Problem.senv_of APCSP.problem)
        (Set.Poly.map dpos ~f:(fun ex -> (ex, [ ex ])))
        (Set.Poly.map dneg ~f:(fun ex -> (ex, [ ex ])))
        (Set.Poly.map undecided ~f:(fun ex -> (ex, [ ex ])))
    in
    Debug.print @@ lazy "<<< unit propagation";
    match res with
    | `Unsat conflicts ->
        Debug.print @@ lazy (str_of_conflicts conflicts);
        VersionSpace.set_unsat_witness vs
        @@ UnsatWitness.make
             (PCSP.Problem.senv_of APCSP.problem)
             (UnsatWitness.Propagation
                {
                  conflicts = Set.to_list conflicts;
                  positives = VersionSpace.witness_examples vs dpos;
                  negatives = VersionSpace.witness_examples vs dneg;
                  undecided = VersionSpace.witness_examples vs undecided;
                });
        Ok State.Unsat
    | `Result (dpos', dneg', undecided') ->
        Debug.print
        @@ lazy
             (VersionSpace.str_of_examples
             @@ Set.Poly.
                  (map ~f:fst dpos', map ~f:fst dneg', map ~f:fst undecided'));
        let new_examples =
          Set.Poly.map ~f:(fun (ex, srcs) ->
              ( ex,
                Set.Poly.of_list
                @@ List.map srcs ~f:(fun e -> (ClauseGraph.Example e, true)) ))
          @@ Set.Poly.union_list [ dpos'; dneg'; undecided' ]
        in
        (* only the examples this propagation produced: the result sets also
           contain the inputs, whose derivation is somebody else's *)
        let before = VersionSpace.examples_of vs in
        Set.iter new_examples ~f:(fun (ex, _) ->
            if not (Set.mem before ex) then
              VersionSpace.record_derivation vs ex ~rule:"unit-propagation"
                ~subst:None);
        Ok (State.of_examples vs new_examples)

  let run_phase iters e =
    Debug.print @@ lazy "**** labeler";
    let open State.Monad_infix in
    TruthTable.with_valid_budget
      (if config.truth_table_valid_timeout > 0 then
         Stdlib.Option.some config.truth_table_valid_timeout
       else Stdlib.Option.none)
    @@ fun () ->
    Ok e >>=? unit_propagation >>=? search_labeling iters

  let run_phase iters e =
    if RLCfg.config.enable then (
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy "begin labeler";
        RLConfig.unlock ());
      let tm = Timer.make () in
      let res = run_phase iters e in
      if RLCfg.config.show_elapsed_time then (
        RLConfig.lock ();
        Debug.print_stdout @@ lazy (sprintf "end labeler: %f" (tm ()));
        RLConfig.unlock ());
      res)
    else run_phase iters e
end

let make rl_config config pcsp =
  (module Make
            (struct
              let config = rl_config
            end)
            (struct
              let config = config
            end)
            (struct
              let problem = pcsp
            end) : ClassifierType)
