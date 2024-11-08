open Core
open Config
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open Effect.Shallow

let args_of penv pvar = List.Assoc.find_exn ~equal:Stdlib.( = ) penv pvar

let str_of_head = function
  | None -> "root"
  | Some pvar -> Ident.name_of_pvar pvar

let str_of_head_with_args penv =
  Option.str_of "root" (fun pvar ->
      Atom.str_of
      @@ Atom.mk_pvar_app pvar
           (List.map ~f:snd @@ args_of penv pvar)
           (Term.of_sort_env @@ args_of penv pvar))

let def_of penv defs pvar =
  match MuCLP.Pred.lookup defs pvar with
  | Some (Mu, args, body) ->
      Formula.rename (tvar_map_of_sort_env_list args (args_of penv pvar)) body
  | _ -> failwith "ProofSearch.def_of"

let seq_map_of penv (problem : Problem.t) =
  let exi_senv =
    Term.pred_to_sort_env_map @@ Map.Poly.of_alist_exn
    @@ List.map penv ~f:(fun (pvar, args) -> (pvar, List.map ~f:snd args))
  in
  Map.Poly.of_alist_exn
  @@ ( None,
       List.sort_by (fun seq -> List.length seq.Sequent.left_atms)
       @@ List.map problem.goals ~f:(fst3 >> Sequent.normalize_body) )
     :: List.map penv ~f:(fun (pvar, _) ->
            ( Some pvar,
              List.sort_by (fun seq -> List.length seq.Sequent.left_atms)
              @@ List.map ~f:Sequent.normalize_body
              @@ Set.to_list
              @@ Sequent.of_formula exi_senv
              @@ Formula.mk_imply
                   (def_of penv problem.defs pvar)
                   (Formula.mk_atom @@ Atom.pvar_app_of_senv pvar
                  @@ args_of penv pvar) ))

let formula_of seq_map pvar_opt =
  Formula.or_of
  @@ List.map ~f:(fun seq ->
         Formula.negate
         @@ Sequent.to_formula { seq with Sequent.right_atms = [] })
  @@ Map.Poly.find_exn seq_map pvar_opt

let convert_model res_dc senv model =
  let model =
    let model =
      if res_dc then remove_dontcare model
      else
        List.filter_map model ~f:(function
          | (_, _), None -> None
          | (x, _), Some t -> Some (x, t))
    in
    try Map.Poly.of_alist_exn model
    with _ ->
      (* z3 may return a model like  [x |-> 1, x |-> 0]*)
      List.classify (fun x y -> Stdlib.(fst x = fst y)) model
      |> List.map ~f:List.hd_exn |> Map.Poly.of_alist_exn
  in
  Set.fold senv ~init:model ~f:(fun model (x, sort) ->
      match Map.Poly.find model x with
      | Some _ -> model
      | None -> Map.Poly.add_exn model ~key:x ~data:(Term.mk_dummy sort))

let qelim ~config phi =
  let res =
    (*Normalizer.normalize @@*)
    Evaluator.simplify
    @@ Z3Smt.Z3interface.qelim ~id:None ~fenv:(LogicOld.get_fenv ()) phi
  in
  assert ((not config.check_validity) || Formula.is_quantifier_free res);
  res

let qelim_except ~config ?(exists = true) args phi =
  let res = qelim ~config @@ snd @@ Formula.quantify_except ~exists args phi in
  assert (
    (not config.check_validity) || Set.is_subset (Formula.fvs_of res) ~of_:args);
  res

let mk_fresh_pvar idx pvar =
  (*Ident.mk_fresh_pvar ()*)
  Ident.Pvar (string_of_int idx ^ "$$$" ^ Ident.name_of_pvar pvar)

let rec expand penv (problem : Problem.t) pvs level =
  let pvren =
    Map.Poly.of_alist_exn
    @@ List.mapi penv ~f:(fun i (pvar, _) -> (pvar, List.nth_exn pvs i))
  in
  if level = 0 then
    ( Set.Poly.of_list
      @@ List.map problem.goals ~f:(fun (seq, _, _) ->
             let phi = Formula.rename_pvars pvren @@ Sequent.to_formula seq in
             (Map.of_set_exn @@ Formula.term_sort_env_of phi, phi)),
      Map.Poly.empty )
  else if level > 0 then
    let level' = level - 1 in
    let pvs' = List.map penv ~f:(fst >> mk_fresh_pvar level') in
    let chcs, pvmap = expand penv problem pvs' level' in
    ( Set.union chcs @@ Set.Poly.of_list
      @@ List.mapi penv ~f:(fun i (pvar, _) ->
             match MuCLP.Pred.lookup problem.defs pvar with
             | Some (Predicate.Mu, args, body) ->
                 let senv, body =
                   Formula.rm_quant ~forall:true
                   @@ Formula.aconv_tvar
                   @@ Formula.mk_imply (Formula.rename_pvars pvren body)
                   @@ Formula.mk_atom
                   @@ Atom.pvar_app_of_senv (List.nth_exn pvs' i) args
                 in
                 ( Map.force_merge (Map.of_set_exn senv)
                     (Map.Poly.of_alist_exn args),
                   body )
             | _ -> failwith "[ProofSearch.expand]"),
      Map.force_merge pvmap
        (Map.Poly.of_alist_exn
        @@ List.mapi pvs' ~f:(fun j pvar -> ((level', j), pvar))) )
  else failwith "[ProofSearch.expand] level >= 0 is required"

let solve ~config penv solve_chc problem (trace1, trace2) =
  assert (Fn.non List.is_empty trace2);
  let chcs, pvmap =
    let level = List.length trace2 - 1 in
    let pvs = List.map penv ~f:(fst >> mk_fresh_pvar level) in
    let chcs, pvmap = expand penv problem pvs level in
    ( chcs,
      Map.force_merge pvmap @@ Map.Poly.of_alist_exn
      @@ List.mapi pvs ~f:(fun j pvar -> ((level, j), pvar)) )
  in
  let chcs =
    let params =
      PCSP.Params.make @@ Logic.of_old_sort_env_map @@ Term.pred_to_sort_env_map
      @@ Map.Poly.of_alist_exn
      @@ List.map (Map.Poly.to_alist pvmap) ~f:(fun ((_, j), pvar) ->
             (pvar, List.map ~f:snd @@ snd @@ List.nth_exn penv j))
    in
    PCSP.Problem.of_old_formulas ~params chcs
  in
  let bpvs =
    Set.Poly.of_list @@ List.map ~f:Ident.pvar_to_tvar @@ Map.Poly.data pvmap
  in
  match solve_chc ~bpvs chcs with
  | Result.Ok (PCSP.Problem.Sat sol, _) ->
      (*print_endline @@ PCSP.Problem.str_of_sol_with_witness @@ PCSP.Problem.Sat sol;*)
      let psub = snd @@ CandSolOld.of_subst sol in
      Option.return
      @@ ( ( trace1,
             List.mapi trace2 ~f:(fun i frame ->
                 List.mapi (List.zip_exn penv frame)
                   ~f:(fun j ((_, params0), _) ->
                     let pvar = Map.Poly.find_exn pvmap (i, j) in
                     let params, phi =
                       match Map.Poly.find (Map.of_set_exn psub) pvar with
                       | Some res -> res
                       | None ->
                           (params0, Formula.mk_false () (*any solution is OK*))
                     in
                     qelim ~config (*Normalizer.normalize @@*)
                     @@ Evaluator.simplify
                     @@ Formula.rename
                          (tvar_map_of_sort_env_list params params0)
                          phi)) ),
           Map.Poly.empty )
  | Result.Ok (PCSP.Problem.Unsat _, _) -> None
  | Result.Ok (PCSP.Problem.Unknown, _) ->
      failwith ("CHC solver returned unknown:\n" ^ PCSP.Problem.str_of chcs)
  | _ -> failwith "ProofSearch.solve"

let interpolate ~config solve_chc args phi1 phi2 =
  let name = "interp" in
  let pvapp = Formula.mk_atom @@ Atom.pvar_app_of_senv (Ident.Pvar name) args in
  let chcs =
    let params =
      PCSP.Params.make
      @@ Map.Poly.singleton (Ident.Tvar name)
      @@ Logic.Sort.mk_fun
      @@ List.map args ~f:(snd >> Logic.ExtTerm.of_old_sort)
      @ [ Logic.BoolTerm.SBool ]
    in
    let senv = Map.Poly.of_alist_exn args in
    let senv1 =
      Map.force_merge senv @@ Map.of_set_exn @@ Formula.term_sort_env_of phi1
    in
    let senv2 =
      Map.force_merge senv @@ Map.of_set_exn @@ Formula.term_sort_env_of phi2
    in
    (*assert (Set.is_subset (Set.inter (Map.Poly.key_set senv1) (Map.Poly.key_set senv2)) ~of_:(Map.Poly.key_set senv));*)
    PCSP.Problem.of_old_formulas ~params
    @@ Set.Poly.of_list
         [
           (senv1, Formula.mk_imply phi1 pvapp);
           (senv2, Formula.mk_imply pvapp phi2);
         ]
  in
  let bpvs = Set.Poly.singleton (Ident.Tvar name) in
  match solve_chc ~bpvs chcs with
  | Result.Ok (PCSP.Problem.Sat sol, _) ->
      let psub = Map.of_set_exn @@ snd @@ CandSolOld.of_subst sol in
      Option.return @@ Evaluator.simplify @@ Formula.subst_preds psub pvapp
  | Result.Ok (PCSP.Problem.Unsat _, _) -> None
  | Result.Ok (PCSP.Problem.Unknown, _) ->
      if config.backup_for_interp then
        let env =
          Set.diff
            (Formula.term_sort_env_of phi2)
            (Formula.term_sort_env_of phi1)
        in
        Option.return @@ Evaluator.simplify @@ qelim ~config
        @@ Formula.mk_forall_if_bounded (Set.to_list env) phi2
      else
        failwith
        @@ sprintf "CHC solver returned unknown for %s and %s"
             (Formula.str_of phi1) (Formula.str_of phi2)
  (* phi1 and phi2 should be quantifier-free *)
  | _ -> failwith "ProofSearch.interpolate"

let get_mbp ~config ~print model0 eliminated0 phi0 =
  if Set.is_empty eliminated0 then phi0
  else (
    print @@ lazy ("\nMBP input: " ^ Formula.str_of phi0);
    print
    @@ lazy
         ("eliminated: "
         ^ str_of_sort_env_list Term.str_of_sort
         @@ Set.to_list eliminated0);
    print
    @@ lazy
         ("model: "
         ^ String.concat_map_list ~sep:", " (Map.Poly.to_alist model0)
               ~f:(function Ident.Tvar tvar, value ->
               sprintf "%s |-> %s" tvar (Term.str_of value)));
    let senv = Set.to_list @@ Formula.sort_env_of phi0 in
    let bounds, phi =
      Formula.split_quantifiers @@ Evaluator.simplify
      @@ LogicOld.Formula.elim_let
      @@ Normalizer.normalize_let ~rename:true
      @@ Normalizer.normalize @@ Formula.rm_div_mod @@ Normalizer.normalize
      @@ Formula.elim_ite
      @@ Formula.mk_exists_if_bounded senv phi0
    in
    print @@ lazy ("preprocessed input: " ^ Formula.str_of phi);
    let eliminated =
      Set.Poly.union_list
      @@ eliminated0
         :: List.map bounds ~f:(function
              | Formula.Exists, senv' ->
                  Set.(diff (Poly.of_list senv') (Set.Poly.of_list senv))
              | _ -> failwith "Universal quantifies are not supported")
    in
    (*print @@ lazy ("eliminated': " ^ str_of_sort_env_list Term.str_of_sort @@ Set.to_list eliminated);*)
    let model =
      let phi = Formula.subst model0 phi in
      if Set.is_empty @@ Formula.fvs_of phi then model0
      else
        match
          Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ()) [ phi ]
        with
        | `Sat sub ->
            Map.force_merge model0 @@ Map.Poly.of_alist_exn
            @@ List.map sub ~f:(function
                 | (x, _s), Some t -> (x, t)
                 | (x, s), None -> (x, Term.mk_dummy s))
        | `Unsat -> failwith "Unreachable here"
        | _ -> failwith "Z3 timeout/unknown"
    in
    (*print @@ lazy ("model': " ^
                     String.concat_map_list ~sep:", " (Map.Poly.to_alist model) ~f:(function
                           (Ident.Tvar tvar, value) -> sprintf "%s |-> %s" tvar (Term.str_of value)));*)
    let atoms =
      let tatoms, fatoms = Formula.atoms_of ~nrec:true phi in
      Set.concat_map
        ~f:(Mbp.normalize_mbp model >> Set.Poly.map ~f:(Mbp.sign model))
      @@ Set.union tatoms fatoms
    in
    let res =
      let rec preprocess atoms =
        Set.concat_map atoms ~f:(function
          | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _)
            when T_irb.is_sint_sreal t1 ->
              Set.Poly.singleton
              @@
              if
                Value.compare Z.Compare.( > ) Q.( > )
                  (Evaluator.eval_term @@ Term.subst model t1)
                  (Evaluator.eval_term @@ Term.subst model t2)
              then
                Normalizer.normalize_atom
                @@
                if T_int.is_sint t1 then T_int.mk_gt t1 t2
                else T_real.mk_rgt t1 t2
              else
                Normalizer.normalize_atom
                @@
                if T_int.is_sint t1 then T_int.mk_gt t2 t1
                else T_real.mk_rgt t2 t1
          | Atom.App
              ( Predicate.Psym T_bool.Eq,
                [
                  (Term.Var (_, s, _) as tx);
                  Term.FunApp (T_bool.Formula phi, [], _);
                ],
                _ )
            when Term.is_bool_sort s
                 && Set.exists ~f:(snd >> Term.is_bool_sort >> not)
                    @@ Formula.term_sort_env_of phi ->
              if
                Value.is_true @@ Evaluator.eval_term
                @@ Map.Poly.find_exn model (fst @@ fst @@ Term.let_var tx)
              then
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model phi)
                @@ T_bool.mk_eq tx @@ T_bool.mk_true ()
              else
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model @@ Evaluator.simplify_neg phi)
                @@ T_bool.mk_eq tx @@ T_bool.mk_false ()
          | Atom.App
              ( Predicate.Psym T_bool.Eq,
                [
                  Term.FunApp (T_bool.Formula phi, [], _);
                  (Term.Var (_, s, _) as tx);
                ],
                _ )
            when Term.is_bool_sort s
                 && Set.exists ~f:(snd >> Term.is_bool_sort >> not)
                    @@ Formula.term_sort_env_of phi ->
              if
                Value.is_true @@ Evaluator.eval_term
                @@ Map.Poly.find_exn model (fst @@ fst @@ Term.let_var tx)
              then
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model phi)
                @@ T_bool.mk_eq tx @@ T_bool.mk_true ()
              else
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model @@ Evaluator.simplify_neg phi)
                @@ T_bool.mk_eq tx @@ T_bool.mk_false ()
          | Atom.App
              ( Predicate.Psym T_bool.Neq,
                [
                  (Term.Var (_, s, _) as tx);
                  Term.FunApp (T_bool.Formula phi, [], _);
                ],
                _ )
            when Term.is_bool_sort s
                 && Set.exists ~f:(snd >> Term.is_bool_sort >> not)
                    @@ Formula.term_sort_env_of phi ->
              if
                Value.is_true @@ Evaluator.eval_term
                @@ Map.Poly.find_exn model (fst @@ fst @@ Term.let_var tx)
              then
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model @@ Evaluator.simplify_neg phi)
                @@ T_bool.mk_eq tx @@ T_bool.mk_true ()
              else
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model phi)
                @@ T_bool.mk_eq tx @@ T_bool.mk_false ()
          | Atom.App
              ( Predicate.Psym T_bool.Neq,
                [
                  Term.FunApp (T_bool.Formula phi, [], _);
                  (Term.Var (_, s, _) as tx);
                ],
                _ )
            when Term.is_bool_sort s
                 && Set.exists ~f:(snd >> Term.is_bool_sort >> not)
                    @@ Formula.term_sort_env_of phi ->
              if
                Value.is_true @@ Evaluator.eval_term
                @@ Map.Poly.find_exn model (fst @@ fst @@ Term.let_var tx)
              then
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model @@ Evaluator.simplify_neg phi)
                @@ T_bool.mk_eq tx @@ T_bool.mk_true ()
              else
                Set.add
                  (preprocess
                  @@ Set.Poly.map ~f:Normalizer.normalize_atom
                  @@ Mbp.atoms_of model phi)
                @@ T_bool.mk_eq tx @@ T_bool.mk_false ()
          | atm -> Set.Poly.singleton atm)
      in
      let is_looping =
        let prev = ref ("", Set.Poly.empty) in
        fun x atoms ->
          if Set.equal (snd !prev) atoms then
            String.(Ident.name_of_tvar x = fst !prev)
          else (
            prev := (Ident.name_of_tvar x, atoms);
            false)
      in
      Evaluator.simplify @@ Normalizer.normalize @@ Formula.and_of
      @@ Set.to_list
      @@ Set.Poly.map ~f:Formula.mk_atom
      @@
      let rec loop eliminated atoms =
        match eliminated with
        | [] -> atoms
        | (x, s) :: eliminated' -> (
            (*Out_channel.output_char stdout '.';*)
            (*print @@ lazy ("eliminating " ^ Ident.name_of_tvar x ^ " in\n" ^ String.concat_map_set ~sep:"\n" ~f:Atom.str_of atoms);*)
            let atoms1, atoms2 =
              Set.partition_tf atoms ~f:(fun atm -> Set.mem (Atom.fvs_of atm) x)
            in
            try
              try
                loop eliminated' @@ Set.union atoms2
                @@ (match s with
                   | T_bool.SBool -> Mbp.Boolean.model_based_projection
                   | T_int.SInt -> Mbp.LIA.model_based_projection
                   | T_real.SReal -> Mbp.LRA.model_based_projection
                   | _ -> failwith "not supported")
                     model x atoms1
              with Mbp.NotNormalized ->
                if is_looping x atoms then failwith "loop detected"
                else loop (eliminated' @ [ (x, s) ]) atoms
            with Failure _ as e ->
              if config.check_validity then raise e
              else
                loop eliminated' @@ Set.union atoms2
                @@
                let sub = Map.Poly.singleton x (Map.Poly.find_exn model x) in
                Set.concat_map atoms1
                  ~f:(Atom.subst sub >> Mbp.normalize_mbp model))
      in
      loop (Set.to_list eliminated) @@ preprocess atoms
    in
    let res = Evaluator.simplify res in
    print @@ lazy ("MBP output: " ^ Formula.str_of res);
    if config.check_validity then (
      if Fn.non Formula.is_quantifier_free phi0 then failwith "wrong MBP @1";
      if Fn.non Evaluator.eval (Formula.subst model0 res) then
        failwith "wrong MBP @2";
      if
        Fn.non Set.is_empty
        @@ Set.inter (Formula.fvs_of res) (Set.Poly.map ~f:fst eliminated0)
      then failwith "wrong MBP @3";
      let vc =
        Formula.mk_imply res
        @@ Formula.mk_exists_if_bounded (Set.to_list eliminated0) phi0
      in
      match
        Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ())
          [ Formula.negate vc ]
      with
      | `Sat _ -> failwith "wrong MBP @4"
      | _ -> res)
    else res)

type frame = Formula.t list
type trace = frame list * frame list
type query = Formula.t
type cex = Formula.t
type induct = (Ident.pvar, Formula.t Set.Poly.t) Map.Poly.t
type gcexs = (Ident.pvar, Formula.t Set.Poly.t) Map.Poly.t

type state = {
  trace : trace;
  query : query;
  cex_acc : cex;
  induct : induct;
  gcexs : gcexs;
}

type result_yld = trace * cex * induct * gcexs
type result_ret = trace * cex * induct * gcexs
type _ Effect.t += Yield : state * cex -> state Effect.t

type status =
  | Init
  | Paused of (trace * query * gcexs -> (result_yld, result_ret) Either.t)
  | Done

let empty_trace = ([], [])

let next_trace_of = function
  | _, [] -> failwith "[next_trace_of]"
  | trace1, frame :: trace2 -> (frame :: trace1, trace2)

let prev_trace_of = function
  | [], _ -> failwith "[prev_trace_of]"
  | frame :: trace1, trace2 -> (trace1, frame :: trace2)

let psub_of penv = function
  | _, [] ->
      Map.Poly.of_alist_exn
      @@ List.map penv ~f:(fun (pvar, args) ->
             (pvar, (args, Formula.mk_false () (*ToDo*))))
  | _, frame :: _ ->
      Map.Poly.of_alist_exn
      @@ List.map2_exn penv frame ~f:(fun (pvar, args) phi ->
             (pvar, (args, phi)))

let get_frame = List.hd_exn

let get_formula penv state pvar =
  let frame = get_frame @@ snd @@ state.trace in
  List.find_map_exn (List.zip_exn penv frame) ~f:(fun ((pvar', _), phi) ->
      if Stdlib.(pvar = pvar') then Some phi else None)

let set_formula_to_frame penv frame pvar phi =
  List.map2_exn penv frame ~f:(fun (pvar', _) phi' ->
      if Stdlib.(pvar = pvar') then phi else phi')

let add_formula_to_frame penv frame pvar phi =
  List.map2_exn penv frame ~f:(fun (pvar', _) phi' ->
      if Stdlib.(pvar = pvar') then Formula.and_of [ phi; phi' ] else phi')

let set_formula penv state pvar phi =
  match state.trace with
  | _, [] -> failwith "[set_formula]"
  | trace1, frame :: trace2 ->
      {
        state with
        trace = (trace1, set_formula_to_frame penv frame pvar phi :: trace2);
      }

let add_formula penv state pvar phi =
  set_formula penv state pvar
    (Formula.and_of [ get_formula penv state pvar; phi ])

let propagate_formula penv (trace1, trace2) pvar phi =
  ( trace1,
    List.map trace2 ~f:(fun frame -> add_formula_to_frame penv frame pvar phi)
  )

let empty_induct = Map.Poly.empty

let merge_induct =
  Map.Poly.merge ~f:(fun ~key:_ -> function
    | `Left s | `Right s -> Some s | `Both (s1, s2) -> Some (Set.union s1 s2))

let apply_induct_rule ~print seq_map penv trace induct =
  if Map.Poly.is_empty induct then (trace, induct)
  else
    let cfg = [ ("model", "true") ] in
    let ctx = Z3.mk_context cfg in
    let solver = Z3.Solver.mk_solver ctx None in
    let z3dtenv =
      Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (LogicOld.get_dtenv ())
    in
    let z3fenv =
      Z3Smt.Z3interface.z3_fenv_of ~id:None ctx [] [] (LogicOld.get_fenv ())
        z3dtenv
    in
    let convert =
      Z3Smt.Z3interface.of_formula_with_z3fenv ~id:None ctx [] [] z3fenv z3dtenv
    in
    let psub = psub_of penv @@ next_trace_of trace in
    let induct =
      Map.Poly.filter_mapi induct ~f:(fun ~key:pvar ~data ->
          let left = formula_of seq_map (Some pvar) in
          Z3Smt.Z3interface.z3_solver_reset solver;
          Z3Smt.Z3interface.z3_solver_add solver
            [ convert @@ Formula.subst_preds psub left ];
          let phis =
            Set.filter data ~f:(fun right ->
                Z3.Solver.push solver;
                Z3Smt.Z3interface.z3_solver_add solver
                  [ convert @@ Evaluator.simplify_neg right ];
                match Z3.Solver.check solver [] with
                | Z3.Solver.UNSATISFIABLE ->
                    Z3.Solver.pop solver 1;
                    true
                | _ -> (
                    (*let psub = Map.Poly.singleton pvar (args_of penv pvar, right) in*)
                    let psub =
                      Map.Poly.mapi psub ~f:(fun ~key ~data:(senv, phi) ->
                          if Ident.pvar_equal key pvar then (senv, right)
                          else (senv, phi))
                    in
                    Z3Smt.Z3interface.z3_solver_add solver
                      [ convert @@ Formula.subst_preds psub left ];
                    match Z3.Solver.check solver [] with
                    | Z3.Solver.UNSATISFIABLE ->
                        Z3.Solver.pop solver 1;
                        true
                    | _ ->
                        Z3.Solver.pop solver 1;
                        false))
          in
          if Set.is_empty phis then None else Some phis)
    in
    ( (match trace with
      | _, [] -> failwith "apply_induct_rule"
      | trace1, frame :: trace2 ->
          ( trace1,
            List.map2_exn penv frame ~f:(fun (pvar, _) phi ->
                match Map.Poly.find induct pvar with
                | None -> phi
                | Some phis ->
                    print
                    @@ lazy
                         ("inductive facts for " ^ Ident.name_of_pvar pvar
                        ^ ": "
                         ^ String.concat_map_set ~sep:" /\\ " ~f:Formula.str_of
                             phis);
                    Formula.and_of @@ (phi :: Set.to_list phis))
            :: trace2 )),
      induct )

let add_to_induct induct pvar phis =
  Map.Poly.set induct ~key:pvar
    ~data:
      (match Map.Poly.find induct pvar with
      | Some phis' -> Set.union phis' phis
      | None -> phis)

let empty_gcexs = Map.Poly.empty

let add_to_gcexs gcexs pvar cexs =
  Map.Poly.set gcexs ~key:pvar
    ~data:
      (match Map.Poly.find gcexs pvar with
      | Some cexs' -> Set.union cexs' cexs
      | None -> cexs)

let get_gcex state pvar =
  Evaluator.simplify @@ Formula.or_of @@ Set.to_list
  @@ Map.Poly.find_exn state.gcexs pvar

let pr_trace ppf (penv, (trace : trace)) =
  let pr_pred ppf ((pvar, args), phi) =
    Format.fprintf ppf "%s(%s) = %s" (Ident.name_of_pvar pvar)
      (String.concat_map_list ~sep:"," args ~f:(fst >> Ident.name_of_tvar))
      (Formula.str_of phi)
  in
  List.pr
    (fun ppf frame -> List.pr pr_pred ", " ppf (List.zip_exn penv frame))
    "@," ppf
  @@ snd trace

let generate ~config ~print
    (iterator : trace * query * gcexs -> (state * cex -> state) -> result_ret) =
  let yield (s, c) = Effect.perform (Yield (s, c)) in
  let status = ref Init in
  let rec handler =
    {
      retc =
        (fun result ->
          status := Done;
          Second result);
      exnc = (fun e -> raise e);
      effc =
        (fun (type b) (eff : b Effect.t) ->
          match eff with
          | Yield (state, cex) ->
              Some
                (fun (k : (b, result_ret) continuation) ->
                  match config.refinement_strategy with
                  | Refine (_, Or) ->
                      (* pass the control to the callee immediately with the state updated with the counterexample *)
                      let state' =
                        {
                          state with
                          cex_acc = Formula.or_of [ state.cex_acc; cex ];
                        }
                      in
                      continue_with k state' handler
                  | Refine (_, Return _) ->
                      (* pass the counterexample to the caller by discarding the delimited continuation of the callee *)
                      status := Done;
                      Second (state.trace, cex, state.induct, state.gcexs)
                  | Refine (_, Yield (_, share_trace_among_coroutines)) ->
                      (* pass the counterexample to the caller after saving the delimited continuation of the callee *)
                      status :=
                        Paused
                          (fun (trace_yield, query_yield, gcexs) ->
                            let state' =
                              {
                                trace =
                                  (if share_trace_among_coroutines then
                                     trace_yield
                                   else state.trace);
                                query = query_yield;
                                cex_acc = state.cex_acc;
                                induct = empty_induct;
                                gcexs;
                              }
                            in
                            print
                            @@ lazy
                                 (sprintf
                                    "  resume with the refined query: %s\n"
                                    (Formula.str_of query_yield));
                            continue_with k state' handler);
                      First (state.trace, cex, state.induct, state.gcexs)
                  | Solve -> assert false)
          | _ -> None);
    }
  in
  fun (trace, query, gcexs) ->
    match !status with
    | Init ->
        continue_with
          (fiber (Fn.flip iterator yield))
          (trace, query, gcexs) handler
    | Paused k -> k (trace, query, gcexs)
    | Done -> failwith "[generate] already done"

let psub_right_of penv pvar_opt current_state =
  match pvar_opt with
  | None -> Map.Poly.empty
  | Some pvar -> Map.Poly.singleton pvar (args_of penv pvar, current_state.query)

let find_countermodel penv pvar_opt seq cexs_left_phis atms_right state =
  let cond =
    let left =
      let psub = psub_of penv @@ next_trace_of state.trace in
      Formula.and_of
      @@ (seq.Sequent.left_phi :: cexs_left_phis)
      @ List.map atms_right ~f:(Atom.subst_preds psub)
    in
    let right =
      let psub_right = psub_right_of penv pvar_opt state in
      Formula.or_of
        [ (Sequent.subst_preds_right psub_right seq).right_phi; state.cex_acc ]
    in
    Evaluator.simplify_neg @@ Formula.mk_imply left right
  in
  (*print @@ lazy (Format.asprintf "seq: %a" (Sequent.pr ~wo_guard:true) seq);
    print @@ lazy (sprintf "cond: %s" (Formula.str_of cond));*)
  (cond, Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ()) [ cond ])

let cex_of_countermodel ~config ~print penv seq cexs_left_phis cond model pvar
    args = function
  | QE ->
      let cex = qelim_except ~config ~exists:true args cond in
      print
      @@ lazy
           (sprintf "      a counterexample for %s by QE: %s"
              (Ident.name_of_pvar pvar) (Formula.str_of cex));
      (cex, true)
  | Model ->
      let senv = Formula.term_sort_env_of cond in
      let model' = convert_model false senv model in
      let cex =
        Formula.and_of
        @@ List.filter_map (args_of penv pvar) ~f:(fun (x, s) ->
               match Map.Poly.find model' x with
               | None -> None
               | Some t -> Some (Formula.eq (Term.mk_var x s) t))
      in
      print
      @@ lazy
           (sprintf "      a counterexample for %s from the model: %s"
              (Ident.name_of_pvar pvar) (Formula.str_of cex));
      (cex, false)
  | MBP _ ->
      let senv = Formula.term_sort_env_of cond in
      let model' = convert_model true senv model in
      let non_arg = Set.mem args >> not in
      let cex =
        try
          get_mbp ~config ~print model' (Set.filter senv ~f:(fst >> non_arg))
          @@ Evaluator.simplify_neg
          @@ Formula.mk_imply
               (Formula.and_of @@ (seq.Sequent.left_phi :: cexs_left_phis))
               (Formula.mk_false ())
        with e ->
          if config.backup_for_mbp then
            (* qelim_except ~config ~exists:true args cond *)
            let model' = convert_model false senv model in
            Formula.and_of
            @@ List.filter_map (args_of penv pvar) ~f:(fun (x, s) ->
                   match Map.Poly.find model' x with
                   | None -> None
                   | Some t -> Some (Formula.eq (Term.mk_var x s) t))
          else raise e
      in
      print
      @@ lazy
           (sprintf "      a counterexample for %s by MBP: %s"
              (Ident.name_of_pvar pvar) (Formula.str_of cex));
      (cex, false)

let rec yield_all_cexs ~config ~print seq_map penv pvar_opt yield seq cexs_left
    state : state =
  let cexs_left_phis =
    List.map cexs_left ~f:(function
      | First (pvar, ftoa) -> Formula.rename ftoa @@ get_gcex state pvar
      | Second cex -> cex)
  in
  match find_countermodel penv pvar_opt seq cexs_left_phis [] state with
  | _cond, `Unsat ->
      print @@ lazy "      no more countermodel";
      state
  | cond, `Sat model -> (
      print
      @@ lazy
           (sprintf "      found a countermodel %s"
              (LogicOld.str_of_model model));
      match pvar_opt with
      | None ->
          print
          @@ lazy (sprintf "      a counterexample for a goal clause: true");
          yield (state, Formula.mk_true () (*ToDo*))
      | Some pvar -> (
          let args = Set.Poly.of_list @@ List.map ~f:fst @@ args_of penv pvar in
          match config.refinement_strategy with
          | Refine (cex_typ, _) ->
              let state =
                let trace, induct =
                  match config.induction with
                  | Some (Config.Normal _) ->
                      apply_induct_rule ~print seq_map penv state.trace
                        state.induct
                  | _ -> (state.trace, state.induct)
                in
                { state with trace; induct }
              in
              let cex, all =
                cex_of_countermodel ~config ~print penv seq cexs_left_phis cond
                  model pvar args cex_typ
              in
              (* [cex] should be satisfiable *)
              yield (state, cex)
              |>
              if all then Fn.id
              else
                yield_all_cexs ~config ~print seq_map penv pvar_opt yield seq
                  cexs_left
          | Solve -> assert false))
  | cond, _ ->
      failwith
      @@ sprintf "Z3 timeout/unknown in model enumeration for: %s"
           (Formula.str_of cond)

let query_of_countermodel ~config ~print penv pvar_opt seq cexs_left
    cexs_left_phis aargs aargs_set atof atms_right state_saved_inv state_saved
    state (senv, model) =
  let non_arg = Set.mem aargs_set >> not in
  match config.refinement_strategy with
  | Refine (QE, _) ->
      print @@ lazy "      a query by QE";
      let ub =
        let psub = psub_of penv @@ next_trace_of state.trace in
        let psub_right = psub_right_of penv pvar_opt state in
        Evaluator.simplify
        @@ Formula.mk_imply
             (Formula.and_of
             @@ (seq.Sequent.left_phi :: cexs_left_phis)
             @ List.map atms_right ~f:(Atom.subst_preds psub))
             (Sequent.subst_preds_right psub_right seq).right_phi
      in
      Formula.rename atof @@ qelim_except ~config ~exists:false aargs_set ub
  | Refine (Model, _) ->
      print @@ lazy "      a query from the countermodel";
      let model' = convert_model false senv model in
      Evaluator.simplify_neg @@ Formula.rename atof @@ Formula.and_of
      @@ List.filter_map aargs ~f:(fun (x, s) ->
             match Map.Poly.find model' x with
             | None -> None
             | Some t -> Some (Formula.eq (Term.mk_var x s) t))
  | Refine (MBP use_saved (* use an invariant state for image finiteness *), _)
    ->
      print
      @@ lazy
           ("      a query by MBP"
           ^
           match use_saved with
           | 0 -> ""
           | 1 -> " using a saved state"
           | 2 -> " using a saved state that is a loop invariant"
           | _ -> failwith "not supported");
      let ub =
        let state =
          match use_saved with
          | 0 -> state
          | 1 -> state_saved
          | 2 -> state_saved_inv
          | _ -> failwith "not supported"
        in
        let cexs_left_phis =
          if use_saved = 0 then cexs_left_phis
          else
            List.map cexs_left ~f:(function
              | First (pvar, ftoa) -> Formula.rename ftoa @@ get_gcex state pvar
              | Second cex -> cex)
        in
        let psub = psub_of penv @@ next_trace_of state.trace in
        let psub_right = psub_right_of penv pvar_opt state in
        Evaluator.simplify
        @@ Formula.mk_imply
             (Formula.and_of
             @@ (seq.left_phi :: cexs_left_phis)
             @ List.map atms_right ~f:(Atom.subst_preds psub))
             (Sequent.subst_preds_right psub_right seq).right_phi
      in
      let mbp =
        let model = convert_model true senv model in
        let ub = Evaluator.simplify_neg ub in
        try
          get_mbp ~config ~print model (Set.filter senv ~f:(fst >> non_arg)) ub
        with e ->
          if config.backup_for_mbp then
            (*qelim_except ~config ~exists:true aargs ub*)
            Evaluator.simplify_neg @@ Formula.rename atof
            @@ Formula.subst
                 (Map.Poly.filter_keys model ~f:non_arg)
                 seq.left_phi
          else raise e
      in
      (*print @@ lazy ("      ub: " ^ Formula.str_of ub);
        print @@ lazy ("      senv: " ^ str_of_sort_env_list Term.str_of_sort @@ Set.to_list @@ Set.filter senv ~f:(fst >> non_arg));*)
      print @@ lazy ("      MBP: " ^ Formula.str_of mbp);
      Formula.rename atof @@ Evaluator.simplify_neg mbp
  | _ -> assert false

let weaken_query ~config ~print solve_chc penv pvar_opt seq cexs_left cex_f
    (pvar, aargs, fargs, atof, _ftoa) atms_right next_query state =
  let right =
    let cexs_left_phis =
      List.map cexs_left ~f:(function
        | First (pvar, ftoa) -> Formula.rename ftoa @@ get_gcex state pvar
        | Second cex -> cex)
    in
    let psub = psub_of penv @@ next_trace_of state.trace in
    let psub_right = psub_right_of penv pvar_opt state in
    Formula.rename atof @@ snd
    @@ Formula.refresh_except aargs
    @@ Evaluator.simplify
    @@ Formula.mk_imply
         (Formula.and_of
         @@ (seq.Sequent.left_phi :: cexs_left_phis)
         @ List.map atms_right ~f:(Atom.subst_preds psub))
         (Sequent.subst_preds_right psub_right seq).right_phi
  in
  if Formula.is_true @@ Evaluator.simplify right then (
    (* for maximal conservativity *)
    print @@ lazy "        query is weakened to true";
    (Formula.mk_true (), state))
  else
    match config.refinement_strategy with
    | Refine (_, Yield (true, _)) -> (
        print
        @@ lazy
             (sprintf "        query weakening by interpolating %s => %s"
                (Formula.str_of cex_f) (Formula.str_of right));
        match interpolate ~config solve_chc fargs cex_f right with
        | Some interp ->
            let interp = qelim ~config interp in
            print
            @@ lazy
                 (sprintf "        interpolant for %s: %s"
                    (Ident.name_of_pvar pvar) (Formula.str_of interp));
            ( Normalizer.normalize @@ Evaluator.simplify
              @@ Formula.or_of [ next_query; interp ],
              state )
        | None ->
            failwith
            @@ sprintf
                 "[ProofSearch.refine] interpolant for %s and %s not found"
                 (Formula.str_of cex_f) (Formula.str_of right))
    | _ ->
        let next_query' =
          Normalizer.normalize @@ Evaluator.simplify
          @@ Formula.or_of [ next_query; cex_f ]
        in
        print
        @@ lazy
             (sprintf "        weakened query for %s: %s" (str_of_head pvar_opt)
                (Formula.str_of next_query'));
        (next_query', state)

let resolve_query ~config ~print solve_chc penv pvar_opt seq refine
    refine_clause cexs_left pvar aargs fargs atof ftoa atms_right query0 state0
    =
  print @@ lazy (sprintf "      begin query for %s" (Ident.name_of_pvar pvar));
  let next_cex =
    generate ~config ~print (fun (trace, query, gcexs) ->
        refine (Some pvar)
          {
            trace;
            query;
            cex_acc = Formula.mk_false ();
            induct = empty_induct;
            gcexs;
          })
  in
  let rec each_cex updated (next_query, state1) =
    (*print @@ lazy (sprintf "        current query: %s" (Formula.str_of next_query));*)
    match next_cex (next_trace_of state1.trace, next_query, state1.gcexs) with
    | Second (trace, cex_f, induct, gcexs) ->
        (* counterexample enumeration is completed or a counterexample is returned *)
        let cex_a = Formula.rename ftoa cex_f in
        print
        @@ lazy
             (sprintf "\n      end query for %s with a counterexample: %s"
                (Ident.name_of_pvar pvar) (Formula.str_of cex_f));
        let state2 =
          {
            state1 with
            trace = prev_trace_of trace;
            induct = merge_induct state1.induct induct;
            gcexs = add_to_gcexs gcexs pvar (Set.Poly.singleton cex_f);
          }
        in
        (*print @@ lazy (Format.asprintf "refined trace: %a" pr_trace (penv, state2.trace));*)
        ( cex_f,
          let updated', state3 =
            if Formula.is_false cex_f then (false, state2)
            else
              let cexs_left =
                (match config.counterexample_sharing with
                | None -> Second cex_a
                | Some _ -> First (pvar, ftoa))
                :: cexs_left
              in
              refine_clause cexs_left atms_right state2
          in
          ( updated || updated',
            if config.query_reuse then
              (* share the successfull query with the current frame *)
              let next_cex =
                generate ~config ~print (fun (trace, query, gcexs) ->
                    refine (Some pvar)
                      {
                        trace;
                        query;
                        cex_acc = Formula.mk_false ();
                        induct = empty_induct;
                        gcexs;
                      })
              in
              let rec loop state4 next_query =
                let trace =
                  match config.refinement_strategy with
                  | Refine (_, Yield (_, share_trace_among_coroutines))
                    when share_trace_among_coroutines ->
                      state4.trace
                  | _ -> state3.trace
                in
                match next_cex (trace, next_query, state4.gcexs) with
                | Second (trace, _cex_f, _induct, _gcexs) ->
                    { state3 with trace }
                | First (trace, cex_f, induct, gcexs) ->
                    loop
                      {
                        state4 with
                        trace;
                        induct = merge_induct state4.induct induct;
                        gcexs =
                          add_to_gcexs gcexs pvar (Set.Poly.singleton cex_f);
                      }
                    @@ Normalizer.normalize @@ Evaluator.simplify
                    @@ Formula.or_of [ next_query; cex_f ]
              in
              loop state3 query0
            else state3 ) )
    | First (trace, cex_f, induct, gcexs) ->
        let cex_a = Formula.rename ftoa cex_f in
        print
        @@ lazy
             (sprintf "\n  yield with the counterexample from %s: %s"
                (Ident.name_of_pvar pvar) (Formula.str_of cex_a));
        let state2 =
          {
            state1 with
            trace = prev_trace_of trace;
            induct = merge_induct state1.induct induct;
            gcexs = add_to_gcexs gcexs pvar (Set.Poly.singleton cex_f);
          }
        in
        let updated', state3 =
          let cexs_left =
            (match config.counterexample_sharing with
            | None -> Second cex_a
            | Some _ -> First (pvar, ftoa))
            :: cexs_left
          in
          refine_clause cexs_left atms_right state2
        in
        state3
        |> weaken_query ~config ~print solve_chc penv pvar_opt seq cexs_left
             cex_f
             (pvar, aargs, fargs, atof, ftoa)
             atms_right next_query
        |> each_cex (updated || updated')
  in
  each_cex false (query0, state0)

let refine_atom ~config ~print solve_chc penv pvar_opt seq refine refine_clause
    cexs_left atm atms_right (state0 : state) =
  let pvar, aargs, fargs, atof, ftoa =
    let pvar, _, aargs, _ = Atom.let_pvar_app atm in
    let aargs =
      (* [aargs] are assumed to be distinct variables *)
      List.map aargs ~f:(Term.let_var >> fst)
    in
    let fargs = args_of penv pvar in
    ( pvar,
      aargs,
      fargs,
      tvar_map_of_sort_env_list aargs fargs,
      tvar_map_of_sort_env_list fargs aargs )
  in
  let aargs_set = Set.Poly.of_list @@ List.map ~f:fst aargs in
  let rec each_countermodel updated local_cex_acc state0_5 state1 =
    let cexs_left_phis =
      List.map cexs_left ~f:(function
        | First (pvar, ftoa) -> Formula.rename ftoa @@ get_gcex state1 pvar
        | Second cex -> cex)
    in
    match
      find_countermodel penv pvar_opt seq cexs_left_phis (atm :: atms_right)
        state1
    with
    | _cond, `Unsat ->
        print @@ lazy "      no more countermodel";
        (updated, state1)
    | cond, `Sat model ->
        let senv = Formula.term_sort_env_of cond in
        print
        @@ lazy
             (sprintf "      found a countermodel %s"
                (LogicOld.str_of_model model));
        let next_query =
          let next_query =
            query_of_countermodel ~config ~print penv pvar_opt seq cexs_left
              cexs_left_phis aargs aargs_set atof atms_right state0 state0_5
              state1 (senv, model)
          in
          match config.refinement_strategy with
          | Refine (_, Return true) ->
              Formula.or_of [ next_query; local_cex_acc ]
          | _ -> next_query
        in
        let cex, (updated, state2) =
          resolve_query ~config ~print solve_chc penv pvar_opt seq refine
            refine_clause cexs_left pvar aargs_set fargs atof ftoa atms_right
            next_query state1
        in
        print @@ lazy "      countermodel resolved\n";
        let local_cex_acc' =
          match config.refinement_strategy with
          | Refine (_, Return true) -> Formula.or_of [ local_cex_acc; cex ]
          | _ -> local_cex_acc
        in
        let state0_5' = if updated then state2 else state0_5 in
        each_countermodel true local_cex_acc' state0_5' state2
    | cond, `Unknown reason ->
        failwith
        @@ sprintf "Z3 unknown (%s) in countermodel generation for: %s" reason
             (Formula.str_of cond)
    | cond, `Timeout ->
        failwith
        @@ sprintf "Z3 timeout in countermodel generation for: %s"
             (Formula.str_of cond)
  in
  each_countermodel false (Formula.mk_false ()) state0 state0

let rec refine_clause ~config ~print solve_chc seq_map penv pvar_opt yield seq
    refine cexs_left atms_right (state0 : state) =
  match atms_right with
  | [] ->
      (* enumerate new counterexamples *)
      print
      @@ lazy
           (sprintf
              "    no more atom for refinement and so enumerate and yield all \
               counterexamples for %s if any"
              (str_of_head pvar_opt));
      let cexs_left =
        List.map cexs_left ~f:(fun cex ->
            match (cex, config.counterexample_sharing) with
            | First (pvar, ftoa), Some (Config.Global true (* use saved *)) ->
                Second (Formula.rename ftoa @@ get_gcex state0 pvar)
            | cex, _ -> cex)
      in
      ( false,
        yield_all_cexs ~config ~print seq_map penv pvar_opt yield seq cexs_left
          state0 )
  | atm :: atms_right' ->
      print
      @@ lazy (sprintf "    begin refinement for atom: %s" (Atom.str_of atm));
      let res =
        let refine_clause =
          refine_clause ~config ~print solve_chc seq_map penv pvar_opt yield seq
            refine
        in
        refine_atom ~config ~print solve_chc penv pvar_opt seq refine
          refine_clause cexs_left atm atms_right' state0
      in
      print @@ lazy (sprintf "    end refinement for atom");
      res

let rec refine ~config ~print solve_chc seq_map penv pvar_opt (state0 : state)
    (yield : state * cex -> state) : result_ret =
  print
  @@ lazy
       (sprintf "\nquery for %s:\n%s"
          (str_of_head_with_args penv pvar_opt)
          (Formula.str_of state0.query));
  (*print @@ lazy (Format.asprintf "trace: %a" pr_trace (penv, state0.trace));*)
  if List.is_empty @@ snd @@ state0.trace then (
    print @@ lazy "returned immediately (frame not available)";
    (state0.trace, state0.cex_acc, state0.induct, state0.gcexs))
  else if
    match pvar_opt with
    | None -> false
    | Some pvar -> (
        let cond =
          Evaluator.simplify_neg
          @@ Formula.mk_imply (get_formula penv state0 pvar) state0.query
        in
        (*print @@ lazy (sprintf "cond: %s" (Formula.str_of cond));*)
        match
          Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ()) [ cond ]
        with
        | `Unsat -> true
        | _ -> false)
  then (
    print @@ lazy "returned immediately (refinement not required)";
    (state0.trace, state0.cex_acc, state0.induct, state0.gcexs))
  else
    let state2 =
      Map.Poly.find_exn seq_map pvar_opt
      |> List.fold_left ~init:state0 ~f:(fun state1 (seq : Sequent.t) ->
             (* for each clause *)
             let seq =
               {
                 seq with
                 left_phi =
                   snd
                   @@ Formula.rm_quant ~forall:false
                   @@ Formula.aconv_tvar seq.left_phi;
               }
             in
             print
             @@ lazy
                  (sprintf "  begin refinement for clause: %s"
                     (Formula.str_of @@ Sequent.to_formula seq));
             let _updated, state2 =
               let refine = refine ~config ~print solve_chc seq_map penv in
               refine_clause ~config ~print solve_chc seq_map penv pvar_opt
                 yield seq refine []
                 (List.map ~f:fst seq.left_atms)
                 state1
             in
             print @@ lazy (sprintf "  end refinement for clause");
             state2)
    in
    (* refinement of the current frame*)
    match pvar_opt with
    | None ->
        print @@ lazy ("done query for " ^ str_of_head pvar_opt);
        (*print @@ lazy (Format.asprintf "trace: %a" pr_trace (penv, state2.trace));*)
        (state2.trace, state2.cex_acc, state2.induct, state2.gcexs)
    | Some pvar ->
        if Formula.is_true @@ Evaluator.simplify state2.query then (
          (* ToDo: reachable? *)
          (* for maximal conservativity *)
          print @@ lazy "  no refinement required";
          (state2.trace, state2.cex_acc, state2.induct, state2.gcexs))
        else
          let interp =
            let left =
              Evaluator.simplify
              @@ Formula.subst_preds (psub_of penv @@ next_trace_of state2.trace)
              @@ snd
              @@ Formula.rm_quant ~forall:false
              @@ Formula.aconv_tvar
              @@ formula_of seq_map (Some pvar)
            in
            let right =
              let query = Formula.or_of [ state2.query; state2.cex_acc ] in
              Evaluator.simplify
              @@ Formula.and_of [ get_formula penv state2 pvar; query ]
            in
            print
            @@ lazy
                 (sprintf "  interpolating %s => %s" (Formula.str_of left)
                    (Formula.str_of right));
            match
              interpolate ~config solve_chc (args_of penv pvar) left right
            with
            | Some interp ->
                let interp = qelim ~config interp in
                print
                @@ lazy (sprintf "  interpolant: %s" (Formula.str_of interp));
                print
                @@ lazy (sprintf "done query for %s" (str_of_head pvar_opt));
                interp
            | None -> failwith "[ProofSearch.refine] interpolant not found"
          in
          let state3 = set_formula penv state2 pvar interp in
          let state4 =
            if config.monotone_trace then
              {
                state3 with
                trace =
                  prev_trace_of
                  @@ propagate_formula penv
                       (next_trace_of state3.trace)
                       pvar interp;
              }
            else state3
          in
          let trace, induct =
            match config.induction with
            | Some (Config.Normal _) ->
                apply_induct_rule ~print seq_map penv state4.trace state4.induct
            | _ -> (state4.trace, state4.induct)
          in
          (*print @@ lazy (Format.asprintf "trace: %a" pr_trace (penv, trace));*)
          ( trace,
            state4.cex_acc,
            (match config.induction with
            | Some (Config.Normal disj) ->
                add_to_induct induct pvar
                @@ (if disj then Set.concat_map ~f:Formula.disjuncts_of
                    else Fn.id)
                @@ Formula.conjuncts_of interp
            | _ -> induct),
            state4.gcexs )

let extend_trace ~config penv (trace1, trace2) =
  assert (List.is_empty trace1);
  ( trace1,
    if config.top_down_search then
      trace2 @ [ List.map penv ~f:(fun _ -> Formula.mk_false ()) ]
    else List.map penv ~f:(fun _ -> Formula.mk_true ()) :: trace2 )

let drop_frame (trace1, trace2) = (trace1, List.tl_exn trace2)

let refine ~config ~print penv solve_chc seq_map problem (trace : trace) =
  match config.refinement_strategy with
  | Solve ->
      (* [config.top_down_search] doesn't matter *)
      solve ~config penv solve_chc problem trace
  | Refine (_cex_typ, _com_typ) -> (
      if config.top_down_search then failwith "not implemented"
      else
        let next =
          generate ~config ~print (fun (trace, query, gcexs) ->
              refine ~config ~print solve_chc seq_map penv None
                {
                  trace;
                  query;
                  cex_acc = Formula.mk_false ();
                  induct = empty_induct;
                  gcexs;
                })
        in
        match
          next
            ( extend_trace ~config penv trace (* for goal clause *),
              Formula.mk_false (),
              empty_gcexs )
        with
        | First (_trace, _cex, _induct, _gcexs) -> (*UNSAT*) None (*ToDo*)
        | Second (trace, cex, induct, _gcexs) ->
            if Formula.is_false cex then (*SAT*)
              Some (drop_frame trace, induct)
            else (*UNSAT*) None (*ToDo*))

let rec is_covered_aux penv convert pre solvers = function
  | [] -> None
  | frame :: trace ->
      let frame =
        List.map2_exn penv frame ~f:(fun (_, _args) phi ->
            (*snd @@ quantify_except ~exists:true (Set.Poly.of_list @@ List.map ~f:fst args)*)
            phi)
      in
      if
        List.for_all2_exn solvers frame ~f:(fun solver phi ->
            Z3.Solver.push solver;
            Z3Smt.Z3interface.z3_solver_add solver
              [ convert @@ Formula.negate phi ];
            let res = Z3.Solver.check solver [] in
            Z3.Solver.pop solver 1;
            match res with Z3.Solver.UNSATISFIABLE -> true | _ -> false)
      then
        Some
          (List.map2_exn penv pre ~f:(fun (pvar, args) phi ->
               (pvar, (args, phi))))
      else (
        List.iter2_exn solvers frame ~f:(fun solver phi ->
            Z3Smt.Z3interface.z3_solver_add solver [ convert phi ]);
        is_covered_aux penv convert
          (List.map2_exn pre frame ~f:Formula.mk_and)
          solvers trace)

let is_covered ~print penv =
  let cfg = [ ("model", "true") ] in
  let ctx = Z3.mk_context cfg in
  let solvers = List.map penv ~f:(fun _ -> Z3.Solver.mk_solver ctx None) in
  let z3dtenv =
    Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (LogicOld.get_dtenv ())
  in
  let z3fenv =
    Z3Smt.Z3interface.z3_fenv_of ~id:None ctx [] [] (LogicOld.get_fenv ())
      z3dtenv
  in
  let convert =
    Z3Smt.Z3interface.of_formula_with_z3fenv ~id:None ctx [] [] z3fenv z3dtenv
  in
  fun (trace : trace) ->
    print @@ lazy "begin coverage check";
    match trace with
    | _, [] | _, [ _ ] ->
        print @@ lazy "end coverage check";
        None
    | _, frame :: trace ->
        List.iter2_exn solvers frame ~f:(fun solver phi ->
            Z3Smt.Z3interface.z3_solver_reset solver;
            Z3Smt.Z3interface.z3_solver_add solver [ convert phi ]);
        let res = is_covered_aux penv convert frame solvers trace in
        print @@ lazy "end coverage check";
        res

let rec search ~config ~print solve_chc penv is_covered seq_map problem trace
    induct =
  let trace, induct =
    let trace' = extend_trace ~config penv trace in
    match config.induction with
    | None -> (trace', induct)
    | Some (Config.Normal _) ->
        assert (not config.top_down_search);
        apply_induct_rule ~print seq_map penv trace' induct
    | Some (Config.Light disj) ->
        assert (not config.top_down_search);
        if List.is_empty @@ snd trace then (trace', induct)
        else
          let linduct =
            Map.Poly.of_alist_exn
            @@ List.map2_exn penv
                 (get_frame @@ snd trace)
                 ~f:(fun (pvar, _args) phi ->
                   ( pvar,
                     (if disj then Set.concat_map ~f:Formula.disjuncts_of
                      else Fn.id)
                     @@ Formula.conjuncts_of phi ))
          in
          (fst @@ apply_induct_rule ~print seq_map penv trace' linduct, induct)
  in
  (* Map.Poly.iteri induct ~f:(fun ~key ~data ->
      print_endline @@ "induct for " ^ Ident.name_of_pvar key ^ ": "
      ^ String.concat_map_set data ~sep:", " ~f:Formula.str_of);
  *)
  match refine ~config ~print penv solve_chc seq_map problem trace with
  | None -> (MuCLP.Problem.Invalid, [])
  | Some (trace', induct') -> (
      print @@ lazy (Format.asprintf "Trace: @[<v>%a@]" pr_trace (penv, trace'));
      print @@ lazy "";
      let induct'' =
        match config.induction with
        | Some (Config.Normal _) -> merge_induct induct induct'
        | _ -> induct
      in
      match is_covered ~print trace' with
      | Some sol ->
          if config.check_validity then
            let vc =
              Formula.subst_preds (Map.Poly.of_alist_exn sol)
              @@ Problem.to_formula problem.defs
                   (List.map ~f:fst3 problem.goals)
            in
            match
              Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ())
                [ Formula.negate vc ]
            with
            | `Unsat -> (MuCLP.Problem.Valid, [])
            | _ ->
                (* bug of [solve_chc]? *)
                if false then (
                  print @@ lazy "Trace: N/A";
                  print @@ lazy "";
                  search ~config ~print solve_chc penv is_covered seq_map
                    problem trace' induct'')
                else failwith "The solution found is not valid"
          else (MuCLP.Problem.Valid, [])
      | None ->
          search ~config ~print solve_chc penv is_covered seq_map problem trace'
            induct'')

let solve ~config ~print pcsp_solver problem =
  let open Or_error.Monad_infix in
  pcsp_solver () >>= fun (module PCSPSolver : PCSPSolver.Solver.SolverType) ->
  print @@ lazy (Format.asprintf "Problem: %a" Problem.pr problem);
  assert (Set.is_empty problem.Problem.lemmas);
  let penv =
    List.map problem.Problem.defs ~f:(fun p ->
        (MuCLP.Pred.pvar_of p, MuCLP.Pred.args_of p))
  in
  let seq_map = seq_map_of penv problem in
  if config.top_down_search then print @@ lazy "Start top-down proof search"
  else print @@ lazy "Start bottom-up proof search";
  Or_error.return
  @@
  if List.is_empty problem.Problem.goals then (MuCLP.Problem.Valid, [])
  else
    search ~config ~print
      (fun ~bpvs arg ->
        PCSPSolver.reset ();
        PCSPSolver.solve ~bpvs arg)
      penv (is_covered penv) seq_map problem empty_trace empty_induct
