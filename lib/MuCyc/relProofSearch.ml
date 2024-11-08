open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open Config
open Sequent
open Lemma
open ProofTree

exception PickPvamFailed
exception UnfoldFailed
exception ValidRuleUnknown
exception Unkown

let livept = ref (LivePT.mk_root ())

(** {i Valid Rule} *)
let valid ~print ~config depth defs sequent =
  match config.valid_with_smt_threshold with
  | Some n when depth >= n -> (* Exceed valid_with_smt_threshold *)
    print @@ lazy ":: Resort to Spacer or MuVal...@.";
    let _muclp = Problem.to_muclp defs [sequent] in
    raise ValidRuleUnknown(*ToDo: call Spacer or MuVal*)
  | _ ->
    (* Check premise |- phi1 => [| A1 \in A2 |] /\ phi2 *)
    try
      if Sequent.is_valid ~print ~config sequent then begin
        livept := LivePT.mk_valid !livept;
        print @@ lazy ":: Valid@.";
        Valid sequent
      end else raise ValidRuleUnknown
    with Z3Smt.Z3interface.Unknown -> raise ValidRuleUnknown

let lookup (defs : MuCLP.Pred.t list) (atm, _) =
  let pvar, _sorts, aargs, _ = Atom.let_pvar_app atm in
  match MuCLP.Pred.lookup defs pvar with
  | None -> None
  | Some (Mu, fargs, body) ->
    let tsub = Map.Poly.of_alist_exn @@ List.zip_exn (List.map ~f:fst fargs) aargs in
    let exi_senv =
      Term.pred_to_sort_env_map @@
      MuCLP.Pred.pred_sort_env_map_of_list Map.Poly.empty defs
    in
    Option.return @@ Set.to_list @@
    Set.Poly.map ~f:(fun (ps, ns, phi) ->
        assert (Set.is_empty ns); Set.to_list ps, phi) @@
    Formula.dnf_of exi_senv @@ Formula.subst tsub body
  | Some ((Nu | Fix), _senv, _body) -> failwith "not supported"

(*let remove_frame_pva = ref (Atom.mk_pvar_app (Ident.Pvar "a") [] [])
  let remove_frame_value = ref (Term.mk_fresh_var (Sort.SVar (Ident.Svar "dummy")))
  let apply_options_for_frames pvam (atms, phi) =
  (* Apply options
       -frame-remove-pva "p(h,...)" and
       -frame-remove-value "(frame_remove_value)".
     (If pvam matches p(h,...),
      replace its recursive predicate p(h1,...)
      with    p(newvar,...) /\ h1 = newvar * (frame_remove_value) *)
  let to_be_removed_id (p, _) =
    Stdlib.(Atom.pvar_of !remove_frame_pva = Atom.pvar_of p)
  in
  let (p1, _), p2 = pvam, !remove_frame_pva in
  let pvar1, _, args1, _ = Atom.let_pvar_app p1 in
  let pvar2, _, args2, _ = Atom.let_pvar_app p2 in
  if (* depth = 0 && *)
    Stdlib.(pvar1 = pvar2) && (* Same predicate variables *)
    Stdlib.(List.for_all2 Stdlib.(=) args1 args2) && (* Same args *)
    List.exists ~f:to_be_removed_id atms (* There are recursive predicates *)
  then
    let rec_p, rec_m = List.find_exn ~f:to_be_removed_id atms in
    match Atom.let_pvar_app rec_p with
    | pvar, _, term :: terms, _ ->
      let sort = Term.sort_of term in
      let newvar = Term.mk_fresh_var sort in
      let eq = (*Formula.mk_atom @@ Atom.Heap.mk_eq (Term.Heap.mk_separate newvar !remove_frame_value) term*) Formula.eq newvar term in
      let new_p =
        Atom.mk_pvar_app pvar (sort :: List.map ~f:Term.sort_of terms) (newvar :: terms)
      in
      (new_p, rec_m) :: List.remove_if ~f:to_be_removed_id atms,
      Formula.mk_and eq phi
    | _ -> failwith ""
  else atms, phi*)

(* ToDo: unused *)
let unfold ~print depth defs sequent pvam =
  match lookup defs pvam with
  | None -> raise UnfoldFailed
  | Some atms_phi_list ->
    print @@ lazy (sprintf ":: Unfolded %s@." (Atom.str_of @@ fst pvam));
    List.map atms_phi_list ~f:(fun (atms, phi) ->
        let gatms = List.map atms ~f:Sequent.guard in
        { sequent with
          left_atms = pvam :: sequent.left_atms @ Sequent.ext_guard_list gatms depth;
          left_phi = Evaluator.simplify @@ Formula.mk_and sequent.left_phi phi })
(* ToDo: unused *)
(** {i Induct Rule} add an induction hypothesis to [lemmas], [pvam] is a picked atom *)
let induct unfolded depth defs lemmas sequent pvam =
  let hyp =
    let pv_senv_list, phis =
      List.unzip_map (fst >> Sequent.normalize_atom) @@
      (* Exclude unfolded atoms from hyp *)
      List.filter sequent.left_atms ~f:(Fn.non @@ List.mem ~equal:Stdlib.(=) unfolded)
    in
    let pv_senv, phi = Sequent.normalize_atom (fst pvam) in
    { sequent with
      left_atms =
        List.map pv_senv_list ~f:(uncurry Atom.pvar_app_of_senv >> Sequent.guard);
      left_phi = Formula.and_of (sequent.left_phi :: phi :: phis) }
    |> Lemma.make (Some (pv_senv, depth))
    (*|> Lemma.forall_elim tenv*)
    |> Lemma.normalize
  in
  hyp, (defs, hyp :: lemmas, { sequent with left_atms = pvam :: sequent.left_atms })

(** {i Unfold Rule} @return branched judgements *)
let unfold_and_induct ~print ~config unfolded depth defs lemmas sequent pvam =
  match lookup defs pvam with
  | None -> raise UnfoldFailed
  | Some atms_phi_list ->
    livept := LivePT.mk_induct !livept;
    livept := LivePT.mk_unfold pvam (List.length atms_phi_list) !livept;
    print @@ lazy (sprintf ":: Unfolded %s@." (Atom.str_of @@ fst pvam));
    let hyp =
      let pv_senv_list, phis =
        List.unzip_map (fst >> Sequent.normalize_atom) @@
        (* Exclude unfolded atoms from hyp *)
        List.filter sequent.left_atms ~f:(Fn.non @@ List.mem ~equal:Stdlib.(=) unfolded)
      in
      let pv_senv, phi = Sequent.normalize_atom (fst pvam) in
      { sequent with
        left_atms =
          List.map pv_senv_list ~f:(uncurry Atom.pvar_app_of_senv >> Sequent.guard);
        left_phi = Formula.and_of (sequent.left_phi :: phi :: phis) }
      |> Lemma.make (Some (pv_senv, depth + 1))
      (*|> Lemma.forall_elim tenv*)
      |> if config.normalize_lemma then Lemma.normalize else Fn.id
    in
    let mk_induct_pt pt = Induct (sequent, pvam, hyp, pt) in
    let mk_unfold_pt pts = Unfold (sequent, pvam, pts) in
    let subgoals =
      List.map atms_phi_list ~f:(fun (atms, phi) ->
          let lemmas' =
            match config.induct_threshold with
            | Some n when depth >= n -> lemmas (* Exceed induct_threshold *)
            | _ -> hyp :: lemmas
          in
          let sequent' =
            let gatms, phi = List.map atms ~f:Sequent.guard, phi
            (*apply_options_for_frames pvam (List.map atms ~f:Sequent.guard, phi)*)
            in
            { sequent with
              left_atms = sequent.left_atms @ Sequent.ext_guard_list gatms (depth + 1);
              left_phi = Formula.mk_and sequent.left_phi phi }
          in
          lemmas', sequent')
    in
    mk_induct_pt, mk_unfold_pt, subgoals

let filter_consistent ~print phi sigmas =
  let checked_true  = ref [] in (* Memoize checked equality *)
  let checked_false = ref [] in (* Memoize checked equality *)
  (** Check the consistency of a given substitution sigma (Optimized for speed).
      e.g. Given phi and [(x,t1); (y,t2); (x,t3)], check phi |= t1=t3. *)
  let rec is_consistent = function
    | [] -> true
    | (x, t) :: rest ->
      try
        let t' = List.Assoc.find_exn ~equal:Stdlib.(=) rest x in
        let eq =
          Evaluator.simplify @@
          (*if Type.is_heap ty then Formula.Heap.mk_eq t t'
             else*) Formula.eq t t'
        in
        let eq' =
          Evaluator.simplify @@
          (*if Type.is_heap ty then Formula.Heap.mk_eq t' t
             else*) Formula.eq (List.Assoc.find_exn ~equal:Stdlib.(=) rest x) t
        in
        if List.mem ~equal:Stdlib.(=) !checked_true eq ||
           List.mem ~equal:Stdlib.(=) !checked_true eq' ||
           Formula.is_true eq then
          is_consistent rest
        else if List.mem ~equal:Stdlib.(=) !checked_false eq ||
                List.mem ~equal:Stdlib.(=) !checked_false eq' ||
                Formula.is_false eq then
          false
        else
          match Z3Smt.Z3interface.check_valid ~id:None (FunEnv.mk_empty ()) @@
            Formula.mk_imply phi eq with
          | `Valid ->
            checked_true := eq :: !checked_true;
            print @@ lazy (sprintf "%s is valid@." (Formula.str_of eq));
            is_consistent rest
          | `Invalid _ ->
            checked_false := eq :: !checked_false;
            print @@ lazy (sprintf "%s is invalid@." (Formula.str_of eq));
            false
          | `Unknown _ -> false
          | _ -> failwith "is_consistent"
      with Not_found_s _ -> is_consistent rest
  in
  List.filter ~f:is_consistent sigmas

let rec apply_defs ~print preds_senv (atms, phi) hatm = function
  | [] -> []
  | (batms, bphi) :: rest ->
    let aside_sigmas =
      Sequent.make_sigmas atms (List.map batms ~f:(Sequent.normalize_atom >> fst(*ToDo*)))
    in
    let sub', exists_vars =
      let tmp = Set.Poly.union_list @@ List.map ~f:Atom.tvs_of (hatm :: batms) in
      Set.filter (Formula.term_sort_env_of bphi) ~f:(fst >> Set.mem tmp >> not)
      |> (Set.Poly.filter_map ~f:(fun (x, sort) ->
          if Sort.is_arrow sort then None (* avoid quantification of ufuns *)
          else
            let newx = Ident.mk_fresh_tvar () in
            Some ((x, Term.mk_var newx sort), (newx, sort))))
      |> Set.to_list
      |> List.unzip
    in
    aside_sigmas
    |> Vector.product List.concat
    |> filter_consistent ~print phi
    |> List.map ~f:((@) sub')
    |> (function
        | [] -> apply_defs ~print preds_senv (atms, phi) hatm rest
        | sigmas ->
          try
            let sigma =
              Map.Poly.of_alist_exn @@ List.find_exn sigmas
                ~f:(Map.Poly.of_alist_exn
                    >> Fn.flip Formula.subst bphi
                    >> Formula.exists exists_vars
                    >> (fun phi ->
                        snd @@ Qelim.qelim_old Map.Poly.empty preds_senv @@
                        (Logic.of_old_sort_env_map @@
                         Map.of_set_exn @@ Formula.term_sort_env_of phi, phi))
                    >> Formula.mk_imply phi
                    >> Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ()))
            in
            [Atom.subst sigma hatm](* one such sigma is enough *)
          with Not_found_s _ -> apply_defs ~print preds_senv (atms, phi) hatm rest)

(** {i Fold Rule} @return added_atms if foldable and [] otherwise *)
let fold ~print ~config defs lemmas sequent =
  let folded_seq =
    let preds_senv = Map.of_set_exn @@ MuCLP.Pred.sort_env_of_list defs in
    let added_atms =
      List.filter ~f:(Fn.non @@ List.mem ~equal:Stdlib.(=) @@ sequent.left_atms) @@
      List.concat_map ~f:(fun gatm ->
          (match lookup defs gatm with
           | None -> raise UnfoldFailed
           | Some atms_phi_list ->
             List.map ~f:Sequent.guard @@ List.unique @@
             apply_defs ~print preds_senv
               (List.map ~f:fst @@ sequent.left_atms, sequent.left_phi)
               (fst gatm) atms_phi_list)) @@
      List.unique @@
      ((if config.fold_lemmas then
          (* LHS atoms of user defined lemma (for successful application of the lemmas) *)
          List.concat_map ~f:(fun (lem : Lemma.t) -> lem.sequent.left_atms) @@
          List.filter ~f:Lemma.is_user_defined_lemma lemmas
        else []) @ sequent.right_atms)
    in
    { sequent with
      left_atms = added_atms @ sequent.left_atms;
      left_phi = sequent.left_phi }
  in
  let added_atms =
    List.filter ~f:(Fn.non @@ List.mem ~equal:Stdlib.(=) sequent.left_atms) @@
    folded_seq.left_atms
  in
  let mk_fold_pt =
    if List.is_empty added_atms
    then Fn.id
    else (fun pt ->
        livept := LivePT.mk_fold !livept;
        print @@ lazy
          (sprintf ":: Folded (added %s)@."
             (String.concat_map_list ~sep:"," ~f:(fst >> Atom.str_of) added_atms));
        Fold (sequent, added_atms, pt))
  in
  mk_fold_pt, folded_seq

(** {i Apply Rule} Apply all lemmas and @return new sequent (LHS will be updated) *)
let apply ~print ~config lemmas sequent =
  let applied_seq, applied_ids, applied_lemmas =
    List.rev lemmas |> List.mapi ~f:(fun i lem -> i + 1, lem) |> List.rev
    |> List.fold_left ~init:(sequent, [], [])
      ~f:(fun (sequent, applied_ids, applied_lemmas) (id, lemma) ->
          print @@ lazy (sprintf ":: Applying [%d]@." id);
          if config.enable_apply_threshold && Lemma.is_induction_hypothesis lemma &&
             2 * (List.length lemma.sequent.left_atms + 1) > List.length sequent.left_atms
          then begin
            print @@ lazy ":: Skipping induction hypothesis (enable_apply_threshold)@.";
            sequent, applied_ids, applied_lemmas
          end else
            let pvars1 =
              List.map lemma.sequent.left_atms ~f:(fst >> Sequent.normalize_atom >> fst(*ToDo*))
            in
            let sigmas =
              (* The construction of sigma proves two premises:
                 |- phi1 => [| (sigma g) \in A1 |] and
                 |- phi1 => [| (sigma A1') \subset A1 |] *)
              ((match lemma.guard with
                  | None -> [[[]]]
                  | Some ((pvar, senv), m) ->
                    Sequent.make_sigmas
                      (List.map ~f:fst @@
                       List.filter sequent.left_atms ~f:(fun (_, g) -> Set.mem g m))
                      [pvar, senv]) @
               Sequent.make_sigmas (List.map ~f:fst sequent.left_atms) pvars1)
              |> Vector.product List.concat
              |> filter_consistent ~print sequent.left_phi
            in
            if List.is_empty sigmas then begin
              print @@ lazy ":: Lemma failed (Empty sigma)@.";
              sequent, applied_ids, applied_lemmas
            end else
              let bvs =
                Set.Poly.union_list @@ List.map ~f:Atom.tvs_of @@
                (match lemma.guard with
                 | None -> []
                 | Some ((pvar, senv), _) -> [Atom.pvar_app_of_senv pvar senv]) @
                List.map pvars1 ~f:(uncurry Atom.pvar_app_of_senv)
              in
              (* Try all sigma candidates *)
              List.fold_left sigmas ~init:(sequent, applied_ids, applied_lemmas)
                ~f:(fun (sequent, applied_ids, applied_lemmas) sigma ->
                    let sigma = Map.Poly.of_alist_exn sigma in
                    let sigma' =
                      Map.force_merge sigma @@
                      Map.Poly.map ~f:Term.mk_fresh_var lemma.sequent.eqvars
                    in
                    let newphi =
                      Formula.forall
                        (Set.to_list @@
                         Set.filter ~f:(fst >> Set.mem bvs >> not) @@
                         Formula.term_sort_env_of lemma.sequent.left_phi) @@
                      Formula.mk_or
                        (if config.check_lemma_lhs then(* force the LHS to be checked *)
                           Formula.mk_false ()
                         else
                           Formula.negate (Formula.subst sigma lemma.sequent.left_phi))
                        (Formula.subst sigma' lemma.sequent.right_phi)
                    in
                    if Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ()) @@
                      Evaluator.simplify @@ Formula.mk_imply sequent.left_phi newphi &&
                       List.is_empty lemma.sequent.right_atms
                    then begin
                      print @@ lazy ":: Lemma failed (No Additional Information)@.";
                      sequent, applied_ids, applied_lemmas
                    end else if
                      Fn.non List.is_empty lemma.sequent.right_atms &&
                      not @@ Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ()) @@
                      Formula.mk_imply sequent.left_phi @@
                      Formula.subst sigma lemma.sequent.left_phi
                    then begin
                      print @@ lazy ":: Lemma failed (Must prove LHS)@.";
                      sequent, applied_ids, applied_lemmas
                    end else begin
                      print @@ lazy ":: Lemma success@.";
                      { sequent with
                        left_atms =
                          sequent.left_atms @
                          Sequent.map_atm ~f:(Atom.subst sigma') lemma.sequent.right_atms;
                        left_phi =
                          Evaluator.simplify @@ Formula.mk_and sequent.left_phi newphi },
                      id :: applied_ids,
                      lemma :: applied_lemmas
                    end))
  in
  let added_atms =
    List.filter applied_seq.left_atms
      ~f:(Fn.non @@ List.mem ~equal:Stdlib.(=) sequent.left_atms)
  in
  let mk_apply_pt =
    if Sequent.equal_light sequent applied_seq
    then Fn.id
    else begin
      print @@ lazy
        (Format.asprintf ":: Applied %a@." (Sequent.pr ~wo_guard:false) applied_seq);
      livept := LivePT.mk_apply (Set.Poly.of_list applied_ids) !livept;
      (fun pt -> Apply (sequent, applied_lemmas, pt))
    end
  in
  mk_apply_pt, applied_seq, added_atms

(* proof search strategy *)
let rec strategy unfolded depth ~print ~config defs lemmas sequent =
  print @@ lazy (Format.asprintf ":: Proof tree overview:@.   %a@." LivePT.pr !livept);
  let init_seq = Sequent.simplify sequent in
  print @@ lazy (Format.asprintf "%a" ProofTree.pr_judgement (defs, lemmas, init_seq));
  try valid ~print ~config depth defs init_seq
  with ValidRuleUnknown ->
    print @@ lazy ":: Unknown@.";
    let mk_apply_pt, applied_seq, added_atms = apply ~print ~config lemmas init_seq in
    (* 1. exclude from induct. hyp. 2. skip unfold *)
    mk_apply_pt @@
    try
      if Sequent.equal_light init_seq applied_seq then raise ValidRuleUnknown
      else valid ~print ~config depth defs applied_seq
    with ValidRuleUnknown ->
      print @@ lazy ":: Unknown (after Apply rule)@.";
      let mk_fold_pt, folded_seq = fold ~print ~config defs lemmas applied_seq in
      mk_fold_pt @@
      try
        if Sequent.equal_light applied_seq folded_seq then raise ValidRuleUnknown
        else valid ~print ~config depth defs folded_seq
      with ValidRuleUnknown ->
        print @@ lazy ":: Unknown (after Fold rule)@.";
        try
          let rec select_pvam pvams =
            if config.ask_pred_app_to_unfold then begin
              print @@ lazy ":: Select unfolded atom:@.";
              List.iteri pvams ~f:(fun i (a, _) ->
                  print @@ lazy (sprintf "@,%d: %s" i (Atom.str_of a)));
              print @@ lazy "@,:: Unfold No(auto=-1): @.";
              let num =
                try Out_channel.(flush stdout); Int.of_string In_channel.(input_line_exn stdin)
                with Failure _ -> -1
              in
              if num < 0 then select_pvam pvams else List.nth_exn pvams num
            end else
              match pvams with
              | [] ->
                print @@ lazy ":: (Warning) Pvam selection failed@.";
                raise PickPvamFailed
              | pvam :: rest ->
                if List.mem ~equal:Stdlib.(=) unfolded pvam then select_pvam rest else pvam
          in
          let pvam = select_pvam folded_seq.left_atms in
          let unfolded' = pvam :: unfolded @ added_atms in
          let mk_induct_pt, mk_unfold_pt, subgoals =
            unfold_and_induct ~print ~config unfolded' depth defs lemmas folded_seq pvam
          in
          mk_induct_pt @@ mk_unfold_pt @@
          List.rev @@ fst @@ List.fold_left subgoals ~init:([], false)
            ~f:(fun (lst, is_invalid) (lems, seq) ->
                if is_invalid then ProofTree.Abort seq :: lst, is_invalid
                else
                  let pt = strategy unfolded' (depth + 1) ~print ~config defs lems seq in
                  pt :: lst, Fn.non ProofTree.is_valid pt)
        with
        | PickPvamFailed ->
          if List.is_empty @@ folded_seq.right_atms then begin
            livept := LivePT.mk_invalid !livept;
            print @@ lazy ":: Invalid@.";
            match Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ()) @@
              [Formula.negate @@ Formula.mk_imply folded_seq.left_phi folded_seq.right_phi] with
            | `Sat model -> InValid (folded_seq, model)
            | `Unsat -> raise Unkown(*ToDo*)
            | _ -> raise Unkown
          end else raise Unkown

let solve ~print ~config pcsp_solver problem =
  try
    let rec solve_aux problem =
      livept := LivePT.mk_root () (* initialization *);
      print @@ lazy
        (Format.asprintf "@.@[<v 3>:: Target Problem:@;%a@]@." Problem.pr problem);
      match problem with
      | Problem.{ env = env; lemmas = lems; defs = defs; goals = (seq, tout, is_hard) :: rest } ->
        let tout = match tout with None -> 0(*ignore timeout*) | Some tout -> tout in
        Timer.enable_timeout tout Fn.id ignore
          (fun () ->
             [strategy [] 0 ~print ~config defs (Set.to_list lems) @@
              (*Sequent.forall_elim env*) seq, is_hard])
          (fun _ -> function
             | [pt, is_hard] ->
               let new_lems =
                 if is_valid pt then Set.add lems (Lemma.of_sequent seq)
                 else lems
               in
               (pt, is_hard) :: solve_aux (Problem.make env new_lems defs rest)
             | _ -> failwith "RelProofSearch.solve")
          (fun _ -> function
             | Timer.Timeout -> solve_aux (Problem.make env lems defs rest)
             | e -> raise e)
      | Problem.{ goals = []; _ } -> [] (* No sequents (Valid) *)
    in
    let open Or_error.Monad_infix in
    pcsp_solver () >>= fun (module PCSPSolver : PCSPSolver.Solver.SolverType) ->
    let prooftrees = solve_aux problem in
    Ok (MuCLP.Problem.
          (if List.for_all prooftrees ~f:(fun (pt, is_hard) -> is_hard && is_valid pt)
           then Valid else Invalid),
        prooftrees)
  with Unkown -> Ok (MuCLP.Problem.Unknown, [])
