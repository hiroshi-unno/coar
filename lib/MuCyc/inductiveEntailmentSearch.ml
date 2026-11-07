(* Horn-clause entailment by induction: the proof search of Hiroshi Unno, Sho
   Torii and Hiroki Sakamoto, "Automating Induction for Solving Horn Clauses",
   CAV 2017 (doi:10.1007/978-3-319-63390-9_30).  A sequent [A~, phi |- psi]
   over predicates defined by least fixpoints is closed by the rules Valid,
   Apply (use an induction hypothesis), Fold, and Unfold together with Induct
   (record the sequent as a hypothesis guarded on the unfolded atom).  Selected
   by [proof_search: Relational]. *)

open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open Config
open Sequent
open EntailmentLemma
open EntailmentProofTree

exception PickPvamFailed
exception UnfoldFailed
exception ValidRuleUnknown
exception Unkown

let livept = ref (LivePT.mk_root ())

(* [open_exists phi]: [phi] with every existential quantifier that is reached
   through conjunctions and disjunctions only removed, its variables renamed to
   fresh ones.  Precondition: none.  Guarantee: [exists y~. open_exists phi]
   is equivalent to [phi], where [y~] are the fresh variables introduced
   (an existential under [/\] or [\/] commutes outward once its variables are
   fresh).  So on the left of a sequent, where free variables are implicitly
   universal over the whole sequent, [open_exists phi] may replace [phi].
   A quantifier under a negation, an implication or a universal is left in
   place. *)
let rec open_exists phi =
  match phi with
  | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
      Formula.mk_binop op (open_exists p) (open_exists q)
  | Formula.Bind (Formula.Exists, senv, body, _) ->
      let ren =
        Map.Poly.of_alist_reduce ~f:(fun x _ -> x)
        @@ List.map senv ~f:(fun (x, _) -> (x, Ident.mk_fresh_tvar ()))
      in
      open_exists (Formula.rename ren body)
  | _ -> phi

(* [lookup defs (atm, _)]: the cases of [atm]'s least-fixpoint definition,
   one [(atoms, phi)] per disjunct of the body's DNF, the formal parameters
   replaced by [atm]'s arguments; [None] when [atm]'s predicate has no
   definition.  The body's existentials (variables local to a clause body,
   which a CHC-to-muCLP translation binds around the atoms) are opened with
   variables fresh for every call ([open_exists]), so two unfoldings of one
   definition never share a local variable and the result has no quantifier
   around a predicate atom, which the DNF cannot take.  Every caller puts
   the cases on the left of a sequent (Unfold) or quantifies the variables
   not matched existentially (Fold), which is where an opened existential
   means what it meant.  Raises [UnfoldFailed] on a greatest-fixpoint
   definition, which the procedure does not handle. *)
let lookup (defs : MuCLP.Pred.t list) (atm, _) =
  let pvar, _sorts, aargs, _ = Atom.let_pvar_app atm in
  match MuCLP.Pred.lookup defs pvar with
  | None -> None
  | Some (Mu, fargs, body) ->
      let tsub =
        Map.Poly.of_alist_exn @@ List.zip_exn (List.map ~f:fst fargs) aargs
      in
      let exi_senv =
        Term.pred_to_sort_env_map
        @@ MuCLP.Pred.pred_sort_env_map_of_list Map.Poly.empty defs
      in
      Option.return @@ Set.to_list
      @@ Set.Poly.map ~f:(fun (ps, ns, phi) ->
          assert (Set.is_empty ns);
          (Set.to_list ps, phi))
      @@ Formula.dnf_of exi_senv @@ Formula.subst tsub @@ open_exists body
  | Some ((Nu | MuOrNu), _senv, _body) -> raise UnfoldFailed

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
          {
            sequent with
            left_atms =
              (pvam :: sequent.left_atms) @ Sequent.ext_guard_list gatms depth;
            left_phi = Evaluator.simplify @@ Formula.mk_and sequent.left_phi phi;
          })

(* ToDo: unused *)
(* {i Induct Rule} add an induction hypothesis to [lemmas], [pvam] is a picked atom *)
let induct unfolded depth defs lemmas sequent pvam =
  let hyp =
    let pv_senv_list, phis =
      List.unzip_map (fst >> Sequent.normalize_atom)
      @@
      (* Exclude unfolded atoms from hyp *)
      List.filter sequent.left_atms
        ~f:(Fn.non @@ Sequent.mem_gatom unfolded)
    in
    let pv_senv, phi = Sequent.normalize_atom (fst pvam) in
    {
      sequent with
      left_atms =
        List.map pv_senv_list
          ~f:(Tuple2.uncurry Atom.pvar_app_of_senv >> Sequent.guard);
      left_phi = Formula.and_of (sequent.left_phi :: phi :: phis);
    }
    |> EntailmentLemma.make (Some (pv_senv, depth))
    (*|> EntailmentLemma.forall_elim tenv*)
    |> EntailmentLemma.normalize
  in
  ( hyp,
    (defs, hyp :: lemmas, { sequent with left_atms = pvam :: sequent.left_atms })
  )

(* {i Unfold Rule} @return branched judgements *)
let unfold_and_induct ~print ~config unfolded depth defs lemmas sequent pvam =
  match lookup defs pvam with
  | None -> raise UnfoldFailed
  | Some atms_phi_list ->
      livept := LivePT.mk_induct !livept;
      livept := LivePT.mk_unfold pvam (List.length atms_phi_list) !livept;
      print @@ lazy (sprintf ":: Unfolded %s@." (Atom.str_of @@ fst pvam));
      let hyp =
        let pv_senv_list, phis =
          List.unzip_map (fst >> Sequent.normalize_atom)
          @@
          (* Exclude unfolded atoms from hyp *)
          List.filter sequent.left_atms
            ~f:(Fn.non @@ Sequent.mem_gatom unfolded)
        in
        let pv_senv, phi = Sequent.normalize_atom (fst pvam) in
        {
          sequent with
          left_atms =
            List.map pv_senv_list
              ~f:(Tuple2.uncurry Atom.pvar_app_of_senv >> Sequent.guard);
          left_phi = Formula.and_of (sequent.left_phi :: phi :: phis);
        }
        |> EntailmentLemma.make (Some (pv_senv, depth + 1))
        (*|> EntailmentLemma.forall_elim tenv*)
        |> if config.normalize_lemma then EntailmentLemma.normalize else Fn.id
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
              let gatms, phi =
                (List.map atms ~f:Sequent.guard, phi)
                (*apply_options_for_frames pvam (List.map atms ~f:Sequent.guard, phi)*)
              in
              {
                sequent with
                left_atms =
                  sequent.left_atms @ Sequent.ext_guard_list gatms (depth + 1);
                left_phi = Formula.mk_and sequent.left_phi phi;
              }
            in
            (lemmas', sequent'))
      in
      (mk_induct_pt, mk_unfold_pt, subgoals)

let filter_consistent ~print phi sigmas =
  let checked_true = ref [] in
  (* Memoize checked equality *)
  let checked_false = ref [] in
  (* Memoize checked equality *)

  (* Check the consistency of a given substitution sigma (Optimized for speed).
      e.g. Given phi and [(x,t1); (y,t2); (x,t3)], check phi |= t1=t3. *)
  let rec is_consistent = function
    | [] -> true
    | (x, t) :: rest -> (
        try
          let t' = List.Assoc.find_exn ~equal:Stdlib.( = ) rest x in
          let eq =
            Evaluator.simplify
            @@
            (*if Type.is_heap ty then Formula.Heap.mk_eq t t'
             else*)
            Formula.eq t t'
          in
          let eq' =
            Evaluator.simplify
            @@
            (*if Type.is_heap ty then Formula.Heap.mk_eq t' t
             else*)
            Formula.eq (List.Assoc.find_exn ~equal:Stdlib.( = ) rest x) t
          in
          if
            List.mem ~equal:Stdlib.( = ) !checked_true eq
            || List.mem ~equal:Stdlib.( = ) !checked_true eq'
            || Formula.is_true eq
          then is_consistent rest
          else if
            List.mem ~equal:Stdlib.( = ) !checked_false eq
            || List.mem ~equal:Stdlib.( = ) !checked_false eq'
            || Formula.is_false eq
          then false
          else
            match
              Z3Smt.Z3interface.check_valid ~id:None (FunEnv.mk_empty ())
              @@ Formula.mk_imply phi eq
            with
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
        with Not_found_s _ -> is_consistent rest)
  in
  List.filter ~f:is_consistent sigmas

let rec apply_defs ~print preds_senv (atms, phi) hatm = function
  | [] -> []
  | (batms, bphi) :: rest -> (
      (* The body atoms in normal form [p(v~)], [v~] fresh, with the equations
         [v~ = t~] joined to the body formula.  Invariant: the case means the
         same, and the [v~] that [sigma] binds to the sequent's atoms are linked
         to the body's own variables, which are then quantified existentially
         like every other body-local variable.  Without the equations the body
         atoms' arguments were never related to the atoms they were matched
         with, and the folded atom could be added on a body it does not have. *)
      let nbatms, eqs = List.unzip_map Sequent.normalize_atom batms in
      let bphi = Formula.and_of (bphi :: eqs) in
      let batms = List.map nbatms ~f:(Tuple2.uncurry Atom.pvar_app_of_senv) in
      let aside_sigmas = Sequent.make_sigmas atms nbatms in
      let sub', exists_vars =
        let tmp =
          Set.Poly.union_list @@ List.map ~f:Atom.tvs_of (hatm :: batms)
        in
        Set.filter (Formula.term_sort_env_of bphi) ~f:(fst >> Set.mem tmp >> not)
        |> Set.Poly.filter_map ~f:(fun (x, sort) ->
            if Sort.is_arrow sort then None (* avoid quantification of ufuns *)
            else
              let newx = Ident.mk_fresh_tvar () in
              Some ((x, Term.mk_var newx sort), (newx, sort)))
        |> Set.to_list |> List.unzip
      in
      aside_sigmas |> Vector.product List.concat
      |> filter_consistent ~print phi
      |> List.map ~f:(( @ ) sub')
      |> function
      | [] -> apply_defs ~print preds_senv (atms, phi) hatm rest
      | sigmas -> (
          try
            let sigma =
              Map.Poly.of_alist_exn
              @@ List.find_exn sigmas
                   ~f:
                     (Map.Poly.of_alist_exn >> Fn.flip Formula.subst bphi
                    >> Formula.exists exists_vars
                     >> (fun phi ->
                     snd
                     @@ Qelim.elim_free_univ_vars_old Map.Poly.empty preds_senv
                     @@ ( Logic.of_old_sort_env_map @@ Map.of_set_exn
                          @@ Formula.term_sort_env_of phi,
                          phi ))
                     >> Formula.mk_imply phi
                     >> Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ())
                     )
            in
            [ Atom.subst sigma hatm ]
            (* one such sigma is enough *)
          with Not_found_s _ ->
            apply_defs ~print preds_senv (atms, phi) hatm rest))

(* {i Fold Rule} @return added_atms if foldable and [] otherwise *)
let fold ~print ~config defs lemmas sequent =
  let folded_seq =
    let preds_senv = Map.of_set_exn @@ MuCLP.Pred.sort_env_of_list defs in
    let added_atms =
      List.filter
        ~f:(Fn.non @@ Sequent.mem_gatom sequent.left_atms)
      @@ List.concat_map ~f:(fun gatm ->
          match lookup defs gatm with
          | None -> raise UnfoldFailed
          | Some atms_phi_list ->
              List.map ~f:Sequent.guard
              @@ List.dedup_keep_last ~equal:Stdlib.( = )
              @@ apply_defs ~print preds_senv
                   (List.map ~f:fst @@ sequent.left_atms, sequent.left_phi)
                   (fst gatm) atms_phi_list)
      @@ List.dedup_keep_last ~equal:Sequent.equal_gatom
      @@ (if config.fold_lemmas then
            (* LHS atoms of user defined lemma (for successful application of the lemmas) *)
            List.concat_map ~f:(fun (lem : EntailmentLemma.t) -> lem.sequent.left_atms)
            @@ List.filter ~f:EntailmentLemma.is_user_defined_lemma lemmas
          else [])
      @ sequent.right_atms
    in
    {
      sequent with
      left_atms = added_atms @ sequent.left_atms;
      left_phi = sequent.left_phi;
    }
  in
  let added_atms =
    List.filter ~f:(Fn.non @@ Sequent.mem_gatom sequent.left_atms)
    @@ folded_seq.left_atms
  in
  let mk_fold_pt =
    if List.is_empty added_atms then Fn.id
    else fun pt ->
      livept := LivePT.mk_fold !livept;
      print
      @@ lazy
           (sprintf ":: Folded (added %s)@."
              (String.concat_map_list ~sep:"," ~f:(fst >> Atom.str_of)
                 added_atms));
      Fold (sequent, added_atms, pt)
  in
  (mk_fold_pt, folded_seq)

(* [extend_by_equations ~exclude sigma phi]: [sigma] extended to the
   variables that equations [z = t] among the conjuncts of [phi] determine,
   repeatedly: [z := sigma(t)] when [z] is not yet bound nor in [exclude] and
   every variable of [t] is.  Precondition: [sigma] binds variables of a lemma
   (renamed apart from the sequent) to terms of the sequent.  Guarantee: the
   result is again such a substitution, extending [sigma]; it binds only
   variables of [phi].  A lemma is universally closed, so any instance of it,
   this one included, is a consequence of it.

   Why it is needed: a lemma's premise atoms reach [sigma] in normal form
   [p(v~)], the [v~] fresh and linked to the lemma's own variables by
   equations [v~ = t~] (and an induction hypothesis's guard parameters are
   linked to the sequent's variables the same way), so matching binds the
   [v~] and leaves the lemma's own variables unbound.  A lemma with no atom on
   its right is applied as a formula with those variables universally
   quantified, which needs no binding; but one with a conclusion atom
   [q(x - 1, ...)] must be instantiated, or its premise check
   [left_phi => sigma(phi)] mentions unbound variables and fails, and the atom
   added would be [q] at unbound variables.  The search's own induction
   hypotheses of a goal with atoms on its right (a lemma being proved) are
   such lemmas, so without this no such goal could use its hypothesis. *)
let extend_by_equations ~exclude sigma phi =
  let eqs =
    List.filter_map (Formula.conjuncts_list_of phi) ~f:(fun c ->
        if Formula.is_eq c then
          let t1, t2, _ = Formula.let_eq c in
          Some (t1, t2)
        else None)
  in
  let bindable sigma = function
    | Term.Var (x, _, _) -> (not (Map.Poly.mem sigma x)) && not (Set.mem exclude x)
    | _ -> false
  in
  let determined sigma t = Set.for_all (Term.tvs_of t) ~f:(Map.Poly.mem sigma) in
  let rec fix sigma =
    let step =
      List.find_map eqs ~f:(fun (t1, t2) ->
          let try_ lhs rhs =
            if bindable sigma lhs && determined sigma rhs then
              let (x, _), _ = Term.let_var lhs in
              Some (x, Term.subst sigma rhs)
            else None
          in
          match try_ t1 t2 with Some b -> Some b | None -> try_ t2 t1)
    in
    match step with
    | None -> sigma
    | Some (x, t) -> fix (Map.Poly.set sigma ~key:x ~data:t)
  in
  fix sigma

(* {i Apply Rule} Apply all lemmas and @return new sequent (LHS will be updated) *)
let apply ~print ~config lemmas sequent =
  let applied_seq, applied_ids, applied_lemmas =
    List.rev lemmas
    |> List.mapi ~f:(fun i lem -> (i + 1, lem))
    |> List.rev
    |> List.fold_left ~init:(sequent, [], [])
         ~f:(fun (sequent, applied_ids, applied_lemmas) (id, lemma) ->
           (* renamed apart from [sequent]: see [EntailmentLemma.refresh] *)
           let lemma = EntailmentLemma.refresh lemma in
           print @@ lazy (sprintf ":: Applying [%d]@." id);
           if
             config.enable_apply_threshold
             && EntailmentLemma.is_induction_hypothesis lemma
             && 2 * (List.length lemma.sequent.left_atms + 1)
                > List.length sequent.left_atms
           then begin
             print
             @@ lazy
                  ":: Skipping induction hypothesis (enable_apply_threshold)@.";
             (sequent, applied_ids, applied_lemmas)
           end
           else
             (* The premise atoms in normal form [p(v~)], [v~] fresh, and the
                equations [v~ = t~] joined to the premise formula.  Invariant: the
                lemma is unchanged in meaning ([p(t~), phi] and
                [p(v~), v~ = t~ /\ phi] are one premise), and the variables
                [sigma] binds -- the [v~] -- are exactly the ones the formula
                links to the atoms' arguments.  Dropping the equations left the
                formula's own atom variables unbound, so the [forall] below
                quantified them and a premise atom was never required to match
                an atom of the sequent: a hypothesis about [p(t~)] then closed
                branches it says nothing about. *)
             let pvars1, eqs =
               List.unzip_map (fst >> Sequent.normalize_atom)
                 lemma.sequent.left_atms
             in
             let lemma =
               {
                 lemma with
                 sequent =
                   {
                     lemma.sequent with
                     left_atms =
                       List.map2_exn pvars1 lemma.sequent.left_atms
                         ~f:(fun (pvar, senv) (_, g) ->
                           (Atom.pvar_app_of_senv pvar senv, g));
                     left_phi = Formula.and_of (lemma.sequent.left_phi :: eqs);
                   };
               }
             in
             let sigmas =
               (* The construction of sigma proves two premises:
                 |- phi1 => [| (sigma g) \in A1 |] and
                 |- phi1 => [| (sigma A1') \subset A1 |] *)
               (match lemma.guard with
                 | None -> [ [ [] ] ]
                 | Some ((pvar, senv), m) ->
                     Sequent.make_sigmas
                       (List.map ~f:fst
                       @@ List.filter sequent.left_atms ~f:(fun (_, g) ->
                           Set.mem g m))
                       [ (pvar, senv) ])
               @ Sequent.make_sigmas (List.map ~f:fst sequent.left_atms) pvars1
               |> Vector.product List.concat
               |> filter_consistent ~print sequent.left_phi
             in
             if List.is_empty sigmas then begin
               print @@ lazy ":: Lemma failed (Empty sigma)@.";
               (sequent, applied_ids, applied_lemmas)
             end
             else
               let bvs =
                 Set.Poly.union_list @@ List.map ~f:Atom.tvs_of
                 @@ (match lemma.guard with
                   | None -> []
                   | Some ((pvar, senv), _) ->
                       [ Atom.pvar_app_of_senv pvar senv ])
                 @ List.map pvars1 ~f:(Tuple2.uncurry Atom.pvar_app_of_senv)
               in
               (* Try all sigma candidates *)
               List.fold_left sigmas
                 ~init:(sequent, applied_ids, applied_lemmas)
                 ~f:(fun (sequent, applied_ids, applied_lemmas) sigma ->
                   let sigma = Map.Poly.of_alist_exn sigma in
                   (* only a lemma with a conclusion atom is instantiated
                      further: one without is used as a formula with its
                      unbound variables quantified, where binding them
                      changes the formula's shape but not its meaning *)
                   let sigma =
                     if List.is_empty lemma.sequent.right_atms then sigma
                     else
                       extend_by_equations
                         ~exclude:(Map.key_set lemma.sequent.eqvars)
                         sigma lemma.sequent.left_phi
                   in
                   let sigma' =
                     Map.force_merge sigma
                     @@ Map.Poly.map ~f:Term.mk_fresh_var lemma.sequent.eqvars
                   in
                   let newphi =
                     Formula.forall
                       (Set.to_list
                       @@ Set.filter ~f:(fst >> Set.mem bvs >> not)
                       @@ Formula.term_sort_env_of lemma.sequent.left_phi)
                     @@ Formula.mk_or
                          (if config.check_lemma_lhs then
                             (* force the LHS to be checked *)
                             Formula.mk_false ()
                           else
                             Formula.negate
                               (Formula.subst sigma lemma.sequent.left_phi))
                          (Formula.subst sigma' lemma.sequent.right_phi)
                   in
                   if
                     Z3Smt.Z3interface.is_valid ~id:None (FunEnv.mk_empty ())
                     @@ Evaluator.simplify
                     @@ Formula.mk_imply sequent.left_phi newphi
                     && List.is_empty lemma.sequent.right_atms
                   then begin
                     print
                     @@ lazy ":: Lemma failed (No Additional Information)@.";
                     (sequent, applied_ids, applied_lemmas)
                   end
                   else if
                     Fn.non List.is_empty lemma.sequent.right_atms
                     && not
                        @@ Z3Smt.Z3interface.is_valid ~id:None
                             (FunEnv.mk_empty ())
                        @@ Formula.mk_imply sequent.left_phi
                        @@ Formula.subst sigma lemma.sequent.left_phi
                   then begin
                     print @@ lazy ":: Lemma failed (Must prove LHS)@.";
                     (sequent, applied_ids, applied_lemmas)
                   end
                   else if
                     (* A lemma with conclusion atoms concludes the
                        disjunction [A~ \/ right_phi] once its left side is
                        shown: its atoms may be added to the left only when
                        the sequent excludes the other disjunct.  Adding
                        both the atoms and [newphi] conjunctively, as this
                        rule once did, added [not (left_phi of the lemma)],
                        which the "Must prove LHS" check has just shown to
                        contradict the sequent: every such application made
                        the sequent's left side false and the sequent valid,
                        so a true lemma such as [P x |- W x] proved any goal
                        it applied to (a wrong [sat] on a problem whose
                        counterexample needs a long derivation). *)
                     Fn.non List.is_empty lemma.sequent.right_atms
                     && not
                        @@ Z3Smt.Z3interface.is_valid ~id:None
                             (FunEnv.mk_empty ())
                        @@ Formula.mk_imply sequent.left_phi
                        @@ Formula.negate
                        @@ Formula.subst sigma' lemma.sequent.right_phi
                   then begin
                     print
                     @@ lazy
                          ":: Lemma failed (the conclusion's constraint is not \
                           excluded)@.";
                     (sequent, applied_ids, applied_lemmas)
                   end
                   else begin
                     print @@ lazy ":: Lemma success@.";
                     ( {
                         sequent with
                         left_atms =
                           sequent.left_atms
                           @ Sequent.map_atm ~f:(Atom.subst sigma')
                               lemma.sequent.right_atms;
                         left_phi =
                           (if List.is_empty lemma.sequent.right_atms then
                              Evaluator.simplify
                              @@ Formula.mk_and sequent.left_phi newphi
                            else
                              (* the lemma's left side holds and its
                                 constraint disjunct is excluded: the atoms
                                 are what it adds *)
                              sequent.left_phi);
                       },
                       id :: applied_ids,
                       lemma :: applied_lemmas )
                   end))
  in
  let added_atms =
    List.filter applied_seq.left_atms
      ~f:(Fn.non @@ Sequent.mem_gatom sequent.left_atms)
  in
  let mk_apply_pt =
    if Sequent.equal_light sequent applied_seq then Fn.id
    else begin
      print
      @@ lazy
           (Format.asprintf ":: Applied %a@."
              (Sequent.pr ~wo_guard:false)
              applied_seq);
      livept := LivePT.mk_apply (Set.Poly.of_list applied_ids) !livept;
      fun pt -> Apply (sequent, applied_lemmas, pt)
    end
  in
  (mk_apply_pt, applied_seq, added_atms)

(* [chc_of defs sequent]: the sequent as a CHC problem over the least
   fixpoints of [defs] -- one definite clause [A~ /\ phi => P(x~)] per case of
   every definition's body ([lookup]), and the goal clause
   [A~ /\ left_phi /\ not right_phi => false].  Precondition: the sequent has
   no atom and no existential on its right ([None] otherwise: a positive
   occurrence of a least fixpoint is not a CHC).  Guarantee: the CHC problem is
   satisfiable iff the sequent is valid in the least model of [defs] (the least
   model of the definite clauses is the least fixpoint, and the goal clause
   says no point of it violates the sequent). *)
let chc_of (defs : MuCLP.Pred.t list) (sequent : Sequent.t) =
  if
    Fn.non List.is_empty sequent.right_atms
    || Fn.non Map.Poly.is_empty sequent.eqvars
  then None
  else
    let definite =
      List.concat_map defs ~f:(fun (pred : MuCLP.Pred.t) ->
          let head = Atom.pvar_app_of_senv pred.name pred.args in
          match lookup defs (head, Set.Poly.empty) with
          | None -> []
          | Some cases ->
              List.map cases ~f:(fun (atms, phi) ->
                  Formula.mk_imply
                    (Formula.and_of (phi :: List.map atms ~f:Formula.mk_atom))
                    (Formula.mk_atom head)))
    in
    let goal =
      Formula.mk_imply
        (Formula.and_of
           (sequent.left_phi
           :: Formula.mk_neg sequent.right_phi
           :: List.map sequent.left_atms ~f:(fst >> Formula.mk_atom)))
        (Formula.mk_false ())
    in
    let penv =
      List.map defs ~f:(fun (pred : MuCLP.Pred.t) ->
          (pred.name, List.map ~f:snd pred.args))
    in
    Some
      ( penv,
        Set.Poly.of_list
        @@ List.map (goal :: definite) ~f:(fun phi ->
            (Map.of_set_exn (Formula.term_sort_env_of phi), phi)) )

(* {i Valid Rule}.  Below depth [valid_with_smt_threshold] (or without one) the
   sequent is valid when its pure part is ([Sequent.is_valid]).  At or beyond
   it, the sequent is asked of the CHC solver [solve_chc] as a whole
   ([chc_of]), as CAV 2017's implementation asked a PDR solver: [sat] closes the
   branch, [unsat] makes it invalid -- the sequent fails in the least model,
   and every sequent of the search follows from the goal and valid
   definitions and hypotheses, so the goal fails too -- and any other answer,
   or a sequent with atoms on its right, leaves the rule undecided. *)
let valid ~print ~config ~solve_chc depth defs sequent =
  let mk_valid () =
    livept := LivePT.mk_valid !livept;
    print @@ lazy ":: Valid@.";
    Valid sequent
  in
  match config.valid_with_smt_threshold with
  | Some n when depth >= n -> (
      print @@ lazy ":: Asking the CHC solver...@.";
      match chc_of defs sequent with
      | None -> raise ValidRuleUnknown
      | Some (penv, chcs) -> (
          match solve_chc penv chcs with
          | `Valid -> mk_valid ()
          | `Invalid -> (
              livept := LivePT.mk_invalid !livept;
              print @@ lazy ":: Invalid (CHC solver)@.";
              (* the model is a report: a point of the pure part where the
                 sequent fails, when Z3 finds one *)
              match
                Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ())
                  [
                    Formula.negate
                    @@ Formula.mk_imply sequent.left_phi sequent.right_phi;
                  ]
              with
              | `Sat model -> InValid (sequent, model)
              | _ -> InValid (sequent, []))
          | `Unknown -> raise ValidRuleUnknown))
  | _ -> (
      (* Check premise |- phi1 => [| A1 \in A2 |] /\ phi2 *)
      try
        if Sequent.is_valid ~print ~config sequent then mk_valid ()
        else raise ValidRuleUnknown
      with Z3Smt.Z3interface.Unknown -> raise ValidRuleUnknown)

(* [under_approx defs k atm]: a formula that implies [atm] in the least
   fixpoint of [defs] -- the derivations of [atm] of height at most [k], each
   case of its definition ([lookup]) with its atoms replaced by their own
   derivations of height [k - 1], an atom at height 0 by [false].  Free
   variables it introduces (a case's opened existentials) are existential:
   any values satisfying the formula are a derivation.  Guarantee:
   [under_approx defs k atm => atm] holds in the least model, for every [k].
   Raises [UnfoldFailed] on a greatest-fixpoint definition.  Size: the
   number of cases times atoms per case, to the power [k]. *)
let rec under_approx defs k atm =
  if k <= 0 then Formula.mk_false ()
  else
    match lookup defs (atm, Set.Poly.empty) with
    | None -> Formula.mk_false ()
    | Some cases ->
        Formula.or_of
        @@ List.map cases ~f:(fun (atms, phi) ->
            Formula.and_of
              (phi :: List.map atms ~f:(under_approx defs (k - 1))))

(* The derivation heights [counterexample_of] tries, smallest first.  A
   refutation is reported only with a derivation of every atom, so a bound
   costs answers, never soundness.  At three, every refutation this engine
   gave on a corpus of 137 Horn-clause problems over lists, trees and
   integers (nine) is found again; the formula's size grows as the number of
   cases times atoms per case to the power of the height. *)
let counterexample_max_height = 3

(* [counterexample_of defs seq]: a model of [seq]'s left atoms' derivations
   of height [<= k] for the smallest [k <= counterexample_max_height] that
   has one, together with the left pure part and the negated right side.
   Precondition: none.  Guarantee: [Some m] only if [seq] fails in the least
   model of [defs] (at [m] every left atom holds by its derivation, the left
   pure part holds and the right side fails).  [None] when the sequent has
   right atoms, an existential variable that a left atom mentions, or no
   such model is found (Z3 answering [unsat] or not deciding). *)
let counterexample_of defs (seq : Sequent.t) =
  let atms = List.map seq.left_atms ~f:fst in
  if
    Fn.non List.is_empty seq.right_atms
    || List.exists atms ~f:(fun a ->
        Set.exists (Atom.tvs_of a) ~f:(Map.Poly.mem seq.eqvars))
  then None
  else
    let right =
      Formula.exists (Map.Poly.to_alist seq.eqvars) seq.right_phi
    in
    let rec go k =
      if k > counterexample_max_height then None
      else
        match
          Z3Smt.Z3interface.check_sat ~id:None (FunEnv.mk_empty ())
            [
              Formula.and_of
                (seq.left_phi :: Formula.negate right
                :: List.map atms ~f:(under_approx defs k));
            ]
        with
        | `Sat model -> Some model
        | _ -> go (k + 1)
        | exception Z3Smt.Z3interface.Unknown -> go (k + 1)
    in
    go 1

(* proof search strategy *)
let rec strategy unfolded depth ~print ~config ~solve_chc defs lemmas sequent =
  print
  @@ lazy (Format.asprintf ":: Proof tree overview:@.   %a@." LivePT.pr !livept);
  let init_seq = Sequent.simplify sequent in
  print
  @@ lazy (Format.asprintf "%a" EntailmentProofTree.pr_judgement (defs, lemmas, init_seq));
  try valid ~print ~config ~solve_chc depth defs init_seq
  with ValidRuleUnknown -> (
    print @@ lazy ":: Unknown@.";
    let mk_apply_pt, applied_seq, added_atms =
      apply ~print ~config lemmas init_seq
    in
    (* 1. exclude from induct. hyp. 2. skip unfold *)
    mk_apply_pt
    @@
      try
        if Sequent.equal_light init_seq applied_seq then raise ValidRuleUnknown
        else valid ~print ~config ~solve_chc depth defs applied_seq
      with ValidRuleUnknown -> (
        print @@ lazy ":: Unknown (after Apply rule)@.";
        let mk_fold_pt, folded_seq =
          fold ~print ~config defs lemmas applied_seq
        in
        mk_fold_pt
        @@
          try
            if Sequent.equal_light applied_seq folded_seq then
              raise ValidRuleUnknown
            else valid ~print ~config ~solve_chc depth defs folded_seq
          with ValidRuleUnknown -> (
            print @@ lazy ":: Unknown (after Fold rule)@.";
            try
              let rec select_pvam pvams =
                if config.ask_pred_app_to_unfold then begin
                  print @@ lazy ":: Select unfolded atom:@.";
                  List.iteri pvams ~f:(fun i (a, _) ->
                      print @@ lazy (sprintf "@,%d: %s" i (Atom.str_of a)));
                  print @@ lazy "@,:: Unfold No(auto=-1): @.";
                  let num =
                    try
                      Out_channel.(flush stdout);
                      Int.of_string In_channel.(input_line_exn stdin)
                    with Failure _ -> -1
                  in
                  if num < 0 then select_pvam pvams else List.nth_exn pvams num
                end
                else
                  match pvams with
                  | [] ->
                      print @@ lazy ":: (Warning) Pvam selection failed@.";
                      raise PickPvamFailed
                  | pvam :: rest ->
                      if Sequent.mem_gatom unfolded pvam then
                        select_pvam rest
                      else pvam
              in
              let pvam = select_pvam folded_seq.left_atms in
              let unfolded' = (pvam :: unfolded) @ added_atms in
              let mk_induct_pt, mk_unfold_pt, subgoals =
                unfold_and_induct ~print ~config unfolded' depth defs lemmas
                  folded_seq pvam
              in
              mk_induct_pt @@ mk_unfold_pt @@ List.rev @@ fst
              @@ List.fold_left subgoals ~init:([], false)
                   ~f:(fun (lst, is_invalid) (lems, seq) ->
                     if is_invalid then (EntailmentProofTree.Abort seq :: lst, is_invalid)
                     else
                       let pt =
                         strategy unfolded' (depth + 1) ~print ~config ~solve_chc defs lems
                           seq
                       in
                       (pt :: lst, Fn.non EntailmentProofTree.is_valid pt))
            with PickPvamFailed -> (
              (* Every left atom has been unfolded on this branch (or was
                 added by Apply from a hypothesis's right-hand atoms, and is
                 never unfolded), and the sequent is still not valid.  It is
                 refuted only by a point where the pure part fails AND every
                 left atom holds in the least fixpoint ([counterexample_of]).
                 A model of the pure part alone is one only while every left
                 atom's derivation is recorded in that pure part: an unfolded
                 atom's chosen case is, and so, recursively, are its case's
                 atoms; an atom Apply adds is implied by atoms of the
                 sequent through a valid hypothesis.  That invariant is a
                 property of the whole search, not of this sequent, and a
                 hypothesis, a generated lemma or an atom kept without its
                 case that breaks it would make the pure model a fake
                 counterexample and a valid goal [invalid].  So the atoms are
                 checked here, by derivations of bounded height; with none
                 found the branch is undecided. *)
              match counterexample_of defs folded_seq with
              | Some model ->
                  livept := LivePT.mk_invalid !livept;
                  print @@ lazy ":: Invalid@.";
                  InValid (folded_seq, model)
              | None -> raise Unkown))))

let solve ~print ~config pcsp_solver problem =
  try
    let open Or_error.Monad_infix in
    pcsp_solver () >>= fun (module PCSPSolver : PCSPSolver.Solver.SolverType) ->
    (* the CHC solver the Valid rule asks beyond [valid_with_smt_threshold];
       [dtenv] gives the datatypes the clauses mention *)
    let solve_chc penv chcs =
      let params =
        PCSP.Params.make ~dtenv:problem.Problem.dtenv
        @@ Logic.of_old_sort_env_map @@ Term.pred_to_sort_env_map
        @@ Map.Poly.of_alist_exn penv
      in
      let bpvs =
        Set.Poly.of_list @@ List.map penv ~f:(fst >> Ident.pvar_to_tvar)
      in
      PCSPSolver.reset ();
      match
        PCSPSolver.solve ~bpvs (PCSP.Problem.of_old_formulas ~params chcs)
      with
      | Ok (PCSP.Problem.Sat _, _) -> `Valid
      | Ok (PCSP.Problem.Unsat _, _) -> `Invalid
      | Ok _ | Error _ -> `Unknown
    in
    let rec solve_aux problem =
      livept := LivePT.mk_root () (* initialization *);
      print
      @@ lazy
           (Format.asprintf "@.@[<v 3>:: Target Problem:@;%a@]@." Problem.pr
              problem);
      match problem with
      | Problem.
          {
            env;
            lemmas = lems;
            defs;
            goals = (seq, tout, is_hard) :: rest;
            dtenv = _dtenv;
          } ->
          (* A soft goal (a conjecture: a user lemma, or a generated
             determinacy conjecture) is tried within its own budget; a hard
             goal is the problem's.  Contract: a soft goal is added to the
             lemmas of the goals after it only if its proof tree is valid --
             it has been proved, from the lemmas proved before it -- and a
             soft goal that is refuted, runs out of its budget, is abandoned
             ([Unkown]) or fails with any other synchronous exception is
             dropped and decides nothing; every later goal is attempted in
             each case.  A hard goal that is abandoned or whose budget ends
             leaves the problem [Unknown].

             The outcome is decided here, not by [Timer.enable_timeout]'s
             handlers alone, because under a budget armed further out
             (RCaml's per-problem timeout) [enable_timeout] runs its body
             without a budget of its own and passes the body's result
             straight back, skipping both handlers: the goals after the
             first were then never attempted, and the verdict was read off
             the first goal's tree alone -- a soft goal's, which counts for
             nothing, so the run answered [Valid] without looking at the
             problem.  So under an outer budget the goal runs directly and a
             [Timeout] is that budget's, passed on to whoever armed it; only
             a [Timeout] of a budget armed here is this goal's.  Under an
             outer budget a soft goal therefore has no budget of its own and
             may use up the outer one, which costs the answer, never its
             correctness. *)
          let attempt () =
            try
              `Done
                (strategy [] 0 ~print ~config ~solve_chc defs
                   (Set.to_list lems) seq)
            with
            | Unkown when not is_hard -> `Dropped "undecided"
            | e when (not is_hard) && not (Timer.is_async e) ->
                `Dropped (Exn.to_string e)
          in
          let outcome =
            if !Timer.already_set then attempt ()
            else
              let tout =
                match tout with
                | Some tout when not is_hard -> tout
                | _ -> 0 (* no budget of its own *)
              in
              Timer.enable_timeout tout Fn.id ignore attempt
                (fun _ r -> r)
                (fun _ -> function
                  | Timer.Timeout when not is_hard ->
                      `Dropped "out of its budget"
                  | Timer.Timeout -> raise Unkown
                  | e -> raise e)
          in
          let report what =
            if not is_hard then
              Out_channel.eprintf "[MuCyc relational] conjecture %s: %s\n%!"
                (Formula.str_of @@ Sequent.to_formula seq)
                what
          in
          (match outcome with
          | `Done pt ->
              let proved = is_valid pt in
              report
                (if proved then "proved, used as a lemma"
                 else "not proved, not used");
              let new_lems =
                if proved then Set.add lems (EntailmentLemma.of_sequent seq)
                else lems
              in
              (pt, is_hard) :: solve_aux (Problem.make env new_lems defs rest)
          | `Dropped why ->
              report (sprintf "not proved (%s), not used" why);
              solve_aux (Problem.make env lems defs rest))
      | Problem.{ goals = []; _ } -> [] (* No sequents (Valid) *)
    in
    let prooftrees = solve_aux problem in
    Ok
      ( MuCLP.Problem.(
          if
            List.for_all prooftrees ~f:(fun (pt, is_hard) ->
                (not is_hard) || is_valid pt)
          then Valid
          else Invalid),
        prooftrees )
  with
  | Unkown -> Ok (Verdict.Unknown, [])
  | e when not (Timer.is_async e) ->
      (* Every other failure of the search -- an atom with no definition or a
         greatest-fixpoint one ([UnfoldFailed]), a definition body the DNF
         cannot take, the unimplemented SMT/PDR fallback of
         [valid_with_smt_threshold] -- leaves the goal undecided: the search
         is a proof attempt, and an abandoned attempt proves and refutes
         nothing.  It is answered [unknown] with the reason on stderr, never
         as an exception escaping to the driver. *)
      Out_channel.eprintf "[MuCyc relational] unknown: %s\n%!"
        (Exn.to_string e);
      Ok (Verdict.Unknown, [])
