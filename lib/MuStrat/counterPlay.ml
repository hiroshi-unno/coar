(* The counter-play read-back of a strategy check: a derivation the CHC
   backend returned against the clauses of a check (a counter-play, a
   [mp]/[hyper-res] proof term) read back into the clauses it instantiates
   and into the ground play it records.

   The clauses are the derivation unfolded per path: each step's stated
   clause with each premise predicate renamed to a fresh copy [p$N] (one copy
   per occurrence of the step), so the dependency graph of the clauses is a
   tree; and the query, the one clause with no head.  A refinement reads the
   copies [k$N] of the refined keys [k] as the unknowns to synthesise.  The
   play is the derivation's steps as a tree of ground atoms, one node per
   distinct step.

   Everything here is a reading: nothing asks a solver, and the clause set is
   built only when it is read.  [Make] takes what the strategy check holds:
   its configuration (read only through [Config.chain_pairs_from_play] and
   the field [refine_counter_play]) and its trace. *)

open Core
open Common.Ext
open Common.Combinator
open Ast

module Make (A : sig
  val config : Config.t
  val print : ?id:int option -> string Lazy.t -> unit
end) =
struct
  let config = A.config

  module Debug = struct
    let print = A.print
  end

  (* The readers of a proof term below raise [Failure] or
     [Assert_failure] on a term that is not of the [mp]/[hyper-res] shape
     the backends produce; they take no other input. *)

  let let_conc t =
    let open Ast.LogicOld in
    if Term.is_var t then
      Formula.mk_atom
      @@ Atom.mk_pvar_app (Ident.tvar_to_pvar @@ Term.tvar_of t) [] []
    else if T_bool.is_formula t then T_bool.let_formula t
    else failwith @@ Term.str_of t

  let rec let_asserted t =
    let open Ast.LogicOld in
    let ts =
      try
        let fvar, _, _, ts, _ = Term.let_fvar_app t in
        assert (String.(Ident.name_of_tvar fvar = "asserted"));
        ts
      with exn_ when not (Common.Timer.is_async exn_) ->
        let sym, ts, _ = Term.let_app t in
        Debug.print @@ lazy ("why " ^ Term.str_of_funsym sym);
        ts
    in
    match ts with
    | [ t ] -> let_conc t
    | _ ->
        if T_bool.is_formula t && (Formula.is_eq @@ T_bool.let_formula t) then
          let phi = T_bool.let_formula t in
          let t, _ (*ToDo*), _ = Formula.let_eq phi in
          let_asserted t
        else failwith @@ "let_asserted: " ^ Term.str_of t

  let rec let_hyper_res t =
    let open Ast.LogicOld in
    let ts =
      try
        let fvar, _, _, ts, _ = Term.let_fvar_app t in
        assert (String.(Ident.name_of_tvar fvar = "hyper-res"));
        ts
      with exn_ when not (Common.Timer.is_async exn_) ->
        let sym, ts, _ = Term.let_app t in
        Debug.print @@ lazy ("why " ^ Term.str_of_funsym sym);
        ts
    in
    match ts with
    | asserted :: rest ->
        let hress, con = List.rest_last rest in
        (let_asserted asserted, hress, let_conc con)
    | _ ->
        if T_bool.is_formula t && (Formula.is_eq @@ T_bool.let_formula t) then
          let phi = T_bool.let_formula t in
          let t, _ (*ToDo*), _ = Formula.let_eq phi in
          let_hyper_res t
        else failwith @@ "let_hyper_res: " ^ Term.str_of t

  let let_mp phi =
    let open Ast.LogicOld in
    let t, _, _ = Formula.let_eq phi in
    let ts =
      try
        let fvar, _, _, ts, _ = Term.let_fvar_app t in
        assert (String.(Ident.name_of_tvar fvar = "mp"));
        ts
      with exn_ when not (Common.Timer.is_async exn_) ->
        let sym, ts, _ = Term.let_app t in
        Debug.print @@ lazy ("why " ^ Term.str_of_funsym sym);
        ts
    in
    match ts with
    | [ ant1; ant2; con ] -> (ant1, let_asserted ant2, let_conc con)
    | _ -> assert false

  let rec analyze_cex hres ren =
    let open Ast.LogicOld in
    let ant, hress, con0 = let_hyper_res hres in
    let senv, ant, _ =
      if Formula.is_forall ant then Formula.let_forall ant else ([], ant, Dummy)
    in
    let (ants1, ants2), con =
      if Formula.is_imply ant then
        let ant, con, _ = Formula.let_imply ant in
        ( List.partition_tf ~f:(fun phi ->
              Formula.is_atom phi
              && (Atom.is_pvar_app @@ fst @@ Formula.let_atom phi))
          @@ Formula.conjuncts_list_of ant,
          con )
      else (([], []), ant)
    in
    let css, ants1 =
      List.unzip
      @@ List.map2_exn hress ants1 ~f:(fun hres ant ->
          let pvs = Formula.pvs_of ant in
          let ren =
            Map.of_set_exn
            @@ Set.Poly.map pvs ~f:(fun pvar ->
                ( pvar,
                  Ident.mk_fresh_pvar
                    ~prefix:(Some (Ident.name_of_pvar pvar ^ "$"))
                    () ))
          in
          (analyze_cex hres ren, Formula.rename_pvars ren ant))
    in
    let css1, css2 = List.unzip css in
    ( Set.add (Set.Poly.union_list css1)
      @@ Formula.mk_forall_if_bounded senv
      @@ Formula.mk_imply
           (Formula.and_of @@ ants1 @ ants2)
           (Formula.rename_pvars ren con),
      Set.add (Set.Poly.union_list css2) @@ Formula.rename_pvars ren con0 )

  (* The ground play a derivation records; see [ChainRegions.play_node]. *)
  type play_node = ChainRegions.play_node = {
    pvar : Ident.pvar;
    args : LogicOld.Term.t list;
    children : play_node list;
    clause : LogicOld.Formula.t;
  }

  (* A table keyed by a derivation step ([hyper-res] term) compared
     physically, hashed on the step's conclusion (a small ground atom, so the
     hash reads all of it; distinct steps with one conclusion share a bucket
     and are told apart by identity).  A derivation, from Spacer's decoder or
     from the ground split, shares a step used by several later ones, and a
     reader that rebuilds the derivation per path reaches a shared step along
     every path: on one counter-play a few hundred distinct steps stood for
     millions of paths.  Kept per walk, never across walks. *)
  module StepTbl = Stdlib.Hashtbl.Make (struct
    type t = LogicOld.Term.t

    let equal = phys_equal

    (* any term hashes; a term that is not an application is hashed on its
       first nodes, which is consistent with [equal] all the same *)
    let hash t =
      match LogicOld.Term.let_fvar_app t with
      | _, _, _, (_ :: _ as ts), _ ->
          Stdlib.Hashtbl.hash_param 100 1000 (List.last_exn ts)
      | _ -> Stdlib.Hashtbl.hash_param 10 100 t
      | exception exn when not (Common.Timer.is_async exn) ->
          Stdlib.Hashtbl.hash_param 10 100 t
  end)

  (* [play_tree_of hres]: the play of the derivation [hres], one node per
     distinct step: a step met again (physically the same term) gets the node
     built for it the first time.  Postcondition: the result is structurally
     equal to the node tree built path by path (the same function of the same
     step), so every reader sees the same play; only the physical sharing,
     hence the memory, differs. *)
  let play_tree_of hres =
    let open Ast.LogicOld in
    let memo = StepTbl.create 256 in
    let rec go hres =
      match StepTbl.find_opt memo hres with
      | Some node -> node
      | None ->
          let clause, hress, con = let_hyper_res hres in
          let pvar, args =
            if Formula.is_atom con then
              match fst @@ Formula.let_atom con with
              | Atom.App (Predicate.Var (pvar, _), args, _) -> (pvar, args)
              | _ -> (Ident.Pvar "", [])
            else (Ident.Pvar "", [])
          in
          let node = { pvar; args; children = List.map hress ~f:go; clause } in
          StepTbl.replace memo hres node;
          node
    in
    go hres

  (* [derivation_roots ~unknowns cex]: the topmost derived atoms of the
     derivation [cex] (an [mp]/[hyper-res] proof term), as
     [VerdictValidation.refutation_validates] reads them.  The backend's
     derivation ends in its own query relation (or in [false]), whose premises
     are then the roots; a derivation ending in an atom of a predicate in
     [unknowns] has that atom as its one root.
     Post: the result is structurally equal to the node trees built path by
     path (each occurrence of a step its own node), as a list of the same
     length in the same order: a root list holding one step twice holds its
     node twice, and so does a children list.  Each distinct step (physically
     the same proof term) is read once, and a step met again gets the node
     built for it the first time, so the nodes share what the derivation
     shares.  The argument: a node is a function of its step alone (its
     conclusion and, recursively, its premises), so the node built at the
     first occurrence is the one the per-path build makes at every occurrence.
     Raises: [VerdictValidation.Reject] on a step whose conclusion is not an
     application of a predicate, and as the readers of a proof term do on a
     term not of that shape -- the same exception the per-path build raises:
     the steps are first met in the order the per-path build meets them, and
     a step met again was read to the end without raising, which the per-path
     build would do again, so both stop at the same first failing step. *)
  let derivation_roots ~unknowns cex =
    let open Ast.LogicOld in
    let atom_of con =
      match con with
      | Formula.Atom (Atom.App (Predicate.Var (pvar, _), args, _), _) ->
          Some (pvar, args)
      | _ -> None
    in
    let memo = StepTbl.create 256 in
    let rec vnode hres =
      match StepTbl.find_opt memo hres with
      | Some node -> node
      | None -> (
          let _, hress, con = let_hyper_res hres in
          match atom_of con with
          | Some (pvar, args) ->
              let node =
                {
                  VerdictValidation.pvar;
                  args;
                  children = List.map hress ~f:vnode;
                }
              in
              StepTbl.replace memo hres node;
              node
          | None ->
              raise
                (VerdictValidation.Reject
                   "a derivation step whose conclusion is not a predicate \
                    application"))
    in
    let hres, _, _ = let_mp cex in
    let _, hress, con = let_hyper_res hres in
    match atom_of con with
    | Some (pvar, _) when Set.mem unknowns pvar -> [ vnode hres ]
    | _ -> List.map hress ~f:vnode

  (* What [read_counter_play] reads off a counter-play.
     - [play]: the ground play ([play_tree_of]), only when
       [Config.chain_pairs_from_play] holds, else [None];
     - [no_key_copy]: true only when no predicate of the clauses can be a
       copy [k$N] of a refined key [k] (decided on the distinct steps, the
       clauses not built);
     - [distinct_steps]: the number of distinct steps of the derivation;
     - [expanded]: built when forced, the clauses as a problem in which every
       predicate is an unknown, the model the derivation states (each derived
       atom, a predicate and its ground arguments), and, under
       [refine_counter_play = Lifted_free_goal], the clauses with the goal
       instance generalised ([None] when the query has no ground argument);
     - [raw_problem]: the first component of [expanded]. *)
  type read = {
    play : play_node option;
    no_key_copy : bool;
    distinct_steps : int;
    expanded :
      (PCSP.Problem.t
      * (Ident.pvar * Logic.term list) Set.Poly.t
      * PCSP.Problem.t option Lazy.t)
      Lazy.t;
    raw_problem : PCSP.Problem.t Lazy.t;
  }

  (* [read_counter_play ~orig_keys_wf ~orig_keys_fn cex]: the read-back of
     the counter-play [cex] (an [mp] proof term) against the refined keys
     [orig_keys_wf] (ranked, [DWF]) and [orig_keys_fn] (Skolem, [FN]).
     Pre: [cex] has the [mp]/[hyper-res] shape the backends return; the keys
     are the opponent side's strategy unknowns.
     Post: see [read]; the clauses are built (and printed) here only when
     [no_key_copy] is false, and otherwise only when [expanded] or
     [raw_problem] is forced.  [no_key_copy = true] implies that the built
     clauses would hold no key copy (the argument is the comment below).
     Effects: the trace, and fresh names drawn when the clauses are built. *)
  let read_counter_play ~orig_keys_wf ~orig_keys_fn cex =
    let open Ast.LogicOld in
    (*if verbose then*)
    Debug.print @@ lazy (sprintf "## cex: %s\n" (Formula.str_of cex));
    let play =
      if Config.chain_pairs_from_play config then
        let hres, _, _ = let_mp cex in
        Some (play_tree_of hres)
      else None
    in
    (* Whether the clauses read off the counter-play can hold a copy of a
       refined key, decided on the counter-play's distinct steps without
       building the clauses.  The clauses ([analyze_cex]) are built per path
       through the derivation, since each occurrence of a step gets its own
       fresh predicate names; a derivation that shares steps (the ground
       split's always does, Spacer's often) has far more paths than steps: one
       counter-play had 163 distinct steps and 4,324,922 paths, and building
       its clauses grew the heap past five gigabytes, to be discarded by
       [key_copies] because no step mentioned a refined key.
       Every predicate of those clauses is a predicate [p] of some step's
       stated clause or of the query, or the fresh copy [p$N] of one, and a
       key copy is a predicate whose name has [k$] as a prefix for a refined
       key [k].  When for every such [p] and [k] neither of [p$] and [k$] is a
       prefix of the other, no [p] and no [p$N] has the prefix [k$] (were
       [k$] a prefix of [p$N], it would be a prefix of [p$] if not longer and
       have [p$] as a prefix otherwise), so no key copy exists and the result
       is the one [key_copies] computes from the built clauses.  Linear in the
       distinct steps; when it answers [true] the clauses are built only if
       the lifted play asks for them. *)
    let no_key_copy, distinct_steps =
      let hres, query, _ = let_mp cex in
      let keys =
        Set.Poly.map (Set.union orig_keys_wf orig_keys_fn) ~f:(fun k ->
            Ident.name_of_tvar k ^ "$")
      in
      let seen = StepTbl.create 256 in
      let names = Hash_set.create (module String) in
      let add_pvs phi =
        Set.iter (Formula.pvs_of phi) ~f:(fun p ->
            Hash_set.add names (Ident.name_of_pvar p ^ "$"))
      in
      let rec walk h =
        if not (StepTbl.mem seen h) then (
          StepTbl.replace seen h ();
          let clause, hress, _ = let_hyper_res h in
          add_pvs clause;
          List.iter hress ~f:walk)
      in
      walk hres;
      add_pvs query;
      ( not
          (Hash_set.exists names ~f:(fun n ->
               Set.exists keys ~f:(fun k ->
                   String.is_prefix n ~prefix:k || String.is_prefix k ~prefix:n))),
        StepTbl.length seen )
    in
    let expanded =
      lazy
      (Common.PhaseTime.with_phase "mustrat-cex-to-chc" @@ fun () ->
      let hres, query, _ = let_mp cex in
      let ren, query =
        let ant, con, _ = Formula.let_imply query in
        let pvs = Formula.pvs_of ant in
        let ren =
          Map.of_set_exn
          @@ Set.Poly.map pvs ~f:(fun pvar ->
              ( pvar,
                Ident.mk_fresh_pvar
                  ~prefix:(Some (Ident.name_of_pvar pvar ^ "$"))
                  () ))
        in
        (ren, Formula.mk_imply (Formula.rename_pvars ren ant) con)
      in
      let cs, model = analyze_cex hres ren in
      let cs = Set.add cs query in
      let model =
        Set.Poly.map model ~f:(fun phi ->
            let pvar, _sorts, ts, _ =
              Atom.let_pvar_app @@ fst @@ Formula.let_atom phi
            in
            (pvar, List.map ~f:Logic.ExtTerm.of_old_term ts))
      in
      let params =
        PCSP.Params.make @@ Logic.of_old_sort_env_map @@ Map.of_set_exn
        @@ Set.concat_map cs
             ~f:(Formula.pred_sort_env_of >> Term.pred_to_sort_env)
      in
      let pairs_of =
        Set.Poly.map ~f:(fun phi ->
            let senv, phi = Formula.rm_quant ~forall:true phi in
            (Map.of_set_exn senv, phi))
      in
      (* [refine_counter_play = Lifted_free_goal]: the same clauses with the
         goal instance generalised -- every ground argument of an atom of the
         (renamed) query replaced by a fresh variable, universally quantified
         -- or [None] when the query has no ground argument.  The query is the
         only clause of the play with no head, and its atoms are premises, so
         the generalised set states the derivation's shape at every goal
         instance rather than at the one the CHC backend chose; the clause
         set read with the original goal is an instance of it. *)
      let general =
        lazy
          (let renamed = Map.Poly.data ren in
           let fresh = ref [] in
           let query' =
             Formula.map_atom query ~f:(function
               | Atom.App (Predicate.Var (p, sorts), ts, info)
                 when List.mem renamed p ~equal:Ident.pvar_equal ->
                   let ts =
                     List.map2_exn ts sorts ~f:(fun t s ->
                         if Set.is_empty (Term.tvs_of t) then (
                           let v = Ident.mk_fresh_tvar () in
                           fresh := (v, s) :: !fresh;
                           Term.mk_var v s)
                         else t)
                   in
                   Formula.mk_atom (Atom.mk_pvar_app ~info p sorts ts)
               | atm -> Formula.mk_atom atm)
           in
           if List.is_empty !fresh then None
           else
             Some
               (PCSP.Problem.of_old_formulas ~params
                  (Set.add (pairs_of cs)
                     ( Map.force_merge
                         (Map.Poly.of_alist_exn !fresh)
                         (fst (Formula.rm_quant ~forall:true query')
                         |> Map.of_set_exn),
                       snd (Formula.rm_quant ~forall:true query') ))))
      in
      (PCSP.Problem.of_old_formulas ~params (pairs_of (Set.add cs query)), model,
       general))
    in
    if not no_key_copy then
      Debug.print
      @@ lazy
           (sprintf "## cex in CHCs:\n%s\n"
           @@ PCSP.Problem.str_of (Tuple3.get1 (Lazy.force expanded)));
    let raw_problem = Lazy.map expanded ~f:Tuple3.get1 in
    { play; no_key_copy; distinct_steps; expanded; raw_problem }

  (* The copies of refined keys among the predicates of the clauses read off
     a counter-play: [keys_wf] the copies [k$N] of a ranked key, [keys_fn]
     those of a Skolem key, and [senv_problem] their sorts.  A copy is a
     predicate whose name has [k$] as a prefix. *)
  type copies = {
    keys_wf : Ident.tvar Set.Poly.t;
    keys_fn : Ident.tvar Set.Poly.t;
    senv_problem : Logic.sort_env_map;
  }

  (* [key_copies ~orig_keys_wf ~orig_keys_fn r]: the copies in [r]'s
     clauses.  Pre: the keys are the ones [r] was read against.  Post: all
     three empty when [r.no_key_copy] (the clauses are then not built);
     otherwise read off the built clauses, forcing them. *)
  let key_copies ~orig_keys_wf ~orig_keys_fn r =
    let { no_key_copy; expanded; _ } = r in
    let problem_senv () =
      if no_key_copy then Map.Poly.empty
      else PCSP.Problem.senv_of (Tuple3.get1 (Lazy.force expanded))
    in
    let wf_senv_problem =
      Map.Poly.filter_keys (problem_senv ()) ~f:(fun x ->
          Set.exists orig_keys_wf ~f:(fun key ->
              String.is_prefix (Ident.name_of_tvar x)
                ~prefix:(Ident.name_of_tvar key ^ "$")))
    in
    let keys_wf = Map.Poly.key_set wf_senv_problem in
    let fn_senv_problem =
      Map.Poly.filter_keys (problem_senv ()) ~f:(fun x ->
          Set.exists orig_keys_fn ~f:(fun key ->
              String.is_prefix (Ident.name_of_tvar x)
                ~prefix:(Ident.name_of_tvar key ^ "$")))
    in
    let keys_fn = Map.Poly.key_set fn_senv_problem in
    let senv_problem = Map.force_merge wf_senv_problem fn_senv_problem in
    { keys_wf; keys_fn; senv_problem }

  (* [refinement_clauses ~preprocess r c]: the clauses a refinement problem
     is built from, [r]'s clauses simplified by [preprocess ~keep] with the
     key copies [c] kept.
     Pre: [c] is [key_copies] of [r]; [preprocess ~keep p] returns [p]
     simplified with every predicate of [keep] kept, in clausal form.
     Post: in clausal form; the empty clause set (with [r]'s parameters when
     its clauses were built, none otherwise) when [c] has no copy, in which
     case the clauses are neither built nor preprocessed here. *)
  let refinement_clauses ~preprocess r c =
    let { raw_problem; distinct_steps; _ } = r in
    let { senv_problem; _ } = c in
    (* When the counter-play holds no copy of a refined key, its clauses are
       not preprocessed: the empty clause set is what preprocessing would
       hand to the refinement's [build_pfwcsp], up to clauses that it drops.
       The counter-play's clauses are a derivation in which each node's
       predicate is a fresh name with one defining clause (its premises'
       names are fresh in turn), so the dependency graph is a tree and has
       no cycle.  Resolution at an unbounded threshold with nothing
       protected then eliminates every predicate, and each clause left
       mentions no predicate.  [build_pfwcsp] keeps a clause only when it
       has a negative atom or a positive atom that is not a key copy, so it
       drops every such clause, and the problem it builds from the
       counter-play is empty either way.  On a counter-play of a few
       thousand clauses the preprocessing took over a minute to return a
       single [false]. *)
    (* [raw_problem], the clauses read off the counter-play, is built only
       when read: here when some key copy exists, and by the lifted play.
       Without a key copy, [problem] is the empty clause set, of which
       [build_pfwcsp] reads only the clauses, so its parameters are left
       empty. *)
    let problem =
      if Map.Poly.is_empty senv_problem then (
        Debug.print
        @@ lazy
             (if Lazy.is_val raw_problem then
                sprintf
                  "## the counter-play holds no copy of a refined key: its %d \
                   clause(s) are not preprocessed"
                  (Set.length
                     (PCSP.Problem.formulas_of (Lazy.force raw_problem)))
              else
                sprintf
                  "## the counter-play holds no copy of a refined key: its \
                   clauses (%d distinct step(s)) are not built"
                  distinct_steps);
        (* in clausal form, as preprocessing returns it: [build_pfwcsp]
           reads the clauses with [clauses_of], which refuses a problem
           that is not in clausal form, an empty one included *)
        PCSP.Problem.of_clauses
          ~params:
            (if Lazy.is_val raw_problem then
               PCSP.Problem.params_of (Lazy.force raw_problem)
             else PCSP.Params.make Map.Poly.empty)
          Set.Poly.empty)
      else
        Common.PhaseTime.with_phase "mustrat-cex-preprocess" @@ fun () ->
        preprocess ~keep:(Map.Poly.key_set senv_problem)
          (Lazy.force raw_problem)
    in
    Debug.print
    @@ lazy
         (sprintf "## preprocessed cex in CHCs:\n%s\n"
         @@ PCSP.Problem.str_of problem);
    problem

  (* [lifted_source r]: the clauses a selection on the lifted play reads,
     with whether they are the generalised-goal ones.  Under
     [refine_counter_play = Lifted_free_goal], the clauses with the goal
     instance generalised when the query has a ground argument ([true]);
     otherwise [r]'s clauses ([false]).  Forces the clauses. *)
  let lifted_source r =
    let { expanded; raw_problem; _ } = r in
      match
        if Config.frees_goal config.refine_counter_play then
          Lazy.force (Tuple3.get3 (Lazy.force expanded))
        else None
      with
      | Some general -> (general, true)
      | None -> (Lazy.force raw_problem, false)

  (* The lifted play's clauses, for a selection that keeps each checked-side
     value a variable: [single] the tags (predicates [T$N] that
     [FreedValues] drew) defined by exactly one ground fact [T(c)], with its
     arguments [c]; [pinned] each such tag's definition as the relation
     [v = c] over fresh parameters; [extra_fn] each such tag's sort, for the
     build to declare it an unknown of kind [FN]; [lifted_raw] the clauses
     with each such fact [T(c)] replaced by the universal fact [T(v)], other
     facts and clauses unchanged. *)
  type lifted = {
    single : (Ident.tvar, Logic.term list) Map.Poly.t;
    pinned : (Ident.tvar, Logic.term) Map.Poly.t;
    extra_fn : Logic.sort_env_map;
    lifted_raw : PCSP.Problem.t;
  }

  (* [lift_tags src]: the lifted play of the clauses [src] (see [lifted]),
     or [None] (traced) when no tag is defined by a single ground fact.
     Pre: [src] is read off a counter-play ([lifted_source]).  Post:
     [lifted_raw] has [src]'s parameters; [single], [pinned] and [extra_fn]
     have the same keys, each a tag of [src].  Pure apart from the trace. *)
  let lift_tags src =
    let tag_copy x =
      match String.rsplit2 (Ident.name_of_tvar x) ~on:'$' with
      | Some (base, _) -> FreedValues.is_tag base
      | None -> false
    in
    let raw_senv = PCSP.Problem.senv_of src in
    (* a fact reads [true => T(c)] *)
    let head_of phi =
      match phi with
      | Logic.App
          ( Logic.App (Logic.Con (Logic.BoolTerm.Imply, _), lhs, _),
            rhs,
            _ )
        when Logic.BoolTerm.is_true lhs ->
          rhs
      | _ -> phi
    in
    let ground_fact (_, phi) =
      let phi = head_of phi in
      Logic.Term.is_var_app phi
      && tag_copy (Logic.Term.pvar_of_atom phi)
      &&
      let _, args = Logic.Term.let_var_app phi in
      List.for_all args ~f:(fun a ->
          Set.is_empty (Logic.Term.fvs_of a))
    in
    let facts, rest =
      Set.partition_tf
        (PCSP.Problem.formulas_of src)
        ~f:ground_fact
    in
    let by_tag =
      Set.fold facts ~init:Map.Poly.empty ~f:(fun m (_, phi) ->
          let x, args = Logic.Term.let_var_app (head_of phi) in
          Map.Poly.add_multi m ~key:x ~data:args)
    in
    let single =
      Map.Poly.filter_map by_tag ~f:(function
        | [ args ] -> Some args
        | _ -> None)
    in
    if Map.Poly.is_empty single then (
      Debug.print
      @@ lazy
           (sprintf
              "## the lifted play: no checked-side value is a \
               single ground fact (%d tag fact(s))"
              (Set.length facts));
      None)
    else
      let params_of key =
        Logic.sort_env_list_of_sorts
          (Logic.Sort.args_of (Map.Poly.find_exn raw_senv key))
      in
      let extra_fn =
        Map.Poly.mapi single ~f:(fun ~key ~data:_ ->
            Map.Poly.find_exn raw_senv key)
      in
      let pinned =
        Map.Poly.mapi single ~f:(fun ~key ~data:args ->
            let params = params_of key in
            Logic.Term.mk_lambda params
              (Logic.BoolTerm.and_of
                 (List.map2_exn params args ~f:(fun (v, s) a ->
                      Logic.BoolTerm.eq_of s (Logic.Term.mk_var v)
                        a))))
      in
      let kept_facts =
        Set.filter facts ~f:(fun (_, phi) ->
            not
              (Map.Poly.mem single
                 (Logic.Term.pvar_of_atom (head_of phi))))
      in
      let univ_facts =
        Map.Poly.fold single ~init:Set.Poly.empty
          ~f:(fun ~key ~data:_ acc ->
            let params = params_of key in
            Set.add acc
              ( Map.Poly.of_alist_exn params,
                Logic.Term.mk_var_app key
                  (List.map params ~f:(fst >> Logic.Term.mk_var)) ))
      in
      let lifted_raw =
        PCSP.Problem.of_formulas
          ~params:(PCSP.Problem.params_of src)
          (Set.Poly.union_list [ rest; kept_facts; univ_facts ])
      in
      Some { single; pinned; extra_fn; lifted_raw }

  (* [play_exceeds ~is_opponent ~bound cex]: whether the derivation [cex]
     (an [mp]/[hyper-res] proof term of a check) concludes, at some step, an
     atom of a predicate whose name [is_opponent] accepts with an integer
     literal of absolute value above [bound] as its last argument -- for an
     opponent's Skolem key, a free choice played beyond the bound.  A step
     whose argument is not a literal is not counted.  Each distinct step
     (physically the same proof term) is read once, so the cost is linear in
     the distinct steps: a derivation is a DAG, and one the ground split
     derives can share its steps so heavily that its unfolding as a tree has
     about 2 * 10^12 nodes over 1,305 distinct steps, which a path-by-path
     walk never finished.  Raises as the readers of a proof term do on a term
     not of that shape; the caller treats a raise as [false]. *)
  let play_exceeds ~is_opponent ~bound cex =
    let open Ast.LogicOld in
    let seen = StepTbl.create 256 in
    let rec go hres =
      if StepTbl.mem seen hres then false
      else (
        StepTbl.replace seen hres ();
        let _, hress, con = let_hyper_res hres in
        (match con with
        | Formula.Atom
            (Atom.App (Predicate.Var (Ident.Pvar name, _), args, _), _)
          when is_opponent name -> (
            match List.last args with
            | Some t when T_int.is_int t ->
                Z.gt (Z.abs (T_int.let_int t)) bound
            | _ -> false)
        | _ -> false)
        || List.exists hress ~f:go)
    in
    try
      let hres, _, _ = let_mp cex in
      go hres
    with exn when not (Common.Timer.is_async exn) -> false

  (* [play_outliers ~is_opponent ~bound cex]: for each free choice of the
     opponent that the derivation [cex] (an [mp]/[hyper-res] proof term of a
     check) plays beyond [bound] -- a derived atom of a predicate
     [is_opponent] accepts whose last argument is an integer literal [r] with
     [|r| > bound] -- the pair [(|r|, m)], where [m] is the largest absolute
     value of an integer literal among the atom's other arguments, or [None]
     when it has none.  The other arguments of an opponent's Skolem key are
     the state at which the opponent chooses (the universals in the key's
     scope), so [m] is how far the play had gone when the choice was made.
     The rest of the derivation is not read for this: the derivations the
     check's solver returns put the continuation of the play, which may carry
     the chosen value, among the premises of the step that uses the choice,
     so no subtree is "before" the choice by its position alone.  A step whose
     result is not a literal is not counted.  Each distinct step (physically
     the same proof term) is read once, so a step shared by several paths
     contributes its pair once and the cost is linear in the distinct steps
     (see [play_exceeds] for the derivation that made a path-by-path walk
     exponential); the only reader, [isolated_outlier], asks whether some
     pair qualifies, which multiplicity does not change.  Raises as the
     readers of a proof term do on a term not of that shape; the caller
     treats a raise as no outlier ([]).  It only reads; the result decides
     whether one more question is asked, never a verdict. *)
  let play_outliers ~is_opponent ~bound cex =
    let open Ast.LogicOld in
    let lits_of args =
      List.filter_map args ~f:(fun t ->
          if T_int.is_int t then Some (Z.abs (T_int.let_int t)) else None)
    in
    let max_of =
      List.fold ~init:None ~f:(fun acc z ->
          match acc with None -> Some z | Some m -> Some (Z.max m z))
    in
    let seen = StepTbl.create 256 in
    let found = ref [] in
    let rec go hres =
      if not (StepTbl.mem seen hres) then (
        StepTbl.replace seen hres ();
        let _, hress, con = let_hyper_res hres in
        (match con with
        | Formula.Atom
            (Atom.App (Predicate.Var (Ident.Pvar name, _), args, _), _)
          when is_opponent name -> (
            match List.rev args with
            | t :: rest when T_int.is_int t ->
                let r = Z.abs (T_int.let_int t) in
                if Z.gt r bound then
                  found := (r, max_of (lits_of rest)) :: !found
            | _ -> ())
        | _ -> ());
        List.iter hress ~f:go)
    in
    try
      let hres, _, _ = let_mp cex in
      go hres;
      List.rev !found
    with exn when not (Common.Timer.is_async exn) -> []

  (* [isolated_outlier outliers]: whether one choice of [play_outliers] alone
     takes the play beyond the bound: its value exceeds every value of the
     state at which it is made, and that state has at least one integer
     value.  On a program that guards a large capacity, one choice from a
     state of small values crosses the guard; on a game whose positions are
     compared with each other, and with no literal beyond 1, the choices
     beyond the bound are the starting positions, made at no state, and do
     not qualify.  "Exceeds" is [r > f * m] for the factor
     [f = isolated_outlier_factor] (at least 1): with [f = 1] a choice one
     past both a small bound and its state (the next value of a counter,
     [4] at a state of at most [3] under a bound of [3]) qualifies as well,
     and the bounded play read in its place can be a longer play whose
     refinement is a larger synthesis problem; with [f = 2] the choice must
     more than double every value of its state, which the capacity choice
     ([2^30 + 1] at a state of at most [16]) does and a counter's next value
     does not.  Only whether one more question is asked depends on it. *)
  let isolated_outlier outliers =
    let f = Z.of_int (Int.max 1 config.Config.isolated_outlier_factor) in
    List.exists outliers ~f:(function
      | r, Some m -> Z.gt r (Z.mul f m)
      | _, None -> false)
end
