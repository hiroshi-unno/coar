(* Elimination of determined variables from a clause's pure part, over the
   higher-order term language [Logic].  Despite the module's name this is not
   quantifier elimination (that is [Z3interface.qelim]): the formula is read
   as a disjunction under the universal closure of its free variables, and a
   variable a disjunct determines is substituted away -- [x != t \/ C(x)]
   becomes [C(t)], a class of variables that disjuncts [x != y] identify
   becomes one variable, and a disjunct [x != c] for a constant fixes [x].
   Each step is exact for the universal closure in every model.

   [elim_free_univ_vars bounds exi_senv (uni_senv, defs, phi)] is the entry
   point: it never eliminates a variable of [bounds], of [exi_senv] (the
   unknowns) or a let-bound one, threads [defs] (the definitions of enclosing
   lets) through the same substitution, and returns the sort environment
   restricted to the variables still free.  It assumes [phi] alpha-renamed
   and let-normalised.  With [~simplify] (the default) the result is also
   simplified, which dominates its cost. *)
open Core
open Common.Ext
open Common.Combinator
open Logic

let eqcs_of ?(only_bvs = None) phi =
  let eqcs, phis =
    List.partition_map (BoolTerm.disjuncts_of phi) ~f:(fun phi ->
        if BoolTerm.is_not phi then
          match Term.let_apps (BoolTerm.let_not phi) with
          | TyApp (Con (BoolTerm.Eq, _), ty, _), [ Var (x1, _); Var (x2, _) ]
            when match only_bvs with
                 | None -> true
                 | Some bvs -> Set.mem bvs x1 && Set.mem bvs x2 ->
              First (Set.Poly.of_list [ x1; x2 ], ty)
          | _ -> Second phi
        else
          match Term.let_apps phi with
          | TyApp (Con (BoolTerm.Neq, _), ty, _), [ Var (x1, _); Var (x2, _) ]
            when match only_bvs with
                 | None -> true
                 | Some bvs -> Set.mem bvs x1 && Set.mem bvs x2 ->
              First (Set.Poly.of_list [ x1; x2 ], ty)
          | _ -> Second phi)
  in
  let eqcs' =
    fix (Set.Poly.of_list eqcs)
      ~f:
        (Set.fold ~init:Set.Poly.empty ~f:(fun eqcs (eqc2, ty2) ->
             let updated = ref false in
             let eqcs' =
               Set.Poly.map eqcs ~f:(fun (eqc1, ty1) ->
                   if not @@ Set.are_disjoint eqc2 eqc1 then (
                     updated := true;
                     (Set.union eqc1 eqc2, ty1))
                   else (eqc1, ty1))
             in
             if !updated then eqcs' else Set.add eqcs (eqc2, ty2)))
      ~equal:Set.eqlen
  in
  (eqcs', phis)

let elim_eqcls let_bounds bounds (uni_senv, defs, phi) =
  let eqcs, phis1 = eqcs_of phi in
  let sub, phis2 =
    Set.Poly.map eqcs ~f:(fun (eqc, ty) ->
        let bvs, fvs = Set.partition_tf ~f:(Map.Poly.mem bounds) eqc in
        match (Set.to_list bvs, Set.to_list fvs) with
        | [], fv :: fvs' ->
            let tt = Term.mk_var fv in
            (List.map fvs' ~f:(fun x -> (x, tt)), [])
        | (bv :: bvs' as bvs), fvs -> (
            match List.find bvs ~f:(Fn.non @@ Map.Poly.mem let_bounds) with
            | None -> (
                match fvs with
                | [] ->
                    let tt = Term.mk_var bv in
                    ( [],
                      List.map (fvs @ bvs') ~f:(fun x ->
                          BoolTerm.neq_of ty tt (Term.mk_var x)) )
                | fv :: fvs' ->
                    let tt = Term.mk_var fv in
                    ( List.map fvs' ~f:(fun x -> (x, tt)),
                      List.map bvs ~f:(fun x ->
                          BoolTerm.neq_of ty tt (Term.mk_var x)) ))
            | Some bv ->
                let bvs' = List.filter bvs ~f:(Stdlib.( <> ) bv) in
                let tt = Term.mk_var bv in
                ( List.map fvs ~f:(fun x -> (x, tt)),
                  List.map bvs' ~f:(fun x ->
                      BoolTerm.neq_of ty tt (Term.mk_var x)) ))
        | _, _ -> assert false)
    |> Set.to_list |> List.unzip
    |> Tuple2.map_both ~f1:List.concat ~f2:List.concat
  in
  let sub = Map.Poly.of_alist_exn sub in
  ( uni_senv,
    List.map defs ~f:(Term.subst sub),
    Term.subst sub @@ BoolTerm.or_of @@ phis1 @ phis2 )

let consts_of bounds phi =
  match Term.let_apps phi with
  | Var (x, _), [] ->
      if Map.Poly.mem bounds x then Second phi
      else First (x, BoolTerm.False, BoolTerm.SBool)
  | Con (BoolTerm.Not, _), [ Var (x, _) ] ->
      if Map.Poly.mem bounds x then Second phi
      else First (x, BoolTerm.True, BoolTerm.SBool)
  | ( TyApp (Con (BoolTerm.Neq, _), ty, _),
      ([ Var (x, _); Con (sym, _) ] | [ Con (sym, _); Var (x, _) ]) ) ->
      if Map.Poly.mem bounds x then Second phi else First (x, sym, ty)
  | ( TyApp (Con (BoolTerm.Eq, _), ty, _),
      ( [ Var (x, _); Con (BoolTerm.True, _) ]
      | [ Con (BoolTerm.True, _); Var (x, _) ] ) ) ->
      if Map.Poly.mem bounds x then Second phi else First (x, BoolTerm.False, ty)
  | ( TyApp (Con (BoolTerm.Eq, _), ty, _),
      ( [ Var (x, _); Con (BoolTerm.False, _) ]
      | [ Con (BoolTerm.False, _); Var (x, _) ] ) ) ->
      if Map.Poly.mem bounds x then Second phi else First (x, BoolTerm.True, ty)
  | _ -> Second phi

let elim_consts bounds (uni_senv, defs, phi) =
  let cm, phis1 =
    List.map (BoolTerm.disjuncts_of phi) ~f:BoolTerm.nnf_of
    |> List.partition_map ~f:(consts_of bounds)
  in
  try
    let sub =
      List.fold ~init:Map.Poly.empty cm ~f:(fun acc (x, sym, _ty) ->
          Map.force_add acc x (Term.mk_con sym))
    in
    ( uni_senv,
      List.map defs ~f:(Term.subst sub),
      Term.subst sub @@ BoolTerm.or_of phis1 )
  with exn_ when not (Common.Timer.is_async exn_) ->
    (uni_senv, [], BoolTerm.mk_bool true)

let reduce (uni_senv, defs, body) =
  let fvs = Set.Poly.union_list @@ List.map ~f:Term.fvs_of (body :: defs) in
  (Map.Poly.filter_keys uni_senv ~f:(Set.mem fvs), defs, body)

let rec qelim_aux1 let_bounds bounds exi_senv (uni_senv, defs, phi) =
  let uni_senv', defs', phi' =
    let bounds' = Map.force_merge_list [ exi_senv; let_bounds; bounds ] in
    (uni_senv, defs, phi) |> elim_consts bounds'
    |> elim_eqcls let_bounds bounds'
    |> elim_consts bounds' |> reduce
  in
  if Map.Poly.length uni_senv > Map.Poly.length uni_senv' then
    qelim_aux1 let_bounds bounds exi_senv (uni_senv', defs', phi')
  else (uni_senv', defs', phi')

let qelim_aux2 let_bounds bounds exi_senv (uni_senv, defs, phi0) =
  let bounds' = Map.force_merge_list [ exi_senv; let_bounds; bounds ] in
  let has_no_inter x s =
    (not @@ Set.mem s x) && Set.are_disjoint (Map.key_set let_bounds) s
  in
  let solve_neq (t1, t2) =
    match (t1, t2) with
    | Var (x, _), t
      when (not (Map.Poly.mem bounds' x)) && has_no_inter x (Term.fvs_of t) ->
        Some (x, t)
    | t, Var (x, _)
      when (not (Map.Poly.mem bounds' x)) && has_no_inter x (Term.fvs_of t) ->
        Some (x, t)
    (* for integers *)
    | App (App (Con ((IntTerm.(Add | Sub) as s), _), Var (x, _), _), t1, _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
    | t2, App (App (Con ((IntTerm.(Add | Sub) as s), _), Var (x, _), _), t1, _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
    | App (App (Con ((IntTerm.Add as s), _), t1, _), Var (x, _), _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
    | t2, App (App (Con ((IntTerm.Add as s), _), t1, _), Var (x, _), _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (IntTerm.neg_sym s) [ t2; t1 ])
    | App (App (Con ((IntTerm.Sub as s), _), t1, _), Var (x, _), _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app s [ t1; t2 ])
    | t2, App (App (Con ((IntTerm.Sub as s), _), t1, _), Var (x, _), _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app s [ t1; t2 ])
    (* for reals *)
    | ( App (App (Con ((RealTerm.(RAdd | RSub) as s), _), Var (x, _), _), t1, _),
        t2 )
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
    | ( t2,
        App (App (Con ((RealTerm.(RAdd | RSub) as s), _), Var (x, _), _), t1, _)
      )
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
    | App (App (Con ((RealTerm.RAdd as s), _), t1, _), Var (x, _), _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
    | t2, App (App (Con ((RealTerm.RAdd as s), _), t1, _), Var (x, _), _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app (RealTerm.neg_sym s) [ t2; t1 ])
    | App (App (Con ((RealTerm.RSub as s), _), t1, _), Var (x, _), _), t2
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app s [ t1; t2 ])
    | t2, App (App (Con ((RealTerm.RSub as s), _), t1, _), Var (x, _), _)
      when (not (Map.Poly.mem bounds' x))
           && has_no_inter x (Set.union (Term.fvs_of t1) (Term.fvs_of t2)) ->
        Some (x, Term.mk_sym_app s [ t1; t2 ])
    | _ -> None
  in
  (* The candidate elimination one disjunct yields, if any.  Everything this
     reads besides the disjunct -- [bounds'], [let_bounds], [exi_senv] -- is
     fixed for the whole call except [merged], the sort environment the
     fallback simplifies in. *)
  let cand_of merged phi =
    match Term.let_apps phi with
    | TyApp (Con (BoolTerm.Neq, _), ty, _), [ t1; t2 ] -> (
        match solve_neq (t1, t2) with
        | Some _ as res -> res
        | None when IntTerm.is_int_sort ty || RealTerm.is_real_sort ty -> (
            (* [Normalizer] emits linear combinations such as
                     [1 + x + -1 * y != 0], which none of the patterns above
                     matches; simplifying both sides first turns them back into
                     the [(1 + x) - y] shape that they do match. *)
            try
              let simplify = ExtTerm.simplify_term exi_senv merged in
              solve_neq (simplify t1, simplify t2)
            with exn_ when not (Common.Timer.is_async exn_) -> None)
        | None -> None)
    | TyApp (Con (BoolTerm.Eq, _), BoolTerm.SBool, _), [ t1; t2 ] -> (
        match (t1, t2) with
        | Var (x, _), t
          when (not (Map.Poly.mem bounds' x)) && has_no_inter x (Term.fvs_of t)
          ->
            Some (x, BoolTerm.neg_of t)
        | t, Var (x, _)
          when (not (Map.Poly.mem bounds' x)) && has_no_inter x (Term.fvs_of t)
          ->
            Some (x, BoolTerm.neg_of t)
        | _ -> None)
    | _ -> None
  in
  (* Each disjunct is carried with the candidate it yields, and only the
     disjuncts a round actually changes are re-examined.  The candidate is a
     function of the disjunct and of the sort environment, and a round changes
     neither for a disjunct the eliminated variable does not occur in: it is
     not substituted, and the only change to the environment is the removal of
     that same variable, which by then occurs nowhere.  Counted on one
     `LinearArbitrary` file before this: 996,815 examinations across 25,249
     rounds, of which 922,328 reached the fallback that simplifies both sides
     of a disequality -- almost all of the search, repeated on disjuncts that
     had not changed since the round before. *)
  let rec loop uni_senv defs phis_c =
    let res = List.find_map phis_c ~f:snd in
    let res =
      match res with
      | Some (x, t) -> Some (x, t)
      | None ->
          (* the disjuncts without their candidates.  Taken here and at the exit
             below rather than at the top of the loop: the search above reads
             only the candidates, so projecting the pair rebuilt a list of every
             disjunct on every round -- 25,249 rebuilds of a 78-element list on
             one `LinearArbitrary` file -- to serve the 613 rounds that reach
             this branch, one per call. *)
          let phis = List.map ~f:fst phis_c in
          List.filter_map phis ~f:(fun phi ->
              match
                List.map
                  (BoolTerm.conjuncts_of phi)
                  ~f:(consts_of Map.Poly.empty)
              with
              | [
               First (x1, sym1, BoolTerm.SBool); First (x2, sym2, BoolTerm.SBool);
              ]
                when Stdlib.(x1 <> x2) ->
                  Some (x1, sym1, x2, sym2)
              | _ -> None)
          |> List.find_distinct_pair
               ~f:(fun (x11, sym11, x12, sym12) (x21, sym21, x22, sym22) ->
                 if
                   Stdlib.(
                     (x11 = x21 && x12 = x22 && sym11 <> sym21)
                     || (x11 = x22 && x12 = x21 && sym11 <> sym22))
                 then
                   if Stdlib.(sym11 = sym12 && sym21 = sym22) then
                     if
                       (not (Map.Poly.mem bounds' x11))
                       && not (Map.Poly.mem let_bounds x12)
                     then Some (x11, BoolTerm.neg_of @@ Term.mk_var x12)
                     else if
                       (not (Map.Poly.mem bounds' x12))
                       && not (Map.Poly.mem let_bounds x11)
                     then Some (x12, BoolTerm.neg_of @@ Term.mk_var x11)
                     else None
                   else if Stdlib.(sym11 <> sym12 && sym21 <> sym22) then
                     if
                       (not (Map.Poly.mem bounds' x11))
                       && not (Map.Poly.mem let_bounds x12)
                     then Some (x11, Term.mk_var x12)
                     else if
                       (not (Map.Poly.mem bounds' x12))
                       && not (Map.Poly.mem let_bounds x11)
                     then Some (x12, Term.mk_var x11)
                     else None
                   else None
                 else None)
    in
    match res with
    | Some (x, t) ->
        let uni_senv' = Map.Poly.remove uni_senv x in
        let sub =
          Map.Poly.singleton x @@ ExtTerm.simplify_term exi_senv uni_senv' t
        in
        if false then
          print_endline
          @@ sprintf "[qelim_aux2] %s ==> %s" (Ident.name_of_tvar x)
               (ExtTerm.str_of t);
        (* Substitute only into the terms the eliminated variable occurs in.
           This loop removes one variable per round and then rewrites every
           definition and every disjunct, and the rewriter rebuilds a term node
           by node whether or not anything under it changed -- so a term that
           cannot mention the variable is copied in full for nothing.  Counted
           on one `LinearArbitrary` file: 1,933,549 terms rewritten across
           25,249 rounds, of which 49,255 (2.5%) mention the variable being
           eliminated and **none** came back physically equal to its input.
           The occurrence test stops at the first hit and builds no set, where
           asking for the free variables would build one per term per round. *)
        let subst_if_occurs t =
          if Term.occurs_free x t then Term.subst sub t else t
        in
        let merged' = Map.force_merge let_bounds uni_senv' in
        let step (t, c) =
          if Term.occurs_free x t then
            (* the sharing-preserving substitution rebuilds only the path down to
               the occurrences, where the ordinary one rebuilds every node and
               renames every binder it passes; the term is kept for the next
               round, so what it leaves shared is what the next round skips *)
            let t' = Term.subst_sharing sub t in
            (t', cand_of merged' t')
          else (t, c)
        in
        loop uni_senv'
          (List.map ~f:subst_if_occurs defs)
          (List.map ~f:step phis_c)
    | None -> (uni_senv, defs, List.map ~f:fst phis_c)
  in
  let uni_senv, defs, phis =
    let merged = Map.force_merge let_bounds uni_senv in
    loop uni_senv defs
      (List.map
         (List.map ~f:BoolTerm.nnf_of (BoolTerm.disjuncts_of phi0))
         ~f:(fun phi -> (phi, cand_of merged phi)))
  in
  (uni_senv, defs, BoolTerm.or_of phis)

let print_log = false

(* An instrument, read once: with [COAR_QELIM_GROWTH] set, every call of
   [app_qelim] whose result is more than four times its input as a tree, or that
   takes more than a second of CPU time, prints one line to stderr with the input's and the
   results' tree sizes (each counted up to ten million nodes) and the result's
   size as a DAG of physically distinct nodes.  It changes nothing it measures. *)
let growth_trace = Option.is_some (Sys.getenv "COAR_QELIM_GROWTH")

(* the number of physically distinct nodes of [t], up to [cap + 1] *)
let dag_size_up_to cap t =
  let seen : (int, term list) Stdlib.Hashtbl.t = Stdlib.Hashtbl.create 1024 in
  let n = ref 0 in
  let exception Over in
  let rec go t =
    let h = Stdlib.Hashtbl.hash_param 30 60 t in
    let bucket = Option.value ~default:[] (Stdlib.Hashtbl.find_opt seen h) in
    if not (List.exists bucket ~f:(phys_equal t)) then (
      Stdlib.Hashtbl.replace seen h (t :: bucket);
      incr n;
      if !n > cap then raise Over;
      match t with
      | Var _ | Con _ -> ()
      | App (t1, t2, _) | Let (_, _, t1, t2, _) ->
          go t1;
          go t2
      | Bin (_, _, _, t1, _) | TyApp (t1, _, _) | TyLam (_, t1, _) -> go t1)
  in
  try
    go t;
    !n
  with Over -> cap + 1

let report_growth ~started phi phi2 phi3 =
  let cap = 10_000_000 in
  let secs = Stdlib.Sys.time () -. started in
  let s_in = Term.ast_size_up_to cap phi in
  let s3 = Term.ast_size_up_to cap phi3 in
  if Float.(secs > 1.0) || s3 > 4 * s_in then
    Printf.eprintf "[qelim-growth] in=%d aux2=%d out=%d out_dag=%d secs=%.3f\n%!"
      s_in
      (Term.ast_size_up_to cap phi2)
      s3 (dag_size_up_to cap phi3) secs

let app_qelim ?(simplify = true) let_bounds bounds exi_senv (uni_senv, defs, phi)
    =
  let fvs =
    Set.diff (Term.fvs_of phi)
      (Map.key_set @@ Map.force_merge_list [ exi_senv; let_bounds; bounds ])
  in
  if Set.is_empty fvs then (
    if print_log then print_endline "[app_qelim] skipped";
    (uni_senv, defs, phi))
  else
    let started = if growth_trace then Stdlib.Sys.time () else 0. in
    let phi_in = phi in
    (
    if print_log then
      print_endline
      @@ sprintf "[app_qelim] begin eliminating %s in %s"
           (String.concat_map_set ~sep:", " ~f:Ident.name_of_tvar fvs)
           (LogicOld.Formula.str_of
           @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi);
    let uni_senv, defs, phi1 =
      qelim_aux1 let_bounds bounds exi_senv (uni_senv, defs, phi)
    in
    if print_log then print_endline "  [app_qelim] qelim_aux1";
    let uni_senv, defs, phi2 =
      qelim_aux2 let_bounds bounds exi_senv (uni_senv, defs, phi1)
    in
    if print_log then print_endline "  [app_qelim] qelim_aux2";
    let phi3 =
      if simplify then
        ExtTerm.simplify_formula exi_senv
          (Map.force_merge let_bounds uni_senv)
          phi2
      else phi2
    in
    (if print_log then
       let _fvs = Set.diff fvs (Term.fvs_of phi2) in
       print_endline
       @@ sprintf "[app_qelim] end: %s"
            (*(String.concat_map_set ~sep:", " ~f:Ident.name_of_tvar fvs)*)
            (LogicOld.Formula.str_of
            @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv phi2));
    if growth_trace then report_growth ~started phi_in phi2 phi3;
    (uni_senv, defs, phi3))

(* Eliminate the free variables of [defs] and [phi] that are *implicitly*
   universally quantified -- a clause's own variables, not the ones a [Bind]
   node quantifies.  The old name of this function was [qelim], which reads as
   quantifier elimination and is what [Z3interface.qelim] really does; on the
   solving path here the formula is quantifier-free at every call (838 of 838
   over three benchmarks) and what the function removes is variables an equality
   or a definition determines -- six universals became three on one measured
   resolvent.

   [~simplify], which defaults to [true], is not a tidying flag: the
   simplification it controls is where nearly all of the time goes, 18.0 s of a
   22.2 s resolution phase on one benchmark, so a caller that does not need it
   should say so.

   @param [bounds] variables that must not be eliminated.
   Assumes [phi] is alpha-renamed and let-normalized. *)
let rec elim_free_univ_vars ?(simplify = true) ?(let_bounds = Map.Poly.empty)
    bounds exi_senv (uni_senv, defs, phi) =
  match phi with
  | Let (var, sort, def, body, info) -> (
      let let_bounds' = Map.Poly.set ~key:var ~data:sort let_bounds in
      match
        elim_free_univ_vars ~simplify ~let_bounds:let_bounds' bounds exi_senv
          (Map.Poly.set uni_senv ~key:var ~data:sort, def :: defs, body)
      with
      | _, [], _ -> assert false
      | uni_senv_body, def' :: defs', body' ->
          let fvs_body = Term.fvs_of body' in
          if Set.mem fvs_body var then
            let uni_senv_body' = Map.Poly.remove uni_senv_body var in
            let uni_senv_def, _, def'' =
              reduce
              @@
              if BoolTerm.is_bool_sort sort then
                let bounds_def =
                  let senv = Map.force_merge exi_senv uni_senv_body' in
                  Set.fold
                    (Set.diff
                       (Set.Poly.union_list
                          (fvs_body :: List.map ~f:Term.fvs_of defs'))
                       (Map.key_set let_bounds'))
                    ~init:bounds
                    ~f:(fun acc tvar ->
                      Map.Poly.set ~key:tvar
                        ~data:(Map.Poly.find_exn senv tvar)
                        acc)
                in
                app_qelim ~simplify let_bounds bounds_def exi_senv
                  (uni_senv, [], def')
              else (uni_senv, [], def')
            in
            ( Map.force_merge uni_senv_def uni_senv_body',
              defs',
              Let (var, sort, def'', body', info) )
          else (uni_senv_body, defs', body'))
  | _ ->
      reduce
      @@ app_qelim ~simplify let_bounds bounds exi_senv (uni_senv, defs, phi)

(* [elim_free_univ_vars] on the first-order term representation, converting in
   and out; the conversion is 0.08 s of 18 on the benchmark above, so it is not
   where this costs *)
let elim_free_univ_vars_old ?(simplify = true) bounds exi_senv (uni_senv, phi) =
  let uni_senv', _, phi' =
    elim_free_univ_vars ~simplify bounds exi_senv
      (uni_senv, [], ExtTerm.of_old_formula phi)
  in
  (uni_senv', ExtTerm.to_old_fml exi_senv uni_senv' phi')

(* let rec qelim_clause exi_senv (uni_senv, ps, ns, phi) =
   let senv = Map.force_merge exi_senv uni_senv in
   let atms = Set.Poly.map (Set.union ps ns) ~f:(ExtTerm.to_old_atom senv) in
   let papp_tvs = of_old_sort_env_list @@ Set.to_list @@ Util.Set.concat_map atms ~f:LogicOld.Atom.term_sort_env_of in
   let bounds = (* this is essential for qualifiers extraction *) Map.force_merge (Map.Poly.of_alist_exn papp_tvs) exi_senv in
   let phi' =
     ExtTerm.simplify_formula senv (snd @@ g bounds @@ snd @@ f bounds phi)
   in
   let uni_senv', ps, ns, phi' = Clause.reduce_sort_map (uni_senv, ps, ns, phi') in
   if Map.Poly.length uni_senv > Map.Poly.length uni_senv' then
     qelim_clause exi_senv (uni_senv', ps, ns, phi')
   else (uni_senv', ps, ns, phi')

   let qelim_clause_set exi_senv = Set.Poly.map ~f:qelim_clause exi_senv *)
