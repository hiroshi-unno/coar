(* MuCyc's solver for prenex quantified formulas over one theory (QBF, linear
   real or integer arithmetic, or bit-vectors, each beside Booleans, with arrays
   and datatypes projected ahead of the arithmetic), by the game-based QSAT
   algorithm of Nikolaj Bjorner and Mikolas Janota, "Playing with Quantified
   Satisfaction" (LPAR-20, 2015): the two players alternate proposing models for
   their quantifier blocks, and a refuted move is generalised by model-based
   projection into a formula that strengthens the frame of the level it came
   from, until the outermost player wins or loses.

   [decide_theory] picks the projection module from the prefix's sorts (a prefix
   with a probabilistic quantifier is classified here and solved by a separate
   solver) and refuses, as an input the solver does not support, a prefix that
   mixes integers, reals and bit-vectors or quantifies over a sort no projection
   module covers.  [QSAT (A)].[solve] runs the search with projection module
   [A]; its options choose the backtracking strategy, which frames and atom sets
   a refutation updates, a substituted lemma (the refuted player's winning move
   replaced by witness terms chosen as in Farzan and Kincaid's strategy
   improvement, IJCAI 2016) in place of the projection at the innermost level,
   and a forward variant that refines candidates for the outermost block by
   instances of the matrix.  The answer is [SAT] when the formula is true and
   [UNSAT] when it is false. *)
open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

type theory = QBF | LRA | LIA | BV
type player = SAT | UNSAT

let decide_theory quantifiers =
  let sortlist =
    List.fold quantifiers ~init:[] ~f:(fun l (_binder, sortenv) ->
        let _, sort = List.unzip sortenv in
        l @ sort)
  in
  (* Pick the one theory whose model-based projection will eliminate every
     quantified variable.  The projection loop sends Bool variables to the
     Boolean module and *all* the others to a single theory module, so a Bool
     prefix combines with any one of Int, Real or bit-vector, but those three
     never combine with each other: a prefix mixing them would hand, say, a
     real-arithmetic atom to the integer projection.  Arrays and datatypes
     are projected by modules of their own ahead of the arithmetic one; every
     other sort (string, tuple, ...) has no projection module wired in here
     at all.  Both refusals used to be a bare [assert false], which told the
     caller neither which sort was at fault nor which of the two reasons
     applied; say it, and say it as a refusal of the input rather than as a
     [Failure], which the command line cannot tell from an internal error and
     prints as a backtrace. *)
  let unsupported what =
    Common.Refusal.refuse
      "MuCyc's QSAT solver handles quantifiers over Bool, Int, Real or \
       bit-vectors (QBF/LIA/LRA/BV) and does not mix Int, Real and \
       bit-vectors with each other; %s"
      what
  in
  let mixed =
    "this prefix quantifies over more than one of Int, Real and bit-vectors"
  in
  let rec loop theory = function
    | [] -> theory
    | T_bool.SBool :: tl -> loop theory tl
    | T_int.SInt :: tl -> (
        match theory with QBF | LIA -> loop LIA tl | _ -> unsupported mixed)
    | T_real.SReal :: tl -> (
        match theory with QBF | LRA -> loop LRA tl | _ -> unsupported mixed)
    (* widths need not agree: the bit-vector projection reads each variable's
       width off the atoms that mention it, so one BV theory covers them all *)
    | T_bv.SBV _ :: tl -> (
        match theory with QBF | BV -> loop BV tl | _ -> unsupported mixed)
    (* arrays and datatypes are projected by their own modules ([Mbp.ARR],
       [Mbp.ADT]) before the arithmetic one, so they do not choose it *)
    | (T_array.SArray _ | T_dt.SDT _ | Sort.SVar _ | T_dt.SUS _) :: tl ->
        loop theory tl
    | sort :: _ ->
        unsupported @@ sprintf "this one quantifies over %s"
        @@ Term.str_of_sort sort
  in
  let theory = loop QBF sortlist in
  (* a prefix over arrays or datatypes and Bool alone still needs an
     arithmetic module for the indices and elements the projections expose *)
  let theory =
    match theory with
    | QBF
      when List.exists sortlist ~f:(function
             | T_array.SArray _ | T_dt.SDT _ | Sort.SVar _ | T_dt.SUS _ -> true
             | _ -> false) ->
        LIA
    | t -> t
  in
  (* a probabilistic (random) quantifier is refused rather than read as an
     ordinary one, which would answer a different question *)
  if List.exists quantifiers ~f:(fst >> Formula.is_random) then
    unsupported "probabilistic (random) quantifiers are not supported"
  else theory

let level_exists atom vlevel =
  Set.fold ~init:Z.zero (Atom.fvs_of atom) ~f:(fun level tvar ->
      match Map.Poly.find vlevel tvar with
      | Some (l, _) -> if Z.is_odd l then Z.max level l else level
      | None -> level)

let level_forall atom vlevel =
  Set.fold ~init:Z.zero (Atom.fvs_of atom) ~f:(fun level tvar ->
      match Map.Poly.find vlevel tvar with
      | Some (l, _) -> if Z.is_even l then Z.max level l else level
      | None -> level)

let level_j j = if Z.is_odd j then level_exists else level_forall

let rec level_j_atom j vlevel = function
  | Formula.Atom (a, _) -> level_j j a vlevel
  | UnaryOp (Not, phi, _) -> level_j_atom j vlevel phi
  | _ -> assert false

let strategy ~print model j atoms vlevel =
  if Map.Poly.is_empty model then Set.Poly.singleton @@ Formula.mk_true ()
  else
    Set.filter atoms ~f:(fun a ->
        Z.Compare.(level_j j a vlevel <= Z.(j - Z.of_int 2)))
    (* An atom the model cannot evaluate -- a selector applied under a
       constructor the model does not give its argument, whose value the
       theory leaves open; an equality between uninterpreted elements -- is
       left out of the strategy.  The strategy only steers which counter-move
       is found next: the verdict is read at levels one and two, whose
       strategies hold ground atoms only, and assuming fewer atoms leaves
       every unsat core a valid reason. *)
    |> Set.Poly.filter_map ~f:(fun atm ->
           try Some (Mbp.sign ~print model atm)
           with exn_ when not (Common.Timer.is_async exn_) -> None)

module type MBP_TYPE = sig
  val let_sort : string Set.Poly.t -> TermSubst.t -> TermSubst.t

  val model_based_projection :
    print:(string lazy_t -> unit) ->
    TermSubst.t ->
    Ident.tvar ->
    Atom.t Set.Poly.t ->
    Atom.t Set.Poly.t
end

let rec bool_var_atom = function
  | Formula.UnaryOp (Not, UnaryOp (Not, phi, _), _) -> bool_var_atom phi
  | Atom (App (Predicate.Var (x, _), [], _), _) ->
      First (Atom.of_bool_var (Ident.pvar_to_tvar x))
  | UnaryOp (Not, Atom (App (Predicate.Var (x, _), [], _), _), _) ->
      First (Atom.of_neg_bool_var (Ident.pvar_to_tvar x))
  | Atom ((App (Predicate.Psym T_bool.(Eq | Neq), [ t1; _t2 ], _) as atm), _)
    when T_bool.is_sbool t1 ->
      First atm
  | Atom (atm, _) -> Second atm
  | UnaryOp (Not, Atom (atm, _), _) ->
      Second
        (match Atom.negate atm with
        | None -> failwith "[bool_var_atom]"
        | Some neg_atm -> neg_atm)
  | _ -> assert false

(* The theory is a parameter: [A] eliminates every non-Bool variable and the Boolean
   projection every Bool one, so this solver covers whichever theories [A] can be
   instantiated with -- today Int, Real and bit-vectors. *)
module QSAT (A : MBP_TYPE) = struct
  let rec level_of level = function
    | [] -> Map.Poly.empty
    | (Formula.Exists, sortenv) :: tl ->
        let level = if Z.is_odd level then level else Z.succ level in
        let map =
          Map.Poly.map (Map.Poly.of_alist_exn sortenv) ~f:(fun s -> (level, s))
        in
        Map.force_merge map (level_of level tl)
    | (Forall, sortenv) :: tl ->
        let level = if Z.is_even level then level else Z.succ level in
        let map =
          Map.Poly.map (Map.Poly.of_alist_exn sortenv) ~f:(fun s -> (level, s))
        in
        Map.force_merge map (level_of level tl)
    | (Random _, _) :: _ ->
        (* the non-probabilistic solver: a probabilistic quantifier has no
           alternation level here, and reaching this means the theory
           classification sent the problem to the wrong solver *)
        failwith
          "this QSAT solver decides universal/existential prefixes and was \
           given a probabilistic quantifier; the probabilistic solver takes \
           those"


  let rec mbp ~print ~config model j vlevel fmls =
    let mbp_main vs fmls =
      let non_bool_atms, bool_atms =
        Set.fold fmls ~init:(Set.Poly.empty, Set.Poly.empty)
          ~f:(fun (c, bc) phi ->
            match bool_var_atom phi with
            | First bool_atm -> (c, Set.add bc bool_atm)
            | Second non_bool_atm -> (Set.add c non_bool_atm, bc))
      in
      print
      @@ lazy
           (sprintf "[mbp_main] vs: %s"
           @@ String.concat_map_list ~sep:", " ~f:Ident.name_of_tvar
           @@ Map.Poly.keys vs);
      print @@ lazy (sprintf "[mbp_main] j: %s" (Z.to_string j));
      print
      @@ lazy
           (sprintf "[mbp_main] non_bool_atms: %s"
           @@ String.concat_map_set ~sep:", " ~f:Atom.str_of non_bool_atms);
      print
      @@ lazy
           (sprintf "[mbp_main] bool_atms: %s"
           @@ String.concat_map_set ~sep:", " ~f:Atom.str_of bool_atms);
      print @@ lazy "";
      (* Each variable goes to the projection of its sort: a datatype first,
         then an array, whose projections leave terms over the fields,
         indices and elements, then the arithmetic theory [A], then Bool. *)
      let rank (_, (_, sort)) =
        match sort with
        | T_dt.SDT _ -> 0
        | T_array.SArray _ -> 1
        | T_bool.SBool -> 3
        | _ -> 2
      in
      let ordered =
        List.stable_sort (Map.Poly.to_alist vs) ~compare:(fun a b ->
            Int.compare (rank a) (rank b))
      in
      (* Where a theory's projection cannot eliminate a variable -- an index
         under a read of an array the block does not bind, a variable under a
         constructor, an element of an uninterpreted sort -- the fallbacks
         below are tried in order: model-guided read-over-write, then
         extensionality, then a term of the formula, and only then the
         variable's value in the model.  Each result holds in the model and
         implies the existential, which is all a projection must guarantee.
         The first three are determined by the formula (the model only picks
         among finitely many cases), so they keep the projections of a formula
         a finite set; the model value does not, and a loop that keeps falling
         back to it enumerates points: that costs termination, never the
         soundness of an answer. *)
      let block = Map.Poly.key_set vs in
      let holds_in_model atom =
        try Evaluator.eval_atom @@ Atom.subst model atom
        with exn_ when not (Common.Timer.is_async exn_) -> false
      in
      let free_of_block t = Set.is_empty (Set.inter (Term.fvs_of t) block) in
      let model_int t =
        try
          match Evaluator.eval_term (Term.subst model t) with
          | Value.Int n -> Some n
          | _ -> None
        with exn_ when not (Common.Timer.is_async exn_) -> None
      in
      let model_str t =
        try Some (Term.str_of @@ Evaluator.simplify_term @@ Term.subst model t)
        with exn_ when not (Common.Timer.is_async exn_) -> None
      in
      (* Model-guided read-over-write.  A read [store(a, j, v)[i]] whose index
         mentions the variable is resolved by the model: where the model gives
         [i] and [j] the same value it becomes [v] with the literal [i = j],
         otherwise [a[i]] with [i != j], and a read of a constant array is its
         value.  The literals hold in the model by construction and the atoms
         keep their value in the model, and under the literals each rewritten
         read equals the original one, so the rewritten atoms with the
         literals imply the original atoms: an existential projection of the
         former is one of the latter.  Where the array was the value the block
         had already been projected to (a store chain over a constant), what is
         left is arithmetic the theory projection can eliminate. *)
      let row_rewrite tvar atoms =
        let lits = ref [] in
        let rec rw t =
          match t with
          | Term.FunApp (T_array.ASelect (s1, s2), [ arr; idx ], info) ->
              let arr = rw arr and idx = rw idx in
              if Set.mem (Term.fvs_of idx) tvar then read s1 s2 info arr idx
              else Term.mk_fsym_app ~info (T_array.ASelect (s1, s2)) [ arr; idx ]
          | Term.FunApp (sym, args, info) ->
              Term.mk_fsym_app ~info sym (List.map args ~f:rw)
          | t -> t
        and read s1 s2 info arr idx =
          match arr with
          | Term.FunApp (T_array.AConst _, [ c ], _) -> c
          | Term.FunApp (T_array.AStore _, [ a; j; v ], _) -> (
              match (model_int idx, model_int j) with
              | Some mi, Some mj ->
                  if Z.equal mi mj then (
                    lits := T_bool.mk_eq idx j :: !lits;
                    v)
                  else (
                    lits := T_bool.mk_neq idx j :: !lits;
                    read s1 s2 info a idx)
              | _ -> Term.mk_fsym_app ~info (T_array.ASelect (s1, s2)) [ arr; idx ])
          | _ -> Term.mk_fsym_app ~info (T_array.ASelect (s1, s2)) [ arr; idx ]
        in
        let atoms' =
          Set.Poly.map atoms ~f:(function
            | Atom.App (pred, args, info) ->
                Atom.mk_app ~info pred (List.map args ~f:rw)
            | atm -> atm)
        in
        if List.is_empty !lits then None
        else
          Some
            (Set.Poly.map ~f:Normalizer.normalize_atom
            @@ Set.union atoms' (Set.Poly.of_list !lits))
      in
      (* A variable of the block that the theory projection cannot eliminate
         (an index of an array the block does not bind, an element of an
         uninterpreted sort) is replaced, before falling back to its model
         value, by a term of the formula itself: a subterm of its sort
         mentioning no variable of the block, under which every atom still
         holds in the model.  Any such term is a projection -- the substituted
         atoms hold in the model by that check, and they imply the existential
         since the term is a witness for it -- and the candidates are finitely
         many, so where one exists the projections of a formula stay a finite
         set.  Candidates the model gives the variable's own value come first.
         Where an atom equates a term [u] free of the block with a constructor
         application in which the variable is an argument, the selector of that
         argument applied to [u] is a candidate too, whatever the variable's
         sort; the substituted equation then says [u] is built by that
         constructor, which the model confirms. *)
      let by_formula_term tvar sort atoms =
        let same_sort t =
          match (sort, Term.sort_of t) with
          | T_int.SInt, T_int.SInt -> true
          | (Sort.SVar _ | T_dt.SUS _), s2 ->
              String.equal (Term.str_of_sort sort) (Term.str_of_sort s2)
          | _ -> false
        in
        let rec sel_cands u = function
          | Term.FunApp (T_dt.DTCons (cname, _, dt), args, _) ->
              List.concat_mapi args ~f:(fun i arg ->
                  match arg with
                  | Term.Var (x, _, _) when Ident.tvar_equal x tvar ->
                      [ T_dt.mk_sel_by_cons dt cname i u ]
                  | Term.FunApp (T_dt.DTCons _, _, _) ->
                      sel_cands (T_dt.mk_sel_by_cons dt cname i u) arg
                  | _ -> [])
          | _ -> []
        in
        let cands =
          (Set.to_list atoms
          |> List.concat_map ~f:(function
               | Atom.App (Predicate.Psym T_bool.(Eq | Neq), [ l; r ], _) ->
                   (if free_of_block l then sel_cands l r else [])
                   @ if free_of_block r then sel_cands r l else []
               | _ -> []))
          @ Set.to_list
              (Set.concat_map atoms
                 ~f:
                   (Atom.filtered_terms_of ~f:(fun t ->
                        same_sort t && free_of_block t)))
        in
        let same_value, others =
          match Map.Poly.find model tvar with
          | None -> ([], cands)
          | Some v -> (
              match sort with
              | T_int.SInt ->
                  let mv = model_int v in
                  List.partition_tf cands ~f:(fun t ->
                      match (model_int t, mv) with
                      | Some n1, Some n2 -> Z.equal n1 n2
                      | _ -> false)
              | _ ->
                  (* an element of an uninterpreted sort has no value but its
                     name in the model: only a candidate the model names the
                     same is known to hold, so the others are not tried *)
                  let mv = model_str v in
                  ( List.filter cands ~f:(fun t ->
                        match (model_str t, mv) with
                        | Some s1, Some s2 -> String.equal s1 s2
                        | _ -> false),
                    [] ))
        in
        List.find_map (same_value @ others) ~f:(fun t ->
            let sub = Map.Poly.singleton tvar t in
            let touched, untouched =
              Set.partition_tf atoms ~f:(fun atm ->
                  Set.mem (Atom.fvs_of atm) tvar)
            in
            let touched' = Set.Poly.map touched ~f:(Atom.subst sub) in
            let atoms' = Set.union untouched touched' in
            (* only the atoms the substitution changed need checking *)
            match sort with
            | Sort.SVar _ | T_dt.SUS _ -> Some atoms'
            | _ ->
                if Set.for_all touched' ~f:holds_in_model then Some atoms'
                else None)
      in
      (* The arithmetic projection is exact only where the variable occurs in
         arithmetic positions: it substitutes a bound or a default into the
         atoms it does not recognise, and where the variable sits under an
         array read or a constructor there that substitute need neither keep
         the atom's value in the model nor lie within the bounds it resolved
         away.  Such a variable goes to the fallbacks below instead. *)
      let rec arith_only tvar t =
        match t with
        | Term.Var _ -> true
        | Term.FunApp (T_int.(Int _ | Neg | Add | Sub | Mul), args, _) ->
            List.for_all args ~f:(arith_only tvar)
        | t -> not (Set.mem (Term.fvs_of t) tvar)
      in
      let arith_atoms tvar atoms =
        Set.for_all atoms ~f:(function
          | Atom.App (_, args, _) as atm ->
              (not (Set.mem (Atom.fvs_of atm) tvar))
              || List.for_all args ~f:(arith_only tvar)
          | _ -> true)
      in
      (* Extensionality.  Where the variable occurs in exactly one atom, that
         atom is a disequality [c * a[i] + r != 0] with [c] one or minus one,
         [a] an array term mentioning no variable of the block, and [r] not
         mentioning [i], then [exists i. a[i] != e] with [e = -r / c] is
         equivalent to [a != K(e)] for the constant array [K(e)]: arrays are
         extensional, so an array differs from a constant one exactly where
         some read differs from the constant.  The projection is exact, holds
         in the model because the atom does, and is determined by the formula
         rather than by a point of the model.
         The same argument gives [exists i. G(i) /\ a[i] != e(i)] as
         [a != lambda j. ite(G(j), e(j), a[j])] for any guard [G], which is
         exact too, but it hands the other player a frame the SMT solver
         answers "incomplete (theory array)" on -- the quantifier is back, as a
         lambda -- so only the constant case is used. *)
      let by_extensionality tvar atoms =
        let with_tvar, without =
          Set.partition_tf atoms ~f:(fun atm -> Set.mem (Atom.fvs_of atm) tvar)
        in
        match Set.to_list with_tvar with
        | [ Atom.App (Predicate.Psym T_bool.Neq, [ l; r ], _) ]
          when Term.is_int_sort (Term.sort_of l) -> (
            let diff = T_int.mk_sub l r in
            let reads =
              Set.to_list
              @@ Term.filtered_terms_of diff ~f:(function
                   | Term.FunApp
                       (T_array.ASelect _, [ arr; Term.Var (x, _, _) ], _) ->
                       Ident.tvar_equal x tvar && free_of_block arr
                   | _ -> false)
            in
            match reads with
            | [ (Term.FunApp (T_array.ASelect (s1, s2), [ arr; _ ], _) as rd) ]
              -> (
                match
                  AffineTerm.find_var_monomial rd
                  @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) diff
                with
                | Some (Value.Int c, rest)
                  when Z.equal c Z.one || Z.equal c Z.minus_one ->
                    let rest_t = AffineTerm.mk_int_term rest in
                    if not (free_of_block rest_t) then None
                    else
                      (* c * a[i] + rest != 0, i.e. a[i] != -rest / c *)
                      let e =
                        if Z.equal c Z.one then T_int.mk_neg rest_t else rest_t
                      in
                      Some
                        (Set.add without
                           (T_bool.mk_neq arr (T_array.mk_const_array s1 s2 e)))
                | _ -> None)
            | _ -> None)
        | _ -> None
      in
      let project_with_fallbacks tvar sort project atoms =
        try
          (match sort with
          | T_int.SInt when not (arith_atoms tvar atoms) ->
              raise Mbp.NotNormalized
          | _ -> ());
          project atoms
        with exn_ when not (Common.Timer.is_async exn_) -> (
          let atoms, reproject =
            match sort with
            | T_int.SInt -> (
                match row_rewrite tvar atoms with
                | Some atoms' -> (
                    ( atoms',
                      if arith_atoms tvar atoms' then
                        try Some (project atoms')
                        with exn_ when not (Common.Timer.is_async exn_) ->
                          None
                      else None ))
                | None -> (atoms, None))
            | _ -> (atoms, None)
          in
          match
            match reproject with
            | Some _ -> reproject
            | None -> (
                match sort with
                | T_int.SInt -> by_extensionality tvar atoms
                | _ -> None)
          with
          | Some atoms' -> atoms'
          | None -> (
              match by_formula_term tvar sort atoms with
              | Some atoms' -> atoms'
              | None -> (
                  match (sort, Map.Poly.find model tvar) with
                  | (Sort.SVar _ | T_dt.SUS _), _ ->
                      (* the model's name for an element is not a term of the
                         problem; a point value would hand the solver an
                         unbound constant *)
                      failwith
                      @@ sprintf
                           "MuCyc's QSAT solver has no projection for %s, a \
                            variable of the uninterpreted sort %s that no \
                            term of the formula equals in the model"
                           (Ident.name_of_tvar tvar) (Term.str_of_sort sort)
                  | _, Some v ->
                      let sub = Map.Poly.singleton tvar v in
                      Set.Poly.map atoms ~f:(Atom.subst sub)
                  | _, None -> raise exn_)))
      in
      let non_bool_atms, bool_atms =
        List.fold ordered ~init:(non_bool_atms, bool_atms)
          ~f:(fun (non_bool_atms, bool_atms) (tvar, (_, sort)) ->
            if Term.is_bool_sort sort then
              ( non_bool_atms,
                Mbp.Boolean.model_based_projection ~print model tvar bool_atms
              )
            else
              match sort with
              | T_dt.SDT _ ->
                  ( project_with_fallbacks tvar sort
                      (Mbp.ADT.model_based_projection ~print model tvar)
                      non_bool_atms,
                    bool_atms )
              | T_array.SArray _ ->
                  ( project_with_fallbacks tvar sort
                      (Mbp.ARR.model_based_projection ~print model tvar)
                      non_bool_atms,
                    bool_atms )
              | Sort.SVar _ | T_dt.SUS _ ->
                  ( project_with_fallbacks tvar sort (fun _ -> failwith "no projection")
                      non_bool_atms,
                    bool_atms )
              | _ ->
                  ( project_with_fallbacks tvar sort
                      (A.model_based_projection ~print model tvar)
                      non_bool_atms,
                    bool_atms ))
      in
      Set.Poly.map ~f:Evaluator.simplify_atom
      @@ Set.union non_bool_atms bool_atms
    in
    let jformulas =
      let vs_tail =
        Map.Poly.filter vlevel ~f:(fun (level, _) ->
            Z.Compare.(level >= Z.(j - Z.one)))
      in
      mbp_main vs_tail fmls
    in
    let index =
      Set.fold jformulas
        ~init:(if Z.is_odd j then Z.one else Z.of_int 2)
        ~f:(fun i jformula -> Z.max i (level_j_atom j vlevel jformula))
    in
    let jformula = Formula.and_of @@ Set.to_list jformulas in
    match config.Config.backtrack_strategy with
    | Original -> (jformula, index)
    | Chronological -> (jformula, Z.(j - Z.of_int 2))
    | NonChronological ->
        if Z.Compare.(index = Z.(j - Z.of_int 2)) then (jformula, index)
        else
          let vs =
            Map.Poly.filter vlevel ~f:(fun (level, _) ->
                Z.Compare.(level >= Z.(index + Z.one)))
          in
          (Formula.and_of @@ Set.to_list @@ mbp_main vs jformulas, index)
    | NonChronologicalRec ->
        if Z.Compare.(index = Z.(j - Z.of_int 2)) then (jformula, index)
        else mbp ~print ~config model Z.(index + Z.of_int 2) vlevel jformulas

  let add_atoms atoms1 atoms2 =
    let neg_atoms1 =
      Set.Poly.filter_map atoms1 ~f:(fun atm ->
          Option.(Atom.negate atm >>= (Normalizer.normalize_atom >> return)))
    in
    Set.union atoms1
    @@ Set.filter ~f:(Set.mem neg_atoms1 >> not)
    @@ Set.Poly.map ~f:Normalizer.normalize_atom atoms2

  let update_frames ~config frames atoms j jformula =
    let newframes =
      if config.Config.update_all_frames_j_and_after then
        Map.Poly.mapi frames ~f:(fun ~key ~data ->
            if Z.Compare.(key < j) then data
            else if Z.(is_even (key - j)) then
              Formula.(mk_and data (negate jformula))
            else data)
      else
        Map.Poly.update frames j ~f:(function
          | Some frame -> Formula.(mk_and frame (negate jformula))
          | None -> assert false)
    in
    let newatoms =
      let jatoms =
        let pos, neg = Formula.atoms_of jformula in
        Set.union pos neg
      in
      Map.Poly.mapi atoms ~f:(fun ~key ~data ->
          if
            (not config.Config.update_only_atoms_j_and_before)
            || Z.Compare.(key <= j)
          then add_atoms data jatoms
          else data)
    in
    (newframes, newatoms)

  (* [pins] fixes variables an outer block has already moved on; they are conjoined to
     every query and never negated.  [on_refute] and [on_subst_lemma] report a refutation
     and a substituted lemma to a caller that drives this search per candidate. *)
  let solve_qsat ?(pins = []) ?(on_refute = fun _ _ _ -> ())
      ?(on_subst_lemma = fun _ _ -> ()) ~print ~config quantifiers f =
    print
    @@ lazy
         (String.concat_map_list ~sep:" " quantifiers ~f:(fun (binder, senv) ->
              Formula.str_of_binder binder
              ^ str_of_sort_env_list Term.str_of_sort senv));
    print @@ lazy "";
    print @@ lazy (Formula.str_of f);
    let vlevel = level_of Z.one quantifiers in
    let names = Set.Poly.singleton "main" in
    let frames =
      Map.Poly.add_exn ~key:(Z.of_int 2) ~data:(Formula.negate f)
        (Map.Poly.singleton Z.one f)
    in
    let atoms0 =
      let pos, neg = Formula.atoms_of f in
      add_atoms Set.Poly.empty (Set.union pos neg)
    in
    let atoms =
      Map.Poly.add_exn ~key:(Z.of_int 2) ~data:atoms0
        (Map.Poly.singleton Z.one atoms0)
    in
    let fenv = (*TODO: generate fenv*) Map.Poly.empty in
    (* At level [max + 2] every atom is fixed by the strategy, so its check
       is unsatisfiable and the search backtracks; a level beyond that means
       the strategy lost atoms it could not evaluate in the model (an
       uninterpreted element compared by equality), and the search would
       climb for ever instead of deciding. *)
    let max_level =
      Map.Poly.fold vlevel ~init:Z.zero ~f:(fun ~key:_ ~data:(l, _) m ->
          Z.max l m)
    in
    (* When the refuted level is the innermost one, every variable left belongs to the
       refuted player, so that player's winning move can be replaced by terms and the whole
       matrix instantiated with it: the instance stays quantifier-free and is implied by the
       win at level [j - 2].  Negating the projected core instead loses the disjunctions of
       the matrix, and where the core carries a divisibility constraint it describes one
       congruence class per refutation. *)
    let subst_lemma ~print model j core =
      let opp =
        Map.Poly.filter vlevel ~f:(fun (l, _) -> Z.Compare.(l = Z.(j - one)))
      in
      if
        (not config.Config.subst_lemma)
        || Z.Compare.(max_level > j)
        || Map.Poly.exists opp ~f:(fun (_, s) ->
               not (Term.is_int_sort s || Term.is_real_sort s))
      then None
      else
        match
          Option.all
          @@ List.map core ~f:(function
               | Formula.Atom (a, _) -> Some a
               | UnaryOp (Not, Atom (a, _), _) -> Atom.negate a
               | _ -> None)
        with
        | None -> None
        | Some atoms ->
            let atoms = Set.Poly.of_list atoms in
            (* A witness term for each of the refuted player's variables, chosen
               under the model by the selection of the strategy improvement
               procedure (Farzan and Kincaid, "Linear Arithmetic Satisfiability
               via Strategy Improvement", IJCAI 2016).

               All or nothing: a variable left without a term would stay free in
               the instance below, so where the selection does not apply to every
               one of them the caller projects instead.  That covers a level whose
               variables are not all of one arithmetic sort, and one carrying a
               sort the selection has no case for. *)
            match
              StratSynth.Old.select_terms model (Map.Poly.to_alist
                @@ Map.Poly.map opp ~f:snd) atoms
            with
            | None ->
                print
                @@ lazy
                     "[solve] no witness term for the refuted level; projecting \
                      instead";
                None
            | Some sub ->
                Map.Poly.iteri sub ~f:(fun ~key:x ~data:t ->
                    print
                    @@ lazy
                         (sprintf "[solve] %s := %s" (Ident.name_of_tvar x)
                            (Term.str_of t)));
            (* the level being refuted keeps its own variables, fresh so that the instance
               constrains no earlier choice *)
            let fresh =
              Map.Poly.filter_mapi vlevel ~f:(fun ~key:_ ~data:(l, s) ->
                  if Z.Compare.(l = j) then
                    Some (Term.mk_var (Ident.mk_fresh_tvar ()) s)
                  else None)
            in
            let base = if Z.is_odd j then f else Formula.negate f in
            let lemma =
              Evaluator.simplify @@ Normalizer.normalize
              @@ Formula.subst (Map.force_merge sub fresh) base
            in
            print
            @@ lazy
                 (sprintf "[solve] subst lemma @ %s: %s"
                    (Z.to_string Z.(j - of_int 2))
                    (Formula.str_of lemma));
            Some (lemma, Z.(j - of_int 2))
    in
    let rec loop model j frames atoms names =
      if Z.Compare.(j > Z.(max_level + of_int 2)) then
        failwith
          "MuCyc's QSAT solver: the strategy could not fix every atom (an \
           atom the model does not evaluate, e.g. an equality between \
           elements of an uninterpreted sort), so the search cannot decide";
      let frame_j = Map.Poly.find_exn frames j in
      print
      @@ lazy
           (sprintf "\n[solve] current frame @ %s: %s" (Z.to_string j)
              (Formula.str_of frame_j));
      let strat_j =
        strategy ~print model j (Map.Poly.find_exn atoms j) vlevel
      in
      print
      @@ lazy
           (sprintf "[solve] strategy @ %s: %s" (Z.to_string j)
              (String.concat_map_set ~sep:", " ~f:Formula.str_of strat_j));
      let pvar_clause_map, names =
        List.foldi (Set.to_list strat_j)
          ~init:(Map.Poly.singleton "main" (Formula.and_of (frame_j :: pins)), names)
          ~f:(fun i (map, names) fml ->
            let name = sprintf "|#S_%s|" (string_of_int i) in
            (Map.Poly.add_exn map ~key:name ~data:fml, Set.add names name))
      in
      match
        Z3Smt.Z3interface.check_sat_unsat_core ~id:None fenv pvar_clause_map
      with
      | `Unsat core ->
          if Z.Compare.(j = Z.one) then UNSAT
          else if Z.Compare.(j = Z.of_int 2) then SAT
          else
            let core =
              List.filter_opt
              @@ List.map core ~f:(function
                   | "main" -> None
                   | v -> Map.Poly.find pvar_clause_map v)
            in
            print
            @@ lazy
                 (sprintf "[solve] unsat core: %s"
                 @@ String.concat_map_list ~sep:", " ~f:Formula.str_of core);
            print @@ lazy (sprintf "[solve] model: %s" (TermSubst.str_of model));
            on_refute j model core;
            (match subst_lemma ~print model j core with
            | Some (lemma, j) ->
                let frames =
                  Map.Poly.update frames j ~f:(function
                    | Some frame -> Formula.mk_and frame lemma
                    | None -> assert false)
                in
                let atoms =
                  let lemma_atoms =
                    let pos, neg = Formula.atoms_of lemma in
                    Set.filter (Set.union pos neg) ~f:(fun atm ->
                        Set.for_all (Atom.fvs_of atm) ~f:(Map.Poly.mem vlevel))
                  in
                  Map.Poly.mapi atoms ~f:(fun ~key ~data ->
                      if
                        (not config.Config.update_only_atoms_j_and_before)
                        || Z.Compare.(key <= j)
                      then add_atoms data lemma_atoms
                      else data)
                in
                on_subst_lemma j lemma;
                loop Map.Poly.empty j frames atoms names
            | None ->
                let jformula, j =
                  mbp ~print ~config model j vlevel (Set.Poly.of_list core)
                in
                let jformula =
                  Evaluator.simplify @@ Normalizer.normalize jformula
                in
                print
                @@ lazy
                     (sprintf "[solve] jformula: %s @ %s"
                        (Formula.str_of jformula) (Z.to_string j));
                let frames, atoms =
                  update_frames ~config frames atoms j jformula
                in
                loop Map.Poly.empty j frames atoms names)
      | `Sat model ->
          let model =
            let model =
              let model = Map.Poly.of_alist_exn @@ remove_dontcare model in
              (* a function the model reader lists without a value (a solver
                 helper, an array read through an auxiliary function) is no
                 use to a substitution; an element of an uninterpreted sort has
                 no literal to evaluate to, so it stays the model's term *)
              let model =
                Map.Poly.filter model ~f:(fun t ->
                    not @@ Sort.is_arrow @@ Term.sort_of t)
              in
              (* the theory's canonicalisation is asked entry by entry, and an
                 entry it cannot evaluate (an uninterpreted element, alone or
                 inside a tuple) stays the model's term *)
              Map.Poly.filter_mapi model ~f:(fun ~key ~data ->
                  let single = Map.Poly.singleton key data in
                  match A.let_sort names single with
                  | m -> Map.Poly.find m key
                  | exception exn_ when not (Common.Timer.is_async exn_) ->
                      if Set.mem names (Ident.name_of_tvar key) then None
                      else Some data)
            in
            Map.Poly.fold vlevel ~init:model
              ~f:(fun ~key ~data:(_, sort) model ->
                match Map.Poly.find model key with
                | Some _ -> model
                | None -> Map.Poly.add_exn model ~key ~data:(Term.mk_dummy sort))
          in
          print
          @@ lazy (sprintf "[solve] new model: %s" (TermSubst.str_of model));
          let frames =
            Map.Poly.update frames (Z.succ j) ~f:(function
              | Some frame -> frame
              | None ->
                  if config.Config.reuse_prev_frame then
                    Map.Poly.find_exn frames (Z.pred j)
                  else if Z.is_odd (Z.succ j) then f
                  else Formula.negate f)
          in
          let atoms =
            Map.Poly.update atoms (Z.succ j) ~f:(function
              | Some atoms -> atoms
              | None ->
                  if config.Config.update_only_atoms_j_and_before then atoms0
                  else Map.Poly.find_exn atoms j)
          in
          loop model (Z.succ j) frames atoms names
      | `Unknown reason ->
          failwith
          @@ sprintf "MuCyc's QSAT solver: the SMT solver answered unknown (%s)"
               reason
      | `Timeout -> raise Common.Timer.Timeout
    in
    loop Map.Poly.empty Z.one frames atoms names

  (* Abstraction refinement over the outermost block of a prefix
     exists X1. forall X2. exists X3. ...  A candidate for X1 has to satisfy every instance
     collected so far, and is then checked by a fresh game with X1 fixed, so the check
     never carries the lemmas learned for another candidate; a refutation at level 3 gives
     the opponent's winning move for X2, whatever the depth of the prefix, and the matrix
     instantiated with it becomes the next instance.  Substituting any term for X2 is
     sound, since the universal implies each of its instances, so the choice of term
     decides only whether the loop terminates. *)
  let solve_fwd ~print ~config quantifiers f =
    let vlevel = level_of Z.one quantifiers in
    let at l =
      Map.Poly.filter vlevel ~f:(fun (l', _) -> Z.Compare.(l' = Z.of_int l))
    in
    let xs = at 1 and ys = at 2 in
    let fresh_of vs =
      Map.Poly.map vs ~f:(fun (_, s) -> Term.mk_var (Ident.mk_fresh_tvar ()) s)
    in
    let max_level =
      Map.Poly.fold vlevel ~init:Z.zero ~f:(fun ~key:_ ~data:(l, _) m ->
          Z.max l m)
    in
    (* An instance carries a copy of every block below the opponent's, and those copies
       keep the quantifier of the block they came from: the deeper blocks still alternate,
       so leaving them free would read a universal as existential and let a candidate
       survive that no strategy can defend.  Innermost first, so the fold nests them in
       prefix order. *)
    let fresh_blocks_below () =
      let rec go l acc =
        if Z.Compare.(l > max_level) then acc
        else
          let vs =
            Map.Poly.filter vlevel ~f:(fun (l', _) -> Z.Compare.(l' = l))
          in
          let sub, senv =
            Map.Poly.fold vs ~init:(Map.Poly.empty, [])
              ~f:(fun ~key ~data:(_, s) (sub, senv) ->
                let x = Ident.mk_fresh_tvar () in
                ( Map.Poly.set sub ~key ~data:(Term.mk_var x s),
                  (x, s) :: senv ))
          in
          go (Z.succ l) ((l, sub, senv) :: acc)
      in
      go (Z.of_int 3) []
    in
    let close_below sub_ys f =
      let blocks = fresh_blocks_below () in
      let sub =
        List.fold blocks ~init:sub_ys ~f:(fun acc (_, sub, _) ->
            Map.force_merge acc sub)
      in
      (* the last block needs no quantifier when it is existential: a free variable in the
         candidate query is read existentially anyway and nothing universal is nested
         inside it, while binding it makes that query quantified, which costs a
         three-level prefix a factor of hundreds *)
      List.fold blocks ~init:(Formula.subst sub f)
        ~f:(fun body (l, _, senv) ->
          if List.is_empty senv then body
          else if Z.Compare.(l = max_level) && Z.is_odd l then body
          else if Z.is_odd l then Formula.mk_exists senv body
          else Formula.mk_forall senv body)
    in
    let rec loop insts =
      let main = Formula.and_of insts in
      match
        Z3Smt.Z3interface.check_sat_unsat_core ~id:None Map.Poly.empty
          (Map.Poly.singleton "main" main)
      with
      | `Unsat _ -> UNSAT
      | `Sat model ->
          let model =
            A.let_sort (Set.Poly.singleton "main")
            @@ Map.Poly.of_alist_exn @@ remove_dontcare model
          in
          let pins =
            Map.Poly.fold xs ~init:[] ~f:(fun ~key:x ~data:(_, s) acc ->
                let t =
                  match Map.Poly.find model x with
                  | Some t -> t
                  | None -> Term.mk_dummy s
                in
                Formula.eq (Term.mk_var x s) t :: acc)
          in
          print
          @@ lazy
               (sprintf "[fwd] candidate: %s"
                  (String.concat_map_list ~sep:", " ~f:Formula.str_of pins));
          let last = ref None in
          let on_refute j m core =
            if Z.Compare.(j = Z.of_int 3) then last := Some (m, core)
          in
          (match solve_qsat ~pins ~on_refute ~print ~config quantifiers f with
          | SAT -> SAT
          | UNSAT ->
              let sub =
                match !last with
                | None -> fresh_of ys
                | Some (m, core) ->
                    let atoms =
                      Set.Poly.of_list
                      @@ List.filter_map core ~f:(function
                           | Formula.Atom (a, _) -> Some a
                           | UnaryOp (Not, Atom (a, _), _) -> Atom.negate a
                           | _ -> None)
                    in
                    fst
                    @@ Map.Poly.fold ys ~init:(Map.Poly.empty, atoms)
                         ~f:(fun ~key:y ~data:(_, s) (sub, atoms) ->
                           (* where the selection does not apply, a fresh variable:
                              the instance is closed below, so a variable without a
                              term costs generality rather than sense *)
                           let t =
                             match
                               StratSynth.Old.select_terms m [ (y, s) ] atoms
                             with
                             | Some sub' -> (
                                 match Map.Poly.find sub' y with
                                 | Some t -> t
                                 | None -> Term.mk_var (Ident.mk_fresh_tvar ()) s)
                             | None -> Term.mk_var (Ident.mk_fresh_tvar ()) s
                           in
                           let one = Map.Poly.singleton y t in
                           ( Map.Poly.set
                               (Map.Poly.map sub ~f:(Term.subst one))
                               ~key:y ~data:t,
                             Set.Poly.map atoms ~f:(fun atm ->
                                 Normalizer.normalize_atom @@ Atom.subst one atm)
                           ))
              in
              let inst =
                Evaluator.simplify @@ Normalizer.normalize @@ close_below sub f
              in
              (* with no move to generalize, the instance holds of the candidate that has
                 just lost, so it alone would let the next round propose that candidate
                 again; excluding it keeps every round a step, and is sound because the
                 candidate has no winning strategy *)
              let extra =
                match !last with
                | None -> [ Formula.negate @@ Formula.and_of pins ]
                | Some _ -> []
              in
              print
              @@ lazy (sprintf "[fwd] instance: %s" (Formula.str_of inst));
              loop ((inst :: extra) @ insts))
      | _ -> assert false
    in
    loop []

  let solve ~print ~config quantifiers f =
    let vlevel = level_of Z.one quantifiers in
    let levels = Set.Poly.of_list @@ List.map (Map.Poly.data vlevel) ~f:fst in
    if
      config.Config.forward
      && Set.mem levels Z.one
      && Set.mem levels (Z.of_int 3)
      (* two levels would make the instance the whole matrix with no opponent move to
         generalize, which is what the substituted lemma already does, and with no variable
         at the outermost level there is no candidate to refine, so every round would pin
         nothing and repeat the same game *)
    then solve_fwd ~print ~config quantifiers f
    else solve_qsat ~print ~config quantifiers f
end
