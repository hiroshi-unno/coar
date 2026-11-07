(** Candidate atoms of the Houdini-style pre-pass of the PCSat validator
    (Flanagan and Leino, FME 2001: the greatest conjunction of candidate atoms
    that is inductive): the declared ones, the generated families, and their
    ranking under the per-family quotas. *)

(* The candidate atoms of the Houdini-style pre-pass for one unknown, over its
   parameters [params]: the declared ones as they are and in their order, then
   the generated ones that can be candidates at all ([usable]), without
   repetition (by printed form, a declared atom included), the smallest by
   [Formula.ast_size] first with ties broken by printed form, so the result is
   a function of the two lists as sets and not of their order, filling up to
   [cap] atoms in all.  The declared atoms are never dropped, even past [cap]:
   the input asked for them. *)

open Core
open Common.Ext
open Common.Combinator
open PCSatCommon
open Ast
open Ast.LogicOld

(* a formula whose free variables are all among [params], with no unknown,
   that is not a Boolean literal: an atom a conjunction over the unknown's
   parameters can carry.  A qualifier over a template's cell column, or an
   atom of a definition body taken from under its binder, has a free
   variable of its own and is refused.  A quantified formula over the
   parameters is kept: the extraction lifts a clause's bounded universal
   premises into such qualifiers ([forall k. 0 <= k < len v => R(v[k])]),
   which are exactly the contract facts a declared list states, and the
   pre-pass's questions carry them as they carry a declared one.

   With [dtenv] (the datatypes the problem itself uses), a formula is also
   refused when a datatype it mentions has a definition different from the
   problem's under the same name.  The atoms of the input's definitions are
   read from the process-global definitions, which are over the sorts the
   input declared; inside the solve of a finite instance, where a quantified
   sort is replaced by an enumeration, the same datatype name is defined over
   the enumeration, and an atom mixing the two made the solver's datatype
   conversion raise. *)
let agrees dtenv phi =
  Map.Poly.is_empty dtenv
  ||
  match DTEnv.force_merge dtenv (DTEnv.of_formula phi) with
  | _ -> true
  | exception exn_ when not (Common.Timer.is_async exn_) -> false

(* a literal, or a quantifier over one ([forall x. true]), which a
   normalisation that simplifies the body but keeps the binder leaves *)
let rec literal = function
  | Formula.Bind (_, _, body, _) -> literal body
  | phi -> Formula.is_true phi || Formula.is_false phi

let usable ?(dtenv = Map.Poly.empty) (params : sort_env_list) phi =
  let names = Set.Poly.of_list (List.map params ~f:fst) in
  agrees dtenv phi
  && Set.is_empty (Formula.pvs_of phi)
  && Set.is_subset (Formula.tvs_of phi) ~of_:names
  && not (literal phi)

(* each atom and its negation: a template hole may take a qualifier in
   either polarity, and a conjunction only in the one it is given *)
let both_polarities phis =
  List.concat_map phis ~f:(fun phi -> [ phi; Evaluator.simplify_neg phi ])

(* Whether [phi], read as a validity question, binds a variable of
   sequence sort existentially: under an [exists] at positive polarity or a
   [forall] at negative polarity.  An implication's premise and a negation
   flip the polarity; any other connective keeps it, and a binder nested in
   an atom (a formula embedded in a term) is not seen, so the answer can
   only be [false] where it might have been [true].  With [arrays], a
   variable of an [Int]-indexed array sort counts as a sequence (the
   array-plus-length encoding of one); without it, exactly as before. *)
let binds_sequence_existentially ?(arrays = false) phi =
  let has_seq =
    List.exists ~f:(fun (_, s) ->
        match s with
        | T_seq.SSeq _ -> true
        | T_array.SArray (si, _) -> arrays && Term.is_int_sort si
        | _ -> false)
  in
  let rec go ~pos = function
    | Formula.Bind (b, senv, body, _) ->
        (match (b, pos) with
          | Formula.Exists, true | Formula.Forall, false -> has_seq senv
          | _ -> false)
        || go ~pos body
    | Formula.UnaryOp (Formula.Not, p, _) -> go ~pos:(not pos) p
    | Formula.BinaryOp ((Formula.And | Formula.Or), p, q, _) ->
        go ~pos p || go ~pos q
    | Formula.BinaryOp (Formula.Imply, p, q, _) ->
        go ~pos:(not pos) p || go ~pos q
    | Formula.BinaryOp (Formula.Iff, p, q, _)
    | Formula.BinaryOp (Formula.Xor, p, q, _) ->
        go ~pos p || go ~pos:(not pos) p || go ~pos q || go ~pos:(not pos) q
    | Formula.LetFormula (_, _, _, body, _) -> go ~pos body
    | _ -> false
  in
  go ~pos:true phi

(* With [quota > 0] the quantified generated atoms are ranked apart from
   the quantifier-free ones: at most [quota] of them are kept, the smallest
   first, and they do not count against [cap], which then bounds the
   declared and the quantifier-free generated atoms together.  A quantified
   atom is larger than the quantifier-free ones over the same terms, so a
   single ranking by size keeps it last and a cap cuts it first, while it is
   the kind of fact (a contract's pointwise postcondition) a loop invariant
   most often needs.  [quota = 0] is the single ranking. *)
(* the usable atoms of [phis], keyed by printed form, without repetition,
   the smallest by [Formula.ast_size] first, ties by printed form, minus
   those whose printed form is in [seen] *)
let ranked ~dtenv ~params ~seen phis =
  List.filter_map phis ~f:(fun phi ->
      if usable ~dtenv params phi then Some (Formula.str_of phi, phi) else None)
  |> List.dedup_and_sort ~compare:(fun (s1, p1) (s2, p2) ->
      match Int.compare (Formula.ast_size p1) (Formula.ast_size p2) with
      | 0 -> String.compare s1 s2
      | c -> c)
  |> List.filter ~f:(fun (str, _) -> not (Hash_set.mem seen str))

(* With [inclusion_quota > 0], the atoms of [inclusions] (the relation
   inclusions) have a quota of their own, outside both [cap] and [quota]:
   the result is exactly the merge of [declared] and [generated] as if
   [inclusions] were empty, followed by at most [inclusion_quota] of the
   usable inclusion atoms not already in it, the smallest first.  So
   switching the family on can only add atoms, never displace one the
   other families keep -- an inclusion is a small quantified formula, and
   ranked with the other quantified atoms it took the whole of [quota]
   ahead of the contract's pointwise facts.  [inclusion_quota = 0] merges
   [inclusions] into [generated], the ranking of before. *)
(* [affine_quota] and [affine] are the same for the affine element
   universals, and [counting_quota] and [counting] for the length sums,
   three-term equations and guarded orders: with several quotas positive,
   the inclusions come first, then the affine atoms, then the counting
   atoms, each deduplicated against everything before *)
let merge ?(quota = 0) ?(inclusion_quota = 0) ?(inclusions = [])
    ?(affine_quota = 0) ?(affine = []) ?(counting_quota = 0) ?(counting = [])
    ?(own_quotas = []) ~dtenv ~cap ~(params : sort_env_list)
    ~(declared : Formula.t list) ~(generated : Formula.t list) () =
  let own =
    [
      (inclusion_quota, inclusions);
      (affine_quota, affine);
      (counting_quota, counting);
    ]
  in
  let generated =
    generated
    @ List.concat_map own ~f:(fun (q, atoms) -> if q <= 0 then atoms else [])
  in
  let seen = Hash_set.create (module String) in
  List.iter declared ~f:(fun phi -> Hash_set.add seen (Formula.str_of phi));
  let fresh = ranked ~dtenv ~params ~seen generated in
  let room = max 0 (cap - List.length declared) in
  let kept =
    if quota <= 0 then declared @ List.map ~f:snd (List.take fresh room)
    else
      let qf, quant =
        List.partition_tf fresh ~f:(fun (_, phi) ->
            Formula.is_quantifier_free phi)
      in
      declared
      @ List.map ~f:snd (List.take qf room)
      @ List.map ~f:snd (List.take quant quota)
  in
  let kept =
    List.fold own ~init:kept ~f:(fun kept (q, atoms) ->
        if q <= 0 then kept
        else (
          List.iter kept ~f:(fun phi -> Hash_set.add seen (Formula.str_of phi));
          kept
          @ List.map ~f:snd (List.take (ranked ~dtenv ~params ~seen atoms) q)))
  in
  (* each family of [own_quotas] after everything above, in order, at most
     its quota of its usable atoms not already kept, in the order given
     (not re-ranked by size: a family whose atoms are all of one size is
     ordered by its own generator) *)
  List.fold own_quotas ~init:kept ~f:(fun kept (atoms, q) ->
      List.iter kept ~f:(fun phi -> Hash_set.add seen (Formula.str_of phi));
      let fresh =
        List.filter atoms ~f:(fun phi ->
            usable ~dtenv params phi
            && not (Hash_set.mem seen (Formula.str_of phi)))
      in
      kept @ List.take fresh (max 0 q))

(* {2 Generated classes}

   Nine families of atoms over an unknown's parameters [params], each
   bounded by its own [limit] ([limit <= 0] gives none) and each a function
   of the parameters' names and sorts (and, for the memberships, the
   quantified facts and the inclusions, of the given definitions and
   formulas) only -- never of examples, a model or the
   synthesizer's state.  They are candidates for the pre-pass and nothing
   else: an atom that is not inductive is dropped by the pre-pass's own
   questions, so a family can only cost questions and never an answer.

   The terms an unknown "reaches" are its parameters and their projections
   through the selectors of single-constructor datatypes, at most two
   selectors deep ([CellQual.terms_of_sort ~depth:2]); two is the depth at
   which the Rust-derived inputs keep an iterator's position
   ([tuple_proj.1 (mut_current it)]), and each further level multiplies the
   terms of a record-heavy signature. *)

let reach_depth = 2

(* A generator given [stop] asks it once per atom it builds or normalises
   and raises [Budget_spent] once it holds: a family over a record-heavy
   signature builds thousands of atoms, and the pre-pass's budget covers
   the time spent building them. *)
exception Budget_spent

let poll stop = if stop () then raise Budget_spent

(* The pre-pass in one or two rounds.  [round ~inclusions ~budget_ms] runs
   one whole pre-pass (candidates, fixed point, final check) with or
   without the inclusion family, under the given budget, and gives its
   outcome.  With [second_round] false it is called once, with the
   inclusions and [budget_ms] -- the one-round pre-pass.  With
   [second_round] true it is called first without the inclusions under
   [budget_ms]; a [`Solution] or [`Not_applicable] (nothing to try, or a
   spent budget) is the outcome, and only a [`Counterexamples] (a fixed
   point the final check rejected) calls it a second time, with the
   inclusions, under [round_budget_ms] when given and [budget_ms]
   otherwise, whose outcome is returned in place of the first.  So [round]
   is called at most twice and at most once without the inclusions. *)
let rounds ~second_round ~budget_ms ~round_budget_ms ~round =
  if not second_round then round ~inclusions:true ~budget_ms
  else
    match round ~inclusions:false ~budget_ms with
    | `Counterexamples _ ->
        round ~inclusions:true
          ~budget_ms:
            (match round_budget_ms with
            | Some _ -> round_budget_ms
            | None -> budget_ms)
    | (`Solution _ | `Not_applicable) as outcome -> outcome

(* the sorts reachable from [s] through single-constructor selectors, [s]
   itself included, to [depth] *)
let rec reached_sorts depth s =
  s
  ::
  (match s with
  | T_dt.SDT dt when depth > 0 -> (
      match Datatype.conses_of dt with
      | [ cons ] ->
          List.concat_map (Datatype.sels_of_cons cons) ~f:(fun sel ->
              reached_sorts (depth - 1) (Datatype.sort_of_sel dt sel))
      | _ -> [])
  | _ -> [])

(* every reached term, with the position of the parameter it starts at, in
   parameter order, each parameter's terms by printed sort and then printed
   term *)
let reached (params : sort_env_list) : (int * Term.t) list =
  List.concat_mapi params ~f:(fun i (x, s) ->
      let arg = [ (Term.mk_var x s, s) ] in
      reached_sorts reach_depth s
      |> List.dedup_and_sort ~compare:(fun a b ->
          String.compare (Term.str_of_sort a) (Term.str_of_sort b))
      |> List.concat_map ~f:(fun so ->
          List.map (CellQual.terms_of_sort ~depth:reach_depth so arg)
            ~f:(fun t -> (i, t))))

(* the terms of sort [s] reached from all of [params] *)
let reached_of_sort (params : sort_env_list) s =
  CellQual.terms_of_sort ~depth:reach_depth s
    (List.map params ~f:(fun (x, s) -> (Term.mk_var x s, s)))

(* the first [n] tuples of the product of [cands], lexicographically: the
   enumeration is bounded by [n] tuples however many columns there are *)
let rec tuples n = function
  | [] -> [ [] ]
  | c :: cs ->
      let rest = tuples n cs in
      List.take
        (List.concat_map c ~f:(fun t -> List.map rest ~f:(fun r -> t :: r)))
        n

(* the normal form the families are deduplicated in and a declared atom is
   compared in: simplified, normalised, simplified *)
let normal phi = Evaluator.(simplify >> Normalizer.normalize >> simplify) phi

(* [atoms] without literals and repetitions (by the printed normal form),
   the smallest by [Formula.ast_size] first, ties by printed form, at most
   [limit]: the bound keeps the simplest atoms, and the result does not
   depend on the order the atoms were produced in *)
let smallest ?(stop = fun () -> false) ~limit atoms =
  List.filter_map atoms ~f:(fun phi ->
      poll stop;
      let phi = normal phi in
      if literal phi then None else Some (Formula.str_of phi, phi))
  |> List.dedup_and_sort ~compare:(fun (s1, p1) (s2, p2) ->
      match Int.compare (Formula.ast_size p1) (Formula.ast_size p2) with
      | 0 -> String.compare s1 s2
      | c -> c)
  |> Fn.flip List.take (max 0 limit)
  |> List.map ~f:snd

(* a sort an equation between two reached terms may be over: not a
   Boolean (a Boolean term's equation is an iff, which the membership
   family states directly) and not an array (an equation between two
   arrays is extensional, a question the solver often leaves undecided) *)
let equatable s = not (Term.is_bool_sort s || Term.is_array_sort s)

(* [t1 = t2] for reached terms [t1], [t2] of one sort starting at two
   different parameters: the frame conditions a loop keeps between its
   entry values and its current ones ([mut_final it = mut_final e],
   [it.1 = en]).  Two terms of one parameter are left out: they state a
   fact about one value, which the other families and the extraction
   cover. *)
let frame_equations ?(stop = fun () -> false) ~limit (params : sort_env_list) =
  if limit <= 0 then []
  else
    let ts =
      List.filter (reached params) ~f:(fun (_, t) -> equatable (Term.sort_of t))
    in
    smallest ~stop ~limit
    @@ List.concat_map ts ~f:(fun (i1, t1) ->
        List.filter_map ts ~f:(fun (i2, t2) ->
            poll stop;
            if
              i1 < i2
              && String.equal
                   (Term.str_of_sort (Term.sort_of t1))
                   (Term.str_of_sort (Term.sort_of t2))
            then Some (Formula.eq t1 t2)
            else None))

(* [t = c(u1, ..., un)] for [c] the one constructor of [t]'s sort: a
   conjunction of field equations the frame family states field by field *)
let single_cons_eq q =
  Formula.is_eq q
  &&
  let t1, t2, _ = Formula.let_eq q in
  List.exists [ t1; t2 ] ~f:(fun t ->
      T_dt.is_cons t
      &&
      match Term.sort_of t with
      | T_dt.SDT dt -> List.length (Datatype.conses_of dt) = 1
      | _ -> false)

(* the memberships of reached terms in the relations the unknown carries
   and in the input's Boolean definitions: [r[t1]...[tk] = true] for a
   reached term [r] whose sort is an array (curried to any depth) ending in
   [Bool] -- a contract predicate the unknown depends on, such as
   [q_invariant] or [q_produces] -- and [d(t1, ..., tk)], the definition's
   body instantiated, for a non-recursive Bool-valued definition of [defs];
   each index or formal of sort [s] filled by the terms of sort [s] reached
   from all of [params], at most [limit] tuples per relation or definition,
   and at most [limit] atoms in all.  A definition none of whose formals'
   sorts is reached is skipped; an instance that is a literal or a
   constructor equation of a single-constructor datatype is dropped. *)
let memberships ?(stop = fun () -> false) ~limit ~(defs : FunEnv.t)
    (params : sort_env_list) =
  if limit <= 0 then []
  else
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let over_params q = Set.is_subset (Formula.tvs_of q) ~of_:pset in
    let rels =
      List.concat_map (reached params) ~f:(fun (_, r) ->
          match CellQual.uncurry_array_sort (Term.sort_of r) with
          | (_ :: _ as idx), e when Term.is_bool_sort e ->
              let cands = List.map idx ~f:(reached_of_sort params) in
              if List.exists cands ~f:List.is_empty then []
              else
                List.map (tuples limit cands) ~f:(fun ts ->
                    Formula.eq (T_array.mk_select_app r ts) (T_bool.mk_true ()))
          | _ -> [])
    in
    let defined =
      Map.Poly.to_alist defs
      |> List.concat_map ~f:(fun (_, (fargs, sret, body, isrec, _)) ->
          if isrec || (not (Term.is_bool_sort sret)) || List.is_empty fargs then
            []
          else
            let cands =
              List.map fargs ~f:(fun (_, s) -> reached_of_sort params s)
            in
            if List.exists cands ~f:List.is_empty then []
            else
              let body = Formula.of_bool_term body in
              List.filter_map (tuples limit cands) ~f:(fun ts ->
                  poll stop;
                  let sub =
                    Map.Poly.of_alist_exn
                      (List.zip_exn (List.map fargs ~f:fst) ts)
                  in
                  let q = Evaluator.simplify (Formula.subst sub body) in
                  if single_cons_eq q || not (over_params q) then None
                  else Some q))
    in
    smallest ~stop ~limit (rels @ defined)

(* the integer terms an unknown reaches: the reached integer terms and the
   lengths of the reached sequences *)
let int_terms (params : sort_env_list) =
  let ts = List.map (reached params) ~f:snd in
  List.filter ts ~f:(fun t -> Term.is_int_sort (Term.sort_of t))
  @ List.filter_map ts ~f:(fun t ->
      match Term.sort_of t with
      | T_seq.SSeq se -> Some (T_seq.mk_len se t)
      | _ -> None)

(* the existential memberships of the relations an unknown carries, for a
   relation [r] (a reached term whose sort is an array, curried to any
   depth, ending in [Bool]) exactly one of whose index sorts no reached term
   has, and that sort a sequence sort: [exists t. r[t1]..[t]..[tk] = true]
   and [exists t. r[..t..] = true /\ len t + x = y] for integer terms [x],
   [y] the unknown reaches ([int_terms]).  The other indices are filled by
   reached terms rooted at pairwise different parameters, and [x] and [y]
   are rooted at different parameters: the shape of a loop's history
   between its entry state and its current one ([exists t. len t + n =
   e.1 /\ produces(e.0, t, s.0)]), which keeps the family to a few dozen
   atoms on a record-heavy signature.

   Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, the
   plain memberships first and then the length ones, each group in the
   order the terms are reached, without repetition by printed form; every
   atom is an existential over one fresh sequence variable whose free
   variables are among [params] (the bound name is chosen apart from
   [params]); a relation with no unreached index sort, or with two or
   more, or whose one unreached sort is not a sequence, gives nothing.
   With [array_pairs], a single-constructor datatype of exactly an
   [Int]-indexed array and an [Int] also counts as a sequence: the
   existential then binds two fresh variables, the value is the
   constructor over them and its length the [Int] one; without it the
   result is the one before the option existed.  A function of [params]'
   names and sorts only. *)
let exists_memberships ?(stop = fun () -> false) ?(array_pairs = false) ~limit
    (params : sort_env_list) =
  if limit <= 0 then []
  else
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let rec pick name =
      if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
      else Ident.Tvar name
    in
    let tvar = pick "hext" in
    let avar = pick "hexa" and lvar = pick "hexl" in
    (* the history as a fresh value of the unreached index sort: its
       binders, the value itself and its length.  A sequence is one bound
       variable.  With [array_pairs], a single-constructor datatype of
       exactly two fields, an [Int]-indexed array and an [Int] (the
       array-plus-length encoding of a sequence), is the constructor over
       two bound variables, its length the [Int] one. *)
    let history_of = function
      | T_seq.SSeq se as sq ->
          let tv = Term.mk_var tvar sq in
          Some ([ (tvar, sq) ], tv, T_seq.mk_len se tv)
      | T_dt.SDT dt when array_pairs -> (
          match Datatype.conses_of dt with
          | [ cons ] -> (
              let fields =
                List.map (Datatype.sels_of_cons cons) ~f:(fun sel ->
                    Datatype.sort_of_sel dt sel)
              in
              let int_indexed = function
                | T_array.SArray (si, _) -> Term.is_int_sort si
                | _ -> false
              in
              let arr s = (avar, s) and len = (lvar, T_int.SInt) in
              let mk binders =
                let args =
                  List.map binders ~f:(fun (x, s) -> Term.mk_var x s)
                in
                Some
                  ( binders,
                    T_dt.mk_cons dt (Datatype.name_of_cons cons) args,
                    Term.mk_var lvar T_int.SInt )
              in
              match fields with
              | [ sa; si ] when int_indexed sa && Term.is_int_sort si ->
                  mk [ arr sa; len ]
              | [ si; sa ] when int_indexed sa && Term.is_int_sort si ->
                  mk [ len; arr sa ]
              | _ -> None)
          | _ -> None)
      | _ -> None
    in
    let rooted = reached params in
    let rooted_of_sort s =
      List.filter rooted ~f:(fun (_, t) ->
          String.equal (Term.str_of_sort (Term.sort_of t)) (Term.str_of_sort s))
    in
    let ints =
      List.concat_mapi params ~f:(fun i (x, s) ->
          List.map (int_terms [ (x, s) ]) ~f:(fun t -> (i, t)))
    in
    let pairs =
      List.concat_map ints ~f:(fun (i1, x) ->
          List.filter_map ints ~f:(fun (i2, y) ->
              if i1 <> i2 then Some (x, y) else None))
    in
    let plain, lengths =
      List.unzip
      @@ List.concat_map rooted ~f:(fun (_, r) ->
          match CellQual.uncurry_array_sort (Term.sort_of r) with
          | (_ :: _ as idx), e when Term.is_bool_sort e -> (
              let cands = List.map idx ~f:rooted_of_sort in
              match
                List.filter_mapi cands ~f:(fun k c ->
                    if List.is_empty c then Some k else None)
              with
              | [ k ] -> (
                  match history_of (List.nth_exn idx k) with
                  | Some (binders, tv, tlen) ->
                      let others = List.filteri cands ~f:(fun j _ -> j <> k) in
                      let rec fill = function
                        | [] -> [ [] ]
                        | c :: cs ->
                            let rest = fill cs in
                            List.concat_map c ~f:(fun (i, t) ->
                                List.filter_map rest ~f:(fun r ->
                                    if List.exists r ~f:(fun (i', _) -> i = i')
                                    then None
                                    else Some ((i, t) :: r)))
                      in
                      List.map
                        (List.take (fill others) limit)
                        ~f:(fun ts ->
                          poll stop;
                          let ts = List.map ts ~f:snd in
                          let args = List.take ts k @ (tv :: List.drop ts k) in
                          let mem =
                            Formula.eq
                              (T_array.mk_select_app r args)
                              (T_bool.mk_true ())
                          in
                          ( Formula.exists binders mem,
                            List.map pairs ~f:(fun (x, y) ->
                                Formula.exists binders
                                  (Formula.mk_and mem
                                     (Formula.eq (T_int.mk_add tlen x) y))) ))
                  | None -> [])
              | _ -> [])
          | _ -> [])
    in
    let seen = Hash_set.create (module String) in
    List.filter
      (plain @ List.concat lengths)
      ~f:(fun phi ->
        let key = Formula.str_of phi in
        if Hash_set.mem seen key then false
        else (
          Hash_set.add seen key;
          true))
    |> Fn.flip List.take limit

(* [x = y => u = v] for a frame equation [u = v] ([frame_equations] at the
   same [limit]) and an equation [x = y] between integer terms the unknown
   reaches ([int_terms]) rooted at different parameters, each pair once.
   The guard is the outer loop, so a small limit keeps every frame
   equation under the first guards rather than one equation under every
   guard.  Contract: [limit <= 0] gives [[]]; otherwise at most [limit]
   quantifier-free implications over [params], without repetition by
   printed form.  A function of [params]' names and sorts only. *)
let guarded_frame_equations ?(stop = fun () -> false) ~limit
    (params : sort_env_list) =
  if limit <= 0 then []
  else
    let frames = frame_equations ~stop ~limit params in
    let ints =
      List.concat_mapi params ~f:(fun i (x, s) ->
          List.map (int_terms [ (x, s) ]) ~f:(fun t -> (i, t)))
    in
    let guards =
      List.concat_map ints ~f:(fun (i1, x) ->
          List.filter_map ints ~f:(fun (i2, y) ->
              if i1 < i2 then Some (Formula.eq x y) else None))
    in
    let seen = Hash_set.create (module String) in
    List.concat_map guards ~f:(fun g ->
        List.map frames ~f:(fun f ->
            poll stop;
            Formula.mk_imply g f))
    |> List.filter ~f:(fun phi ->
        let key = Formula.str_of phi in
        if Hash_set.mem seen key then false
        else (
          Hash_set.add seen key;
          true))
    |> Fn.flip List.take limit

(* oriented inequalities over the integer terms an unknown reaches
   ([int_terms]), in this order: the sign facts [0 <= t] and [t = 0]; the
   orders [t1 <= t2]; and the differences [t1 <= t2 - t3] -- the bounds a loop
   keeps between a counter, its limits and a length ([st <= it.0],
   [len out <= it.0 - st], [n <= e.cur.1]).  Both [t1 <= t2 - t3] and
   [t3 <= t2 - t1] are produced although they are one linear fact: which of
   the two reads as the contract wrote it depends on the input, and the
   deduplication below is by normal form, which does not always identify
   them.  The first [limit] in that order
   after deduplication by normal form, so a small limit keeps the signs and
   the orders and the cubic family comes last. *)
let inequalities ?(stop = fun () -> false) ~limit (params : sort_env_list) =
  if limit <= 0 then []
  else
    let ts = List.mapi (int_terms params) ~f:(fun i t -> (i, t)) in
    let zero = T_int.zero () in
    let signs =
      List.concat_map ts ~f:(fun (_, t) ->
          [ Formula.leq zero t; Formula.eq t zero ])
    in
    let orders =
      List.concat_map ts ~f:(fun (i1, t1) ->
          List.filter_map ts ~f:(fun (i2, t2) ->
              if i1 <> i2 then Some (Formula.leq t1 t2) else None))
    in
    let diffs =
      List.concat_map ts ~f:(fun (i1, t1) ->
          List.concat_map ts ~f:(fun (i2, t2) ->
              List.filter_map ts ~f:(fun (i3, t3) ->
                  poll stop;
                  if i1 <> i3 && i2 <> i1 && i2 <> i3 then
                    Some (Formula.leq t1 (T_int.mk_sub t2 t3))
                  else None)))
    in
    let seen = Hash_set.create (module String) in
    let rec take n acc = function
      | [] -> List.rev acc
      | _ when n <= 0 -> List.rev acc
      | phi :: rest ->
          poll stop;
          let phi = normal phi in
          let key = Formula.str_of phi in
          if literal phi || Hash_set.mem seen key then take n acc rest
          else (
            Hash_set.add seen key;
            take (n - 1) (phi :: acc) rest)
    in
    (* the lists are built whole: at most (terms)^3 small formulas, which a
       signature with a few dozen integer terms keeps in the thousands *)
    take limit [] (signs @ orders @ diffs)

(* whether a quantified formula is a definition in disguise: an
   existential with a conjunct, or a universal with a disjunct, that is an
   equation (resp. a disequation) over a bound variable -- the shape a
   [let] or a one-point rule leaves ([exists v. v = t /\ ...]), which says
   nothing a candidate needs and whose instances only cost questions *)
let one_point = function
  | Formula.Bind (binder, bs, body, _) -> (
      let bound = Set.Poly.of_list (List.map bs ~f:fst) in
      let mentions q = not (Set.are_disjoint (Formula.tvs_of q) bound) in
      let is_neq = function
        | Formula.UnaryOp (Formula.Not, q, _) -> Formula.is_eq q
        | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ _; _ ], _), _) ->
            true
        | _ -> false
      in
      match binder with
      | Formula.Exists ->
          Set.exists (Formula.conjuncts_of body) ~f:(fun q ->
              Formula.is_eq q && mentions q)
      | Formula.Forall ->
          Set.exists (Formula.disjuncts_of body) ~f:(fun q ->
              is_neq q && mentions q)
      | _ -> false)
  | _ -> false

(* the maximal quantified subformulas of [phi] that apply no unknown and
   are not [one_point], looking through the ones that are *)
let rec quantified_subformulas acc phi =
  match phi with
  | Formula.Bind (_, _, body, _)
    when Set.is_empty (Formula.pvs_of phi) && one_point phi ->
      (* a [let] in disguise: look inside it, where its bound variable is
         one more free variable to fill *)
      quantified_subformulas acc body
  | Formula.Bind (_, _, _, _) when Set.is_empty (Formula.pvs_of phi) ->
      phi :: acc
  | Formula.UnaryOp (_, phi, _) -> quantified_subformulas acc phi
  | Formula.BinaryOp (_, phi1, phi2, _) ->
      quantified_subformulas (quantified_subformulas acc phi1) phi2
  | Formula.Bind (_, _, phi, _) -> quantified_subformulas acc phi
  | Formula.LetFormula (_, _, _, phi, _) -> quantified_subformulas acc phi
  | _ -> acc

(* the quantified facts the input states, moved onto the unknown: each
   maximal quantified subformula of a formula of [sources] that applies no
   unknown, with each of its free variables replaced by a term of the same
   sort the unknown reaches, at most [limit] instantiations per subformula.
   A contract's postcondition stated over a call's result
   ([forall j. 0 <= j < len r => r[j] >= k]) becomes the same fact over the
   loop's accumulator.  A subformula with a free variable of a sort no
   parameter reaches is skipped.  [sources] is a list of groups in priority
   order (the input's own assertions before the preprocessed clauses, whose
   quantifiers are mostly the ones preprocessing introduced); within a
   group the universals come before the existentials and the smaller before
   the larger, and the first [limit] atoms in that order after
   deduplication by normal form are kept. *)
(* With [frame] (a sublist of [params]), the subformulas instantiated are
   the ones without it, and each of them that has a free variable of an
   opaque sort (a sort variable, an uninterpreted sort, a datatype) some
   term reached from [frame] has is instantiated afresh, every such variable
   filled from the frame terms only, in place of its instances of before; a subformula with no such variable keeps its instances.  So the
   subformulas are the same as without [frame] (a quota left over by a
   subformula that now has fewer instances is not refilled from other facts:
   that brought heavier universals in, which as hypotheses slowed every
   question of a pass), and the instances differ only in where they put
   their frame-sorted variables.  [frame] is meant to be the parameters
   every loop of the unknown passes on unchanged ([frame_positions]): a
   fact the input states about a function's own arguments (a precondition
   over [iter], [init], [f]) is inductive over a loop that keeps those
   arguments, while its instances at the loop's moving values (the current
   iterator, the accumulator, the closure state) are typically not, each
   cost the pre-pass a question that the solver could leave undecided at its
   whole budget, and the instance at the kept values may not have been among
   the first [limit] at all.  With [frame = []] the atoms are those of
   before.  Only which candidates are offered changes, so this can lose an
   answer (an instance at a moving value that was needed) and never make
   one wrong. *)
(* [quantified_facts_split] is [quantified_facts] returning a pair
   [(inside, beside)].  With [closed_beside = false] (the default), [inside]
   is [quantified_facts]' list and [beside] is empty.  With
   [closed_beside = true], a closed atom (no free term variable: a sentence,
   a constant over the unknown's parameters) does not count against
   [limit]: of the ordered, deduplicated atoms, the first [limit] are the
   window [quantified_facts] keeps; [inside] is built from the window's
   atoms that are not closed, and [beside] from the window's closed atoms
   followed by the next atoms that are not closed, as many as the window
   had closed ones (so [limit] atoms that are not closed in all, when there
   are that many).  With [frame] both are then built as [quantified_facts]
   builds its list, from the inside atoms first.
   Contract: (1) every atom of [inside] is in [quantified_facts]' list, so a
   quota that ranks [inside] in place of that list keeps every atom it kept
   that is in [inside] (removing atoms from a ranked pool never demotes
   another); (2) every atom of [quantified_facts]' list is in [inside] or in
   [beside]; [beside] holds no atom of [inside].  So a caller that offers
   [beside] outside every limit and quota offers every atom offered without
   the switch, and only adds candidates.  Why: a sentence the input states
   (one a preprocessing step dropped as valid stays in the input's own
   record) is instantiated as it is, and being small it ranked ahead of the
   open facts and took the slot of the last one, which an answer needed.
   Adding candidates cannot make an answer wrong: the pre-pass reports a
   fixed point only after the ordinary check against every clause. *)
let rec quantified_facts ?stop ?frame ~limit ~sources params =
  fst
    (quantified_facts_split ?stop ?frame ~closed_beside:false ~limit ~sources
       params)

and quantified_facts_split ?(stop = fun () -> false) ?(frame = [])
    ?(closed_beside = false) ~limit ~(sources : Formula.t list list)
    (params : sort_env_list) =
  if limit <= 0 then ([], [])
  else
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let instances_with reached q =
      let fvs = Set.to_list (Formula.term_sort_env_of q) in
      let cands = List.map fvs ~f:(fun (_, s) -> reached s) in
      if List.exists cands ~f:List.is_empty then []
      else
        List.filter_map (tuples limit cands) ~f:(fun ts ->
            poll stop;
            let sub =
              Map.Poly.of_alist_exn (List.zip_exn (List.map fvs ~f:fst) ts)
            in
            let q = Formula.subst sub q in
            if Set.is_subset (Formula.tvs_of q) ~of_:pset then Some q else None)
    in
    let instances = instances_with (reached_of_sort params) in
    (* the sorts the restriction applies to: a sort variable, an
       uninterpreted sort or a datatype -- the values a program passes
       around without comparing them by size (a closure's state, an
       iterator, an accumulator of a generic type).  An integer, real,
       Boolean, bit-vector, sequence or array variable is filled as before:
       a fact over those is typically a range or a length relation between
       a kept bound and a moving counter ([forall x. lo <= x < cur => ...]),
       and the moving instance is the one a loop needs *)
    let opaque = function
      | Sort.SVar _ | T_dt.SUS _ | T_dt.SDT _ -> true
      | _ -> false
    in
    let frame_terms s = if opaque s then reached_of_sort frame s else [] in
    (* whether [q] has a free variable of such a sort a frame term has *)
    let frame_sorted q =
      (not (List.is_empty frame))
      && Set.exists (Formula.term_sort_env_of q) ~f:(fun (_, s) ->
          not (List.is_empty (frame_terms s)))
    in
    let frame_instances =
      instances_with (fun s ->
          match frame_terms s with [] -> reached_of_sort params s | ts -> ts)
    in
    let normal_atoms phis =
      List.filter_map phis ~f:(fun phi ->
          poll stop;
          let phi = normal phi in
          if literal phi then None else Some (Formula.str_of phi, phi))
    in
    (* each atom with the subformula it instantiates *)
    let rank group =
      List.fold group ~init:[] ~f:quantified_subformulas
      |> List.concat_map ~f:(fun q ->
          List.map (normal_atoms (instances q)) ~f:(fun (k, p) -> (k, p, q)))
      |> List.dedup_and_sort ~compare:(fun (s1, p1, _) (s2, p2, _) ->
          match Bool.compare (Formula.is_exists p1) (Formula.is_exists p2) with
          | 0 -> (
              match Int.compare (Formula.ast_size p1) (Formula.ast_size p2) with
              | 0 -> String.compare s1 s2
              | c -> c)
          | c -> c)
    in
    let seen = Hash_set.create (module String) in
    let ordered =
      List.concat_map sources ~f:rank
      |> List.filter ~f:(fun (key, _, _) ->
          if Hash_set.mem seen key then false
          else (
            Hash_set.add seen key;
            true))
    in
    let window = List.take ordered limit in
    (* each selected atom tagged [true] when it goes [beside] *)
    let selected =
      if not closed_beside then List.map window ~f:(fun a -> (a, false))
      else
        let closed (_, p, _) = Set.is_empty (Formula.tvs_of p) in
        let win_closed, win_open = List.partition_tf window ~f:closed in
        if List.is_empty win_closed then List.map window ~f:(fun a -> (a, false))
        else (
          (* an instrument, deciding nothing: one event per unknown whose
             window had a closed atom, so a run says whether the switch
             changed its candidate list *)
          Common.PhaseTime.event_here "houdini-quantified-closed-beside";
          let extra =
            List.filter ordered ~f:(Fn.non closed)
            |> Fn.flip List.take limit
            |> Fn.flip List.drop (List.length win_open)
          in
          if not (List.is_empty extra) then
            Common.PhaseTime.event_here "houdini-quantified-closed-beside-extra";
          List.map win_open ~f:(fun a -> (a, false))
          @ List.map (win_closed @ extra) ~f:(fun a -> (a, true)))
    in
    let tagged =
      if List.is_empty frame then
        List.map selected ~f:(fun ((_, p, _), b) -> (p, b))
      else
        (* each frame-sorted subformula's atoms replaced, at the place of its
           first one, by its frame instances *)
        let out = Hash_set.create (module String) in
        let replaced = Hash_set.create (module String) in
        List.concat_map selected ~f:(fun ((key, phi, q), b) ->
            if not (frame_sorted q) then
              if Hash_set.mem out key then []
              else (
                Hash_set.add out key;
                [ (phi, b) ])
            else
              let qk = Formula.str_of q in
              if Hash_set.mem replaced qk then []
              else (
                Hash_set.add replaced qk;
                List.filter_map
                  (normal_atoms (frame_instances q))
                  ~f:(fun (k, p) ->
                    if Hash_set.mem out k then None
                    else (
                      Hash_set.add out k;
                      Some (p, b)))))
    in
    let beside, inside = List.partition_tf tagged ~f:snd in
    (List.map inside ~f:fst, List.map beside ~f:fst)

(* The parameter positions (from 0) of the unknown [p] that every clause
   applying [p] both in its head and in its body passes on unchanged: at
   such a position, each head application and each body application of [p]
   in the clause have the same variable.  [[]] when no clause applies [p]
   on both sides (no loop, so nothing is kept by one), and a position where
   some clause passes anything other than one same variable (a term, or two
   variables an equation of the clause's pure part identifies) is not
   reported: the test is syntactic and can only answer [false] where the
   position is in fact unchanged.  A function of the clauses only. *)
let frame_positions (clauses : Clause.t list) (p : Ident.tvar) : int list =
  let apps atoms =
    List.filter_map (Set.to_list atoms) ~f:(fun a ->
        match Logic.Term.let_apps a with
        | Logic.Var (q, _), args when Ident.tvar_equal p q -> Some args
        | _ -> None)
  in
  let loops =
    List.filter_map clauses ~f:(fun ((_, ps, ns, _) : Clause.t) ->
        match (apps ps, apps ns) with
        | [], _ | _, [] -> None
        | hs, bs -> Some (hs @ bs))
  in
  match loops with
  | [] -> []
  | (first :: _) :: _ ->
      List.filter
        (List.range 0 (List.length first))
        ~f:(fun i ->
          List.for_all loops ~f:(fun apps ->
              match
                List.map apps ~f:(fun args ->
                    match List.nth args i with
                    | Some (Logic.Var (x, _)) -> Some x
                    | _ -> None)
              with
              | Some x :: rest ->
                  List.for_all rest ~f:(function
                    | Some y -> Ident.tvar_equal x y
                    | None -> false)
              | _ -> false))
  | [] :: _ -> []

(* Relation inclusions between two reached terms: for a relation [R] the
   unknown carries -- a reached term whose sort is an array, curried to
   depth k >= 2, ending in [Bool], as in [memberships] -- with first index
   sort [s], and for each ordered pair [(t1, t2)] of distinct terms (by
   printed form) of sort [s] reached from all of [params],
     [forall x2 ... xk. R[t1][x2]...[xk] = true => R[t2][x2]...[xk] = true];
   and for a non-recursive Bool-valued definition [d] of [defs] with k >= 2
   formals, the first of sort [s], the same with [d]'s body instantiated
   ([forall x2 ... xk. d(t1, x2, ...) => d(t2, x2, ...)]).  This is the
   fact a loop keeps between an iterator's entry state and its current one
   ([forall x. produces(cur it, x) => produces(cur e, x)]): what remains to
   be produced from here was producible from the start.

   Contract: [limit <= 0] gives [[]]; otherwise at most [limit] pairs per
   relation or definition and at most [limit] atoms in all (the smallest
   by [Formula.ast_size] after normalisation, [smallest]); every atom is a
   universal whose free variables are among [params] (the bound names are
   chosen apart from [params], so no parameter is captured); a relation of
   depth 1 or a definition of one formal gives nothing (there is no
   remaining argument to quantify, and the quantifier-free implication is
   not a conjunct a loop invariant usually needs); a sort with fewer than two
   reached terms gives nothing.  A function of [params]' names and sorts and
   of [defs] only.  [stop] is polled once per atom built, as in the other
   families, so the pre-pass's whole-pass budget covers this one too. *)
(* The syntactic test behind [houdini.candidates.inclusions.skip_constructor_equations].
   [constructor_equation_body ~varied ~rest body] holds when [body] is an
   equation, either side first, between a variable [x] of [rest] and a
   constructor application [c(u1, ..., un)] such that [x] occurs in no
   [ui], [varied] occurs in some [ui], and every [ui] that mentions
   [varied] IS the variable [varied].

   Equivalence (in the standard structure, where a datatype is its term
   algebra and a constructor is injective): with [d] that definition,
   [forall rest'. d(t1, rest') => d(t2, rest')] is
   [forall rest'. x = c(u[t1]) => x = c(u[t2])]; instantiating [x] at
   [c(u[t1])] (the one-point rule, sound because [x] is not in the [ui])
   gives [forall rest''. c(u[t1]) = c(u[t2])], by injectivity
   [forall rest''. /\ ui[t1] = ui[t2]]; an argument without [varied] gives
   [ui = ui], and one that is [varied] gives [t1 = t2], so the inclusion
   is equivalent to [t1 = t2], and [t1 = t2] implies it back.  The frame
   family offers that equation exactly when [t1] and [t2] start at two
   different parameters and their sort is [equatable] ([skip_pair]); for
   a pair of one parameter, or of a Boolean or array sort, the inclusion
   is kept.  An argument that is a proper function of [varied] ([fst a],
   [a + 1]) makes the inclusion only implied by [t1 = t2], strictly
   weaker, so it is not skipped: an invariant may need the weaker fact.
   The frame family's own [limit] may still cut the equation; the skip
   does not look at that cut. *)
let constructor_equation_body ~varied ~(rest : sort_env_list) body =
  Formula.is_eq body
  &&
  let l, r, _ = Formula.let_eq body in
  let rest_vars = Set.Poly.of_list (List.map rest ~f:fst) in
  let mentions v u = Set.mem (Term.tvs_of u) v in
  let shape x c =
    match (x, c) with
    | Term.Var (x, _, _), Term.FunApp (T_dt.DTCons _, us, _)
      when Set.mem rest_vars x ->
        (not (List.exists us ~f:(mentions x)))
        && List.exists us ~f:(mentions varied)
        && List.for_all us ~f:(fun u ->
            (not (mentions varied u))
            ||
            match u with
            | Term.Var (y, _, _) -> Stdlib.(y = varied)
            | _ -> false)
    | _ -> false
  in
  shape l r || shape r l

(* the pairs of reached terms the frame family equates: two different
   starting parameters (each reached term mentions exactly its parameter)
   and an [equatable] sort *)
let skip_pair t1 t2 =
  equatable (Term.sort_of t1)
  && not (Set.equal (Term.tvs_of t1) (Term.tvs_of t2))

(* With [guard = Some (y, g)] (a formula [g] over the one integer variable
   [y], as [range_guards] returns), every atom carries [g] on each of its
   integer binders as one more premise
   ([forall x2 ... xk. g[x2] /\ ... /\ R[t1][x2]...[xk] = true => ...]), and a
   relation or definition with no integer binder after its first argument
   gives nothing; otherwise the contract above, unchanged.  A guarded atom
   is implied by its unguarded one, so the family offers a weaker fact, which
   is what a loop keeps when every step states the inclusion only inside the
   guard. *)
let inclusions ?(stop = fun () -> false) ?(skip_constructor_equations = false)
    ?guard ~limit ~(defs : FunEnv.t) (params : sort_env_list) =
  if limit <= 0 then []
  else
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let over_params q = Set.is_subset (Formula.tvs_of q) ~of_:pset in
    (* the premise [guard] puts on the binders [bs]: [Some None] without a
       guard, [Some (Some g)] with one and an integer binder, [None] with
       one and no integer binder (the atom is not offered) *)
    let premise bs =
      match guard with
      | None -> Some None
      | Some (y, g) -> (
          match
            List.filter_map bs ~f:(fun (x, s) ->
                if Term.is_int_sort s then
                  Some
                    (Formula.subst
                       (Map.Poly.singleton y (Term.mk_var x s))
                       g)
                else None)
          with
          | [] -> None
          | gs -> Some (Some (Formula.and_of gs)))
    in
    let implication bs lhs rhs =
      match premise bs with
      | None -> None
      | Some None -> Some (Formula.forall bs (Formula.mk_imply lhs rhs))
      | Some (Some g) ->
          Some
            (Formula.forall bs
               (Formula.mk_imply (Formula.mk_and g lhs) rhs))
    in
    (* bound names [hincl1, hincl2, ...], each made apart from [params] *)
    let binders sorts =
      List.mapi sorts ~f:(fun i s ->
          let rec pick name =
            if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
            else Ident.Tvar name
          in
          (pick (sprintf "hincl%d" (i + 1)), s))
    in
    let distinct_reached s =
      List.dedup_and_sort (reached_of_sort params s) ~compare:(fun a b ->
          String.compare (Term.str_of a) (Term.str_of b))
    in
    let pairs ts =
      List.take
        (List.concat_map ts ~f:(fun t1 ->
             List.filter_map ts ~f:(fun t2 ->
                 if String.equal (Term.str_of t1) (Term.str_of t2) then None
                 else Some (t1, t2))))
        limit
    in
    let rels =
      List.concat_map (reached params) ~f:(fun (_, r) ->
          match CellQual.uncurry_array_sort (Term.sort_of r) with
          | s :: (_ :: _ as rest), e when Term.is_bool_sort e ->
              let bs = binders rest in
              let xs = List.map bs ~f:(fun (x, s) -> Term.mk_var x s) in
              let mem t =
                Formula.eq
                  (T_array.mk_select_app r (t :: xs))
                  (T_bool.mk_true ())
              in
              List.filter_map
                (pairs (distinct_reached s))
                ~f:(fun (t1, t2) ->
                  poll stop;
                  implication bs (mem t1) (mem t2))
          | _ -> [])
    in
    let defined =
      Map.Poly.to_alist defs
      |> List.concat_map ~f:(fun (_, (fargs, sret, body, isrec, _)) ->
          match fargs with
          | (f1, s) :: (_ :: _ as rest)
            when (not isrec) && Term.is_bool_sort sret ->
              let bs = binders (List.map rest ~f:snd) in
              let body = Formula.of_bool_term body in
              let ctor_eq =
                skip_constructor_equations
                && constructor_equation_body ~varied:f1 ~rest body
              in
              let inst t =
                Formula.subst
                  (Map.Poly.of_alist_exn
                     ((f1, t)
                     :: List.map2_exn rest bs ~f:(fun (y, _) (x, s) ->
                         (y, Term.mk_var x s))))
                  body
              in
              List.filter_map
                (pairs (distinct_reached s))
                ~f:(fun (t1, t2) ->
                  poll stop;
                  if ctor_eq && skip_pair t1 t2 then None
                  else
                    match implication bs (inst t1) (inst t2) with
                    | Some q when over_params q -> Some q
                    | _ -> None)
          | _ -> [])
    in
    smallest ~stop ~limit (rels @ defined)

(* The ranges the input states for a bound integer variable.  Read the body
   of a universal binding an integer [x] as a disjunction (an implication
   [a => b] as the negated conjuncts of [a] and the disjuncts of [b]), and
   the body of an existential as a conjunction; call a part an integer
   literal on [x] when it is a comparison of integers, or its negation, that
   mentions [x].  When every integer literal on [x] mentions no variable
   other than [x], there is at least one, and some part is not one, the
   guard is their conjunction (for a universal, of their negations): the
   range under which the rest is stated, with constant bounds
   ([-2^63 <= x /\ x < 2^63], the one a frontend puts on every quantified
   variable of a machine-integer type).  A binder with an integer literal
   that mentions another variable ([0 <= k /\ k < len s]) gives no guard:
   its range is not constant, and the constant half alone ([0 <= k]) would
   be a guard the input never states.

   Contract: each guard is returned as [(y, g)] with [y] one fixed variable
   name and [tvs_of g = {y}]; without repetition by printed form; at most
   [limit], the smallest by [Formula.ast_size] first (ties by printed
   form); [limit <= 0] gives [[]].  A function of [sources] only.  Formulas
   embedded in terms are not looked into. *)
let range_guards ~limit (sources : Formula.t list) =
  if limit <= 0 then []
  else
    let y = Ident.Tvar "hguard" in
    let int_comparison = function
      | Formula.Atom (Atom.App (Predicate.Psym _, t :: _, _), _)
      | Formula.UnaryOp
          ( Formula.Not,
            Formula.Atom (Atom.App (Predicate.Psym _, t :: _, _), _),
            _ ) -> (
          (* a term whose sort cannot be read is not taken as an integer *)
          try Term.is_int_sort (Term.sort_of t)
          with exn_ when not (Common.Timer.is_async exn_) -> false)
      | _ -> false
    in
    let int_literal_on x d =
      int_comparison d && Set.mem (Formula.tvs_of d) x
    in
    let alone x d =
      Set.is_empty (Formula.pvs_of d)
      && Set.equal (Formula.tvs_of d) (Set.Poly.singleton x)
    in
    let rec disjuncts phi =
      match phi with
      | Formula.BinaryOp (Formula.Or, a, b, _) -> disjuncts a @ disjuncts b
      | Formula.BinaryOp (Formula.Imply, a, b, _) ->
          List.map (Formula.conjuncts_list_of a) ~f:Formula.negate
          @ disjuncts b
      | _ -> [ phi ]
    in
    let guard_of ~exists x body =
      let parts =
        if exists then Formula.conjuncts_list_of body else disjuncts body
      in
      let own, rest = List.partition_tf parts ~f:(int_literal_on x) in
      if
        List.is_empty own || List.is_empty rest
        || not (List.for_all own ~f:(alone x))
      then None
      else
        let g =
          Formula.and_of (if exists then own else List.map own ~f:Formula.negate)
        in
        Some
          (Formula.subst (Map.Poly.singleton x (Term.mk_var y T_int.SInt)) g)
    in
    let rec go acc phi =
      match phi with
      | Formula.Bind (((Formula.Forall | Formula.Exists) as b), bs, body, _) ->
          let exists = match b with Formula.Exists -> true | _ -> false in
          let acc =
            List.fold bs ~init:acc ~f:(fun acc (x, s) ->
                if Term.is_int_sort s then
                  match guard_of ~exists x body with
                  | Some g -> g :: acc
                  | None -> acc
                else acc)
          in
          go acc body
      | Formula.Bind (_, _, body, _) -> go acc body
      | Formula.UnaryOp (_, p, _) -> go acc p
      | Formula.BinaryOp (_, p, q, _) -> go (go acc p) q
      | Formula.LetFormula (_, _, _, p, _) -> go acc p
      | _ -> acc
    in
    List.fold sources ~init:[] ~f:go
    |> List.map ~f:(fun g -> (Formula.ast_size g, Formula.str_of g, g))
    |> List.dedup_and_sort ~compare:(fun (n1, s1, _) (n2, s2, _) ->
        match Int.compare n1 n2 with 0 -> String.compare s1 s2 | c -> c)
    |> Fn.flip List.take limit
    |> List.map ~f:(fun (_, _, g) -> (y, g))

(* The inclusions of [inclusions], each guarded by one of [guards] (from
   [range_guards]) on its integer binders: at most [limit] in all, the
   smallest first, each guard contributing at most [limit / |guards|]
   (at least one), so that a small guard does not fill the quota alone;
   [inclusions]' contract otherwise.  [guards = []] gives [[]].  Only which candidates are offered changes: a guarded
   inclusion is a weaker fact than its unguarded one and is kept only if the
   fixed point finds it inductive. *)
let guarded_inclusions ?(stop = fun () -> false)
    ?(skip_constructor_equations = false) ~guards ~limit ~defs params =
  if limit <= 0 then []
  else
    let per = max 1 (limit / max 1 (List.length guards)) in
    smallest ~stop ~limit
      (List.concat_map guards ~f:(fun guard ->
           inclusions ~stop ~skip_constructor_equations ~guard ~limit:per
             ~defs params))

(* {3 Counting families: length sums, affine elements, three-term
   equations}

   Three families over the integer and sequence terms an unknown reaches
   ([reached]), for the facts a loop over a counting range keeps: how many
   items it has collected, what they are, and how far it has gone. *)

(* [atoms] with each atom normalised, without literals and repetitions (by
   the printed normal form), at most [limit], taken in the order of the
   atoms' sizes BEFORE normalisation (ties by printed form): unlike
   [smallest], only the atoms up to the [limit]-th distinct one are
   normalised, so a cubic family costs [limit] normalisations and a sort *)
let smallest_raw ?(stop = fun () -> false) ~limit atoms =
  let sorted =
    List.map atoms ~f:(fun phi ->
        (Formula.ast_size phi, Formula.str_of phi, phi))
    |> List.sort ~compare:(fun (n1, s1, _) (n2, s2, _) ->
        match Int.compare n1 n2 with 0 -> String.compare s1 s2 | c -> c)
  in
  let seen = Hash_set.create (module String) in
  let rec take n acc = function
    | [] -> List.rev acc
    | _ when n <= 0 -> List.rev acc
    | (_, _, phi) :: rest ->
        poll stop;
        let phi = normal phi in
        let key = Formula.str_of phi in
        if literal phi || Hash_set.mem seen key then take n acc rest
        else (
          Hash_set.add seen key;
          take (n - 1) (phi :: acc) rest)
  in
  take limit [] sorted

(* the reached integer terms and the reached sequence terms, each without
   repetition by printed form, in [reached]'s order *)
let ints_and_seqs (params : sort_env_list) =
  let dedup ts =
    let seen = Hash_set.create (module String) in
    List.filter ts ~f:(fun t ->
        let k = Term.str_of t in
        if Hash_set.mem seen k then false
        else (
          Hash_set.add seen k;
          true))
  in
  let ts = List.map (reached params) ~f:snd in
  ( dedup (List.filter ts ~f:(fun t -> Term.is_int_sort (Term.sort_of t))),
    dedup
      (List.filter ts ~f:(fun t ->
           match Term.sort_of t with T_seq.SSeq _ -> true | _ -> false)) )

let same_term t1 t2 = String.equal (Term.str_of t1) (Term.str_of t2)

(* Empty-guarded frame equations: [len s = 0 => u = v] for [s] a reached
   sequence and [u = v] a frame equation ([frame_equations] at the same
   [limit]) -- [len sk = 0 => m.0 = s.0]: while the history a loop keeps
   is empty, the iterator it advances is still the one it started from,
   and the unguarded frame equation is refuted by the step clause.  The
   guards of [guarded_frame_equations] equate two reached integer terms and
   cannot say this, since [0] is not a reached term.  The sequence is the
   outer loop, so a small limit keeps every frame equation under the first
   sequences rather than one equation under every sequence.

   Contract: [limit <= 0] gives [[]]; otherwise at most [limit]
   quantifier-free implications whose free variables are among [params],
   without repetition by printed form, each [len s = 0 => e] with [s] a
   reached sequence term and [e] one of [frame_equations ~limit params];
   no reached sequence, or no frame equation, gives nothing.  A function of
   [params]' names and sorts only; [stop] is polled once per atom built. *)
let empty_guarded_frames ?(stop = fun () -> false) ~limit
    (params : sort_env_list) =
  if limit <= 0 then []
  else
    let _, seqs = ints_and_seqs params in
    let frames =
      if List.is_empty seqs then [] else frame_equations ~stop ~limit params
    in
    let seen = Hash_set.create (module String) in
    List.concat_map seqs ~f:(fun s ->
        match Term.sort_of s with
        | T_seq.SSeq se ->
            let guard = Formula.eq (T_seq.mk_len se s) (T_int.zero ()) in
            List.map frames ~f:(fun f ->
                poll stop;
                Formula.mk_imply guard f)
        | _ -> [])
    |> List.filter ~f:(fun phi ->
        let key = Formula.str_of phi in
        if Hash_set.mem seen key then false
        else (
          Hash_set.add seen key;
          true))
    |> Fn.flip List.take limit

(* Length sums: [len s + x = t] (written [len s = t] when [x] is zero) for
   [s] a reached sequence, [x] zero or a reached integer term, and [t] a
   reached integer term or the length of another reached sequence, with
   [t] neither [x] nor [len s] -- [len out + a.0 = b.0], the number of
   items a loop has collected from a range it has advanced from [a] to
   [b].

   Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, each
   a normalised equation whose free variables are among [params], the
   smallest before normalisation first ([smallest_raw]), so the [x = 0]
   forms come before the shifted ones; no sequence reached gives nothing.
   A function of [params]' names and sorts only; [stop] is polled once
   per atom built and once per atom normalised. *)
let length_sums ?(stop = fun () -> false) ~limit (params : sort_env_list) =
  if limit <= 0 then []
  else
    let ints, seqs = ints_and_seqs params in
    let len_of s =
      match Term.sort_of s with
      | T_seq.SSeq se -> T_seq.mk_len se s
      | _ -> assert false
    in
    let lens = List.map seqs ~f:len_of in
    let shifts = T_int.zero () :: ints in
    smallest_raw ~stop ~limit
    @@ List.concat_map lens ~f:(fun len ->
        List.concat_map shifts ~f:(fun x ->
            List.filter_map (ints @ lens) ~f:(fun t ->
                poll stop;
                if same_term t x || same_term t len then None
                else
                  let lhs =
                    if T_int.is_zero x then len else T_int.mk_add len x
                  in
                  Some (Formula.eq lhs t))))

(* Last-element equations: [v = s[len t]] for [v] a reached term, [s] a
   reached sequence whose elements have [v]'s sort and [t] another reached
   sequence -- [g = fs[len s]]: a loop that keeps its history in ghost
   sequences holds the current value (the closure's state, the
   accumulator) as the last entry of a history one longer than the history
   of produced items, and no other family states it, since [len t] reaches
   no parameter.

   Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, each
   a normalised equation whose free variables are among [params], the
   smallest before normalisation first ([smallest_raw]); no reached
   sequence of a reached term's sort gives nothing, and [s[len s]] (a read
   past the end) is never built.  A function of [params]' names and sorts
   only; [stop] is polled once per atom built and once per atom
   normalised. *)
let last_element_equations ?(stop = fun () -> false) ~limit
    (params : sort_env_list) =
  if limit <= 0 then []
  else
    let _, seqs = ints_and_seqs params in
    let vs =
      List.filter_map (reached params) ~f:(fun (_, v) ->
          let s = Term.sort_of v in
          if equatable s then Some v else None)
    in
    smallest_raw ~stop ~limit
    @@ List.concat_map seqs ~f:(fun s ->
        match Term.sort_of s with
        | T_seq.SSeq se ->
            List.concat_map seqs ~f:(fun t ->
                if same_term s t then []
                else
                  let len_t =
                    match Term.sort_of t with
                    | T_seq.SSeq te -> T_seq.mk_len te t
                    | _ -> assert false
                  in
                  List.filter_map vs ~f:(fun v ->
                      poll stop;
                      if
                        String.equal
                          (Term.str_of_sort (Term.sort_of v))
                          (Term.str_of_sort se)
                      then Some (Formula.eq v (T_seq.mk_nth se s len_t))
                      else None))
        | _ -> [])

(* Affine elements: [forall i. 0 <= i /\ i < len s => s[i] = t + i]
   (written [s[i] = i] when [t] is zero) for [s] a reached sequence of
   integers and [t] zero or a reached integer term (another reached
   sequence's length included, never [len s] itself) -- [out[i] = a.0 + i],
   the content of a sequence collected from the range starting at [a.0].

   Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, the
   smallest after normalisation first ([smallest]); every atom is a
   universal over one integer whose free variables are among [params], the
   bound name chosen apart from [params] so no parameter is captured; no
   reached sequence of integers gives nothing.  A function of [params]'
   names and sorts only; [stop] is polled once per atom built. *)
let affine_elements ?(stop = fun () -> false) ~limit (params : sort_env_list) =
  if limit <= 0 then []
  else
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let rec pick name =
      if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
      else Ident.Tvar name
    in
    let i = (pick "haff", T_int.SInt) in
    let iv = Term.mk_var (fst i) T_int.SInt in
    let ints, seqs = ints_and_seqs params in
    let int_seqs =
      List.filter seqs ~f:(fun s ->
          match Term.sort_of s with
          | T_seq.SSeq se -> Term.is_int_sort se
          | _ -> false)
    in
    let lens =
      List.map seqs ~f:(fun s ->
          match Term.sort_of s with
          | T_seq.SSeq se -> (s, T_seq.mk_len se s)
          | _ -> assert false)
    in
    smallest ~stop ~limit
    @@ List.concat_map int_seqs ~f:(fun s ->
        let len = T_seq.mk_len T_int.SInt s in
        let offsets =
          (T_int.zero () :: ints)
          @ List.filter_map lens ~f:(fun (u, l) ->
              if same_term u s then None else Some l)
        in
        List.map offsets ~f:(fun t ->
            poll stop;
            let value = if T_int.is_zero t then iv else T_int.mk_add t iv in
            Formula.forall [ i ]
              (Formula.mk_imply
                 (Formula.and_of
                    [ Formula.leq (T_int.zero ()) iv; Formula.lt iv len ])
                 (Formula.eq (T_seq.mk_nth T_int.SInt s iv) value))))

(* Prefix elements: [forall i. 0 <= i /\ i < x => s[i] = c] for [s] a
   reached sequence of integers, [x] a reached integer term (the length of
   another reached sequence included, never [len s] itself) and [c] one of
   [consts] -- the part of a sequence a loop has already overwritten with a
   constant ([fin[i] = 0] below the iterator's position), which no fact
   over the whole sequence states and which a contract's postcondition
   states only for the full range.

   Contract: [limit <= 0] or [consts = []] gives [[]]; otherwise at most
   [limit] atoms, in the order of [consts], then of the sequences, then of
   the bounds (not re-ranked by size: all atoms of the family have one
   shape), without repetition by printed normal form; every atom is a
   universal over one integer whose free variables are among [params], the
   bound name chosen apart from [params] so no parameter is captured; no
   reached sequence of integers or no reached integer term gives nothing.
   A function of [params]' names and sorts and of [consts] only; [stop] is
   polled once per atom built. *)
let prefix_elements ?(stop = fun () -> false) ~limit ~(consts : Term.t list)
    (params : sort_env_list) =
  if limit <= 0 || List.is_empty consts then []
  else
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let rec pick name =
      if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
      else Ident.Tvar name
    in
    let i = (pick "hpre", T_int.SInt) in
    let iv = Term.mk_var (fst i) T_int.SInt in
    let ints, seqs = ints_and_seqs params in
    let int_seqs =
      List.filter seqs ~f:(fun s ->
          match Term.sort_of s with
          | T_seq.SSeq se -> Term.is_int_sort se
          | _ -> false)
    in
    let lens =
      List.map seqs ~f:(fun s ->
          match Term.sort_of s with
          | T_seq.SSeq se -> (s, T_seq.mk_len se s)
          | _ -> assert false)
    in
    let seen = Hash_set.create (module String) in
    List.concat_map consts ~f:(fun c ->
        List.concat_map int_seqs ~f:(fun s ->
            let bounds =
              ints
              @ List.filter_map lens ~f:(fun (u, l) ->
                  if same_term u s then None else Some l)
            in
            List.map bounds ~f:(fun x -> (c, x, s))))
    |> List.filter_map ~f:(fun (c, x, s) ->
        poll stop;
        let phi =
          normal
          @@ Formula.forall [ i ]
               (Formula.mk_imply
                  (Formula.and_of
                     [ Formula.leq (T_int.zero ()) iv; Formula.lt iv x ])
                  (Formula.eq (T_seq.mk_nth T_int.SInt s iv) c))
        in
        let key = Formula.str_of phi in
        if literal phi || Hash_set.mem seen key then None
        else (
          Hash_set.add seen key;
          Some phi))
    |> Fn.flip List.take limit

(* the integer literals of [phis], each once, the smallest in absolute
   value first, at most [n]: the constants a loop writes are among the
   program's own literals *)
let sorted_int_literals (phis : Formula.t list) =
  List.concat_map phis ~f:(fun phi ->
      Set.to_list (Formula.filtered_terms_of ~f:T_int.is_int phi))
  |> List.dedup_and_sort ~compare:(fun t1 t2 ->
      let n1 = T_int.let_int t1 and n2 = T_int.let_int t2 in
      match Z.compare (Z.abs n1) (Z.abs n2) with 0 -> Z.compare n1 n2 | c -> c)

let int_literals ~n phis = List.take (sorted_int_literals phis) n

(* The input's assertions are read here in two ways only: as a group of
   [quantified_facts]' sources and through [int_literals].  A group [g] and
   the reversed list of its maximal quantified subformulas,
   [List.rev (List.fold g ~init:[] ~f:quantified_subformulas)], give
   [quantified_facts] the same list: each element of the second is a
   quantified formula that applies no unknown and is not [one_point], which
   [quantified_subformulas] returns whole, so folding over the reversed list
   rebuilds the list.  And [int_literals ~n] is a prefix of
   [sorted_int_literals].  So the digest below answers both readers exactly
   as the assertions do, and it is all of them that has to be held. *)
let quantified_group phis =
  List.rev (List.fold phis ~init:[] ~f:quantified_subformulas)

let digest_input_assertions () =
  match LogicOld.get_input_record () with
  | LogicOld.InputAsRead phis ->
      LogicOld.set_input_record
        (LogicOld.InputDigest
           {
             quantified = quantified_group phis;
             int_literals = sorted_int_literals phis;
           })
  | LogicOld.InputDigest _ -> ()

let input_quantified_group () =
  match LogicOld.get_input_record () with
  | LogicOld.InputAsRead phis -> phis
  | LogicOld.InputDigest { quantified; _ } -> quantified

let input_int_literals ~n =
  match LogicOld.get_input_record () with
  | LogicOld.InputAsRead phis -> int_literals ~n phis
  | LogicOld.InputDigest { int_literals; _ } -> List.take int_literals n

(* Three-term equations: [x = y - z] for three distinct reached integer
   terms (sequence lengths included, as in [int_terms]) -- [n = b.0 - it0.0],
   a counter equal to the distance between two positions.  [x = y - z] and
   [z = y - x] are one linear fact: only the one with [x] before [z] in
   [int_terms]' order is built, which halves the atoms built, and the two
   would anyway share a normal form ([0 = y - x - z]), which the
   deduplication of [smallest_raw] identifies.

   Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, each
   a normalised equation over [params], the smallest before normalisation
   first ([smallest_raw]); fewer than three distinct terms give nothing.  A
   function of [params]' names and sorts only; [stop] is polled once per
   atom built and once per atom normalised. *)
let three_term_equations ?(stop = fun () -> false) ~limit
    (params : sort_env_list) =
  if limit <= 0 then []
  else
    let ts =
      let seen = Hash_set.create (module String) in
      List.filter (int_terms params) ~f:(fun t ->
          let k = Term.str_of t in
          if Hash_set.mem seen k then false
          else (
            Hash_set.add seen k;
            true))
      |> List.mapi ~f:(fun i t -> (i, t))
    in
    smallest_raw ~stop ~limit
    @@ List.concat_map ts ~f:(fun (ix, x) ->
        List.concat_map ts ~f:(fun (iy, y) ->
            List.filter_map ts ~f:(fun (iz, z) ->
                poll stop;
                if ix < iz && iy <> ix && iy <> iz then
                  Some (Formula.eq x (T_int.mk_sub y z))
                else None)))

(* The element sorts of the sequences [phis] build by concatenation
   ([seq.++], a push [s ++ unit e] included), each once, ordered by printed
   sort.  A function of the formulas only; terms under binders and inside
   formulas embedded in terms are read too. *)
let concatenated_elem_sorts (phis : Formula.t list) : Sort.t list =
  List.concat_map phis ~f:(fun phi ->
      Set.to_list
      @@ Formula.filtered_terms_of phi ~f:(function
        | Term.FunApp (T_seq.SqConcat _, _, _) -> true
        | _ -> false))
  |> List.filter_map ~f:(function
    | Term.FunApp (T_seq.SqConcat se, _, _) -> Some se
    | _ -> None)
  |> List.dedup_and_sort ~compare:(fun a b ->
      String.compare (Term.str_of_sort a) (Term.str_of_sort b))

(* Shifted elements: [forall i. 0 <= i < len b => a[len c + i] = b[i]] for
   three pairwise distinct reached sequences [a], [b], [c] of one sort
   [Seq e], with [e] among [elem_sorts] -- [v[len v0 + i] = pushed[i]]: a
   loop that pushes every item it takes onto a sequence [a] that started as
   [c], and onto a history [b] of its own, keeps [b] as the part of [a] past
   [c]'s length, i.e. [a = c ++ b] pointwise.  No other family relates two
   sequences at an offset that is a third one's length: [affine_elements]
   relates a sequence to integers, and the inclusions relate memberships.
   [elem_sorts] is meant to be the element sorts of the sequences the
   problem's clauses build by concatenation ([concatenated_elem_sorts]), so
   that an input that never concatenates gets nothing from the family.

   Contract: [limit <= 0] or [elem_sorts = []] gives [[]]; otherwise at most
   [limit] atoms, the smallest after normalisation first ([smallest]); every
   atom is a universal over one integer whose free variables are among
   [params], the bound name chosen apart from [params] so no parameter is
   captured; fewer than three reached sequences of one admitted sort give
   nothing.  The number of atoms built is at most [n (n-1) (n-2)] for [n]
   reached sequences of one sort.  A function of [params]' names and sorts
   and of [elem_sorts] only; [stop] is polled once per atom built. *)
let shifted_elements ?(stop = fun () -> false) ~limit
    ~(elem_sorts : Sort.t list) (params : sort_env_list) =
  if limit <= 0 || List.is_empty elem_sorts then []
  else
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let rec pick name =
      if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
      else Ident.Tvar name
    in
    let i = (pick "hshf", T_int.SInt) in
    let iv = Term.mk_var (fst i) T_int.SInt in
    let _, seqs = ints_and_seqs params in
    let admitted se =
      List.exists elem_sorts ~f:(fun e ->
          String.equal (Term.str_of_sort e) (Term.str_of_sort se))
    in
    let seqs =
      List.filter_map seqs ~f:(fun s ->
          match Term.sort_of s with
          | T_seq.SSeq se when admitted se -> Some (s, se)
          | _ -> None)
    in
    let same_sort se1 se2 =
      String.equal (Term.str_of_sort se1) (Term.str_of_sort se2)
    in
    smallest ~stop ~limit
    @@ List.concat_map seqs ~f:(fun (a, se) ->
        List.concat_map seqs ~f:(fun (b, sb) ->
            if same_term a b || not (same_sort se sb) then []
            else
              List.filter_map seqs ~f:(fun (c, sc) ->
                  poll stop;
                  if same_term c a || same_term c b || not (same_sort se sc)
                  then None
                  else
                    Some
                      (Formula.forall [ i ]
                         (Formula.mk_imply
                            (Formula.and_of
                               [
                                 Formula.leq (T_int.zero ()) iv;
                                 Formula.lt iv (T_seq.mk_len se b);
                               ])
                            (Formula.eq
                               (T_seq.mk_nth se a
                                  (T_int.mk_add (T_seq.mk_len se c) iv))
                               (T_seq.mk_nth se b iv)))))))

(* Affix elements: for two distinct reached sequences [a], [b] of one sort
   [Seq e], the prefix universal
   [forall i. 0 <= i < len b => a[i] = b[i]] ([b] is a prefix of [a]) and
   the suffix universal
   [forall i. 0 <= i < len b => a[len a - len b + i] = b[i]] ([b] is a
   suffix of [a]).  The prefix is the half of [a = b ++ c] that
   [shifted_elements] does not state: a loop that pushes onto a sequence
   [a] that started as [b] keeps [b] as [a]'s prefix ([*v = *vec ++
   produced] of an [extend] loop needs both halves, and the shifted
   family gives only the part past [len b]).  The suffix is what a loop
   that consumes a sequence from its front keeps: the rest [b] of the
   sequence [a] it started from ([it = v0[len v0 - len it ..]] of a
   slice iterator).  Neither can be stated by the other families:
   [prefix_elements] equates a prefix to a constant, [affine_elements] a
   sequence to integers, and the frame equations whole terms.  Neither
   atom says anything about lengths: [len b <= len a], which makes the
   indices in range, is the length families' (and the solver's) to
   state; without it an index past [a]'s end reads an unconstrained
   element, which a later clause still has to agree with.

   Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, the
   smallest after normalisation first ([smallest]); every atom is a
   universal over one integer whose free variables are among [params],
   the bound name chosen apart from [params] so no parameter is captured;
   fewer than two reached sequences of one element sort give nothing.
   With [n] reached sequences of one sort the family builds [2 n (n-1)]
   atoms before the cut.  A function of [params]' names and sorts only;
   [stop] is polled once per atom built. *)
let affix_elements ?(stop = fun () -> false) ~limit (params : sort_env_list) =
  if limit <= 0 then []
  else
    let pset = Set.Poly.of_list (List.map params ~f:fst) in
    let rec pick name =
      if Set.mem pset (Ident.Tvar name) then pick (name ^ "_")
      else Ident.Tvar name
    in
    let i = (pick "haff", T_int.SInt) in
    let iv = Term.mk_var (fst i) T_int.SInt in
    let _, seqs = ints_and_seqs params in
    let seqs =
      List.filter_map seqs ~f:(fun s ->
          match Term.sort_of s with T_seq.SSeq se -> Some (s, se) | _ -> None)
    in
    let same_sort se1 se2 =
      String.equal (Term.str_of_sort se1) (Term.str_of_sort se2)
    in
    let in_b se b =
      Formula.and_of
        [ Formula.leq (T_int.zero ()) iv; Formula.lt iv (T_seq.mk_len se b) ]
    in
    smallest ~stop ~limit
    @@ List.concat_map seqs ~f:(fun (a, se) ->
        List.concat_map seqs ~f:(fun (b, sb) ->
            poll stop;
            if same_term a b || not (same_sort se sb) then []
            else
              [
                Formula.forall [ i ]
                  (Formula.mk_imply (in_b se b)
                     (Formula.eq (T_seq.mk_nth se a iv) (T_seq.mk_nth se b iv)));
                Formula.forall [ i ]
                  (Formula.mk_imply (in_b se b)
                     (Formula.eq
                        (T_seq.mk_nth se a
                           (T_int.mk_add
                              (T_int.mk_sub (T_seq.mk_len se a)
                                 (T_seq.mk_len se b))
                              iv))
                        (T_seq.mk_nth se b iv)));
              ]))

(* Concatenation equations: [a = c ++ b] for three pairwise distinct
   reached sequences [a], [b], [c] of one sort [Seq e], with [e] among
   [elem_sorts] -- [*v = *vec ++ produced]: the whole of what
   [shifted_elements] and the prefix atom of [affix_elements] state
   pointwise, as one quantifier-free equation, which the solver decides
   without instantiating a universal, and from which a postcondition
   stated as a concatenation follows without extensionality over
   sequences.  [elem_sorts] is meant to
   be [concatenated_elem_sorts] of the problem's clauses, as for the
   shifted family: an input that never concatenates gets nothing.

   Contract: [limit <= 0] or [elem_sorts = []] gives [[]]; otherwise at
   most [limit] atoms, the smallest after normalisation first
   ([smallest]); each an equation between sequence terms whose free
   variables are among [params]; fewer than three reached sequences of one
   admitted sort give nothing.  The number of atoms built is at most
   [n (n-1) (n-2)] for [n] reached sequences of one sort.  A function of
   [params]' names and sorts and of [elem_sorts] only; [stop] is polled
   once per atom built. *)
let concat_equations ?(stop = fun () -> false) ~limit
    ~(elem_sorts : Sort.t list) (params : sort_env_list) =
  if limit <= 0 || List.is_empty elem_sorts then []
  else
    let _, seqs = ints_and_seqs params in
    let admitted se =
      List.exists elem_sorts ~f:(fun e ->
          String.equal (Term.str_of_sort e) (Term.str_of_sort se))
    in
    let seqs =
      List.filter_map seqs ~f:(fun s ->
          match Term.sort_of s with
          | T_seq.SSeq se when admitted se -> Some (s, se)
          | _ -> None)
    in
    let same_sort se1 se2 =
      String.equal (Term.str_of_sort se1) (Term.str_of_sort se2)
    in
    smallest ~stop ~limit
    @@ List.concat_map seqs ~f:(fun (a, se) ->
        List.concat_map seqs ~f:(fun (b, sb) ->
            if same_term a b || not (same_sort se sb) then []
            else
              List.filter_map seqs ~f:(fun (c, sc) ->
                  poll stop;
                  if same_term c a || same_term c b || not (same_sort se sc)
                  then None
                  else Some (Formula.eq a (T_seq.mk_concat se c b)))))

(* Guarded orders: [len s = 0 \/ t1 <= t2] for [s] a reached sequence and
   [t1], [t2] two distinct reached integer terms (sequence lengths not
   included) -- [len out = 0 \/ b.0 <= b.1]: a range iterator that has
   produced an item was not past its end, while the empty production
   starts from any range, so the unguarded order is refuted by the fact
   clause and only the guarded one is inductive.

   Contract: [limit <= 0] gives [[]]; otherwise at most [limit] atoms, each
   a normalised disjunction over [params], the smallest before
   normalisation first ([smallest_raw]); no reached sequence, or fewer than
   two reached integer terms, gives nothing.  A function of [params]'
   names and sorts only; [stop] is polled once per atom built and once per
   atom normalised. *)
let guarded_orders ?(stop = fun () -> false) ~limit (params : sort_env_list) =
  if limit <= 0 then []
  else
    let ints, seqs = ints_and_seqs params in
    smallest_raw ~stop ~limit
    @@ List.concat_map seqs ~f:(fun s ->
        let empty =
          match Term.sort_of s with
          | T_seq.SSeq se -> Formula.eq (T_seq.mk_len se s) (T_int.zero ())
          | _ -> assert false
        in
        List.concat_map ints ~f:(fun t1 ->
            List.filter_map ints ~f:(fun t2 ->
                poll stop;
                if same_term t1 t2 then None
                else Some (Formula.or_of [ empty; Formula.leq t1 t2 ]))))

(* {3 Constructor cases}

   The terms an unknown reaches stop at a datatype with more than one
   constructor ([reached_sorts]): a selector of one constructor is not a total
   function of such a value, so no family above looks inside it.  An adapter
   whose state wraps another iterator in an option ([Fuse { iter: Option<I> }])
   has its whole relation inside that option, [produces(s, v, o)] holding
   between [s.iter]'s and [o.iter]'s contents what the inner iterator's
   [produces] holds between its own states, and offering nothing there leaves
   the pre-pass with a fixed point that says nothing about the produced items.
   The family below opens such a case under the constructor's tester. *)

(* the reached terms whose sort is a datatype of more than one constructor,
   the ones [reached] stops at, with the position of their parameter *)
let case_terms (params : sort_env_list) : (int * Term.t) list =
  List.filter (reached params) ~f:(fun (_, t) ->
      match Term.sort_of t with
      | T_dt.SDT dt -> List.length (Datatype.conses_of dt) > 1
      | _ -> false)

let tester dt cons t =
  Formula.mk_atom (T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t)

(* The opened views of [params]: for each multi-constructor datatype sort that
   a case term has and each of its constructors [c] with at least one field,
   the parameter list in which every parameter some case term [t] of that sort
   starts at is replaced by fresh variables [y], one per field of [c] and per
   such [t] (in the order of [case_terms]), and every other parameter is kept.
   With it, for each fresh [y], the selector term [sel_c(t)] it stands for and
   the tester [is_c(t)] under which that term denotes a field of [t].  Every
   case term of the sort is opened at the same constructor at once, so a
   relation between two states ([s.iter], [o.iter]) is opened on both sides. *)
let opened_views (params : sort_env_list) :
    (sort_env_list * (Ident.tvar * Term.t * Formula.t) list) list =
  let cases = case_terms params in
  let sorts =
    List.dedup_and_sort
      ~compare:(fun (k1, _) (k2, _) -> String.compare k1 k2)
      (List.map cases ~f:(fun (_, t) ->
           (Term.str_of_sort (Term.sort_of t), Term.sort_of t)))
  in
  List.concat_map sorts ~f:(fun (key, sort) ->
      match sort with
      | T_dt.SDT dt ->
          let ts =
            List.filter cases ~f:(fun (_, t) ->
                String.equal key (Term.str_of_sort (Term.sort_of t)))
          in
          List.filter_map (Datatype.conses_of dt) ~f:(fun cons ->
              match Datatype.sels_of_cons cons with
              | [] -> None
              | sels ->
                  let opened =
                    List.map ts ~f:(fun (i, t) ->
                        ( i,
                          List.map sels ~f:(fun sel ->
                              ( Ident.mk_fresh_tvar (),
                                Datatype.sort_of_sel dt sel,
                                T_dt.mk_sel dt (Datatype.name_of_sel sel) t,
                                tester dt cons t )) ))
                  in
                  let params' =
                    List.concat_mapi params ~f:(fun i (x, s) ->
                        match
                          List.filter opened ~f:(fun (j, _) -> i = j)
                        with
                        | [] -> [ (x, s) ]
                        | os ->
                            List.concat_map os ~f:(fun (_, ys) ->
                                List.map ys ~f:(fun (y, s, _, _) -> (y, s))))
                  in
                  Some
                    ( params',
                      List.concat_map opened ~f:(fun (_, ys) ->
                          List.map ys ~f:(fun (y, _, t, g) -> (y, t, g))) ))
      | _ -> [])

(* Constructor-case atoms: [is_c(t1) /\ ... => a[sel_c(t1)/y1, ...]] for each
   atom [a] that one of [families] (the generated families, given as a
   function of a parameter list) builds over an opened view of [params]
   ([opened_views]) and that mentions a fresh variable of the view, guarded by
   the testers of the case terms whose fields it mentions; then, over the case
   terms [t], [u] of one sort at two parameters and each constructor [c] of
   it, [is_c(t) => is_c(u)] (the constructor is kept along the relation) and
   [is_c(t) => e] for [e] a frame equation of [params] or [len s = 0] for a
   reached sequence [s] (in that case nothing is produced and nothing moves:
   [is_None(s.iter) => len v = 0], [is_None(s.iter) => s = o]).  The
   tester-only atoms come first, then each family's atoms over each view, at
   most [limit] from each, in the family's own order.

   Why it is sound to offer them: they are candidates only, each an ordinary
   quantifier-free or universally quantified formula over the unknown's
   parameters, and the pre-pass keeps an atom only when its questions confirm
   it; the guard makes every selector application denote a field of a value
   built by that constructor, so an atom's truth never depends on how a solver
   interprets a selector applied to another constructor (an underspecified
   term).

   Contract: [limit <= 0] gives [[]]; otherwise atoms whose free variables are
   all among [params] (the fresh variables are substituted away), without
   repetition by printed form; no case term gives [[]].  A function of
   [params]' names and sorts and of [families]; [stop] is polled once per atom
   built. *)
let constructor_cases ?(stop = fun () -> false) ~limit
    ~(families : sort_env_list -> Formula.t list list) (params : sort_env_list)
    =
  if limit <= 0 then []
  else
    let cases = case_terms params in
    if List.is_empty cases then []
    else
      let testers_only =
        let frames = frame_equations ~stop ~limit params in
        let empties =
          List.filter_map (snd (ints_and_seqs params)) ~f:(fun s ->
              match Term.sort_of s with
              | T_seq.SSeq se ->
                  Some (Formula.eq (T_seq.mk_len se s) (T_int.zero ()))
              | _ -> None)
        in
        List.concat_map cases ~f:(fun (i, t) ->
            match Term.sort_of t with
            | T_dt.SDT dt ->
                List.concat_map (Datatype.conses_of dt) ~f:(fun cons ->
                    let g = tester dt cons t in
                    List.filter_map cases ~f:(fun (j, u) ->
                        poll stop;
                        if
                          i <> j
                          && String.equal
                               (Term.str_of_sort (Term.sort_of t))
                               (Term.str_of_sort (Term.sort_of u))
                        then Some (Formula.mk_imply g (tester dt cons u))
                        else None)
                    @ List.map (empties @ frames) ~f:(fun e ->
                        poll stop;
                        Formula.mk_imply g e))
            | _ -> [])
        |> Fn.flip List.take limit
      in
      let opened =
        List.concat_map (opened_views params) ~f:(fun (params', ys) ->
            List.concat_map (families params') ~f:(fun atoms ->
                List.filter_map atoms ~f:(fun phi ->
                    poll stop;
                    let fvs = Formula.tvs_of phi in
                    match
                      List.filter ys ~f:(fun (y, _, _) -> Set.mem fvs y)
                    with
                    | [] -> None
                    | used ->
                        let sub =
                          Map.Poly.of_alist_exn
                            (List.map used ~f:(fun (y, t, _) -> (y, t)))
                        in
                        let guards =
                          List.dedup_and_sort
                            ~compare:(fun g1 g2 ->
                              String.compare (Formula.str_of g1)
                                (Formula.str_of g2))
                            (List.map used ~f:(fun (_, _, g) -> g))
                        in
                        Some
                          (Formula.mk_imply (Formula.and_of guards)
                             (Formula.subst sub phi)))
                |> Fn.flip List.take limit))
      in
      let seen = Hash_set.create (module String) in
      List.filter (testers_only @ opened) ~f:(fun phi ->
          let key = Formula.str_of phi in
          if Hash_set.mem seen key then false
          else (
            Hash_set.add seen key;
            true))

(* the keys a declared atom and a generated one are compared by in the
   census, so that two atoms that differ only in the names of their bound
   variables, the order of a quantified body's disjuncts (conjuncts under
   an existential) or the sides of an equation share a key: the printed
   normal form with the bound variables renamed in order of occurrence;
   for a quantified atom, its binder kind with the sorted printed parts of
   its body; for an equation, the one with its sides swapped *)
let census_keys phi =
  let canon phi =
    let phi = normal phi in
    let taken = Formula.names_spelled_in phi in
    let c = ref 0 in
    let rec next () =
      incr c;
      let x = Ident.Tvar (sprintf "#hb%d" !c) in
      if Set.mem taken x then next () else x
    in
    Formula.aconv_tvar_norm next phi
  in
  let phi = canon phi in
  let parts =
    match phi with
    | Formula.Bind (binder, bs, body, _) ->
        let ps =
          match binder with
          | Formula.Exists -> Formula.conjuncts_of body
          | _ -> Formula.disjuncts_of body
        in
        [
          sprintf "%s %s. %s"
            (Formula.str_of_binder binder)
            (String.concat_map_list ~sep:"," bs ~f:(snd >> Term.str_of_sort))
            (String.concat ~sep:" | "
            @@ List.sort ~compare:String.compare
            @@ List.map (Set.to_list ps) ~f:Formula.str_of);
        ]
    | _ -> []
  in
  let swapped =
    if Formula.is_eq phi then
      let t1, t2, _ = Formula.let_eq phi in
      [ Formula.str_of (canon (Formula.eq t2 t1)) ]
    else []
  in
  (Formula.str_of phi :: parts) @ swapped

(* [premise_redundant clauses p params atom]: whether, in every clause
   that applies the unknown [p] (in its head or its body), each
   application's instance of [atom] (over [params], [p]'s parameters, put
   to the application's arguments) is a premise of the clause -- a
   conjunct of the negation of one of the disjuncts of the clause's pure
   part, compared by [census_keys] after [bool_eq_canon].  [false] when no clause applies [p]
   or an instance cannot be built.
   Why such an atom can be left out of a conjunctive candidate [C /\ a]
   for [p] without changing anything a clause says: at each application
   of [p] in a clause, [a]'s instance is already a premise of that clause,
   so a body application gains nothing from it and a head application's
   demand for it holds outright; [C] and [C /\ a] make each clause valid
   together or not at all.  The typical case is a law of a universally
   quantified function the unknown carries as a parameter (reflexivity of
   a history invariant) that the reader made a premise of every clause
   applying the unknown: generated as a candidate, it was asked once per
   clause and pass, and carried as a hypothesis by every other question.
   The test is syntactic and can only answer [false] where the atom is in
   fact redundant. *)
(* [phi] with each equation or disequation between a Boolean term and a
   Boolean constant written one way: [(<false>) != t] where it says that
   [t] holds ([t = true], [true = t], [t != false]) and [(<false>) = t]
   where it says that it does not.  The reader writes a law's
   [R(x, x)] as [(<false>) != R[x][x]], a generated atom says
   [(<true>) = R[x][x]], and the two are one formula.  Equivalent to [phi]
   in every model. *)
let bool_eq_canon phi =
  Formula.map_atom phi ~f:(fun atom ->
      match atom with
      | Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op), [ t1; t2 ], _)
        -> (
          let const t =
            if T_bool.is_true t then Some true
            else if T_bool.is_false t then Some false
            else None
          in
          let is_eq = match op with T_bool.Eq -> true | _ -> false in
          match (const t1, const t2) with
          | Some c, None | None, Some c ->
              let t = if Option.is_some (const t1) then t2 else t1 in
              let f = T_bool.mk_false () in
              Formula.mk_atom
                (if Bool.equal is_eq c then T_bool.mk_neq f t
                 else T_bool.mk_eq f t)
          | _ -> Formula.mk_atom atom)
      | _ -> Formula.mk_atom atom)

let premise_redundant (clauses : Clause.t list) (p : Ident.tvar)
    (params : sort_env_list) : Formula.t -> bool =
  let occurrences =
    List.filter_map clauses ~f:(fun ((uni_senv, ps, ns, phi) : Clause.t) ->
        let apps =
          List.filter_map
            (Set.to_list ps @ Set.to_list ns)
            ~f:(fun a ->
              match Logic.Term.let_apps a with
              | Logic.Var (q, _), args when Ident.tvar_equal p q -> Some args
              | _ -> None)
        in
        if List.is_empty apps then None
        else
          let premises =
            lazy
              (let keys = Hash_set.create (module String) in
               (try
                  Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv phi
                  |> Formula.disjuncts_of |> Set.to_list
                  |> List.iter ~f:(fun d ->
                      Evaluator.simplify_neg d |> Formula.conjuncts_of
                      |> Set.iter ~f:(fun c ->
                          List.iter
                            (census_keys (bool_eq_canon c))
                            ~f:(Hash_set.add keys)))
                with exn_ when not (Common.Timer.is_async exn_) -> ());
               keys)
          in
          Some (uni_senv, apps, premises))
  in
  fun atom ->
    (not (List.is_empty occurrences))
    && List.for_all occurrences ~f:(fun (uni_senv, apps, premises) ->
        List.for_all apps ~f:(fun args ->
            match List.zip params args with
            | List.Or_unequal_lengths.Unequal_lengths -> false
            | Ok pairs -> (
                try
                  let sub =
                    Map.Poly.of_alist_exn
                    @@ List.map pairs ~f:(fun ((x, _), t) ->
                        (x, Logic.ExtTerm.to_old_trm Map.Poly.empty uni_senv t))
                  in
                  let keys = Lazy.force premises in
                  List.exists
                    (census_keys (bool_eq_canon (Formula.subst sub atom)))
                    ~f:(Hash_set.mem keys)
                with exn_ when not (Common.Timer.is_async exn_) -> false)))
