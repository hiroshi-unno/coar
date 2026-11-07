(* The checked side's strategy values kept as variables in a strategy check.

   A strategy check substitutes the checked side's Skolem strategy into the
   clauses: a key [K] with parameters [x, y] ([y] the value it decides) and a
   term set [{t_1, .., t_m}] (each [t_i] a formula over [x, y], usually
   [y = s_i(x)]) replaces every literal [not K(a, y)] of the co-CHC by the
   alternatives [t_i(a, y)], joined by [or].  With the one-point form the
   value [s_i(a)] is inlined, so a counter-play's clause instances carry the
   checked side's current constants in place of [y]: a chain-pair region
   projected from them fixes the opponent's move at the value it took, and a
   ranking fitted to such regions ranks the opponent's current strategy rather
   than the game.

   Here each term is replaced by an application [T_i(x, y)] of a fresh
   predicate (a tag), defined by the one clause [t_i(x, y) => T_i(x, y)].
   Exact when [K] occurs only as the negated literal [not K(a, y)] in the
   negation normal form of every co-CHC formula: the conversion to CHC form
   leaves the tags alone (they are not among the predicates it negates), so
   every [T_i] occurs only as a body premise and in its definition's head; its
   least interpretation is the relation [t_i], and substituting that relation
   back gives the formula the plain substitution gives.  So the check has the
   same solutions on the original predicates, and a derivation of the tagged
   check unfolds into one of the untagged check by resolving each tag leaf
   with its definition.  A key that occurs in any other way is left to the
   plain substitution.

   The region reading drops a tag premise from a derivation segment: [y] is
   then constrained only by the clauses that use it, and the region holds the
   steps of the same derivation shape under every value of the opponent's
   move. *)

open Core
open Common.Ext
open Ast

(* The names of every tag drawn in this process, so that the reading of a
   derivation can recognise a tag node: the names are fresh, so a name here is
   never a predicate of a problem.  Written only while a check is built, which
   happens on the main domain. *)
let tags : string Hash_set.t = Hash_set.create (module String)
let is_tag name = Hash_set.mem tags name

(* A census line on stderr for each check built with tags and each region read
   with a value freed, only when the environment variable
   [COAR_MUSTRAT_FREED_LOG] is set: a measurement instrument that tells where
   the field can act without the solver's verbose trace, whose printing would
   change the run's timing.  Nothing is printed otherwise. *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let log_enabled =
  Lazy.from_val (Option.is_some (Sys.getenv "COAR_MUSTRAT_FREED_LOG"))

let log msg =
  if Lazy.force log_enabled then (
    Out_channel.output_string stderr ("FREED " ^ msg ^ "\n");
    Out_channel.flush stderr)

(* [negative_only key t]: [t], a formula in negation normal form, mentions
   [key] only as literals [not key(args)] with [key] absent from [args], below
   [and] and [or] only. *)
let rec negative_only key t =
  let mentions t = Set.mem (Logic.ExtTerm.fvs_of t) key in
  match Logic.Term.let_apps t with
  | Logic.Con ((Logic.BoolTerm.And | Logic.BoolTerm.Or), _), _ :: _ :: _ ->
      List.for_all
        (match Logic.Term.let_apps t with
        | Logic.Con (Logic.BoolTerm.And, _), _ -> Logic.BoolTerm.conjuncts_of t
        | _ -> Logic.BoolTerm.disjuncts_of t)
        ~f:(negative_only key)
  | _ ->
      (not (mentions t))
      || Logic.BoolTerm.is_not t
         &&
         match Logic.Term.let_apps (Logic.BoolTerm.let_not t) with
         | Logic.Var (v, _), args ->
             Ident.tvar_equal v key && not (List.exists args ~f:mentions)
         | _ -> false

(* [has_head ~is_pred t]: [t], a co-CHC formula in negation normal form,
   becomes a clause with a head in CHC form -- it has a literal [not p(args)]
   with [is_pred p], [p] one of the predicates the conversion negates -- or
   may: a leaf other than a literal (a quantifier, an equality between
   Booleans) that mentions such a predicate counts as a head, so the test errs
   towards [true].  A clause without a head is a query, the root of every
   derivation of the check: no chain-pair segment (which runs from one visit
   of a ranked predicate down to the next) and no side derivation below one
   uses its instance, so a value freed there is read by no region. *)
let rec has_head ~is_pred t =
  match Logic.Term.let_apps t with
  | Logic.Con (Logic.BoolTerm.And, _), _ :: _ :: _ ->
      List.exists (Logic.BoolTerm.conjuncts_of t) ~f:(has_head ~is_pred)
  | Logic.Con (Logic.BoolTerm.Or, _), _ :: _ :: _ ->
      List.exists (Logic.BoolTerm.disjuncts_of t) ~f:(has_head ~is_pred)
  | Logic.Var (v, _), _ when is_pred v -> false
  | _ -> (
      let mentions_pred t =
        Set.exists (Logic.ExtTerm.fvs_of t) ~f:is_pred
      in
      if Logic.BoolTerm.is_not t then
        match Logic.Term.let_apps (Logic.BoolTerm.let_not t) with
        | Logic.Var (v, _), _ when is_pred v -> true
        | _ -> mentions_pred t
      else mentions_pred t)

(* [tag_with_translation ~dedup ~taken ~is_pred formulas strat_fn]: [strat_fn] with the term
   set of every key that the co-CHC formulas [formulas] mention, only as
   negated literals, and in at least one formula that has a head
   ([has_head]), replaced by tag applications, together with the tags'
   definitions (CHC-form formulas [not t \/ T(x', y)], universally closed)
   and the tags' sorts.

   A tag is shared.  The tag of a term [t] of a key [K(x, y)] takes only the
   parameters [x'] of [x] that [t] mentions, then [y]; and two terms, of one
   key or of two, that are the same formula once their kept parameters are
   renamed by position (and have the same sorts) get one tag and one
   definition.  Exact as for one tag per term: a tag still occurs only as a
   body premise and in its definition's head, and its least interpretation is
   the relation every term it stands for states.  It matters for size: an
   integer transition system's strategy decides hundreds of nondeterministic
   draws, most by a constant [y = 0] over a dozen state parameters, and one
   tag per term made the check six times larger than the untagged one (712
   tags of arity up to 16), where shared they are a few unary tags.

   Pre: [is_pred p] holds exactly for the predicates the conversion to CHC
   form negates, never for a key of [strat_fn]; each term of a key mentions
   no free variable but the key's parameters (a key whose terms do is left as
   it is); [dedup params terms] returns a sublist of [terms] equivalent to it
   under [or] (the caller's deduplication, applied here because tags of
   equivalent terms would not be recognised as equal later); [taken v] holds
   for every name the check uses.
   Post: the returned strategy maps each tagged key to its parameters and one
   tag application per kept term, whose last argument is the key's result
   parameter; every tag is fresh, recorded in [tags], and has exactly one
   definition among those returned; every other key is unchanged.  The fourth
   component maps each tagged key to the pairs (kept term, its tag
   application), one per kept term; their second components are the key's
   new term set.

   Why only keys under a head.  A tagged key is out of the one-point
   placement of term alternatives (its terms are tag applications, not
   equations [y = s]), so a clause holding one is placed by footprints for
   all its keys.  A key stated only in queries buys nothing for that: no
   region reads a value freed there.  Leaving a key untagged is the plain
   substitution for that key, so the check is unchanged in meaning either
   way.  With [~query_keys:true] a key stated only in queries is tagged as
   well (the other conditions unchanged): the selection on a lifted play reads
   the opponent's values from the tags whatever clause they sit in, and a
   value inlined into a query is a constant it cannot generalise.  Exact for
   the same reason as any tag (the tag occurs only as a body premise and in
   its definition's head). *)
let tag_with_translation ?(query_keys = false) ~dedup ~taken ~is_pred formulas
    strat_fn =
  (* the shared tags drawn so far: (sorts, canonical term) and the tag *)
  let shared = ref [] in
  (* per tagged key, each kept term with the tag application replacing it *)
  let translation = ref Map.Poly.empty in
  let record key term app =
    translation := Map.Poly.add_multi !translation ~key ~data:(term, app);
    app
  in
  (* each formula's free variables, negation normal form and [has_head],
     computed once rather than once per key: an integer transition system's
     check has hundreds of keys, and recomputing them per key was a visible
     part of building the tagged check *)
  let formulas =
    List.map formulas ~f:(fun (_, phi) ->
        let nnf = lazy (Logic.ExtTerm.nnf_of phi) in
        ( Logic.ExtTerm.fvs_of phi,
          nnf,
          lazy (has_head ~is_pred (Lazy.force nnf)) ))
  in
  let strat_fn, defs, senv =
  Map.Poly.fold strat_fn ~init:(strat_fn, [], Map.Poly.empty)
    ~f:(fun ~key ~data:(params, terms) (strat_fn, defs, senv) ->
      let mentioning =
        List.filter formulas ~f:(fun (fvs, _, _) -> Set.mem fvs key)
      in
      let param_names = Set.Poly.of_list (List.map params ~f:fst) in
      if
        List.is_empty mentioning
        || List.is_empty params
        || (not query_keys)
           && not
                (List.exists mentioning ~f:(fun (_, _, head) -> Lazy.force head))
        || (not
              (List.for_all mentioning ~f:(fun (_, nnf, _) ->
                   negative_only key (Lazy.force nnf))))
        || Set.exists terms ~f:(fun t ->
               not (Set.is_subset (Logic.ExtTerm.fvs_of t) ~of_:param_names))
      then (strat_fn, defs, senv)
      else
        let xs, ret = (List.drop_last_exn params, List.last_exn params) in
        let apps, defs, senv =
          List.fold (dedup params terms) ~init:([], defs, senv)
            ~f:(fun (apps, defs, senv) term ->
              let fvs = Logic.ExtTerm.fvs_of term in
              let kept =
                List.filter xs ~f:(fun (v, _) -> Set.mem fvs v) @ [ ret ]
              in
              (* the kept parameters renamed by position, to names nothing
                 else in the tree draws (so none is bound inside a term); they
                 are local to the comparison and to the definition's
                 universal closure *)
              let canon_params =
                List.mapi kept ~f:(fun i (_, s) ->
                    (Ident.Tvar (sprintf "#fv%d" i), s))
              in
              let canon =
                Logic.ExtTerm.rename
                  (Map.Poly.of_alist_exn
                  @@ List.map2_exn kept canon_params ~f:(fun (v, _) (c, _) ->
                      (v, c)))
                  term
              in
              let sorts = List.map kept ~f:snd in
              let app name =
                Logic.ExtTerm.mk_var_app name
                  (List.map kept ~f:(fun (v, _) -> Logic.ExtTerm.mk_var v))
              in
              match
                List.find !shared ~f:(fun ((sorts', canon'), _) ->
                    Stdlib.( = ) sorts sorts'
                    && Stdlib.( = ) canon canon')
              with
              | Some (_, name) -> (record key term (app name) :: apps, defs, senv)
              | None ->
                  let name =
                    Ident.mk_fresh_tvar_avoiding ~prefix:"FV_"
                      ~taken:(fun v -> taken v || Map.Poly.mem senv v)
                      ()
                  in
                  Hash_set.add tags (Ident.name_of_tvar name);
                  shared := ((sorts, canon), name) :: !shared;
                  let def =
                    ( Map.Poly.of_alist_exn canon_params,
                      Logic.BoolTerm.or_of
                        [
                          Logic.BoolTerm.neg_of canon;
                          Logic.ExtTerm.mk_var_app name
                            (List.map canon_params ~f:(fun (c, _) ->
                                 Logic.ExtTerm.mk_var c));
                        ] )
                  in
                  ( record key term (app name) :: apps,
                    def :: defs,
                    Map.Poly.set senv ~key:name
                      ~data:
                        (Logic.Sort.mk_fun (sorts @ [ Logic.BoolTerm.SBool ]))
                  ))
        in
        ( Map.Poly.set strat_fn ~key ~data:(params, Set.Poly.of_list apps),
          defs,
          senv ))
  in
  (strat_fn, defs, senv, !translation)

(* [tag_with_translation] without the translation. *)
let tag ~dedup ~taken ~is_pred formulas strat_fn =
  let strat_fn, defs, senv, _ =
    tag_with_translation ~dedup ~taken ~is_pred formulas strat_fn
  in
  (strat_fn, defs, senv)
