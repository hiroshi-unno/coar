(* A measurement instrument, read only when COAR_MUSTRAT_JOINT_WALL is set:
   one stderr line per accepted refinement and ranking key, saying whether
   the installed ranking and the installed Skolem terms, each fitted to its
   own demand, still fit together on the counter-play they were read from.

   The question.  A refinement of the ranked side fixes its ranking from the
   chain pairs of the play, whose decisions are the values the play took,
   and selects its terms at another model; nothing ties the two.  So the
   terms can move the ranked side differently from the play, and along the
   play's path segments, with the decisions made by the terms, the pair of
   states the segment joins need not decrease under the ranking: each fits
   its own demand and together they lose (the separated refinement's
   counter-example: from x = 1 the move y := x stays at 1, which the ranking
   x does not decrease, although x decreases on every pair of the play
   x = 2, 1, 0).

   What is computed, per play and ranking key with chain pairs:
   - [ground]: how many of the play's ground chain pairs the installed
     ranking contains (its own demand);
   - per path segment of a chain pair (as the region construction reads
     segments: the clause instances along it, off-path premises dropped
     except the ranked side's decisions), with the upper visit's state pinned
     at the play's value, two path conditions: [played], each decision fixed
     at the value the play took, and [term], each decision bound to the
     installed terms of its key at the premise's arguments (the disjunction
     over the key's terms; only the terms this refinement added when it added
     any).  Each is asked of Z3 twice, with the ranking and with its
     negation at the segment's two states, giving the status [vacuous] (the
     path condition unsatisfiable), [lose] (satisfiable, never with the
     ranking: no resolution meets the joint demand), [mixed] (both),
     [contained] (only with the ranking) or [undecided];
   - [losing_terms]: of the bound terms, how many, put alone at their key
     (every other key keeping its bound terms), make some segment through a
     decision [lose] that is not [lose] under [played] ([-1] when a single
     term is bound in all);
   - [class]: [J] when the ranking contains every ground pair and some
     segment through a decision is [lose] under [term] but not under
     [played]; [Jterm] when that holds of some single term but the term set
     as a whole has a meeting resolution on every such segment (the owner of
     the set can still pick a term that decreases); otherwise
     [notJ:<reason>] ([ground]: the ranking misses a ground pair; [region]:
     a segment loses under the played values too, so the term is not the
     cause; [mixed]: every losing resolution has a meeting one beside it;
     [fits]: no segment loses) or [undecided]; before all of these,
     [noterms] when the ranked side has no Skolem key (its moves are all
     choices between disjuncts, which this instrument does not bind) and
     [nodecision] when no segment passes one of its decisions, the two
     cases in which the question cannot be asked.
   - the ranked side's choices between disjuncts, read as decisions too.  In
     the check such a choice is a choice between alternative clauses with
     one head (the derivation, i.e. the ranked side, takes one of them), and
     the strategy installs nothing for it: the next check resolves it
     pointwise, so the installed choice is any alternative.  A step of a
     segment is a [choice] step when the check has two or more clauses with
     the node's head predicate each having exactly one premise of the next
     node's predicate (the skeleton kept); [free] is the segment's path
     condition with every choice step stated as the disjunction of those
     alternatives' instances (head and successor equations and pure part,
     their side premises dropped, their variables fresh), every other step
     as under [played], asked as [played] is.  A resolution the play did not
     take is then a model of [free] that is not one of [played].  [dclass]:
     [nochoice] when no segment has a choice step; [J] when some segment
     with one is [lose] under [played] but has a meeting resolution under
     [free] ([mixed] or [contained]) -- the play's own resolution cannot meet
     the installed ranking there and another resolution of the ranked side's
     choices can, which is the wall of a ranking that exists only for
     another resolution; [notJ:region] when such a segment is [lose] under
     both; [fits:altloses] when every segment meets under [played] and some
     other resolution does not (harmless: the fixpoint picks pointwise);
     [fits] otherwise, or [undecided].  [choice_segments] counts the
     segments with a choice step; at most [max_choice_steps] steps of one
     segment are freed, the rest keep the play's instance
     ([choice_capped] counts them), so on a long segment [free] frees a
     prefix of the choices only.

   Approximations, stated so that a line is read as what it is: side premises
   off the path are dropped (as the region construction drops them), so the
   path condition over-approximates the steps the skeleton admits and
   [lose] or [mixed] may come from a step no derivation makes; only the
   first refinement form's plays are read; a premise whose arity does not
   match its key's parameters is left free and counted as [unbound].  When on,
   the instrument creates fresh variable names, so a run with it is not
   name-for-name the run without it.  It decides nothing and changes no
   strategy. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let enabled = Lazy.from_val (Option.is_some (Sys.getenv "COAR_MUSTRAT_JOINT_WALL"))

let refinements = ref 0

type status = Vacuous | Lose | Mixed | Contained | Undecided

let str_of_status = function
  | Vacuous -> "vacuous"
  | Lose -> "lose"
  | Mixed -> "mixed"
  | Contained -> "contained"
  | Undecided -> "undecided"

let check phis =
  match
    Z3Smt.Z3interface.check_sat ~timeout:(Some 2000) ~id:None (get_fenv ()) phis
  with
  | `Sat _ -> `Sat
  | `Unsat -> `Unsat
  | _ -> `Unknown

(* The status of the path condition [phi] against the ranking formula [rho]
   (over the segment's two states). *)
let status phi rho =
  match check [ phi ] with
  | `Unsat -> Vacuous
  | `Unknown -> Undecided
  | `Sat -> (
      match (check [ phi; rho ], check [ phi; Formula.mk_neg rho ]) with
      | `Unsat, `Sat -> Lose
      | `Sat, `Sat -> Mixed
      | `Sat, `Unsat -> Contained
      | `Unsat, `Unsat -> Vacuous
      | _ -> Undecided)

(* A ranking (a lambda over the two states' positions, the upper visit
   first) as a formula at the terms [ts]. *)
let ranking_at ranking ts =
  let params, body = Logic.Term.let_lam ranking in
  if List.length params <> List.length ts then None
  else
    let phi =
      Logic.ExtTerm.to_old_fml Map.Poly.empty
        (Map.Poly.of_alist_exn params)
        body
    in
    Some
      (Formula.subst
         (Map.Poly.of_alist_exn
            (List.map2_exn params ts ~f:(fun (x, _) t -> (x, t))))
         phi)

let truncate s =
  let s = String.map s ~f:(function '\n' | '\t' -> ' ' | c -> c) in
  if String.length s <= 400 then s else String.prefix s 397 ^ "..."

(* The ranked side's choice at the path step from [node] to its [next_idx]-th
   premise, read off the check's clauses [clauses] (see [dclass] above):
   [Some [the disjunction of the alternatives' instances]] over the step's
   variables [xs] (the node's arguments) and [xs'] (the next node's) when
   there are two or more alternatives, [None] otherwise (the step keeps the
   clause instance the play took).  Counts the choice steps in [counter]
   (reset per segment by the caller); past [max_choice_steps] in one segment
   a step keeps the play's instance, counted in [choice_steps_capped]: a
   long segment's path condition with a disjunction at every step was seen
   not to return within the run's budget (42 chain pairs on a 42-visit play),
   and freeing a prefix of the choices still makes [free] contain
   [played]. *)
let max_choice_steps = 6

let choice_steps_capped = ref 0

let choice_step clauses counter (node : ChainRegions.play_node) next_idx xs
    xs' =
  match List.nth node.children next_idx with
  | None -> None
  | Some _ when !counter >= max_choice_steps ->
      incr choice_steps_capped;
      None
  | Some child ->
      let cs = PassedChoices.clauses_with_head clauses node.pvar in
      if List.length cs > PassedChoices.max_clauses_per_head then None
      else
        let vars = List.map ~f:(fun (v, s) -> Term.mk_var v s) in
        let alts =
          List.filter_map cs ~f:(fun c ->
              let ((_, _, ns, phi) as c) = PassedChoices.freshen c in
              match PassedChoices.head_of c with
              | None -> None
              | Some (_, _, hs) -> (
                  let on_path =
                    List.filter (Set.to_list ns) ~f:(fun a ->
                        Atom.is_pvar_app a
                        &&
                        let p, _, _, _ = Atom.let_pvar_app a in
                        Ident.pvar_equal p child.ChainRegions.pvar)
                  in
                  match on_path with
                  | [ a ] -> (
                      let _, _, us, _ = Atom.let_pvar_app a in
                      match
                        ( PassedChoices.eqs hs (vars xs),
                          PassedChoices.eqs us (vars xs') )
                      with
                      | Some e1, Some e2 ->
                          Some (Formula.and_of (e1 @ e2 @ [ Formula.mk_neg phi ]))
                      | _ -> None)
                  | _ -> None))
        in
        if List.length alts < 2 then None
        else (
          incr counter;
          Some [ Formula.or_of alts ])

(* [report ~clauses ~chain_pairs ~chain_regions ~plays ~before ~after]: the
   lines described above, for the refinement that turned the strategy [before]
   (rankings, Skolem term sets) into [after] on the plays [plays].
   [chain_pairs tree ~wf_key ~arity] is the check's chain-pair reader and
   [chain_regions ?bind_decision ?bind_step ~observe tree ~wf_key ~arity] its
   region reader with the instrument's hooks, [clauses] (forced only when
   the instrument is on) the clauses of the check whose counter-play the
   plays are, which give the choices between disjuncts, reading the ranked side's Skolem
   keys as its decisions.  Never raises but an asynchronous exception. *)
let report ~clauses ~chain_pairs ~chain_regions ~plays ~before ~after =
  if Lazy.force enabled then (
    incr refinements;
    (* the check's clauses, as [PassedChoices] reads them; none when they
       cannot be read *)
    let clauses =
      try Lazy.force clauses
      with exn when not (Common.Timer.is_async exn) -> []
    in

    let choices = ref 0 in
    let n_ref = !refinements in
    let wf0, fn0 = before and wf1, fn1 = after in
    ignore wf0;
    (* the terms each key is bound to: those this refinement added, or all
       of its terms when it added none *)
    let new_keys = ref 0 in
    let bound_terms =
      Map.Poly.mapi fn1 ~f:(fun ~key ~data:(params, terms) ->
          let added =
            match Map.Poly.find fn0 key with
            | Some (_, old) -> Set.diff terms old
            | None -> terms
          in
          if not (Set.is_empty added) then incr new_keys;
          (params, if Set.is_empty added then terms else added))
    in
    let unbound = ref 0 and binds = ref 0 and last_error = ref "" in
    (* [bind_with only phi child]: [only = Some (k, t)] binds the key [k] to
       its term [t] alone, every other key to its bound terms *)
    let bind_with only phi (child : ChainRegions.play_node) =
      ignore child;
      let bound_terms =
        match only with
        | None -> bound_terms
        | Some (k, t) ->
            Map.Poly.change bound_terms k
              ~f:(Option.map ~f:(fun (ps, _) -> (ps, Set.Poly.singleton t)))
      in
      match fst (Formula.let_atom phi) with
      | Atom.App (Predicate.Var (pvar, _), args, _) -> (
          incr binds;
          match
            Map.Poly.find bound_terms (Ident.Tvar (Ident.name_of_pvar pvar))
          with
          | Some (params, terms) when List.length params = List.length args ->
              (* a term over the key's parameters and its result: a formula *)
              let sub =
                Map.Poly.of_alist_exn
                  (List.map2_exn params args ~f:(fun (x, _) t -> (x, t)))
              in
              let senv = Map.Poly.of_alist_exn params in
              Some
                [
                  Formula.or_of
                    (List.map (Set.to_list terms) ~f:(fun t ->
                         Formula.subst sub
                           (Logic.ExtTerm.to_old_fml Map.Poly.empty senv t)));
                ]
          | Some (params, terms) when List.length params + 1 = List.length args
            ->
              (* a term over the key's parameters: the result's value *)
              let ins = List.drop_last_exn args and res = List.last_exn args in
              let sub =
                Map.Poly.of_alist_exn
                  (List.map2_exn params ins ~f:(fun (x, _) t -> (x, t)))
              in
              let senv = Map.Poly.of_alist_exn params in
              Some
                [
                  Formula.or_of
                    (List.map (Set.to_list terms) ~f:(fun t ->
                         Formula.eq res
                           (Term.subst sub
                              (Logic.ExtTerm.to_old_term Map.Poly.empty senv t
                                 []))));
                ]
          | _ ->
              incr unbound;
              Some [])
      | _ ->
          incr unbound;
          Some []
    in
    Map.Poly.iteri wf1 ~f:(fun ~key ~data:ranking ->
        let arity = List.length (fst (Logic.Term.let_lam ranking)) in
        let n = arity / 2 in
        List.iteri plays ~f:(fun play_i tree ->
            try
              let pairs = chain_pairs tree ~wf_key:key ~arity in
              if not (List.is_empty pairs) then (
                let ground_in =
                  List.count pairs ~f:(fun (a, b) ->
                      match ranking_at ranking (a @ b) with
                      | None -> false
                      | Some phi -> (
                          let phi = Evaluator.simplify phi in
                          Formula.is_true phi
                          ||
                          match check [ Formula.mk_neg phi ] with
                          | `Unsat -> true
                          | _ -> false))
                in
                (* the statuses of every segment, with the number of
                   decisions bound along it *)
                (* [only_bound]: a segment with nothing bound is not asked
                   (its status is the [played] one, filled in by the
                   caller), which keeps the [free] pass to the segments
                   through a choice: on a 42-visit play the 903 segments
                   took about a minute per pass *)
                let collect ?(only_bound = false) ?bind_decision ?bind_step () =
                  let out = ref [] in
                  let observe (upper, _lower) xs ys phi =
                    let d = !binds + !choices in
                    binds := 0;
                    choices := 0;
                    let pin =
                      List.map2_exn xs
                        (List.drop upper.ChainRegions.args
                           (List.length upper.ChainRegions.args - n))
                        ~f:(fun (v, s) t -> Formula.eq (Term.mk_var v s) t)
                    in
                    let st =
                      if only_bound && d = 0 then Undecided
                      else
                      try
                        match
                          ranking_at ranking
                            (List.map (xs @ ys) ~f:(fun (v, s) ->
                                 Term.mk_var v s))
                        with
                        | None -> Undecided
                        | Some rho ->
                            (* the simplifier states a term table ([case]) by
                             its branches, which the Z3 encoding needs *)
                            status
                              (Evaluator.simplify (Formula.and_of (phi :: pin)))
                              (Evaluator.simplify rho)
                      with exn when not (Common.Timer.is_async exn) ->
                        last_error := Exn.to_string exn;
                        Undecided
                    in
                    out := (st, d) :: !out
                  in
                  binds := 0;
                  choices := 0;
                  chain_regions ?bind_decision ?bind_step ~observe tree
                    ~wf_key:key ~arity;
                  List.rev !out
                in
                let played = collect () in
                (* the choices between disjuncts bound to any alternative *)
                choice_steps_capped := 0;
                let free =
                  let free =
                    collect ~only_bound:true
                      ~bind_step:(choice_step clauses choices) ()
                  in
                  if List.length free = List.length played then
                    List.map2_exn free played ~f:(fun (t, c) (p, _) ->
                        ((if c = 0 then p else t), c))
                  else free
                in
                let choice_segments =
                  List.count free ~f:(fun (_, c) -> c > 0)
                in
                let dclass =
                  let paired =
                    if List.length played = List.length free then
                      List.zip_exn played free
                    else []
                  in
                  let some f =
                    List.exists paired ~f:(fun ((p, _), (t, c)) ->
                        c > 0 && f p t)
                  in
                  if choice_segments = 0 then "nochoice"
                  else if
                    some (fun p t ->
                        Stdlib.( = ) p Lose
                        && (Stdlib.( = ) t Mixed || Stdlib.( = ) t Contained))
                  then "J"
                  else if
                    some (fun p t -> Stdlib.( = ) p Lose && Stdlib.( = ) t Lose)
                  then "notJ:region"
                  else if
                    (not (List.is_empty paired))
                    && List.for_all paired ~f:(fun ((_, _), (t, _)) ->
                           Stdlib.( = ) t Undecided)
                  then "undecided"
                  else if
                    some (fun p t ->
                        Stdlib.( = ) p Contained && Stdlib.( = ) t Mixed)
                  then "fits:altloses"
                  else "fits"
                in
                unbound := 0;
                let term = collect ~bind_decision:(bind_with None) () in
                let unbound_term = !unbound in
                (* each bound term alone: [Some segments] for a term that
                   loses a segment the played values do not *)
                let single_terms =
                  Map.Poly.fold bound_terms ~init:[]
                    ~f:(fun ~key ~data:(_, ts) acc ->
                      List.map (Set.to_list ts) ~f:(fun t -> (key, t)) @ acc)
                in
                let losing_terms =
                  if List.length single_terms <= 1 then -1
                  else
                    List.count single_terms ~f:(fun kt ->
                        let alone =
                          collect ~bind_decision:(bind_with (Some kt)) ()
                        in
                        List.length alone = List.length played
                        && List.exists2_exn played alone
                             ~f:(fun (p, _) (t, d) ->
                               d > 0 && Stdlib.( = ) t Lose
                               && not (Stdlib.( = ) p Lose)))
                in
                let count l s =
                  List.count l ~f:(fun (s', _) -> Stdlib.( = ) s s')
                in
                let tally l =
                  String.concat ~sep:","
                    (List.map [ Vacuous; Lose; Mixed; Contained; Undecided ]
                       ~f:(fun s ->
                         sprintf "%s=%d" (str_of_status s) (count l s)))
                in
                let with_decision = List.count term ~f:(fun (_, d) -> d > 0) in
                let paired =
                  if List.length played = List.length term then
                    List.zip_exn played term
                  else []
                in
                let cls =
                  if with_decision = 0 then
                    if Map.Poly.is_empty fn1 then "noterms" else "nodecision"
                  else if ground_in < List.length pairs then "notJ:ground"
                  else if
                    List.exists paired ~f:(fun ((p, _), (t, d)) ->
                        d > 0 && Stdlib.( = ) t Lose
                        && not (Stdlib.( = ) p Lose))
                  then "J"
                  else if losing_terms > 0 then "Jterm"
                  else if count term Lose > 0 then "notJ:region"
                  else if count term Mixed > 0 then "notJ:mixed"
                  else if
                    (not (List.is_empty term))
                    && count term Undecided = List.length term
                  then "undecided"
                  else "notJ:fits"
                in
                let terms_str =
                  String.concat ~sep:"; "
                    (Map.Poly.fold bound_terms ~init:[]
                       ~f:(fun ~key ~data:(params, ts) acc ->
                         let senv = Map.Poly.of_alist_exn params in
                         sprintf "%s:{%s}" (Ident.name_of_tvar key)
                           (String.concat ~sep:","
                              (List.map (Set.to_list ts) ~f:(fun t ->
                                   try
                                     Term.str_of
                                       (Logic.ExtTerm.to_old_term Map.Poly.empty
                                          senv t [])
                                   with
                                   | exn when not (Common.Timer.is_async exn) ->
                                     Logic.ExtTerm.str_of t)))
                         :: acc))
                in
                let rho_str =
                  try
                    let params, body = Logic.Term.let_lam ranking in
                    Formula.str_of @@ Evaluator.simplify
                    @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                         (Map.Poly.of_alist_exn params)
                         body
                  with exn when not (Common.Timer.is_async exn) ->
                    Logic.ExtTerm.str_of ranking
                in
                eprintf
                  "mustrat-joint-wall: refinement=%d key=%s play=%d pairs=%d \
                   ground_in=%d segments=%d/%d with_decision=%d \
                   new_term_keys=%d/%d unbound=%d losing_terms=%d/%d \
                   played={%s} term={%s} class=%s choice_segments=%d/%d \
                   choice_capped=%d free={%s} dclass=%s rho=%s terms=%s%s\n\
                   %!"
                  n_ref (Ident.name_of_tvar key) play_i (List.length pairs)
                  ground_in (List.length term) (List.length played)
                  with_decision !new_keys (Map.Poly.length fn1) unbound_term
                  losing_terms (List.length single_terms) (tally played)
                  (tally term) cls choice_segments (List.length free)
                  !choice_steps_capped (tally free) dclass (truncate rho_str) (truncate terms_str)
                  (if String.is_empty !last_error then ""
                   else " error=" ^ truncate !last_error))
            with exn when not (Common.Timer.is_async exn) ->
              eprintf
                "mustrat-joint-wall: refinement=%d key=%s play=%d error=%s\n%!"
                n_ref (Ident.name_of_tvar key) play_i
                (truncate (Exn.to_string exn)))))
