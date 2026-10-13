(* Proving a piece of the zero-unknown verdict by applying its quantified
   hypotheses forward, one instance at a time.

   The question.  A piece [phi] is valid exactly when its negation [N =
   nnf (not phi)] is unsatisfiable.  [N] is a conjunction: FACTS (conjuncts
   that bind no array or sequence at their top) and HYPOTHESES (conjuncts
   [forall xs. d_1 \/ ... \/ d_n] binding an array or a sequence).  A lemma
   the clause calls is such a hypothesis, [not P_1 \/ ... \/ not P_k \/ C],
   and so is the negated goal [forall ys. not B].

   The rule.  For a hypothesis [H] and a substitution [theta] of all its
   binders, the instance [H theta = e_1 \/ ... \/ e_n] follows from [N].
   Each disjunct [e_i] is asked about alone: when [facts /\ e_i] is
   unsatisfiable (a validity question the caller's [valid] proves), [e_i] is
   dropped.  If every disjunct is dropped, [N] is unsatisfiable and [phi] is
   valid.  If exactly one is left, it follows from [N] and becomes a fact for
   the next instances.  Anything else is no conclusion.
   Soundness: [N] implies [facts] and [H theta]; [facts] implies the negation
   of every dropped disjunct; so [N] implies the one left (or [false] when
   none is).  Only proofs of validity are read, never a model, and a fact
   is only ever added as a consequence of [N], so [true] is returned only
   when [phi] is valid in every model the caller's [valid] quantifies over.

   Why asked one disjunct at a time.  On a Rust-derived filter's
   transitivity law (a lemma applied at the premises' witnesses, the goal at
   the lemma's joined index map), each of the sixteen small questions is
   decided in about 0.1 s, while the same instances asked as one question,
   and the uninstantiated piece, are left undecided by z3 and cvc5 at 30 s:
   the solver does not find the order in which the lemma's premises have to
   be discharged before its conclusion meets the goal.

   Which instances.  The binders of [H] that are not index maps are matched
   against the facts' ground terms ([SeqInstantiation.matched_substitutions]:
   a lemma's premise [R(a, s, b)] against the fact [R(a, x, b)]).  An index
   map binder [f] ([Int -> _] array) read as [nth S (select f _)] with [S]
   closed by that match is offered the free maps [g] the facts read as
   [nth S (select g _)] (the map that belongs to the sequence [S]); one read
   as [nth (p ++ q) (select f _)] is offered first the joins
   [lambda k. ite (k < c) (g[k]) (h[k - c] + d)] of two such free maps, [c]
   the length of a proper prefix of another closed concatenation of the
   body and [d] of [p ++ q] -- the index map of a filter's visited items over
   the concatenation of two runs.  Every instance is an instance, so the
   choice affects only which are tried.  At most [max_instances] per
   hypothesis and round, [max_rounds] rounds, [max_questions] questions in
   all.

   The extended route ([extended]).  Five additions, each exact or a choice
   of which questions to ask, so the soundness argument above is unchanged:
   (1) a piece that is a conjunction is proved conjunct by conjunct, and a
   conclusion that is a conjunction holding a witness goal is split,
   one piece per conjunct ([goal_pieces], distribution of a disjunction over
   one conjunction), and each piece tries its negated goal first; (2) the
   existential facts are opened over fresh variables
   ([skolemize_existential_facts]); (3) a sequence binder is offered the
   one-step extensions [g ++ [e]] of the facts' sequences
   ([extension_candidates]), and, where any is offered, the instances that
   build their terms, then those whose terms the facts relate, are tried
   first ([rank_by_cooccurrence]; with none offered, the instances and their
   order are the plain route's); a hypothesis that leaves a fact is kept for
   the next round, its instances tried there not asked again; (4) a disjunct the facts leave undecided (neither proved
   nor given a countermodel) is asked again by cases: an existential's
   integer binders opened and its widest disjunctive conjunct distributed
   ([case_questions]), and a case still undecided split on an index against
   a concatenation's prefix ([index_cases]); (5) each such case is asked
   beside selections of the facts, smallest first ([fact_tiers]: the
   quantified facts about the instance's opened existentials, its own
   sequences, the disjunct's collections, its other variables, all), a
   refutation from a sub-list of the facts being one from all of them.  At
   most [max_questions_extended] questions.  What it is for: a loop step
   whose new witness extends the invariant's history by the one item [next]
   produced ([fs ++ [f']], [s ++ [v]]), undecided by z3 and cvc5 whole and
   with the witness given, whose cases were each decided in under a second
   beside the two or three facts about their terms. *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

let max_instances = 8
let max_rounds = 3
let max_questions = 64

(* the extended route asks a disjunct again by cases and fact selections, so
   it is given more questions *)
let max_questions_extended = 192

(* what this process asked and proved, read by the trace and the tests *)
let questions_asked = ref 0
let pieces_tried = ref 0
let pieces_proved = ref 0

(* The extended route, set by the coordinator from its configuration;
   process-wide, as [SeqInstantiation]'s switches are.  With it on, [prove]
   splits a conjunctive conclusion into pieces first ([goal_pieces]) and tries
   each piece's negated goal before the other hypotheses, opens the
   existential facts ([skolemize_existential_facts]), offers a sequence binder
   the one-step extensions [g ++ [e]] of the facts' sequences
   ([extension_candidates]), and tries first the instances whose terms the
   facts relate ([rank_by_cooccurrence]).  Every one of these changes only
   which questions are asked, never what a proof is. *)
let extended = ref false

(* [Some n] (set by the coordinator; [None] by default): with the extended
   route on, a piece some of whose goal pieces have a witness goal that only
   the last-disjunct rule finds (nothing was split) is first given a short
   extended probe -- each goal piece tried goal first with at most [n]
   questions, stopping at the first piece not proved -- before the plain
   route and the full extended route, which skips the pieces the probe
   proved.  Only the order and the question caps change: every question is
   still a validity question whose [`Valid] only is read.  Why: on a loop
   step whose witness goal the plain route never reaches, the plain route
   spent its whole 64-question budget (35-60 s) before the extended route
   proved the piece in 11 questions; the plain route still runs first on
   every piece the probe does not prove, which keeps the input whose pieces
   it proves in about 32 s answering (each probe costs at most [n]
   questions per piece). *)
let goal_first_probe = ref None

(* the question cap of one [prove_one] call: the probe's while it runs *)
let question_cap_override = ref None

let question_cap () =
  match !question_cap_override with
  | Some n -> n
  | None -> if !extended then max_questions_extended else max_questions

(* whether the trace prints each disjunct the facts do not refute (a
   census's diagnosis; off in the solver) *)
let trace_disjuncts = ref false

let binds_collection senv =
  List.exists senv ~f:(fun (_, s) ->
      Term.is_array_sort s || SeqInstantiation.is_seq_sort s)

let is_index_map_sort = function
  | T_array.SArray (T_int.SInt, _) -> true
  | _ -> false

(* reads [nth S (select (Var g) _)] of [phi], entering binders, as (S, g) *)
let nth_select_reads phi =
  Set.to_list
  @@ Formula.filtered_terms_of phi ~f:(function
    | Term.FunApp
        ( T_seq.SqNth _,
          [ _; Term.FunApp (T_array.ASelect _, [ Term.Var _; _ ], _) ],
          _ ) ->
        true
    | _ -> false)
  |> List.filter_map ~f:(function
    | Term.FunApp
        ( T_seq.SqNth _,
          [ s; Term.FunApp (T_array.ASelect _, [ Term.Var (g, _, _); _ ], _) ],
          _ ) ->
        Some (s, g)
    | _ -> None)

let concat_lengths u =
  match u with
  | Term.FunApp (T_seq.SqConcat se, _, _) ->
      let ops = SeqInstantiation.flatten_concat u in
      List.init
        (List.length ops - 1)
        ~f:(fun p ->
          T_seq.mk_len se
            (SeqInstantiation.concat_of se (List.take ops (p + 1))))
  | _ -> []

let is_concat = function
  | Term.FunApp (T_seq.SqConcat _, _, _) -> true
  | _ -> false

(** the terms offered to the index map binder [f] of sort [sort] in [body]
    (already instantiated at every other binder), [free] deciding which
    variables are the piece's own: the free maps the facts pair with the
    sequence [body] reads [f] over and the joins described in the header, the
    joins first when that sequence is a concatenation *)
let map_candidates ~free ~fact_reads f sort body =
  let closed t = Set.for_all (Term.tvs_of t) ~f:free in
  let own =
    List.filter_map (nth_select_reads body) ~f:(fun (s, g) ->
        if Ident.tvar_equal g f && closed s then Some s else None)
    |> SeqInstantiation.dedup_terms
  in
  let maps_of s =
    List.filter_map fact_reads ~f:(fun (s', g) ->
        if Stdlib.( = ) s s' && free g then Some (Term.mk_var g sort) else None)
  in
  let paired = SeqInstantiation.dedup_terms (List.concat_map own ~f:maps_of) in
  let joins =
    match sort with
    | T_array.SArray (T_int.SInt, T_int.SInt) ->
        let inner = List.filter own ~f:is_concat in
        let visited =
          Set.to_list
            (Formula.filtered_terms_of body ~f:(fun t ->
                 is_concat t && closed t))
          |> List.filter ~f:(fun u ->
              not (List.mem inner u ~equal:Stdlib.( = )))
          |> SeqInstantiation.dedup_terms
        in
        let maps =
          List.filter_map fact_reads ~f:(fun (_, g) ->
              if free g then Some (Term.mk_var g sort) else None)
          |> List.filter ~f:(fun t -> Stdlib.( = ) (Term.sort_of t) sort)
          |> SeqInstantiation.dedup_terms
        in
        let join g h c d =
          let k = Ident.mk_fresh_tvar () in
          let kv = Term.mk_var k T_int.SInt in
          let rd a i = T_array.mk_select T_int.SInt T_int.SInt a i in
          T_array.mk_lambda (k, T_int.SInt) T_int.SInt
            (T_bool.ifte (Formula.lt kv c) (rd g kv)
               (T_int.mk_add (rd h (T_int.mk_sub kv c)) d))
        in
        List.concat_map visited ~f:(fun v ->
            List.concat_map (concat_lengths v) ~f:(fun c ->
                List.concat_map inner ~f:(fun u ->
                    List.concat_map (concat_lengths u) ~f:(fun d ->
                        List.concat_map maps ~f:(fun g ->
                            List.filter_map maps ~f:(fun h ->
                                if Stdlib.( = ) g h then None
                                else Some (join g h c d)))))))
        |> List.filter_map ~f:(SeqInstantiation.guard_array_witness ~body f)
        |> fun ts -> List.take ts max_instances
    | _ -> []
  in
  (* the shifts [lambda k. k + len p] for the proper prefixes [p] of a
     concatenation [body] reads [f] over, and the identity: the index map of
     the items a step appends to a history [p] *)
  let shifts =
    match sort with
    | T_array.SArray (T_int.SInt, T_int.SInt) ->
        let shift d =
          let k = Ident.mk_fresh_tvar () in
          let kv = Term.mk_var k T_int.SInt in
          T_array.mk_lambda (k, T_int.SInt) T_int.SInt
            (match d with None -> kv | Some d -> T_int.mk_add kv d)
        in
        (List.concat_map (List.filter own ~f:is_concat) ~f:(fun u ->
             List.map (concat_lengths u) ~f:(fun d -> shift (Some d)))
        @ if List.is_empty own then [] else [ shift None ])
        (* a total lambda is no witness in every model: guarded by the
           ranges [body] reads [f] in *)
        |> List.filter_map ~f:(SeqInstantiation.guard_array_witness ~body f)
    | _ -> []
  in
  (* a read of a concatenation in the facts is mostly the out-of-range branch
     of a split read, which pairs the concatenation with a map of one of its
     parts: there the joins come first *)
  (if List.exists own ~f:is_concat then joins @ paired else paired @ joins)
  @ shifts

(** the one-step extensions offered to the sequence binder [x] (element
    sort [se]) of [body]: [g ++ [e]] for every sequence [g] of sort [Seq se]
    free in [fact_phi] and every closed term [e] that [body] compares, by [=]
    or [!=], with a read [seq.nth x i] -- elements read at an index other than
    the literal [0] first, since a history grows at its end.  What it is for:
    a loop step whose invariant says [produces(entry, v, it)] with the
    witness chain [fs] and whose call of [next] gives the chain [[f, f']] of
    one more step has as its new witness [fs ++ [f']], a term no clause
    writes; the goal pins [f'] as the read at the chain's last index. *)
let extension_candidates ~free ~fact_phi x se body =
  let closed t = Set.for_all (Term.tvs_of t) ~f:free in
  let is_zero = function
    | Term.FunApp (T_int.Int z, [], _) -> Z.equal z Z.zero
    | _ -> false
  in
  let read_of = function
    | Term.FunApp (T_seq.SqNth _, [ Term.Var (y, _, _); i ], _)
      when Ident.tvar_equal x y ->
        Some i
    | _ -> None
  in
  let pos, neg = Formula.atoms_of ~nrec:true body in
  let elements =
    Set.to_list (Set.union pos neg)
    |> List.filter_map ~f:(function
      | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ a; b ], _) -> (
          match (read_of a, read_of b) with
          | Some i, None when closed b -> Some (i, b)
          | None, Some i when closed a -> Some (i, a)
          | _ -> None)
      | _ -> None)
  in
  let elements =
    let late, first = List.partition_tf elements ~f:(fun (i, _) -> not (is_zero i)) in
    SeqInstantiation.dedup_terms (List.map (late @ first) ~f:snd)
  in
  let seqs =
    Set.to_list (Formula.sort_env_of fact_phi)
    |> List.filter_map ~f:(fun (g, s) ->
        if free g && Stdlib.( = ) s (T_seq.SSeq se) then Some g else None)
    |> List.sort ~compare:Ident.tvar_compare
  in
  List.concat_map elements ~f:(fun e ->
      List.map seqs ~f:(fun g ->
          T_seq.mk_concat se (Term.mk_var g (T_seq.SSeq se)) (T_seq.mk_unit se e)))

(** [subs] ordered, stably, first by how many binders they give a term other
    than a variable (a step's witness extends the previous one, so it is
    built, not named), then by how many facts relate the terms they give two
    different binders: a fact counts once for each pair of binders [x], [y]
    such that it mentions a free variable of the term for [x] that is a
    sequence's or an array's and one of the term for [y]; the most related
    first.  A heuristic only: every substitution is an instance.  Why: the
    witness of a step joins the invariant's chain [fs] and its items [s],
    which the invariant's facts mention together, while the other sequences
    of the same sorts are other copies of the same existential. *)
let rank_by_cooccurrence ~facts subs =
  let fact_vars = List.map facts ~f:Formula.tvs_of in
  let collection_vars t =
    Set.to_list (Term.term_sort_env_of t)
    |> List.filter_map ~f:(fun (y, s) ->
        if Term.is_array_sort s || SeqInstantiation.is_seq_sort s then Some y
        else None)
    |> Set.Poly.of_list
  in
  let score sub =
    let vs = List.map (Map.Poly.data sub) ~f:collection_vars in
    let rec pairs = function
      | [] -> []
      | a :: rest -> List.map rest ~f:(fun b -> (a, b)) @ pairs rest
    in
    List.sum (module Int) (pairs vs) ~f:(fun (a, b) ->
        List.count fact_vars ~f:(fun fv ->
            (not (Set.is_empty (Set.inter a fv)))
            && not (Set.is_empty (Set.inter b fv))))
  in
  let built sub =
    List.count (Map.Poly.data sub) ~f:(function Term.Var _ -> false | _ -> true)
  in
  List.map subs ~f:(fun s -> ((built s, score s), s))
  |> List.stable_sort ~compare:(fun (a, _) (b, _) ->
      Tuple2.compare ~cmp1:Int.compare ~cmp2:Int.compare b a)
  |> List.map ~f:snd

(** the substitutions of all of [senv] tried for the hypothesis
    [forall senv. body], at most [max_instances] *)
let instances ~free ~facts senv body =
  let fact_phi = Formula.and_of facts in
  let ground = SeqInstantiation.ground_funapps fact_phi in
  let fact_reads = nth_select_reads fact_phi in
  let maps, others =
    List.partition_tf senv ~f:(fun (_, s) -> is_index_map_sort s)
  in
  let firsts =
    if List.is_empty others then [ Map.Poly.empty ]
    else
      let extra =
        if not !extended then []
        else
          List.concat_map others ~f:(fun (x, s) ->
              match SeqInstantiation.elem_of_seq s with
              | Some se ->
                  List.map (extension_candidates ~free ~fact_phi x se body)
                    ~f:(fun t -> (x, t))
              | None -> [])
      in
      (* with no extension to offer, the instances and their order are the
         plain route's *)
      if not (List.is_empty extra) then
        SeqInstantiation.matched_substitutions ~extra ~max:(4 * max_instances)
          ~open_scalars:false ~ground others body
        |> rank_by_cooccurrence ~facts
      else
      SeqInstantiation.matched_substitutions ~open_scalars:false ~ground others
        body
  in
  List.concat_map firsts ~f:(fun sub ->
      let body1 = Formula.subst sub body in
      let rec go acc = function
        | [] -> [ acc ]
        | (f, sort) :: rest ->
            List.concat_map
              (List.take (map_candidates ~free ~fact_reads f sort body1) 4)
              ~f:(fun t -> go (Map.Poly.set acc ~key:f ~data:t) rest)
      in
      go sub maps)
  |> fun subs -> List.take subs max_instances

(** [conjuncts] with every selector application [sel x] that a conjunct
    [sel x = c(..)] equates to a constructor application replaced, in every
    other conjunct, by [c(..)], and simplified (so [proj_0 (sel x)] becomes the
    field itself). Exact: each rewritten conjunct is equivalent to its original
    wherever the defining conjunct holds, and that conjunct is kept. A binder
    that binds a variable of [sel x] or of [c(..)] is not entered. What it is
    for: a goal written over [proj_0 (final m)] meets the facts over the field
    [x3] that [final m = (x3, x11)] names, and the matching of the instances is
    syntactic. *)
let subst_projection_definitions conjuncts =
  let is_sel_of_var = function
    | Term.FunApp ((T_dt.DTSel _ | T_tuple.TupleSel _), [ Term.Var _ ], _) ->
        true
    | _ -> false
  in
  let is_cons_app = function
    | Term.FunApp ((T_dt.DTCons _ | T_tuple.TupleCons _), _, _) -> true
    | _ -> false
  in
  let defs =
    List.filter_map conjuncts ~f:(function
      | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _) as
        c ->
          (* [sel x = c(..)] with [x] not in [c(..)], either way round *)
          let def s t =
            is_sel_of_var s && is_cons_app t
            && Set.is_empty (Set.inter (Term.tvs_of s) (Term.tvs_of t))
          in
          if def t1 t2 then Some (c, t1, t2)
          else if def t2 t1 then Some (c, t2, t1)
          else None
      | _ -> None)
  in
  let replace (s, t) =
    let blocked = Set.union (Term.tvs_of s) (Term.tvs_of t) in
    let rec rt u =
      if Stdlib.( = ) u s then t
      else
        match u with
        | Term.Var _ | Term.LetTerm _ -> u
        | Term.FunApp (T_bool.Formula f, [], info) ->
            Term.mk_fsym_app ~info (T_bool.Formula (rf f)) []
        | Term.FunApp (T_array.ALambda ((y, _), _), _, _) when Set.mem blocked y
          ->
            u
        | Term.FunApp (fsym, args, info) ->
            Term.mk_fsym_app ~info fsym (List.map args ~f:rt)
    and rf f =
      match f with
      | Formula.Atom (Atom.App (pred, args, ainfo), info)
        when not (Predicate.is_fix pred) ->
          Formula.mk_atom ~info
            (Atom.mk_app ~info:ainfo pred (List.map args ~f:rt))
      | Formula.Atom _ -> f
      | Formula.UnaryOp (op, f1, info) -> Formula.mk_unop ~info op (rf f1)
      | Formula.BinaryOp (op, f1, f2, info) ->
          Formula.mk_binop ~info op (rf f1) (rf f2)
      | Formula.Bind (binder, bound, body, info) ->
          if List.exists bound ~f:(fun (y, _) -> Set.mem blocked y) then f
          else Formula.mk_bind ~info binder bound (rf body)
      | Formula.LetRec _ | Formula.LetFormula _ -> f
    in
    rf
  in
  if List.is_empty defs then conjuncts
  else
    List.map conjuncts ~f:(fun c ->
        let c' =
          List.fold defs ~init:c ~f:(fun c (d, s, t) ->
              if phys_equal c d then c else replace (s, t) c)
        in
        if phys_equal c' c then c else Evaluator.simplify c')

(** the pieces of [phi] read as a disjunction [d_1 \/ ... \/ d_n]: the
    first disjunct [d_i = c_1 /\ ... /\ c_k] with [1 < k <= max] one of
    whose conjuncts is an existential binding an array or a sequence (a goal
    that asks for a witness) is split, one piece
    [d_1 \/ .. \/ c_j \/ .. \/ d_n] per conjunct, so that [phi] is valid
    exactly when every piece is (distribution of [\/] over [/\] along one
    disjunct, exact in every model); [[phi]] itself when there is no such
    disjunct.  Only that disjunct is split: a negated premise is often a small
    conjunction too, and splitting it only multiplies the pieces.  What it is
    for: a clause whose conclusion is a conjunction (a loop invariant whose
    conjuncts are a [produces] existential and the adapter's own invariant)
    gives a negation in which the goal's existential is one disjunct of a
    fact, never a hypothesis of its own; split, each conclusion conjunct is
    the negated goal of one piece. *)
(* an existential binding an array or a sequence: a goal asking for a
   witness *)
let is_witness_goal = function
  | Formula.Bind (Formula.Exists, senv, _, _) -> binds_collection senv
  | _ -> false

let goal_pieces ?(max = 16) phi =
  let ds = Formula.disjuncts_list_of phi in
  let split =
    List.find_mapi ds ~f:(fun i d ->
        let c = Formula.conjuncts_list_of d in
        if List.length c > 1 && List.length c <= max
           && List.exists c ~f:is_witness_goal
        then Some (i, c)
        else None)
  in
  match split with
  | Some (i, c) ->
      List.map c ~f:(fun x ->
          Formula.or_of (List.mapi ds ~f:(fun j d -> if j = i then x else d)))
  | None -> [ phi ]

(** the cases of a disjunct [e] of an instance, read as a conjunction to be
    refuted: [e]'s existential integer binders are replaced by fresh free
    variables (exact for refutation, as [skolemize_existential_facts] says),
    and the conjunct of the result with the most disjuncts, [B_1 \/ ... \/
    B_m], is distributed: one case [rest /\ B_i] per disjunct, so that [e]
    with the facts is unsatisfiable exactly when every case is.  [[e]] when
    there is nothing to distribute.  What it is for: the negation of a
    universal goal conjunct (a chain property over every index of a history
    extended by one step) is [exists k. range(k) /\ (B_1 \/ ... \/ B_m)],
    each [B_i] one property violated at [k]; Z3 left that question
    undecided beside the facts' quantified chain properties, and decides the
    cases one at a time. *)
let case_questions e =
  let fresh = ref [] in
  let e =
    match e with
    | Formula.Bind (Formula.Exists, senv, body, _)
      when List.for_all senv ~f:(fun (_, s) -> Stdlib.( = ) s T_int.SInt) ->
        let sub =
          Map.Poly.of_alist_exn
          @@ List.map senv ~f:(fun (x, s) ->
              let y = Ident.mk_fresh_tvar () in
              fresh := y :: !fresh;
              (x, Term.mk_var y s))
        in
        Formula.subst sub body
    | _ -> e
  in
  let fresh = List.rev !fresh in
  let cs = Formula.conjuncts_list_of e in
  let widest =
    List.foldi cs ~init:None ~f:(fun i best c ->
        let n = List.length (Formula.disjuncts_list_of c) in
        match best with
        | Some (_, m) when m >= n -> best
        | _ -> if n > 1 then Some (i, n) else best)
  in
  ( fresh,
    match widest with
    | None -> [ e ]
    | Some (i, _) ->
        let rest = List.filteri cs ~f:(fun j _ -> j <> i) in
        List.map
          (Formula.disjuncts_list_of (List.nth_exn cs i))
          ~f:(fun b -> Formula.and_of (rest @ [ b ])) )

(** [conjuncts] with every top-level existential [exists xs. body] replaced
    by the conjuncts of [body] over fresh free variables, other conjuncts
    kept.  Exact for the question asked of them: a conjunction with
    [exists xs. body] is unsatisfiable exactly when the same conjunction with
    [body] over constants occurring nowhere else is, and the route only ever
    reads unsatisfiability (a proof of validity of the negation) of
    conjunctions of these facts with instances.  What it is for: a call's
    postcondition [produces(a, [v], b)] whose item [v] is existential in the
    negation names the history [x ++ [v]] the goal's witness is built from;
    matching needs that history as a ground term. *)
let skolemize_existential_facts conjuncts =
  let rec go acc = function
    | [] -> List.rev acc
    | Formula.Bind (Formula.Exists, senv, body, _) :: rest ->
        let sub =
          Map.Poly.of_alist_exn
          @@ List.map senv ~f:(fun (x, s) ->
              (x, Term.mk_var (Ident.mk_fresh_tvar ()) s))
        in
        go acc (Formula.conjuncts_list_of (Formula.subst sub body) @ rest)
    | c :: rest -> go (c :: acc) rest
  in
  go [] conjuncts

(** the selections of [facts] a question about [e] is asked with, smallest
    first, each a sub-list of [facts] (so a refutation with any of them is a
    refutation with all): every quantifier-free fact, plus (00) the
    quantified facts that share a variable of [opened] (the facts' opened
    existentials the instance uses: a call's postcondition about the one
    item it produced), then (0) the
    quantified facts that share a variable of [focus] (the instance's own
    sequences and arrays and the facts' opened existentials it uses), then
    (1) the quantified facts that share a free variable of an array or sequence sort
    with [e], then (2) those that share any free variable with [e] other
    than the variables more than half of the quantified facts mention, then
    (3) all of [facts]; a selection equal to a later one is left out.
    What it is for: on a loop step's goal, Z3 left a small question
    undecided beside about twenty quantified facts (other copies of the same
    invariant, the chain properties of other histories) and decided it at
    once beside the two or three that mention its terms. *)
let fact_tiers ?(opened = Set.Poly.empty) ?(focus = Set.Poly.empty) facts e =
  let qf, q = List.partition_tf facts ~f:Formula.is_quantifier_free in
  let collection_vars phi =
    Set.to_list (Formula.sort_env_of phi)
    |> List.filter_map ~f:(fun (y, s) ->
        if Term.is_array_sort s || SeqInstantiation.is_seq_sort s then Some y
        else None)
    |> Set.Poly.of_list
  in
  let e_vars = Formula.tvs_of e and e_coll = collection_vars e in
  let q_vars = List.map q ~f:Formula.tvs_of in
  let n_q = List.length q in
  let common =
    List.fold q_vars ~init:Map.Poly.empty ~f:(fun m vs ->
        Set.fold vs ~init:m ~f:(fun m v ->
            Map.Poly.update m v ~f:(function None -> 1 | Some k -> k + 1)))
    |> Map.Poly.filter ~f:(fun k -> 2 * k > n_q)
    |> Map.Poly.key_set
  in
  let shares vs f = List.zip_exn q q_vars |> List.filter_map ~f:(fun (phi, fv) ->
      if f fv vs then Some phi else None)
  in
  let t1 =
    qf @ shares e_coll (fun fv vs -> not (Set.is_empty (Set.inter fv vs)))
  in
  let t2 =
    qf
    @ shares (Set.diff e_vars common) (fun fv vs ->
        not (Set.is_empty (Set.inter fv vs)))
  in
  let t0 =
    if Set.is_empty focus then t1
    else qf @ shares focus (fun fv vs -> not (Set.is_empty (Set.inter fv vs)))
  in
  let t00 =
    if Set.is_empty opened then t0
    else
      qf @ shares opened (fun fv vs -> not (Set.is_empty (Set.inter fv vs)))
  in
  let tiers = [ t00; t0; t1; t2; facts ] in
  let same t t' = List.equal phys_equal t t' in
  List.filteri tiers ~f:(fun i t ->
      not (List.exists (List.drop tiers (i + 1)) ~f:(same t)))

(** the index cases of [e] for each of at most [max_index_candidates]
    candidates [(t, g)]: [g] a proper prefix of a concatenation that [e]
    reads at the index [t] ([seq.nth (g ++ _) t]) or extracts from [0] for
    the length [t], [t] mentioning a variable of [fresh]; reads at a larger
    constant offset ([k + c]) first, as the read past the end of [g] is the
    one whose boundary separates an invariant's positions from a step's.
    Per candidate the three formulas [e] with [t < len g], with [t = len g]
    and with [t > len g] conjoined, each simplified with the reads' guards
    the case decides ([SeqInstantiation.case_form] on the negation).  [e]
    with the facts is unsatisfiable exactly when each of a candidate's three
    is, as the cases cover every model. *)
let max_index_candidates = 2

let index_cases ~fresh e =
  let mentions_fresh t =
    Set.exists (Term.tvs_of t) ~f:(fun v ->
        List.mem fresh v ~equal:Ident.tvar_equal)
  in
  let offset = function
    | Term.FunApp
        ( T_int.Add,
          ([ _; Term.FunApp (T_int.Int c, [], _) ]
          | [ Term.FunApp (T_int.Int c, [], _); _ ]),
          _ ) ->
        c
    | _ -> Z.zero
  in
  let prefix u =
    match u with
    | Term.FunApp (T_seq.SqConcat se, _, _) -> (
        match List.rev (SeqInstantiation.flatten_concat u) with
        | _ :: (_ :: _ as rev_prefix) ->
            Some (SeqInstantiation.concat_of se (List.rev rev_prefix))
        | _ -> None)
    | _ -> None
  in
  let candidates =
    Set.to_list
      (Formula.filtered_terms_of e ~f:(function
        | Term.FunApp
            (T_seq.SqNth _, [ Term.FunApp (T_seq.SqConcat _, _, _); t ], _) ->
            mentions_fresh t
        | Term.FunApp
            ( T_seq.SqExtract _,
              [ Term.FunApp (T_seq.SqConcat _, _, _); Term.FunApp (T_int.Int z, [], _); t ],
              _ ) ->
            Z.equal z Z.zero && mentions_fresh t
        | _ -> false))
    |> List.filter_map ~f:(function
      | Term.FunApp (T_seq.SqNth _, [ u; t ], _)
      | Term.FunApp (T_seq.SqExtract _, [ u; _; t ], _) ->
          Option.map (prefix u) ~f:(fun g -> (offset t, (t, g)))
      | _ -> None)
    |> List.stable_sort ~compare:(fun (c1, _) (c2, _) -> Z.compare c2 c1)
    |> List.map ~f:snd
    |> List.fold ~init:[] ~f:(fun acc p ->
        if List.mem acc p ~equal:Stdlib.( = ) then acc else acc @ [ p ])
  in
  let neg = lazy (Formula.nnf_of (Formula.negate e)) in
  List.take candidates max_index_candidates
  |> List.map ~f:(fun (t, g) ->
      let lg =
        match Term.sort_of g with
        | T_seq.SSeq se -> T_seq.mk_len se g
        | _ -> assert false
      in
      List.map
        [ Formula.geq t lg; Formula.neq t lg; Formula.leq t lg ]
        ~f:(fun lit ->
          match lit with
          | Formula.Atom (a, _) ->
              Formula.nnf_of
                (Formula.negate (SeqInstantiation.case_form (Lazy.force neg) a))
          | _ -> assert false))

(** [true] only when [phi] is valid, as [prove] (below) states; [goal] is
    the conclusion conjunct [goal_pieces] chose for this piece, or, when it
    split nothing, the piece's last top-level witness-goal disjunct; its
    negation is tried first among the hypotheses.  [goal] changes only that
    order. *)
let prove_one ~trace ~skolemize ~goal ~usable ~valid ~outcome phi =
  let n = Formula.nnf_of (Formula.negate phi) in
  let conjuncts =
    subst_projection_definitions
    @@ (if skolemize then skolemize_existential_facts else Fn.id)
    @@ Formula.conjuncts_list_of n
  in
  (* the negated goal first: it is [goal]'s own conjunct of the negation, and
     [subst_projection_definitions] may have rewritten it, so it is found by
     its binders *)
  let conjuncts =
    match goal with
    | None -> conjuncts
    | Some g -> (
        match Formula.nnf_of (Formula.negate g) with
        | Formula.Bind (Formula.Forall, gsenv, _, _) ->
            let is_goal = function
              | Formula.Bind (Formula.Forall, senv, _, _) ->
                  Stdlib.( = ) senv gsenv
              | _ -> false
            in
            let gs, rest = List.partition_tf conjuncts ~f:is_goal in
            trace
              (lazy
                (sprintf "lemma application: %d goal hypotheses first"
                   (List.length gs)));
            gs @ rest
        | _ ->
            trace (lazy "lemma application: a goal that is not a witness goal");
            conjuncts)
  in
  trace
    (lazy
      (sprintf "lemma application: %d conjuncts, %d hypotheses"
         (List.length conjuncts)
         (List.count conjuncts ~f:(function
           | Formula.Bind (Formula.Forall, senv, _, _) -> binds_collection senv
           | _ -> false))));
  let is_hyp = function
    | Formula.Bind (Formula.Forall, senv, _, _) -> binds_collection senv
    | _ -> false
  in
  (* the variables the opened existential facts introduced *)
  let skolems =
    Set.diff
      (Set.Poly.union_list (List.map conjuncts ~f:Formula.tvs_of))
      (Formula.tvs_of n)
  in
  let hyps, facts = List.partition_tf conjuncts ~f:is_hyp in
  let free_vars = Formula.tvs_of n in
  let free x = Set.mem free_vars x in
  let asked = ref 0 in
  (* [facts /\ e] unsatisfiable, asked as the validity of its negation *)
  let ask facts e =
    if !asked >= question_cap () then `Unknown
    else (
      incr asked;
      incr questions_asked;
      let fs = List.filter facts ~f:usable in
      let q = Formula.negate (Formula.and_of (e :: fs)) in
      let r =
        match outcome with
        | Some o -> o q
        | None -> if valid q then `Valid else `Unknown
      in
      if !trace_disjuncts then
        trace
          (lazy
            (sprintf
               "lemma application: question %d: %d facts (%d quantified), \
                size %d, %s"
               !asked (List.length fs)
               (List.count fs ~f:(Fn.non Formula.is_quantifier_free))
               (Formula.ast_size e)
               (match r with
                | `Valid -> "refuted"
                | `Invalid -> "satisfiable"
                | `Unknown -> "open")));
      r)
  in
  let refuted facts e = match ask facts e with `Valid -> true | _ -> false
  in
  (* [`Proved], [`Fact e] (the one disjunct left), or [`Nothing] *)
  (* with the extended route, a disjunct the facts do not refute whole is
     asked again by cases ([case_questions]): refuted when every case is *)
  (* [c] refuted with the selections of [fact_tiers], smallest first *)
  let refuted_tiered ~focus ~skip_all facts c =
    let tiers =
      fact_tiers ~opened:(Set.inter focus skolems) ~focus facts c
    in
    let tiers =
      if skip_all then
        List.filter tiers ~f:(fun t -> not (List.equal phys_equal t facts))
      else tiers
    in
    List.exists tiers ~f:(fun t -> refuted t c)
  in
  let refuted_by_cases ~focus facts e =
    !extended
    &&
    let fresh, cases = case_questions e in
    trace
      (lazy
        (sprintf "lemma application: disjunct asked by %d cases"
           (List.length cases)));
    List.for_all cases ~f:(fun c ->
        (* [e] itself was asked with every fact already *)
        let whole = phys_equal c e in
        refuted_tiered ~focus ~skip_all:whole facts c
        ||
        List.exists (index_cases ~fresh c) ~f:(fun ics ->
            trace (lazy "lemma application: case asked by index cases");
            List.for_all ics ~f:(refuted_tiered ~focus ~skip_all:false facts)))
  in
  let apply ?(focus = Set.Poly.empty) facts inst =
    let rec go left = function
      | [] -> (
          match left with [] -> `Proved | [ e ] -> `Fact e | _ -> `Nothing)
      | e :: rest ->
          (* the cases are asked only when the whole question was left
             undecided: a countermodel of [facts /\ e] is one of some case
             and some selection of the facts too *)
          let r =
            match ask facts e with
            | `Valid -> true
            | `Invalid -> false
            | `Unknown -> refuted_by_cases ~focus facts e
          in
          trace
            (lazy
              (sprintf "lemma application: disjunct of size %d %s%s"
                 (Formula.ast_size e)
                 (if r then "refuted" else "not refuted")
                 (if r || not !trace_disjuncts then ""
                  else ": " ^ Formula.str_of e)));
          if r then go left rest
          else if List.length left >= 1 then `Nothing
          else go [ e ] rest
    in
    go [] (Formula.disjuncts_list_of inst)
  in
  let tried = ref [] in
  (* an instance's own sequences and arrays, and the opened existentials
     its terms use: what [fact_tiers] selects quantified facts by first *)
  let focus_of sub =
    Set.Poly.union_list
      (List.map (Map.Poly.data sub) ~f:(fun t ->
           Set.to_list (Term.term_sort_env_of t)
           |> List.filter_map ~f:(fun (y, srt) ->
               if
                 Term.is_array_sort srt || SeqInstantiation.is_seq_sort srt
                 || Set.mem skolems y
               then Some y
               else None)
           |> Set.Poly.of_list))
  in
  (* the hypothesis [body] at [sub]; an index map guarded by the range it is
     read in (see [SeqInstantiation.guard_array_witness]) leaves, once its
     reads are beta-reduced, an [ite] on that range under the very premise
     that states it, which the matching below cannot see through, so such
     [ite]s are decided by their context first (an exact rewrite) *)
  let instance_of body sub =
    let phi = Evaluator.simplify @@ Formula.nnf_of (Formula.subst sub body) in
    let phi =
      if
        Map.Poly.exists sub ~f:(fun t ->
            SeqInstantiation.mentions_comprehension t)
      then Evaluator.simplify (Evaluator.decide_contextual_ites phi)
      else phi
    in
    Evaluator.split_seq_reads_for_validity phi
  in
  let rec round k facts hyps =
    if
      k > max_rounds || List.is_empty hyps
      || !asked >= question_cap ()
    then
      false
    else
      let progress = ref false in
      let rec over_hyps facts kept = function
        | [] -> `Facts (facts, List.rev kept)
        | (Formula.Bind (_, senv, body, _) as h) :: rest -> (
            let insts = instances ~free ~facts senv body in
            trace
              (lazy
                (sprintf
                   "lemma application: a hypothesis over %d binders, %d \
                    instances"
                   (List.length senv) (List.length insts)));
            (* with the extended route an instance that leaves a fact ends
               the hypothesis's turn, as in the plain route, but the
               hypothesis is kept for the next round, whose instances are
               computed beside the new fact; an instance tried before (the
               same formula) is not tried again *)
            let rec try_insts_ext facts gained = function
              | [] -> if gained then `Gained facts else `Keep
              | sub :: more -> (
                  let inst = instance_of body sub in
                  if List.mem !tried inst ~equal:Stdlib.( = ) then
                    try_insts_ext facts gained more
                  else (
                    tried := inst :: !tried;
                    trace
                      (lazy
                        (sprintf "lemma application: instance %s"
                           (String.concat ~sep:", "
                           @@ List.map (Map.Poly.to_alist sub) ~f:(fun (x, t) ->
                               Ident.name_of_tvar x ^ " := " ^ Term.str_of t))));
                    if !trace_disjuncts then
                      trace
                        (lazy
                          (sprintf "lemma application: focus %s"
                             (String.concat ~sep:" "
                                (List.map (Set.to_list (focus_of sub))
                                   ~f:Ident.name_of_tvar))));
                    match apply ~focus:(focus_of sub) facts inst with
                    | `Proved -> `Proved
                    | `Fact e ->
                        trace
                          (lazy
                            "lemma application: one disjunct left, kept as a \
                             fact");
                        let fresh =
                          List.filter (Formula.conjuncts_list_of e) ~f:(fun c ->
                              not (List.mem facts c ~equal:Stdlib.( = )))
                        in
                        (* as the plain route, the next hypothesis is taken
                           after a fact; the hypothesis is kept, and its
                           untried instances are tried in the next round *)
                        if List.is_empty fresh then
                          try_insts_ext facts gained more
                        else `Gained (facts @ fresh)
                    | `Nothing -> try_insts_ext facts gained more))
            in
            let rec try_insts = function
              | [] -> `Keep
              | sub :: more -> (
                  trace
                    (lazy
                      (sprintf "lemma application: instance %s"
                         (String.concat ~sep:", "
                         @@ List.map (Map.Poly.to_alist sub) ~f:(fun (x, t) ->
                             Ident.name_of_tvar x ^ " := " ^ Term.str_of t))));
                  let inst = instance_of body sub in
                  match apply facts inst with
                  | `Proved -> `Proved
                  | `Fact e -> `Fact e
                  | `Nothing -> try_insts more)
            in
            match
              if !extended then try_insts_ext facts false insts
              else try_insts insts
            with
            | `Gained facts ->
                progress := true;
                over_hyps facts (h :: kept) rest
            | `Proved -> `Proved
            | `Fact e ->
                progress := true;
                trace
                  (lazy "lemma application: one disjunct left, kept as a fact");
                over_hyps (facts @ Formula.conjuncts_list_of e) kept rest
            | `Keep -> over_hyps facts (h :: kept) rest)
        | h :: rest -> over_hyps facts (h :: kept) rest
      in
      match over_hyps facts [] hyps with
      | `Proved -> true
      | `Facts (facts, hyps) -> !progress && round (k + 1) facts hyps
  in
  (* with the extended route, the facts alone first: a piece of a split
     conclusion is often a consequence of the premises that needs no
     hypothesis at all *)
  let proved =
    (!extended && refuted facts (Formula.mk_true ())) || round 1 facts hyps
  in
  trace
    (lazy
      (sprintf "lemma application: %s after %d questions"
         (if proved then "proved" else "not proved")
         !asked));
  proved

(** [true] only when [phi] is valid; [valid psi] must be [true] only when [psi]
    is valid. [usable fact] says whether a fact may be put in a question (the
    caller's refusal of a shape it may not return on).  With [skolemize]
    (default [!extended]) the top-level existential facts are opened first
    ([skolemize_existential_facts]).  With [!extended], [phi] is split into
    its conjuncts and each by [goal_pieces], and proved when every piece is
    (exact, as that function says) -- after the plain route has failed on
    [phi] whole, which is tried first (after a short goal-first probe under
    [goal_first_probe]) -- each piece trying its own negated goal first.  [outcome psi], when
    given, is used in place of [valid]: [`Valid] only when [psi] is valid
    (as [valid] promises), [`Invalid] when a countermodel was found, and
    [`Unknown] otherwise; the extended route asks a disjunct again by cases
    only after [`Unknown]. *)
let prove ?(trace = fun (_ : string lazy_t) -> ()) ?(skolemize = !extended)
    ?outcome ~usable ~valid phi =
  incr pieces_tried;
  trace
    (lazy
      (sprintf "lemma application: a piece of size %d: %s"
         (Formula.ast_size phi)
         (String.prefix (Formula.str_of phi) 600)));
  let plain () =
    Ref.set_temporarily extended false ~f:(fun () ->
        prove_one ~trace ~skolemize:false ~goal:None ~usable ~valid ~outcome phi)
  in
  (* the goal pieces of the extended route, each with its goal and whether
     that goal was found by the last-witness-disjunct rule *)
  let goal_pieces_of () =
    let conjuncts = Formula.conjuncts_list_of phi in
    let pieces =
      List.concat_map conjuncts ~f:(fun c ->
          let ds = Formula.disjuncts_list_of c in
          List.map (goal_pieces c) ~f:(fun p -> (ds, p)))
    in
    trace
      (lazy
        (sprintf "lemma application: %d conjuncts, %d goal pieces"
           (List.length conjuncts) (List.length pieces)));
    List.map pieces ~f:(fun (ds, p) ->
        (* the conjunct this piece took: its disjunct not among [ds] *)
        match
          List.find (Formula.disjuncts_list_of p) ~f:(fun d ->
              not (List.mem ds d ~equal:Stdlib.( = )))
        with
        | Some _ as g -> (p, g, false)
        | None ->
            (* nothing was split ([goal_pieces] returned the conjunct
               whole): the piece's last top-level disjunct that is a
               witness goal is its goal.  This is the shape of a piece
               whose conclusion an earlier split already took apart, so
               that the witness existential is a disjunct of its own;
               without it the goal's negation keeps its place among the
               hypotheses and is tried after every law ahead of it, which
               can spend the question budget before the goal is reached.
               The last, not the first: a premise universal over a
               sequence (a law) is, negated, a witness existential too,
               and a clause read as a disjunction puts its negated
               premises before its conclusion.  The disjuncts are read
               off [p]'s negation normal form, so that an implication's
               conclusion is one of them; [prove_one] finds the goal
               among the negation's conjuncts by its binders, which the
               normal form keeps.
               Contract: [goal] decides only the order in which
               [prove_one] tries the hypotheses, never what a proof is
               -- every question asked is still a validity question
               whose [`Valid] only is read -- so [prove] stays [true]
               only when [phi] is valid, whichever disjunct is taken;
               the order changes only which proof (if any) is found
               within the question budget. *)
            let g =
              List.find
                (List.rev (Formula.disjuncts_list_of (Formula.nnf_of p)))
                ~f:is_witness_goal
            in
            (p, g, Option.is_some g))
  in
  (* computed once, so that the probe and the full route see the same pieces
     (physically: a piece the probe proved is recognised by identity) *)
  let goal_pieces_of =
    let gps = lazy (goal_pieces_of ()) in
    fun () -> Lazy.force gps
  in
  (* the pieces the probe proved, skipped by the full extended route (a
     proved piece is valid, whichever pass proved it) *)
  let probe_proved = ref [] in
  let probe () =
    match !goal_first_probe with
    | None -> false
    | Some n ->
        let gps = goal_pieces_of () in
        if not (List.exists gps ~f:(fun (_, _, w) -> w)) then false
        else (
          trace
            (lazy
              (sprintf "lemma application: goal-first probe, %d questions per \
                        piece"
                 n));
          let proved =
            Ref.set_temporarily question_cap_override (Some n) ~f:(fun () ->
                List.for_all gps ~f:(fun (p, goal, _) ->
                    let ok =
                      prove_one ~trace ~skolemize ~goal ~usable ~valid
                        ~outcome p
                    in
                    if ok then probe_proved := p :: !probe_proved;
                    ok))
          in
          trace
            (lazy
              (sprintf "lemma application: goal-first probe %s"
                 (if proved then "proved the piece" else "left the piece")));
          proved)
  in
  let proved =
    if !extended && probe () then true
    else if !extended && plain () then true
    else if !extended then
      (* the plain route first: it asks at most [max_questions] questions and
         proves what it proves in the same order as without the extension, so
         the extension's larger budget and its case questions are spent only on
         a piece the plain route leaves (asked first on a file whose pieces the
         plain route proved in about 32 s, they ran 45 s on the first piece
         alone and the run lost its answer).  A conjunction is valid exactly when each conjunct is: the ladder
         hands over a coarse piece that is a conjunction of its sub-pieces *)
      List.for_all (goal_pieces_of ()) ~f:(fun (p, goal, _) ->
          List.mem !probe_proved p ~equal:phys_equal
          || prove_one ~trace ~skolemize ~goal ~usable ~valid ~outcome p)
    else prove_one ~trace ~skolemize ~goal:None ~usable ~valid ~outcome phi
  in
  if proved then incr pieces_proved;
  proved

(** The route's question as the zero-unknown verdict asks it: the validity of
    [psi] in a fresh Z3 context under [ms] milliseconds, [`Valid] only from
    Z3's proof (the sequence-axiom fallback's included), [`Invalid] when Z3
    found a countermodel (read only by the extended route, to skip asking by
    cases), [`Unknown] otherwise -- and without asking when Z3 may not return
    on the shape.  Labelled ["lemma"] for [COAR_Z3_RLIMIT_LOG].

    [rlimits = (native, fallback)] bounds the question by Z3's resource count
    instead of by the wall clock: [native] units for the question as asked,
    [fallback] for the sequence-axiom fallback asked after an undecided
    answer, whose wall-clock budget is then [ms] in place of the
    process-wide one, so that [ms] is the kill of both and the count is what
    stops a question that does not decide.  An exhausted count is
    [`Unknown], which the route reads as it reads a timeout.  [None]: the
    wall clock alone, the fallback at its process-wide budget.  The bounds
    change only which questions are decided, never what a decision says. *)
(* With [COAR_DUMP_LEMMA_QUESTIONS=dir] in the environment, every check one
   route question makes (the native one and the sequence-axiom fallback's) is
   written as [dir/lN-PID_k.smt2] before it is asked, with its answer appended
   ([Z3interface.with_query_dump]).  A diagnostic: nothing is written and the
   answer is unchanged without the variable. *)
let lemma_dump_count = Atomic.make 0

let with_lemma_dump f =
  match Sys.getenv "COAR_DUMP_LEMMA_QUESTIONS" with
  | None -> f ()
  | Some dir ->
      Z3Smt.Z3interface.with_query_dump
        (sprintf "%s/l%d-%d" dir
           (Atomic.fetch_and_add lemma_dump_count 1)
           (Common.ForkGuard.self_pid ()))
        f

let z3_outcome ~ms ?rlimits psi =
  if Z3Smt.Z3interface.may_not_return psi then `Unknown
  else
    with_lemma_dump @@ fun () ->
    let native, fallback =
      match rlimits with None -> (None, None) | Some (n, f) -> (Some n, Some f)
    in
    let fenv =
      Z3Smt.Z3interface.fenv_reached_by (Ast.LogicOld.get_fenv ()) psi
    in
    match
      Z3Smt.Z3interface.with_rlimit ~label:"lemma" native @@ fun () ->
      Z3Smt.Z3interface.with_seq_axiom_rlimit fallback @@ fun () ->
      Z3Smt.Z3interface.with_seq_axiom_fallback_base
        (Option.map fallback ~f:(fun _ -> ms))
      @@ fun () ->
      Z3Smt.Z3interface.check_valid ~timeout:(Some ms) ~fresh_solver:true
        ~id:None fenv psi
    with
    | `Valid -> `Valid
    | `Invalid _ -> `Invalid
    | _ -> `Unknown
