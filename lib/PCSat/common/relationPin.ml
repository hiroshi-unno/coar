open Core
open Common.Ext

(* Refuting a constraint with no predicate variable left by fixing the
   Boolean-valued arrays free in one of its clauses -- universally quantified
   relations such as an iterator's [produces] or a closure's [post] -- to
   finite relations built from the clause itself, and asking whether the
   clause's negation is then satisfiable.

   The shape it is for.  A clause [C] (valid when it holds for every value of
   its free variables) whose free variables include curried arrays
   [r : A1 -> ... -> An -> Bool] that no clause defines: the clause's
   hypotheses assert some ground facts [r(t)] and state laws over [r] -- a
   transitivity law [r(p, s1, q) /\ r(q, s2, u) => r(p, s1 ++ s2, u)], a
   reflexivity law [forall p. r(p, [], p)] -- and its conclusion demands
   something of [r].  A countermodel has to choose [r]; left free, the solver
   has to build the relation from the laws by quantifier instantiation, and
   on such clauses it does not return.  Chosen well -- the least relation the
   hypotheses force -- the question becomes nearly ground.

   The route, per piece [P] of [C] ([SeqInstantiation.pieces]: [C] holds in a
   model exactly when every piece does, so a countermodel of a piece is one
   of [C]), with [N] the negation normal form of [not P]:
   1. Shape.  Choose a length for every free sequence variable of [P]: the
      lengths a model of a quantifier-free relaxation of [N]
      ([ScalarPin.relaxations], each satisfied by every model of [N]) gives,
      asked with the lengths' sum fixed to 0, 1, 2, ... in turn so that short
      shapes come first, a few per sum, each tried shape excluded from the
      next question.  Each sequence [s] of length [k] is replaced by
      [unit c1 ++ ... ++ unit ck] over fresh element variables and the
      equation [s = unit c1 ++ ... ++ unit ck] is kept, as [SeqPin] does:
      the elements, and every other scalar, stay free for the solver.
      Alternatively ([shapes ~by_length_vectors]), the vectors of a sum that
      the relaxation's length-only conjuncts allow are listed and each is
      confirmed with its lengths fixed, so a sum those conjuncts rule out
      costs no question.
   2. Relations.  Read [N]'s conjuncts (each a requirement of every model of
      [N]) as Horn rules over the relations: a positive ground atom [r(t)] is
      a fact; [forall ys. G \/ r(v)] with no other relation atom is a
      pattern, kept symbolic as the set [{x | exists ys. not G /\ x = v}];
      and [forall ys. not r1(u1) \/ ... \/ not rm(um) \/ G \/ r(v)] is a
      law.  A universal over at most two integers is also read at each
      value 0 to 3 of its binders: an instance that simplifies to a
      conjunction of positive atoms gives facts (a read of a pinned sequence
      is a case split on the index, so the instance is often a fact where
      the rule itself is not a flat disjunction), and a pattern every one of
      whose instances is decided so is not kept symbolic.
      The facts are closed under the laws by
      syntactic matching of [u_j] against the tuples found so far (an
      instance whose [not G] simplifies to false, or whose conclusion keeps a
      variable the premises do not bind, is not added), concatenations
      normalised, until nothing new comes or more than [max_tuples] tuples
      are found, in which case the piece is given up.  Each relation [r] is
      then fixed to the array [lambda x. \/_t (x = t) \/ patterns(x)], and
      each full application [r(a)] in [N] is replaced by that membership
      formula at [a]; a relation also used otherwise (partially applied,
      compared as an array) is left free.
   3. Ask.  The pinned [N] is asked for SATISFIABILITY, under a budget.

   Why a [sat] answer is a refutation.  The pinned query is [N] with a
   conjunct [s = lit_s] added for every sequence and [r] replaced by its
   pinned value [L_r]; [exists r. r = L_r /\ N(r)] is [N(L_r)], so the query
   is equivalent to [N /\ /\_s s = lit_s /\ /\_r r = L_r], a STRENGTHENING of
   [N].  A model of it is therefore a model of [N], i.e. of the background
   theory with values for [P]'s free variables -- the relations among them,
   taking the pinned values -- at which [P], hence [C], is false.  [C]'s free
   variables are universal (a [declare-forall-fun] relation is one: the
   clause must hold for every relation), so the constraint is false in that
   model, which with no predicate variable left is a refutation under the
   every-model reading.  Nothing about the pinned relations has to be least,
   or even to satisfy the hypotheses: a choice that violates one only makes
   the query unsatisfiable.  That is also why only [sat] is read: an
   [unsat], [unknown] or [timeout] answer is about the strengthening and says
   nothing about [N], so it costs time and never an answer.  The pinned
   values are added to the model as [r = lambda ...] so that the recorded
   countermodel names them.

   What it cannot do.  A countermodel whose relation is not generated by the
   syntactic closure (a law instance whose premises match only up to an
   equation the model makes true), or whose sequences are longer than the
   shapes tried, is not found; a relation read through an equality of
   arrays or a partial application is not pinned; a variable at two sorts
   leaves the piece alone. *)

open Ast.LogicOld

let max_tuples = 64
let max_rounds = 16
let max_attempts = 8
let max_length_sum = 8
let shapes_per_sum = 3
let max_length = 4
let unroll_values = [ 0; 1; 2; 3 ]
let max_unrolled_binders = 2

(** the number of indices of a curried Boolean-valued array sort, [None] for any
    other sort *)
let rec relation_arity = function
  | T_array.SArray (_, T_bool.SBool) -> Some 1
  | T_array.SArray (_, s) -> Option.map (relation_arity s) ~f:(( + ) 1)
  | _ -> None

let rec index_sorts = function
  | T_array.SArray (si, T_bool.SBool) -> [ si ]
  | T_array.SArray (si, s) -> si :: index_sorts s
  | _ -> []

(** [select (... (select r a1) ...) an] as [(r, [a1; ...; an])] when [r] is a
    variable *)
let rec chain = function
  | Term.FunApp (T_array.ASelect _, [ a; i ], _) ->
      Option.map (chain a) ~f:(fun (r, is) -> (r, is @ [ i ]))
  | Term.Var (r, _, _) -> Some (r, [])
  | _ -> None

(** [phi] as a literal [(positive, r, args)] over a full application of one of
    [rels] (name and arity) *)
let rel_literal rels phi =
  let full t =
    match chain t with
    | Some (r, args) -> (
        match List.Assoc.find rels r ~equal:Ast.Ident.tvar_equal with
        | Some n when n = List.length args -> Some (r, args)
        | _ -> None)
    | None -> None
  in
  let is_const b = T_bool.is_true b || T_bool.is_false b in
  let of_sides pos eq t1 t2 =
    let t, b =
      if is_const t2 then (t1, Some t2)
      else if is_const t1 then (t2, Some t1)
      else (t1, None)
    in
    Option.bind b ~f:(fun b ->
        Option.map (full t) ~f:(fun (r, args) ->
            (Bool.equal pos (Bool.equal eq (T_bool.is_true b)), r, args)))
  in
  let of_atom pos = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
        of_sides pos true t1 t2
    | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) ->
        of_sides pos false t1 t2
    | _ -> None
  in
  match phi with
  | Formula.Atom (a, _) -> of_atom true a
  | Formula.UnaryOp (Formula.Not, Formula.Atom (a, _), _) -> of_atom false a
  | _ -> None

let rec strip_foralls acc = function
  | Formula.Bind (Formula.Forall, senv, body, _) ->
      strip_foralls (acc @ senv) body
  | phi -> (acc, phi)

(** a term with its concatenations flattened and nested to the right, empty
    operands dropped, and simplified *)
let rec normalize t =
  let t = Ast.Evaluator.simplify_term t in
  match t with
  | Term.FunApp (T_seq.SqConcat se, _, _) -> (
      match
        List.map ~f:normalize (SeqInstantiation.flatten_concat t)
        |> List.concat_map ~f:SeqInstantiation.flatten_concat
      with
      | [] -> T_seq.mk_empty se
      | ts ->
          let rev = List.rev ts in
          List.fold (List.tl_exn rev) ~init:(List.hd_exn rev) ~f:(fun acc u ->
              T_seq.mk_concat se u acc))
  | _ -> t

type rule =
  | Fact of Ast.Ident.tvar * Term.t list
  | Pattern of sort_env_list * Formula.t * Ast.Ident.tvar * Term.t list
      (** [forall ys. cond => r(v)] *)
  | Law of
      sort_env_list
      * (Ast.Ident.tvar * Term.t list) list
      * Formula.t
      * Ast.Ident.tvar
      * Term.t list  (** [forall ys. r1(u1) /\ ... /\ cond => r(v)] *)

let int_assignments ys =
  let rec go = function
    | [] -> [ [] ]
    | y :: rest ->
        List.concat_map (go rest) ~f:(fun a ->
            List.map unroll_values ~f:(fun n ->
                (y, T_int.mk_int (Z.of_int n)) :: a))
  in
  go (List.map ~f:fst ys)

(** the rules [N]'s conjunct [c] states, as the header describes; a conjunct of
    any other shape states none (it stays in the query all the same) *)
let rec rules_of rels c =
  match rel_literal rels c with
  | Some (true, r, args) -> [ Fact (r, args) ]
  | Some _ -> []
  | None -> (
      match c with
      | Formula.BinaryOp (Formula.And, _, _, _) ->
          List.concat_map (Formula.conjuncts_list_of c) ~f:(rules_of rels)
      | Formula.Bind (Formula.Forall, _, _, _) -> (
          let ys, body = strip_foralls [] c in
          match body with
          | Formula.BinaryOp (Formula.And, _, _, _) ->
              List.concat_map (Formula.conjuncts_list_of body) ~f:(fun b ->
                  rules_of rels (Formula.mk_forall ys b))
          | _ ->
              let lits =
                List.map (Formula.disjuncts_list_of body) ~f:(fun d ->
                    (d, rel_literal rels d))
              in
              let pos =
                List.filter_map lits ~f:(function
                  | _, Some (true, r, a) -> Some (r, a)
                  | _ -> None)
              in
              let neg =
                List.filter_map lits ~f:(function
                  | _, Some (false, r, a) -> Some (r, a)
                  | _ -> None)
              in
              let cond =
                Formula.and_of
                @@ List.filter_map lits ~f:(function
                  | d, None -> Some (Formula.nnf_of (Formula.mk_neg d))
                  | _ -> None)
              in
              let unrollable =
                List.length ys <= max_unrolled_binders
                && List.for_all ys ~f:(fun (_, s) -> Stdlib.( = ) s T_int.SInt)
              in
              (* an integer-bound rule is also read at each of [unroll_values]:
                 the instance, simplified, is usually a conjunction of facts
                 even where the rule's own shape is not a flat disjunction (a
                 read of a pinned sequence is a case split on the index) *)
              let instances =
                if not unrollable then []
                else
                  List.map (int_assignments ys) ~f:(fun a ->
                      Ast.Evaluator.simplify
                        (Formula.subst (Map.Poly.of_alist_exn a) body))
              in
              let decided phi =
                Formula.is_true phi || Formula.is_false phi
                || List.for_all (Formula.conjuncts_list_of phi) ~f:(fun c ->
                    match rel_literal rels c with
                    | Some (true, _, _) -> true
                    | _ -> false)
              in
              let from_instances =
                List.concat_map instances ~f:(fun phi ->
                    if decided phi then rules_of rels phi else [])
              in
              let own =
                match (pos, neg) with
                | [ (r, v) ], [] ->
                    if unrollable && List.for_all instances ~f:decided then []
                    else [ Pattern (ys, cond, r, v) ]
                | [ (r, v) ], _ :: _ -> [ Law (ys, neg, cond, r, v) ]
                | _ -> []
              in
              from_instances @ own)
      | _ -> [])

let subst_list sub = List.map ~f:(fun t -> normalize (Term.subst sub t))

(** the tuples of each relation (the facts closed under the laws) and the
    symbolic patterns, or [None] past [max_tuples] *)
let close rules =
  let tuples = Hashtbl.Poly.create () in
  let count = ref 0 in
  let add r args =
    let args = List.map ~f:normalize args in
    let known = Hashtbl.find_multi tuples r in
    if List.mem known args ~equal:Stdlib.( = ) then false
    else begin
      Hashtbl.add_multi tuples ~key:r ~data:args;
      incr count;
      true
    end
  in
  let symbolic = ref [] in
  List.iter rules ~f:(function
    | Fact (r, a) -> ignore (add r a : bool)
    | Pattern (ys, cond, r, v) -> symbolic := (ys, cond, r, v) :: !symbolic
    | Law _ -> ());
  let laws =
    List.filter_map rules ~f:(function
      | Law (ys, prems, cond, r, v) -> Some (ys, prems, cond, r, v)
      | _ -> None)
  in
  let fire (ys, prems, cond, r, v) =
    let vars = Set.Poly.of_list (List.map ys ~f:fst) in
    let rec go sub = function
      | [] ->
          let bound y = Map.Poly.mem sub y in
          let conclusion_free =
            Set.for_all
              (Set.inter vars
                 (Set.union
                    (Set.Poly.union_list (List.map v ~f:Term.tvs_of))
                    (Formula.tvs_of cond)))
              ~f:bound
          in
          if not conclusion_free then []
          else if
            Formula.is_false (Ast.Evaluator.simplify (Formula.subst sub cond))
          then []
          else [ subst_list sub v ]
      | (r', u) :: rest ->
          List.concat_map (Hashtbl.find_multi tuples r') ~f:(fun t ->
              match SeqInstantiation.match_patterns ~vars sub u t with
              | Some sub -> go sub rest
              | None -> [])
    in
    List.map (go Map.Poly.empty prems) ~f:(fun a -> (r, a))
  in
  let rec rounds k =
    if !count > max_tuples then None
    else if k = 0 then Some ()
    else
      let fresh =
        List.concat_map laws ~f:fire |> List.filter ~f:(fun (r, a) -> add r a)
      in
      if List.is_empty fresh then Some () else rounds (k - 1)
  in
  Option.bind (rounds max_rounds) ~f:(fun () ->
      if !count > max_tuples then None
      else Some ((fun r -> Hashtbl.find_multi tuples r), !symbolic))

(** membership of [args] in the pinned relation [r] *)
let membership ~tuples ~symbolic r args =
  let of_tuple t = Formula.and_of (List.map2_exn args t ~f:Formula.eq) in
  let of_pattern (ys, cond, r', v) =
    if not (Ast.Ident.tvar_equal r r') then None
    else
      let fresh =
        List.map ys ~f:(fun (y, s) -> (y, (Ast.Ident.mk_fresh_tvar (), s)))
      in
      let sub =
        Map.Poly.of_alist_exn
        @@ List.map fresh ~f:(fun (y, (y', s)) -> (y, Term.mk_var y' s))
      in
      Some
        (Formula.mk_exists_if_bounded (List.map fresh ~f:snd)
           (Formula.and_of
              (Formula.subst sub cond
              :: List.map2_exn args v ~f:(fun a t ->
                  Formula.eq a (Term.subst sub t)))))
  in
  Formula.or_of
    (List.map (tuples r) ~f:of_tuple @ List.filter_map symbolic ~f:of_pattern)

(** [phi] with every full application of a relation of [rels] replaced by its
    membership formula *)
let pin_in ~tuples ~symbolic rels phi =
  Formula.map_term phi ~f:(fun t ->
      match chain t with
      | Some (r, args) -> (
          match List.Assoc.find rels r ~equal:Ast.Ident.tvar_equal with
          | Some n when n = List.length args && n > 0 ->
              T_bool.of_formula (membership ~tuples ~symbolic r args)
          | _ -> t)
      | None -> t)

(** the pinned value of [r] as an array, for the recorded model *)
let lambda_of ~tuples ~symbolic r sort =
  let sorts = index_sorts sort in
  let zs = List.map sorts ~f:(fun s -> (Ast.Ident.mk_fresh_tvar (), s)) in
  let body =
    T_bool.of_formula
      (membership ~tuples ~symbolic r
         (List.map zs ~f:(fun (z, s) -> Term.mk_var z s)))
  in
  List.fold_right zs ~init:(body, T_bool.SBool) ~f:(fun (z, s) (t, se) ->
      (T_array.mk_lambda (z, s) se t, T_array.SArray (s, se)))
  |> fst

(** The pinned negation of [piece] at the sequence lengths [lengths], with the
    pinned relations, or [None] when the closure gives up or a relation stays
    free. *)
let pinned_negation ~log rels seqs lengths piece =
  let defs =
    List.map2_exn seqs lengths ~f:(fun (s, se) k ->
        (s, se, SeqPin.literal_of se k))
  in
  let sub =
    Map.Poly.of_alist_exn @@ List.map defs ~f:(fun (s, _, t) -> (s, t))
  in
  let neg =
    Ast.Evaluator.simplify @@ Formula.nnf_of @@ Formula.mk_neg
    @@ Ast.Evaluator.rewrite_seq_read_over_concat (Formula.subst sub piece)
  in
  List.iter (Formula.conjuncts_list_of neg) ~f:(fun c ->
      log (lazy ("[relation pin] conjunct: " ^ Formula.str_of c)));
  let rules =
    List.concat_map (Formula.conjuncts_list_of neg) ~f:(rules_of rels)
  in
  match close rules with
  | None ->
      log (lazy "[relation pin] closure exceeds its bound: given up");
      None
  | Some (tuples, symbolic) ->
      let pinned = pin_in ~tuples ~symbolic rels neg in
      let still_free =
        List.exists rels ~f:(fun (r, _) -> Set.mem (Formula.tvs_of pinned) r)
      in
      if still_free then (
        log
          (lazy
            "[relation pin] a relation is used other than applied: left alone");
        None)
      else
        let eqs =
          List.map defs ~f:(fun (s, se, t) ->
              Formula.eq (Term.mk_var s (T_seq.SSeq se)) t)
        in
        log
        @@ lazy
             (sprintf "[relation pin] %s"
                (String.concat ~sep:"; "
                @@ List.map rels ~f:(fun (r, _) ->
                    sprintf "%s: %d tuples, %d symbolic patterns"
                      (Ast.Ident.name_of_tvar r)
                      (List.length (tuples r))
                      (List.count symbolic ~f:(fun (_, _, r', _) ->
                           Ast.Ident.tvar_equal r r')))));
        List.iter symbolic ~f:(fun (ys, cond, r, v) ->
            log
            @@ lazy
                 (sprintf "[relation pin] pattern %s over %s: %s => (%s)"
                    (Ast.Ident.name_of_tvar r)
                    (String.concat ~sep:" "
                       (List.map ys ~f:(fun (y, _) -> Ast.Ident.name_of_tvar y)))
                    (Formula.str_of cond)
                    (String.concat ~sep:", " (List.map v ~f:Term.str_of))));
        Some (Formula.and_of (pinned :: eqs), tuples, symbolic)

(** the most candidate vectors of one sum [shapes] confirms one at a time
    under [by_length_vectors]; a sum with more is left to the per-sum guesses *)
let max_vector_candidates = 2 * shapes_per_sum

(** the most length vectors (over all sums) [length_vectors] enumerates; with
    more sequences than that allows it declines *)
let max_vectors = 20000

(** the number of vectors of [k] naturals summing to [n] (each unbounded),
    saturated at [max_vectors + 1]: an upper bound on what [vectors k n]
    returns *)
let count_vectors k n =
  (* C(n + k - 1, k - 1), built as a product of exact binomials *)
  let rec go i acc =
    if i > k - 1 then acc
    else if acc > max_vectors then max_vectors + 1
    else go (i + 1) (acc * (n + i) / i)
  in
  if k <= 0 then if n = 0 then 1 else 0 else go 1 1

(** the vectors of [k] naturals, each at most [max_length], summing to [n],
    in lexicographic order *)
let rec vectors k n =
  if k = 0 then if n = 0 then [ [] ] else []
  else
    List.concat_map
      (List.init (Int.min n max_length + 1) ~f:Fn.id)
      ~f:(fun first ->
        List.map (vectors (k - 1) (n - first)) ~f:(List.cons first))

(** [relaxed] with every sequence of [seqs] replaced by a literal of its
    length in [v] over fresh element variables ([SeqPin.literal_of]):
    satisfiable exactly when [relaxed] has a model in which each sequence has
    that length, since a sequence of length [k] is the concatenation of its
    [k] elements.  The formula is handed to the solver as substituted: the
    evaluator's simplification with reads over concatenations rewritten,
    which this once applied, expands every read of a literal into the chain
    of its positions, and on a Rust-derived input with eight sequences six
    such calls took 77 s of the early relation pin while the solver decides
    the substituted formula at once; the formula is the same either way *)
let relaxed_at ~relaxed seqs v =
  let sub =
    Map.Poly.of_alist_exn
    @@ List.map2_exn seqs v ~f:(fun (s, se) k -> (s, SeqPin.literal_of se k))
  in
  Formula.subst sub relaxed

(** [None] when the vectors to enumerate for [seqs] are too many
    ([max_vectors]); otherwise [Some f] where [f sum] is [Some vs], the length
    vectors of [seqs] with that sum (entries at most [max_length]) that no
    length-only conjunct of [relaxed] excludes, in lexicographic order, when
    there are at most [max_vector_candidates] of them, and [None] when there
    are more.  A conjunct is length-only when it has a free variable and every
    free variable of it is a sequence of [seqs]; it excludes [v] when, with
    each [seq.len s] replaced by [s]'s entry of [v], it simplifies to [false].
    Every model of [relaxed] whose lengths are [v] satisfies each conjunct at
    those lengths, so an excluded vector has no model of [relaxed]: the vectors
    left are a superset of those the per-sum guesses can return at that sum. *)
let length_vectors ~relaxed seqs =
  let k = List.length seqs in
  let total =
    List.fold
      (List.init (max_length_sum + 1) ~f:Fn.id)
      ~init:0
      ~f:(fun acc n -> Int.min (max_vectors + 1) (acc + count_vectors k n))
  in
  if total > max_vectors then None
  else
    let is_seq x =
      List.exists seqs ~f:(fun (s, _) -> Ast.Ident.tvar_equal s x)
    in
    let length_only =
      List.filter (Formula.conjuncts_list_of relaxed) ~f:(fun c ->
          let tvs = Formula.tvs_of c in
          (not (Set.is_empty tvs)) && Set.for_all tvs ~f:is_seq)
    in
    (* Whether a conjunct simplifies to [false] at [v] depends on [v]'s
       entries for the sequences the conjunct mentions only, so each
       conjunct's answer is kept per projection of [v] onto those sequences:
       the same simplification as asking it at every vector, asked once per
       distinct projection.  Why: on a Rust-derived input with eight
       sequences, simplifying every length-only conjunct at each of the
       vectors took 62 s of the early relation pin's shape search, against a
       few hundred distinct projections per conjunct. *)
    let conj_tables =
      List.map length_only ~f:(fun c ->
          let tvs = Formula.tvs_of c in
          let idx =
            List.filter_mapi seqs ~f:(fun i (s, _) ->
                if Set.mem tvs s then Some i else None)
          in
          (c, idx, Hashtbl.Poly.create ()))
    in
    let excluded v =
      let va = Array.of_list v in
      List.exists conj_tables ~f:(fun (c, idx, tbl) ->
          let key = List.map idx ~f:(fun i -> va.(i)) in
          Hashtbl.find_or_add tbl key ~default:(fun () ->
              let at =
                List.map idx ~f:(fun i -> (fst (List.nth_exn seqs i), va.(i)))
              in
              let len_term = function
                | Term.FunApp (T_seq.SqLen _, [ Term.Var (s, _, _) ], _) as t
                  -> (
                    match List.Assoc.find at s ~equal:Ast.Ident.tvar_equal with
                    | Some n -> T_int.mk_int (Z.of_int n)
                    | None -> t)
                | t -> t
              in
              Formula.is_false
                (Ast.Evaluator.simplify (Formula.map_term c ~f:len_term))))
    in
    Some
      (fun sum ->
        let candidates =
          List.filter (vectors k sum) ~f:(fun v -> not (excluded v))
        in
        if List.length candidates <= max_vector_candidates then Some candidates
        else None)

(** the length vectors to try for [seqs], shortest sums first, each a model of
    [relaxed] with the lengths bounded, at most [shapes_per_sum] per sum and
    [max_attempts] in all.

    With [by_length_vectors], a sum whose length vectors the length-only
    conjuncts of [relaxed] narrow to at most [max_vector_candidates]
    ([length_vectors]) is searched by asking [guess], for each candidate in
    lexicographic order, whether [relaxed] has a model with exactly those
    lengths ([relaxed_at]); a sum left with no candidate asks nothing, and a
    sum left with more is asked as without it.  The shapes so found are
    models of [relaxed] with the lengths bounded, as the per-sum guesses'
    are; where a sum has at most [shapes_per_sum] such vectors both routes
    find all of them (in an order that may differ), and an undecided
    confirmation drops its vector only, where an undecided per-sum guess ends
    the sum's search.  The question asked of a candidate has no sequence
    length left to choose, which is what made a per-sum guess slow: on a
    Rust-derived input the guess at the refuting sum took 0.5-2.6 s of CPU
    near idle and overran a one-second cap under load, losing the shape. *)
let shapes ?infeasible ?(by_length_vectors = false) ~guess ~relaxed seqs =
  if List.is_empty seqs then [ [] ]
  else
    let ns = List.map seqs ~f:(fun _ -> Ast.Ident.mk_fresh_tvar ()) in
    let nvar n = Term.mk_var n T_int.SInt in
    let links =
      List.map2_exn seqs ns ~f:(fun (s, se) n ->
          Formula.and_of
            [
              Formula.eq (nvar n)
                (T_seq.mk_len se (Term.mk_var s (T_seq.SSeq se)));
              Formula.geq (nvar n) (T_int.zero ());
              Formula.leq (nvar n) (T_int.mk_int (Z.of_int max_length));
            ])
    in
    let value_of model n =
      List.find_map model ~f:(fun ((y, _), t) ->
          if Ast.Ident.tvar_equal n y then t else None)
      |> Option.bind ~f:(function
        (* the query bounds each length by [max_length]; a value outside a
           native int would break that bound and is declined *)
        | Term.FunApp (T_int.Int z, [], _) when Z.fits_int z -> Some (Z.to_int z)
        | _ -> None)
    in
    (* every per-sum question below is this one with conjuncts added, so
       when it is unsatisfiable none of them has a model and no shape is
       found; asked once, it replaces the nine to twenty-seven per-sum
       questions such a piece would otherwise cost.  Anything but a proof of
       unsatisfiability leaves the search as it was. *)
    let hopeless =
      match infeasible with
      | Some infeasible -> infeasible (Formula.and_of (relaxed :: links))
      | None -> false
    in
    let found = ref [] in
    let excluding v =
      Formula.mk_neg @@ Formula.and_of
      @@ List.map2_exn ns v ~f:(fun n k ->
          Formula.eq (nvar n) (T_int.mk_int (Z.of_int k)))
    in
    let by_vectors =
      if by_length_vectors then length_vectors ~relaxed seqs else None
    in
    if not hopeless then
    List.iter
      (List.init (max_length_sum + 1) ~f:Fn.id)
      ~f:(fun sum ->
        match
          Option.bind by_vectors ~f:(fun at_sum ->
              Common.PhaseTime.with_phase "vectors" @@ fun () -> at_sum sum)
        with
        | Some candidates ->
            let at_sum = ref 0 in
            List.iter candidates ~f:(fun v ->
                if
                  List.length !found < max_attempts
                  && !at_sum < shapes_per_sum
                  && Option.is_some
                       (guess
                          ( Common.PhaseTime.with_phase "relax-at" @@ fun () ->
                            relaxed_at ~relaxed seqs v ))
                then (
                  incr at_sum;
                  found := !found @ [ v ]))
        | None ->
        let rec per k =
          if k = 0 || List.length !found >= max_attempts then ()
          else
            let q =
              Formula.and_of
                ((relaxed :: links)
                @ [
                    Formula.eq
                      (T_int.mk_sum (T_int.zero ()) (List.map ns ~f:nvar))
                      (T_int.mk_int (Z.of_int sum));
                  ]
                @ List.map !found ~f:excluding)
            in
            match guess q with
            | None -> ()
            | Some model -> (
                match Option.all (List.map ns ~f:(value_of model)) with
                | None -> ()
                | Some v ->
                    found := !found @ [ v ];
                    per (k - 1))
        in
        per shapes_per_sum);
    !found

(** whether a Boolean-valued array is among [c]'s free variables, the shape
    every clause the relation pin can refute has; [false] when a name occurs
    at two sorts ([ScalarPin.free_vars]), where the pin leaves [c] alone *)
let mentions_relation c =
  match ScalarPin.free_vars c with
  | Some vars ->
      List.exists vars ~f:(fun (_, s) -> Option.is_some (relation_arity s))
  | None -> false

(** A countermodel of [and_of clauses]: a model of the negation of one of its
    clauses' pieces with the clause's relations pinned, or [None]. [guess] is
    asked for models of quantifier-free formulas only, and what it returns is
    never reported; [infeasible], when given, is asked once per piece before
    the per-sum guesses, a quantifier-free formula every guess of the piece
    strengthens, and must hold only when that formula is unsatisfiable (then
    the piece has no shape and its guesses are not asked, which is what they
    would all have answered); [ask] is a satisfiability question whose model, when there
    is one, is the countermodel. Clauses whose index [already_valid] holds are
    skipped, and nothing is asked when [enabled] is false.  With [expired],
    no further clause or piece is started once [expired ()] holds (a piece's
    relaxations, two sequence instantiations, are the costly part of it), and
    the relaxations are built as [ScalarPin.relaxations_until] builds them;
    this only stops the search earlier, so a countermodel it returns is one as
    without it.  Without [expired] the search is unchanged.  With
    [skip_relation_free_clauses], a clause with no Boolean-valued array among
    its free variables is skipped before its pieces are computed, and with
    [cheap_infeasible] (a satisfiability question that holds only on
    [unsat]) a piece whose [ScalarPin.cheapest_relaxation] has no model is
    skipped before its relaxations are built; neither skips a piece the pin
    could refute.  [by_length_vectors] is [shapes]'s. *)
let refute ?(log = fun (_ : string lazy_t) -> ()) ?expired ?infeasible
    ?by_length_vectors ?(skip_relation_free_clauses = false) ?cheap_infeasible
    ~enabled
    ~already_valid
    ~(guess : Formula.t -> model option) ~(ask : Formula.t -> model option)
    clauses =
  if not enabled then None
  else
    let attempts = ref 0 in
    let try_piece piece =
      Common.PhaseTime.event_here ~in_copy:false "piece";
      match ScalarPin.free_vars piece with
      | None -> None
      | Some vars ->
          let rels =
            List.filter_map vars ~f:(fun (x, s) ->
                Option.map (relation_arity s) ~f:(fun n -> (x, n)))
          in
          if List.is_empty rels then (
            Common.PhaseTime.event_here ~in_copy:false "skip-norel";
            None)
          else if
            (* [ScalarPin.cheapest_relaxation]: [not piece] has no model, and
               every pinned negation is a strengthening of it; asked before
               the instantiated relaxations, the costly part, are built *)
            match cheap_infeasible with
            | Some f -> f (ScalarPin.cheapest_relaxation piece)
            | None -> false
          then (
            log (lazy "[relation pin] piece skipped: its relaxation has no model");
            Common.PhaseTime.event_here ~in_copy:false "skip-infeasible";
            None)
          else
            let seqs =
              List.filter_map vars ~f:(function
                | x, T_seq.SSeq se -> Some (x, se)
                | _ -> None)
            in
            let relaxed =
              Common.PhaseTime.with_phase "relax" @@ fun () ->
              Formula.and_of @@ Sequence.to_list
              @@ ScalarPin.relaxations_until ?expired piece
            in
            log
            @@ lazy
                 (sprintf "[relation pin] piece with relations %s: %s"
                    (String.concat ~sep:", "
                    @@ List.map rels ~f:(fun (r, _) -> Ast.Ident.name_of_tvar r)
                    )
                    (Formula.str_of piece));
            List.find_map
              (Common.PhaseTime.with_phase "shapes" @@ fun () ->
               shapes ?infeasible ?by_length_vectors ~guess ~relaxed seqs)
              ~f:(fun lengths ->
                if !attempts >= max_attempts then None
                else
                  match
                    Common.PhaseTime.with_phase "pin-build" @@ fun () ->
                    pinned_negation ~log rels seqs lengths piece
                  with
                  | None -> None
                  | Some (q, tuples, symbolic) -> (
                      incr attempts;
                      log
                      @@ lazy
                           (sprintf "[relation pin] lengths %s"
                              (String.concat ~sep:", "
                              @@ List.map2_exn seqs lengths ~f:(fun (s, _) k ->
                                  sprintf "%s = %d" (Ast.Ident.name_of_tvar s) k)
                              ));
                      match ask q with
                      | None -> None
                      | Some model ->
                          Some
                            (model
                            @ List.map rels ~f:(fun (r, _) ->
                                let s =
                                  List.Assoc.find_exn vars r
                                    ~equal:Ast.Ident.tvar_equal
                                in
                                ((r, s), Some (lambda_of ~tuples ~symbolic r s)))
                            )))
    in
    let expired_now () = match expired with Some f -> f () | None -> false in
    (* a clause none of whose free variables is a Boolean-valued array has no
       piece with one (a piece's free variables are among its clause's), so
       with [skip_relation_free_clauses] its pieces are not computed; a clause
       with a name at two sorts is split as before *)
    let relation_free c =
      skip_relation_free_clauses
      &&
      match ScalarPin.free_vars c with
      | Some vars ->
          not
            (List.exists vars ~f:(fun (_, s) -> Option.is_some (relation_arity s)))
      | None -> false
    in
    List.find_mapi clauses ~f:(fun i c ->
        if already_valid i || expired_now () then None
        else if relation_free c then (
          Common.PhaseTime.event_here ~in_copy:false "skip-norel-clause";
          None)
        else
          (* per-clause span: which clauses a run reaches depends on which
             earlier stages proved valid *)
          Common.PhaseTime.with_phase (sprintf "clause%d" i) @@ fun () ->
          List.find_map
            (Common.PhaseTime.with_phase "pieces" @@ fun () ->
             SeqInstantiation.pieces
               (Ast.Evaluator.simplify (Formula.nnf_of c)))
            ~f:(fun piece -> if expired_now () then None else try_piece piece))
