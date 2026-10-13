open Core
open Common
open Common.Ext

(* Sequence binders instantiated where that only STRENGTHENS the validity
   question.

   When every predicate variable has been eliminated, the verdict is whether
   the remaining constraint [phi] is valid, and a query whose quantifier binds
   a sequence is not asked at all where the solver may not return on it.  In
   the constraints of Rust-derived problems such binders sit in a clause's
   premise: a hypothesis [forall s. psi(s)], which the clause's disjunctive
   form writes as a disjunct [exists s. not psi(s)].

   The rule, and why it is sound for VALIDITY only.  A subformula at positive
   polarity may be replaced by a stronger one, and at negative polarity by a
   weaker one, and either replacement gives a formula [phi'] with
   [phi' => phi] valid (monotonicity of the connectives, of both quantifiers,
   and of implication in its antitone argument).  So:
   - an existential over a sequence at POSITIVE polarity is replaced by the
     disjunction of its instances at chosen terms: each instance implies the
     existential;
   - a universal over a sequence at NEGATIVE polarity -- a premise's
     hypothesis -- is replaced by the conjunction of its instances: the
     universal implies each instance, so the premise only gets weaker.
   Hence a proof that [phi'] is valid is a proof that [phi] is valid.  Nothing
   else may be read from [phi']: a countermodel of [phi'] need not be one of
   [phi], and [phi'] being unknown says nothing.  A binder at the other
   polarity, or under an [iff]/[xor] (both polarities at once), or inside an
   embedded formula term, is left bound -- the query then still binds a
   sequence and is not asked.  This is the instantiation step of FreqHorn's
   quantified-invariant check (Fedyukovich, Prabhu, Madhukar and Gupta,
   "Quantified Invariants via Syntax-Guided Synthesis", CAV 2019), which
   instantiates a premise's universal at the conclusion's terms and likewise
   licenses only a valid answer.

   Which terms.  An instance term must be well sorted where it is placed, and
   any such term keeps the rule sound, so the choice only decides whether the
   instance is useful.  Candidates are the sequence terms of the clause that
   mention nothing bound, and the empty sequence, ranked like an e-matching
   trigger: first the terms got by matching a read whose index concatenates
   the bound variable with other operands against a read of the clause of the
   same array, modulo associativity of concatenation (such a match also binds
   the other variables of the quantifier its operands meet, and those are
   instantiated too, soundly for the same reason); then the indices of reads
   of that array; then the same two for arrays of the same sort; then the
   other sequence terms, smallest first; and last the empty sequence.  With
   [chain_concat_candidates] set, a positive existential is first offered the
   concatenations of two chained applications of the relation its body
   applies it to ([chain_concat_candidates_for]).  A
   second pass also draws on the terms the first pass's instances build.  At
   most [max_terms_per_binder] terms per binder and
   [max_instances_per_quantifier] instances per quantifier are taken; the
   bounds are a choice that keeps the query small, not a measurement. *)
open Ast.LogicOld

(* Tracing only: called with the seconds a form of [first_proved] took to
   build and the form built ([None]: nothing to ask), and with a note at each
   clause [prove_valid] starts, so that a trace says whether a silent stretch
   is a form being built or a question being asked.  Set by the coordinator
   to its debug printer; the default does nothing, and no answer reads it. *)
let form_built_trace : (float -> Formula.t option -> unit) ref =
  ref (fun _ _ -> ())

let clause_trace : (string Lazy.t -> unit) ref = ref (fun _ -> ())

(* Measurement only: with COAR_SEQINST_TIMING=<file> set, [instantiate] and
   [instantiate_deep_unsimplified] append one line each to <file> giving the
   seconds they took, split into the candidate-term computation and the rest,
   tagged with [instr_tag] (set by the caller to name the question) and the
   process id, so that a forked copy's work is recorded too.  Unset, nothing
   is timed and nothing is written; no answer reads any of it. *)
let instr_file =
  match Sys.getenv "COAR_SEQINST_TIMING" with
  | None | Some "" -> None
  | Some f -> Some f

let instr_tag = ref ""
let instr_candidates_s = ref 0.

let instr_line line =
  Option.iter instr_file ~f:(fun file ->
      Out_channel.with_file file ~append:true ~f:(fun oc ->
          Out_channel.output_string oc
            (sprintf "%s\tpid=%d\t%s\n" !instr_tag
               (Core_unix.getpid () |> Pid.to_int)
               line)))

let instr_time f =
  match instr_file with
  | None -> (f (), 0.)
  | Some _ ->
      let t0 = Core_unix.gettimeofday () in
      let r = f () in
      (r, Core_unix.gettimeofday () -. t0)

let max_terms_per_binder = 10
let max_extra_terms = 4
let max_instances_per_quantifier = 32

(* An observer of every quantifier this module instantiates, for census tools:
   called with the step ("seq" or "int"), each bound variable with the number
   of candidate terms it was offered, and the instances built.  [None], the
   default, costs nothing and changes nothing. *)
let census :
    (string -> (Ast.Ident.tvar * int) list -> Formula.t list -> unit) option ref
    =
  ref None

let observe step choices instances =
  match !census with
  | Some f -> f step choices instances
  | None -> ()

let elem_of_seq = function T_seq.SSeq se -> Some se | _ -> None

(** [ts] without repetitions, first occurrences kept in order *)
let dedup_terms ts =
  (* the first occurrence of each term, in order, as the quadratic
     [List.mem]-based fold this replaces kept them: membership is asked of a
     table hashed over the whole term (the default hash reads ten nodes, and
     these terms share long prefixes), so that a candidate list of thousands
     of terms costs one structural comparison per collision rather than one
     per earlier element *)
  let seen = Common.Ext.Hashtbl.PolyDeep.create () in
  List.filter ts ~f:(fun t ->
      if Hashtbl.mem seen t then false
      else (
        Hashtbl.set seen ~key:t ~data:();
        true))

(** the arrays [a] such that [select a x] occurs in [phi] *)
let arrays_indexed_by x phi =
  Set.to_list
  @@ Formula.filtered_terms_of phi ~f:(function
    | Term.FunApp (T_array.ASelect _, [ _; Term.Var (y, _, _) ], _) ->
        Ast.Ident.tvar_equal x y
    | _ -> false)
  |> List.filter_map ~f:(function
    | Term.FunApp (T_array.ASelect _, [ a; _ ], _) -> Some a
    | _ -> None)

(** the first elements of the cartesian product of [choices], in order *)
let product ~limit choices =
  List.fold_right choices ~init:[ [] ] ~f:(fun opts acc ->
      List.take
        (List.concat_map opts ~f:(fun o -> List.map acc ~f:(fun r -> o :: r)))
        limit)

(** [build] applied to the elements of [combos] in order.  With [budget =
    Some left], building stops before an element once [!left] is not
    positive, the first element always being built, and each built formula's
    [Formula.ast_size] is taken off [!left]; with [None], every element is
    built.  (The sequence pass does not call this once the budget is spent:
    it leaves the binder uninstantiated instead.)

    Contract: the result is a non-empty prefix of [List.map combos ~f:build]
    when [combos] is non-empty.  A caller uses it for the instances of one
    quantifier that may be instantiated soundly for validity, where any
    non-empty subset of the instances is a strengthening, so a prefix keeps
    soundness and only decides which instances are asked.

    Why a budget: the per-quantifier limit bounds the instances of one
    binder but not their size, and a binder's body already holds its inner
    binders' instances, so nested binders multiply.  On a Rust-derived map
    clause of about 2,900 nodes, positive sequence existentials nested four
    deep took 32 instances each and the bodies grew 31, 301, 9,742, 321,554
    nodes, the next level being about ten million; building it exhausted
    memory (above 11 GB) in a solution check that could only have left the
    constraint unchecked.  Counting the nodes built across one pass bounds
    that pass's output by the budget plus one instance per binder that
    reaches it. *)
let instances_within ?budget combos ~build =
  match budget with
  | None -> List.map combos ~f:build
  | Some left ->
      let rec go acc = function
        | [] -> List.rev acc
        | _ :: _ when (not (List.is_empty acc)) && !left <= 0 -> List.rev acc
        | c :: cs ->
            let f = build c in
            left := !left - Formula.ast_size f;
            go (f :: acc) cs
      in
      go [] combos

(** the sequence terms of [phi] that mention only variables in [free] *)
let ground_sequences ~free phi =
  Set.to_list
  @@ Formula.filtered_terms_of phi ~f:(fun t ->
      Option.is_some (elem_of_seq (Term.sort_of t))
      && Set.is_subset (Term.tvs_of t) ~of_:free)

(** the reads [select a i] of [phi] whose index [i] is one of [pool] *)
let reads_of ~pool phi =
  Set.to_list
  @@ Formula.filtered_terms_of phi ~f:(function
    | Term.FunApp (T_array.ASelect _, [ _; i ], _) ->
        List.mem pool i ~equal:Stdlib.( = )
    | _ -> false)
  |> List.filter_map ~f:(function
    | Term.FunApp (T_array.ASelect _, [ a; i ], _) -> Some (a, i)
    | _ -> None)

(** the operands of a chain of concatenations, empty sequences dropped, left
    to right.  Built onto an accumulator: appending the left operand's list at
    each node, as [flatten_concat_def] does, is quadratic on the left-nested
    chains [concat_of] builds, and the candidates of the zero-unknown check
    flatten such chains at every read. *)
let flatten_concat t =
  let rec go t acc =
    match t with
    | Term.FunApp (T_seq.SqConcat _, [ t1; t2 ], _) -> go t1 (go t2 acc)
    | Term.FunApp (T_seq.SqEmpty _, [], _) -> acc
    | _ -> t :: acc
  in
  go t []

(** the definition [flatten_concat] keeps *)
let rec flatten_concat_def t =
  match t with
  | Term.FunApp (T_seq.SqConcat _, [ t1; t2 ], _) ->
      flatten_concat_def t1 @ flatten_concat_def t2
  | Term.FunApp (T_seq.SqEmpty _, [], _) -> []
  | _ -> [ t ]

let concat_of se = function
  | [] -> T_seq.mk_empty se
  | t :: ts -> List.fold ts ~init:t ~f:(T_seq.mk_concat se)

(** Terms for [x] got by matching, modulo associativity, each read
    [select a (x ++ p1 ++ ... ++ pk)] of [body] (or [p1 ++ ... ++ pk ++ x])
    against each read [select a' u] of [reads] ([a'] the same array when
    [same_array], an array of the same sort otherwise): [x] is taken to be
    what is left of [u]'s operands once [k] are removed from the other end.
    Each term comes with the bindings the removed operands give to the
    variables of [others] -- a [p_i = unit v] against an operand [unit w]
    binds [v] to [w] -- so that the instance is the whole match and not only
    its sequence part.  Operands that fit no such shape are not compared:
    the match only proposes terms, and any term is a sound instance. *)
let concat_matches ~same_array ~others x se ~reads body =
  let is_var v = function
    | Term.Var (y, _, _) -> Ast.Ident.tvar_equal v y
    | _ -> false
  in
  let patterns =
    Set.to_list
    @@ Formula.filtered_terms_of body ~f:(function
      | Term.FunApp (T_array.ASelect _, [ _; i ], _) -> (
          match flatten_concat i with
          | _ :: _ :: _ as ops ->
              is_var x (List.hd_exn ops) || is_var x (List.last_exn ops)
          | _ -> false)
      | _ -> false)
    |> List.filter_map ~f:(function
      | Term.FunApp (T_array.ASelect _, [ a; i ], _) ->
          let ops = flatten_concat i in
          let at_head = is_var x (List.hd_exn ops) in
          let rest = if at_head then List.tl_exn ops else List.drop_last_exn ops in
          Some (a, at_head, rest)
      | _ -> None)
  in
  let bind_operand p u =
    match (p, u) with
    | ( Term.FunApp (T_seq.SqUnit _, [ Term.Var (v, _, _) ], _),
        Term.FunApp (T_seq.SqUnit _, [ w ], _) )
      when List.exists others ~f:(fun (y, _) -> Ast.Ident.tvar_equal v y) ->
        Some (v, w)
    | _ -> None
  in
  List.concat_map patterns ~f:(fun (a, at_head, rest) ->
      let k = List.length rest in
      List.filter_map reads ~f:(fun (a', u) ->
          if
            not
              (if same_array then Stdlib.( = ) a' a
               else Stdlib.( = ) (Term.sort_of a') (Term.sort_of a))
          then None
          else
            let us = flatten_concat u in
            let n = List.length us - k in
            if n < 0 then None
            else
              let t, matched =
                if at_head then (concat_of se (List.take us n), List.drop us n)
                else (concat_of se (List.drop us k), List.take us k)
              in
              let binds =
                List.filter_map (List.zip_exn rest matched) ~f:(fun (p, u) ->
                    bind_operand p u)
                |> List.dedup_and_sort ~compare:(fun (v1, _) (v2, _) ->
                    Ast.Ident.tvar_compare v1 v2)
              in
              (* one variable matched twice with different operands: keep
                 neither binding rather than choose *)
              let binds =
                List.filter binds ~f:(fun (v, w) ->
                    List.for_all (List.zip_exn rest matched) ~f:(fun (p, u) ->
                        match bind_operand p u with
                        | Some (v', w') when Ast.Ident.tvar_equal v v' ->
                            Stdlib.( = ) w w'
                        | _ -> true))
              in
              Some (t, binds)))

(* Whether a positive sequence existential is also offered the concatenation
   of two sequences the clause relates by two chained applications of the
   relation its body applies it to ([chain_concat_candidates]).  Set by the
   coordinator from its configuration; process-wide, as the other switches of
   this module are. *)
let chain_concat_candidates = ref false

(* Whether a caller outside the zero-unknown verdict that asks [prove_valid]
   (the validator's Houdini pre-pass) first passes the clause and each form
   through [Ast.Evaluator.elim_onepoint_and_split_binders], as the verdict
   does when its configuration says so.  The rewrite is an equivalence in
   every model, so it changes which forms are proved, never what a proof
   means.  Set by the coordinator from the same configuration field;
   read by nothing in this module. *)
let onepoint_split_forms = ref false

let max_chain_concat_candidates = 4

(** the applications [select (... (select h i1) ...) in] of [phi], each as
    its head [h] (not itself a read) and its arguments [[i1; ...; in]],
    every read chain taken whole (a chain's inner reads are not listed
    again) *)
let select_chains phi =
  let rec chain acc = function
    | Term.FunApp (T_array.ASelect _, [ a; i ], _) -> chain (i :: acc) a
    | h -> (h, acc)
  in
  let all =
    Set.to_list
    @@ Formula.filtered_terms_of phi ~f:(function
      | Term.FunApp (T_array.ASelect _, _, _) -> true
      | _ -> false)
  in
  (* the arrays read, held in a table: a list searched once per read made
     this quadratic in the number of reads, which reached thousands in an
     instantiated clause *)
  let inner = Hashtbl.PolyDeep.create () in
  List.iter all ~f:(function
    | Term.FunApp (T_array.ASelect _, [ a; _ ], _) ->
        Hashtbl.set inner ~key:a ~data:()
    | _ -> ());
  List.filter_map all ~f:(fun t ->
      if Hashtbl.mem inner t then None else Some (chain [] t))

(* the atoms of [phi], under any binder and any connective *)
let rec atoms_anywhere_for_chains = function
  | Formula.Atom (a, _) -> [ a ]
  | Formula.UnaryOp (_, p, _) | Formula.Bind (_, _, p, _) ->
      atoms_anywhere_for_chains p
  | Formula.BinaryOp (_, p, q, _) ->
      atoms_anywhere_for_chains p @ atoms_anywhere_for_chains q
  | Formula.LetRec _ | Formula.LetFormula _ -> []

(* Whether [chain_concat_candidates_for] reads only the applications of the
   piece whose arguments mention no variable the piece binds, after rebinding
   such variables by constructor injectivity where it can
   ([chain_apps_free_only]).  Off: every application [select_chains] lists,
   under binders or not, as before.  Set by the coordinator from its
   configuration; process-wide, as [chain_concat_candidates] is. *)
let chain_candidates_free_only = ref false

(* the variables bound anywhere in [phi] (by a quantifier) *)
let bound_vars_of phi =
  let acc = ref Set.Poly.empty in
  let rec go = function
    | Formula.Bind (_, senv, body, _) ->
        acc := Set.union !acc (Set.Poly.of_list (List.map senv ~f:fst));
        go body
    | Formula.UnaryOp (_, p, _) -> go p
    | Formula.BinaryOp (_, p, q, _) -> go p; go q
    | Formula.LetFormula (_, _, _, body, _) -> go body
    | Formula.Atom _ | Formula.LetRec _ -> ()
  in
  go phi;
  !acc

(** The applications [select_chains whole] lists, keeping only those whose
    arguments mention no variable bound in [whole], after a substitution of
    bound variables by free terms read off constructor equations: an
    equation [v = C(a1, ..., an)] (either way round, anywhere in [whole])
    beside an equation or disequation [v = C(t1, ..., tn)] / [v != C(t1,
    ..., tn)] whose sides mention no bound variable maps each bound [ai]
    that is a variable to [ti].  Why: a premise [forall i. r = Some i =>
    h(b, [i], c)] -- an iterator's [next] ensures -- reaches a validity
    question as an existential over [i] next to the disjunct
    [r != Some x] that says what [r] is, and the chained pair it should give
    is [h(b, [x], c)]; read under its binder it gives [t ++ [i]] with [i]
    free, which proves nothing.  Contract: the result is a sublist of
    [select_chains whole] with a substitution applied to some entries;
    every term in it mentions only variables free in [whole]. Any term is a
    sound instance of a positive existential, so this only decides which
    instances are tried. *)
let chain_apps_free_only whole =
  let bound = bound_vars_of whole in
  let mentions_bound t = not (Set.is_empty (Set.inter (Term.tvs_of t) bound)) in
  let cons_of = function
    | Term.FunApp (T_dt.DTCons (c, _, _), args, _) -> Some (c, args)
    | _ -> None
  in
  let eqs =
    List.filter_map (atoms_anywhere_for_chains whole) ~f:(function
      | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ a; b ], _) -> (
          match (a, cons_of b, b, cons_of a) with
          | Term.Var (v, _, _), Some ca, _, _ -> Some (v, ca)
          | _, _, Term.Var (v, _, _), Some cb -> Some (v, cb)
          | _ -> None)
      | _ -> None)
  in
  let sub =
    List.fold eqs ~init:Map.Poly.empty ~f:(fun sub (v, (c, args)) ->
        if not (List.exists args ~f:mentions_bound) then sub
        else
          List.fold eqs ~init:sub ~f:(fun sub (v', (c', args')) ->
              if
                Ast.Ident.tvar_equal v v' && String.equal c c'
                && List.length args = List.length args'
                && not (List.exists args' ~f:mentions_bound)
              then
                List.fold2_exn args args' ~init:sub ~f:(fun sub a t ->
                    match a with
                    | Term.Var (i, _, _) when Set.mem bound i ->
                        Map.Poly.set sub ~key:i ~data:t
                    | _ -> sub)
              else sub))
  in
  List.filter_map (select_chains whole) ~f:(fun (h, args) ->
      let args =
        if Map.Poly.is_empty sub then args
        else List.map args ~f:(Term.subst sub)
      in
      if mentions_bound h || List.exists args ~f:mentions_bound then None
      else Some (h, args))

(** Candidate witnesses [x0 ++ x1] for the sequence binder [x] of a positive
    existential whose [body] applies a relation [h] (an array read as a
    chain of [select]s) with [x] at argument position [j]:
    [h(s1, x, e1)] in [body], [s1] the arguments before [j] and [e1] those
    after, none of them mentioning a variable in [bound] (so the
    application is the goal's and not, say, a premise of a law whose own
    binders [x] is one of).  Every pair of applications [h(s, x0, m)] and [h(m', x1, e)] of
    [whole] -- the piece, so a premise stated as another disjunct counts,
    and so does any conjunct -- with [x0] and [x1] at position [j], as many
    arguments before [j] as after, and the arguments after [j] of the first
    equal to those before [j] of the second ([m = m'], compared
    syntactically) gives [x0 ++ x1], nested to the right.  A pair whose
    endpoints are the goal's own ([s = s1] and [e = e1]) is ranked first.
    Why: a transitivity law [h(a, u, b) /\ h(b, v, c) => h(a, u ++ v, c)] --
    the one an iterator's [produces] states -- proves the goal at exactly
    that witness, which the clause itself never writes.  Only syntactic
    premises are read: a pair that holds only as an instance of such a law
    (both premises under the law's own binders) is not looked for.  Any term
    is a sound instance, so this only decides which instances are tried; at
    most [max_chain_concat_candidates] terms.  [whole_chains], when given,
    must be [select_chains whole]; a caller asking about many binders of one
    [whole] passes it so that the chains are listed once. *)
let chain_concat_candidates_for ?whole_chains ~whole ~bound x se body =
  let is_x = function
    | Term.Var (y, _, _) -> Ast.Ident.tvar_equal x y
    | _ -> false
  in
  let goals =
    List.concat_map (select_chains body) ~f:(fun (h, args) ->
        List.filter_mapi args ~f:(fun j a ->
            if is_x a then Some (h, j, args) else None))
  in
  let apps =
    if !chain_candidates_free_only then chain_apps_free_only whole
    else
      match whole_chains with
      | Some chains -> Lazy.force chains
      | None -> select_chains whole
  in
  let split j args = (List.take args j, List.drop args (j + 1)) in
  let ranked =
    List.concat_map goals ~f:(fun (h, j, gargs) ->
        let n = List.length gargs in
        let before = j and after = n - j - 1 in
        let gs, ge = split j gargs in
        if
          before <> after || before = 0
          || List.exists (gs @ ge) ~f:(fun t ->
              not (Set.is_empty (Set.inter (Term.tvs_of t) bound)))
        then []
        else
          let same =
            List.filter apps ~f:(fun (h', args) ->
                Stdlib.( = ) h h'
                && List.length args = n
                && not (is_x (List.nth_exn args j)))
          in
          List.concat_map same ~f:(fun (_, a1) ->
              List.filter_map same ~f:(fun (_, a2) ->
                  let s, m = split j a1 and m', e = split j a2 in
                  if not (List.equal Stdlib.( = ) m m') then None
                  else
                    let t =
                      match
                        List.rev
                          (flatten_concat (List.nth_exn a1 j)
                          @ flatten_concat (List.nth_exn a2 j))
                      with
                      | [] -> T_seq.mk_empty se
                      | last :: ops ->
                          List.fold ops ~init:last ~f:(fun acc op ->
                              T_seq.mk_concat se op acc)
                    in
                    let first =
                      List.equal Stdlib.( = ) s gs && List.equal Stdlib.( = ) e ge
                    in
                    Some (first, t))))
  in
  let firsts, rest = List.partition_tf ranked ~f:fst in
  List.take (dedup_terms (List.map (firsts @ rest) ~f:snd))
    max_chain_concat_candidates

(* ---- Prepend and pointwise-concatenation candidates (two switchable rules) ----

   Both rules only propose instance terms for a positive sequence existential,
   and any well-sorted term is a sound instance of one (the instance implies
   the existential), so neither can make a form prove anything the piece does
   not entail: they only decide which instances are tried.  Both are off by
   default and set by the coordinator from its configuration; process-wide, as
   the other switches of this module are. *)

(* Whether a positive sequence existential is also offered [unit e ++ u]
   ([prepend_unit_candidates_for]). *)
let prepend_unit_candidates = ref false

let max_prepend_unit_candidates = 4

(* Whether a positive sequence existential is also offered pointwise
   concatenations ([pointwise_concat_candidates_for]), and a piece whose
   distribution over its disjunctions would exceed [max_pieces] is still split
   along one side ([pieces]). *)
let pointwise_concat_candidates = ref false

let max_pointwise_concat_candidates = 8

(** [t] as a sequence built from [ops] by concatenation, nested to the right *)
let concat_right se ops =
  match List.rev ops with
  | [] -> T_seq.mk_empty se
  | last :: rest ->
      List.fold rest ~init:last ~f:(fun acc op -> T_seq.mk_concat se op acc)

(** the atoms of [phi], under any binder and any connective (an embedded
    formula term stays inside its atom) *)
let rec atoms_anywhere = function
  | Formula.Atom (a, _) -> [ a ]
  | Formula.UnaryOp (_, p, _) | Formula.Bind (_, _, p, _) -> atoms_anywhere p
  | Formula.BinaryOp (_, p, q, _) -> atoms_anywhere p @ atoms_anywhere q
  | Formula.LetRec _ | Formula.LetFormula _ -> []

let is_unit = function
  | Term.FunApp (T_seq.SqUnit _, [ _ ], _) -> true
  | _ -> false

(** Candidate witnesses [unit e ++ u] for the sequence binder [x] of a
    positive existential whose [body] builds [x ++ p1 ++ ... ++ pk] (anywhere,
    not only as a read index).  Each sequence term [u ++ q1 ++ ... ++ qk] of
    [whole] (the piece) mentioning only free variables of [whole], with each
    [q_i] a singleton where [p_i] is one, gives [u] as the match of [x] -- the
    term [concat_matches] gives for a read -- and then every singleton
    [unit e] of [whole] over free variables is prepended to it, the
    singletons not among the matched operands [q_i] first.  Why: a
    preservation law stated at a state [(s ++ [e1]) ++ [e2]] and needed one
    step later, after the step produced an item [e], holds at the sequence
    [[e] ++ u] the step prepends, which the clause itself never writes (for an
    iterator, the item [next] returned before the items the law ranges over).
    At most [max_prepend_unit_candidates] terms. *)
let prepend_unit_candidates_for ~whole x se body =
  let free = Formula.tvs_of whole in
  let is_x = function
    | Term.Var (y, _, _) -> Ast.Ident.tvar_equal x y
    | _ -> false
  in
  let is_seq t = Stdlib.( = ) (Term.sort_of t) (T_seq.SSeq se) in
  let ground t = Set.is_subset (Term.tvs_of t) ~of_:free in
  let patterns =
    Set.to_list
    @@ Formula.filtered_terms_of body ~f:(function
      | Term.FunApp (T_seq.SqConcat _, _, _) as t -> (
          is_seq t
          && match flatten_concat t with
             | h :: _ :: _ -> is_x h
             | _ -> false)
      | _ -> false)
    |> List.map ~f:(fun t -> List.tl_exn (flatten_concat t))
  in
  let targets =
    Set.to_list
    @@ Formula.filtered_terms_of whole ~f:(fun t ->
        is_seq t && ground t
        && match t with Term.FunApp (T_seq.SqConcat _, _, _) -> true | _ -> false)
  in
  let units =
    Set.to_list
    @@ Formula.filtered_terms_of whole ~f:(fun t ->
        is_seq t && is_unit t && ground t)
  in
  let matches =
    List.concat_map patterns ~f:(fun rest ->
        let k = List.length rest in
        List.filter_map targets ~f:(fun t ->
            let us = flatten_concat t in
            let n = List.length us - k in
            if n < 1 then None
            else
              let tail = List.drop us n in
              if
                List.for_all2_exn rest tail ~f:(fun p q ->
                    (not (is_unit p)) || is_unit q)
              then Some (List.take us n, tail)
              else None))
  in
  List.take
    (dedup_terms
    @@ List.concat_map matches ~f:(fun (u, tail) ->
        let inside, outside =
          List.partition_tf units ~f:(List.mem tail ~equal:Stdlib.( = ))
        in
        List.map (outside @ inside) ~f:(fun e -> concat_right se (e :: u))))
    max_prepend_unit_candidates

(** Candidate witnesses [u1 ++ ... ++ um] for the sequence binder [x] of a
    positive existential whose [body] reads [x] pointwise ([seq.nth x k])
    and mentions a sequence [w1 ++ ... ++ wm] over free variables of [whole]
    (the piece): each [u_i] is a sequence of [whole] over free variables that
    some atom of [whole] not mentioning [x] reads at the same index as [w_i]
    ([seq.nth u_i k] beside [seq.nth w_i k]) -- the premise
    [forall k. R(u_i[k], w_i[k])], which a clause's disjunctive form writes as
    [exists k. not R(u_i[k], w_i[k])].  A singleton [w_i = unit e] is read the
    same way, so an element [t] with [R(t, e)] is found where the clause reads
    it as [seq.nth (unit t) k] beside [seq.nth (unit e) k].  Why: a goal
    [exists s. forall k. R(s[k], (w1 ++ w2)[k])] -- the inner witness of a
    [Map]'s [produces] after one more item -- holds at [u1 ++ u2], which the
    clause never writes.  The relation of the premise is not compared with the
    goal's: any term is a sound instance, so co-occurrence only ranks.  Where
    [t] is bound by a universal of the piece (an item a premise quantifies
    over), it is a candidate only once that universal is skolemized
    ([skolemize_positive_universals]).  At most
    [max_pointwise_concat_candidates] terms, products taken in order. *)
let pointwise_concat_candidates_for ~whole x se body =
  let free = Formula.tvs_of whole in
  let is_seq t = Stdlib.( = ) (Term.sort_of t) (T_seq.SSeq se) in
  let ground t = Set.is_subset (Term.tvs_of t) ~of_:free in
  let mentions_x t = Set.mem (Term.tvs_of t) x in
  let reads_x_pointwise =
    not
      (Set.is_empty
         (Formula.filtered_terms_of body ~f:(function
           | Term.FunApp (T_seq.SqNth _, [ Term.Var (y, _, _); _ ], _) ->
               Ast.Ident.tvar_equal x y
           | _ -> false)))
  in
  if not reads_x_pointwise then []
  else
    let wholes =
      Set.to_list
      @@ Formula.filtered_terms_of body ~f:(fun t ->
          is_seq t && ground t
          && match t with
             | Term.FunApp (T_seq.SqConcat _, _, _) -> true
             | _ -> false)
    in
    (* for each atom of [whole] not mentioning [x], its reads grouped by index *)
    let groups =
      List.concat_map (atoms_anywhere whole) ~f:(fun a ->
          if Set.mem (Atom.tvs_of a) x then []
          else
            let reads =
              Set.to_list
              @@ Atom.filtered_terms_of a ~f:(function
                | Term.FunApp (T_seq.SqNth _, [ s; _ ], _) -> is_seq s
                | _ -> false)
              |> List.filter_map ~f:(function
                | Term.FunApp (T_seq.SqNth _, [ s; k ], _) -> Some (s, k)
                | _ -> None)
            in
            List.map reads ~f:(fun (_, k) ->
                List.filter_map reads ~f:(fun (s, k') ->
                    if Stdlib.( = ) k k' then Some s else None)))
    in
    let related w =
      dedup_terms
      @@ List.concat_map groups ~f:(fun g ->
          if List.mem g w ~equal:Stdlib.( = ) then
            List.filter g ~f:(fun u ->
                (not (Stdlib.( = ) u w)) && ground u && not (mentions_x u))
          else [])
    in
    List.take
      (dedup_terms
      @@ List.concat_map wholes ~f:(fun wt ->
          let ws = flatten_concat wt in
          let choices = List.map ws ~f:related in
          if List.length ws < 2 || List.exists choices ~f:List.is_empty then []
          else
            List.map
              (product ~limit:max_pointwise_concat_candidates choices)
              ~f:(concat_right se)))
      max_pointwise_concat_candidates

(* ---- end of the prepend and pointwise-concatenation candidates ---- *)

(** Every chain of concatenations of [phi] rebuilt nested to the right,
    with empty operands dropped: [(a ++ b) ++ c] becomes [a ++ (b ++ c)].
    Exact, by associativity and the unit laws.  Why it is applied: an
    instance can build an index such as [(unit y ++ w) ++ unit a ++ unit b]
    where the clause holds [unit y ++ ((w ++ unit a) ++ unit b)], and a
    solver matching a quantifier's pattern syntactically against the ground
    terms it holds would see two unrelated terms.  It has not been shown to
    decide anything on its own: the inputs it was written for were decided
    only once the matching also bound the other binders. *)
let right_nest_concats phi =
  Formula.map_term phi ~f:(function
    | Term.FunApp (T_seq.SqConcat se, _, _) as t -> (
        match List.rev (flatten_concat t) with
        | [] -> T_seq.mk_empty se
        | last :: rest ->
            List.fold rest ~init:last ~f:(fun acc op ->
                T_seq.mk_concat se op acc))
    | t -> t)

let by_size =
  List.stable_sort ~compare:(fun t1 t2 ->
      Int.compare (Term.ast_size t1) (Term.ast_size t2))

(** the candidates of the two switchable rules above, for a positive
    existential ([with_extra]) only: the prepend terms, then the pointwise
    concatenations *)
let extra_rule_candidates ~with_extra ~whole x se body =
  if not with_extra then []
  else
    (if !prepend_unit_candidates then prepend_unit_candidates_for ~whole x se body
     else [])
    @
    if !pointwise_concat_candidates then
      pointwise_concat_candidates_for ~whole x se body
    else []

(* Array witnesses for a PROOF, built so that they exist in every model of
   the array theory.

   An instance [phi[t/x]] implies [exists x. phi] in a model only when [t]
   denotes an element of that model's array carrier.  The axioms of the
   array theory (read over write, extensionality) do not make every function
   an array: the functions differing from a constant function at finitely
   many indices are a model too, closed under [store], in which no array
   reads [i] at every [i].  There [exists a. forall i. a[i] = i] is false,
   while its instance at [lambda k. k] is true, so a proof through a total
   lambda (or through a constant array, which a carrier need not hold
   either) proves a sentence that is not valid.

   What every carrier does hold: any array [d] under finitely many [store]s.
   So a total witness [lambda k. u] is replaced by
     [lambda k. ite (R(k)) u (select d k)]
   with [R] confining [k] to finitely many integers for every value of its
   free variables and [d] a fresh array variable, free in the instance.  A
   validity question reads its free variables universally, so a proof of
   the instance proves it for every [d]; in any model take any array for
   [d], and the lambda is [d] under finitely many stores, an element of the
   carrier, which witnesses the existential.  [R] is read off [body], the
   existential's scope: for each universal [forall i. P(i) \/ ... x[i + c]
   ...] whose premises [P] (the disjuncts mentioning neither [x] nor a
   variable bound inside [body] other than [i]) confine [i] to an interval
   bounded on both sides, the range [not P(k - c)] (dually, for an
   existential [exists i. P'(i) /\ ... x[i + c] ...], the range [P'(k - c)]);
   and each read [x[t]]
   whose index mentions nothing bound inside [body], the point [k = t].
   Where nothing bounded can be read, no witness is offered.  Which [R] is
   chosen decides only whether the proof goes through, never soundness. *)
let witness_read_ranges ~body x =
  let inner_bound =
    Set.Poly.map (Formula.quantified_sort_env_of body) ~f:fst
  in
  let free_of_inner t =
    Set.is_empty (Set.inter (Term.tvs_of t) inner_bound)
    && not (Set.mem (Term.tvs_of t) x)
  in
  let reads_of phi =
    Set.to_list
      (Formula.filtered_terms_of phi ~f:(function
        | Term.FunApp (T_array.ASelect _, [ Term.Var (y, _, _); _ ], _) ->
            Ast.Ident.tvar_equal x y
        | _ -> false))
    |> List.filter_map ~f:(function
      | Term.FunApp (_, [ _; idx ], _) -> Some idx
      | _ -> None)
  in
  let points =
    reads_of body
    |> List.filter ~f:free_of_inner
    |> List.dedup_and_sort ~compare:Stdlib.compare
    |> List.map ~f:(fun t kv -> Formula.eq kv t)
  in
  let rec disj = function
    | Formula.BinaryOp (Formula.Or, p, q, _) -> disj p @ disj q
    | Formula.BinaryOp (Formula.Imply, p, q, _) ->
        List.map (Formula.conjuncts_list_of p) ~f:Formula.mk_neg @ disj q
    | p -> [ p ]
  in
  let ranges = ref [] in
  (* [i] bound by a universal whose matrix is the disjunction of premises
     and reads, or (the same binder in the negated form a refutation route
     works on) by an existential whose matrix is their conjunction *)
  let range_of binder i m =
    let ds =
      match binder with
      | Formula.Forall -> disj m
      | _ -> Formula.conjuncts_list_of m
    in
    let xs, ps =
      List.partition_tf ds ~f:(fun d -> Set.mem (Formula.tvs_of d) x)
    in
    let ps =
      List.filter ps ~f:(fun d ->
          Set.for_all (Formula.tvs_of d) ~f:(fun v ->
              Ast.Ident.tvar_equal v i || not (Set.mem inner_bound v)))
    in
    let neg =
      match binder with
      | Formula.Forall -> Formula.mk_neg (Formula.or_of ps)
      | _ -> Formula.and_of ps
    in
    if (not (List.is_empty ps)) && Ast.Evaluator.int_interval_bounded i neg
    then
      List.concat_map xs ~f:reads_of
      |> List.iter ~f:(fun idx ->
          match Ast.Evaluator.affine_part_in i idx with
          | Some (a, r)
            when Z.equal a Z.one
                 && Set.is_empty (Set.inter (Term.tvs_of r) inner_bound)
                 && not (Set.mem (Term.tvs_of r) x) ->
              ranges :=
                (fun kv ->
                  Formula.subst
                    (Map.Poly.singleton i (T_int.mk_sub kv r))
                    neg)
                :: !ranges
          | _ -> ())
  in
  let rec go = function
    | Formula.Bind (((Formula.Forall | Formula.Exists) as binder), senv, m, _)
      ->
        List.iter senv ~f:(fun (i, s) ->
            if Stdlib.( = ) s T_int.SInt then range_of binder i m);
        go m
    | Formula.Bind (_, _, m, _) | Formula.UnaryOp (_, m, _) -> go m
    | Formula.BinaryOp (_, p, q, _) ->
        go p;
        go q
    | _ -> ()
  in
  go body;
  List.rev !ranges @ points

(** does [t] build an array by comprehension, a lambda or a constant array,
    anywhere inside it *)
let rec mentions_comprehension = function
  | Term.FunApp ((T_array.ALambda _ | T_array.AConst _), _, _) -> true
  | Term.FunApp (_, args, _) -> List.exists args ~f:mentions_comprehension
  | Term.LetTerm (_, _, d, b, _) ->
      mentions_comprehension d || mentions_comprehension b
  | Term.Var _ -> false

(** the witness [t] for the array binder [x] of [body], made one every model
    of the array theory holds (see [witness_read_ranges]): a lambda
    [lambda k. u] over [Int] guarded by the ranges [body] reads [x] in, with
    a fresh array outside them; [None] when no bounded range is read, or
    when [t] builds an array by comprehension any other way.  A term without
    a lambda or a constant array is returned as it is. *)
let guard_array_witness ~body x t =
  match t with
  | Term.FunApp (T_array.ALambda ((k, (T_int.SInt as si)), se), [ u ], _)
    when not (mentions_comprehension u) -> (
      match witness_read_ranges ~body x with
      | [] -> None
      | ranges ->
          let k' = Ast.Ident.mk_fresh_tvar () in
          let d = Ast.Ident.mk_fresh_tvar () in
          let kv = Term.mk_var k' si in
          Some
            (T_array.mk_lambda (k', si) se
               (T_bool.ifte
                  (Formula.or_of (List.map ranges ~f:(fun r -> r kv)))
                  (Term.subst (Map.Poly.singleton k kv) u)
                  (T_array.mk_select si se
                     (Term.mk_var d (T_array.SArray (si, se)))
                     kv))))
  | t when mentions_comprehension t -> None
  | t -> Some t

(** a fresh array variable of [sort], read universally where it is put in a
    validity question: the sound replacement of a constant-array witness *)
let fresh_array_witness sort = Term.mk_var (Ast.Ident.mk_fresh_tvar ()) sort

(* Whether a positive existential over an array of sort [Int -> E] is also
   instantiated, at the ARRAY VIEWS [lambda k. seq.nth s k] of the sequences
   [s] of sort [Seq E] in the pool ([array_view_candidates]).  Why: a
   Rust-derived clause can state a loop's history twice, once as a premise
   sequence [x0] (its length, its first element, consecutive steps) and once
   as a goal [exists iters : Int -> E. ...] over an array of the same states;
   the witness is the sequence read as an array, a term the clause never
   writes, and without it the existential stays bound and the solver answers
   "incomplete quantifiers".  Sound as every instance here is: an instance of
   a positive existential implies it, so only a proof of validity is read.
   Set by the coordinator from its configuration; process-wide, as
   [chain_concat_candidates] is. *)
let seq_array_view_candidates = ref false

let max_array_view_candidates = 4

(** the array views [lambda k. seq.nth s k] of the sequences [s] of [pool]
    whose element sort is [se], smallest first, at most
    [max_array_view_candidates], each with a binder [k] drawn fresh here, so
    that no substitution into a body containing it can capture it.  The view
    reads [s] at every index, including those outside [0, len s), where
    [seq.nth] is the theory's unspecified value, which is a value all the
    same: the view is a term of sort [Int -> se] and any such term is a
    sound instance. *)
let array_view_candidates ~pool se =
  List.filter pool ~f:(fun s -> Stdlib.( = ) (Term.sort_of s) (T_seq.SSeq se))
  |> by_size
  |> (fun ss -> List.take ss max_array_view_candidates)
  |> List.map ~f:(fun s ->
      let k = Ast.Ident.mk_fresh_tvar () in
      T_array.mk_lambda (k, T_int.SInt) se
        (T_seq.mk_nth se s (Term.mk_var k T_int.SInt)))

(** whether [a] is an array view, possibly under [store]s *)
let rec view_rooted = function
  | Term.FunApp (T_array.ALambda _, [ _ ], _) -> true
  | Term.FunApp (T_array.AStore _, [ a; _; _ ], _) -> view_rooted a
  | _ -> false

(** the read [select a i] of a view [a] under [store]s, written without
    the array: [select (store a k v) i] is [ite (i = k) v (select a i)]
    (read over write, valid in ArraysEx) and [select (lambda k. b) i] is
    [b[i/k]] (beta reduction) *)
let rec read_view a i =
  match a with
  | Term.FunApp (T_array.ALambda ((k, _), _), [ body ], _) ->
      Term.subst (Map.Poly.singleton k i) body
  | Term.FunApp (T_array.AStore _, [ a'; k; v ], _) ->
      T_bool.mk_if_then_else
        (T_bool.of_formula (Formula.eq i k))
        v (read_view a' i)
  | _ ->
      (* not reached: [reduce_view_reads] calls this on [view_rooted] terms *)
      T_array.mk_select_app a [ i ]

(** [phi] with every read of a view under [store]s written without the
    array ([read_view]).  An equivalence in every model, so a form rewritten
    by it asks the same question.  Why: a clause whose goal array was fixed
    at one index by the one-point rule reads it as [store it 0 c]; with the
    view substituted, the question reads [store (lambda k. nth x0 k) 0 c] at a
    bound index under a quantifier, which the solver was measured to leave
    undecided at its 10 s budget, while the premise it must match is stated
    over [nth x0 j] directly. *)
let reduce_view_reads phi =
  Formula.map_term phi ~f:(function
    | Term.FunApp (T_array.ASelect _, [ a; i ], _) when view_rooted a ->
        read_view a i
    | t -> t)

(** whether [s] is the sort of an array binder [array_view_candidates] may
    instantiate: [Int -> E] with some sequence of sort [Seq E] in [pool] *)
let array_view_sort ~pool = function
  | T_array.SArray (T_int.SInt, se) ->
      List.exists pool ~f:(fun s ->
          Stdlib.( = ) (Term.sort_of s) (T_seq.SSeq se))
  | _ -> false

(* Whether a positive existential over an array of sort [Int -> E] is also
   instantiated at its POINTWISE DEFINITIONS ([pointwise_witness_candidates]):
   for an equation [select x j = u] anywhere in the binder's body (under a
   further binder, inside a conditional term, at either polarity), [j] an
   integer variable and [u] mentioning neither [x] nor any variable other
   than [j] that is not free in the whole formula, the array
   [lambda j'. u[j'/j]].  Why: a Rust-derived clause states a history in
   the array-and-length encoding of sequences as
   [exists ta. ... /\ forall k. 0 <= k < n => ta[k] = k + c], whose witness
   is that very function of [k], a term the clause never writes, and no
   sequence of sort [Seq E] is there for an array view.  Sound as every
   instance is: an instance of a positive existential implies it, so only a
   proof of validity is read.  Set by the coordinator from its
   configuration; process-wide, as [seq_array_view_candidates] is. *)
let pointwise_array_witnesses = ref false

let max_pointwise_witnesses = 4

(** the pointwise definitions of the array binder [x] of sort [sort] read
    off [body] (see [pointwise_array_witnesses]), distinct, smallest first,
    at most [max_pointwise_witnesses], each a lambda with a binder drawn
    fresh here, so that no substitution into a body containing it can
    capture it.  With [neq], a disequation's atom [select x j != u] is read
    as the equation it negates.  [free] is the set of variables a candidate may mention
    besides the read index: the free variables of the whole formula.  Empty
    for any sort but [Int -> E]. *)
let pointwise_witness_candidates ?(neq = false) ~free x sort body =
  match sort with
  | T_array.SArray (T_int.SInt, se) ->
      let pos, neg = Formula.atoms_of body in
      (* each definition's body over one placeholder index, so that two
         reads defining the same function compare equal *)
      let kc = Ast.Ident.mk_fresh_tvar () in
      Set.to_list (Set.union pos neg)
      |> List.filter_map ~f:(function
        | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq as p), [ t1; t2 ], _)
          when neq || Stdlib.( = ) p T_bool.Eq -> (
            match Ast.Evaluator.isolate_array_read x t1 t2 with
            | Some
                ( Term.FunApp
                    (T_array.ASelect _, [ _; Term.Var (j, T_int.SInt, _) ], _),
                  u )
              when (not (Ast.Ident.tvar_equal j x))
                   && Stdlib.( = ) (Term.sort_of u) se
                   && Set.for_all (Term.tvs_of u) ~f:(fun y ->
                       Ast.Ident.tvar_equal y j || Set.mem free y) ->
                Some
                  (Term.subst
                     (Map.Poly.singleton j (Term.mk_var kc T_int.SInt))
                     u)
            | _ -> None)
        | _ -> None)
      |> List.dedup_and_sort ~compare:Stdlib.compare
      |> by_size
      |> (fun bs -> List.take bs max_pointwise_witnesses)
      |> List.map ~f:(fun b ->
          let k = Ast.Ident.mk_fresh_tvar () in
          T_array.mk_lambda (k, T_int.SInt) se
            (Term.subst (Map.Poly.singleton kc (Term.mk_var k T_int.SInt)) b))
  | _ -> []

(** An INSTANCE of the validity question [phi] at the pointwise definitions
    of its free arrays, for refuting it: every free variable [x] of sort
    [Int -> E] for which [pointwise_witness_candidates] reads a definition
    [lambda k. u] off [phi] (an equation [select x j = u], or the atom of a
    disequation [select x j != u], anywhere in it: a clause in the
    disjunctive form states a premise's equation as a disequation) is
    replaced by the smallest one, simultaneously; [None] when no free array
    has one.  The result comes with the substitution, as [((x, sort), t)].

    Contract: [phi] is read as valid when it holds for every value of its
    free variables, so [phi] valid implies its instance valid, and a
    countermodel of the instance (a model of its negation) is one of [phi]
    with [x] taking the value of the lambda there.  So only a refutation may
    be read from the instance; a proof of it says nothing about [phi].

    Why: a clause of a Rust-derived problem states a history in the
    array-and-length encoding of sequences as a premise
    [forall i. 0 <= i < n => a[i] = i + c] over a FREE array [a], and its
    countermodel needs [a] to be that function.  A satisfiability question
    about the clause's negation leaves the array to the solver's
    model-based quantifier instantiation, which on such an input found it in
    0.6 s with one random seed and gave up ("incomplete quantifiers") after
    4-14 s with eight of ten others; with the array fixed to the lambda the
    same question was [sat] in 0.05 s on every seed tried. *)
let pointwise_array_instance phi =
  let free = Formula.tvs_of phi in
  let senv = Set.to_list (Formula.term_sort_env_of phi) in
  (* a name met at two sorts (an array at [Int -> E] in one place and at
     another index sort in another) is left alone: substituting the lambda
     for every occurrence would put an [Int]-indexed array where the other
     sort is read, an ill-sorted question the solver rejects *)
  let one_sort x =
    List.count senv ~f:(fun (y, _) -> Ast.Ident.tvar_equal x y) = 1
  in
  let defs =
    senv
    |> List.filter ~f:(fun (x, _) -> one_sort x)
    |> List.filter_map ~f:(fun (x, sort) ->
        match
          pointwise_witness_candidates ~neq:true ~free:(Set.remove free x) x
            sort phi
        with
        | t :: _ -> Some ((x, sort), t)
        | [] -> None)
  in
  if List.is_empty defs then None
  else
    let sub =
      Map.Poly.of_alist_exn @@ List.map defs ~f:(fun ((x, _), t) -> (x, t))
    in
    Some (Formula.subst sub phi, defs)

(** one pass over [phi], instantiating every sequence binder that may be
    instantiated soundly for validity, with candidate terms drawn from
    [pool] and ranked by [reads]; with [seq_array_view_candidates] set, a
    positive existential's array binders of sort [Int -> E] too, at the
    array views of the pool's sequences of sort [Seq E] *)
let instantiate_with ?(extra = fun _ -> []) ?budget ~pool ~reads phi =
  let whole = phi in
  (* listed once for every binder of this pass: on an instantiated clause with
     about 4,600 read chains, listing them again at each of some 1,700 binders
     took longer than a checker's run *)
  let whole_chains = lazy (select_chains whole) in
  let whole_free = lazy (Formula.tvs_of whole) in
  (* candidate instances for the sequence binder [x], each a term and the
     bindings of [others] its match gave (empty for a term that was not got
     by matching) *)
  let candidates ~with_extra ~bound ~others x sort body =
    let fits (t, binds) =
      Stdlib.( = ) (Term.sort_of t) sort
      && Set.is_empty (Set.inter (Term.tvs_of t) bound)
      && List.for_all binds ~f:(fun (_, w) ->
          Set.is_empty (Set.inter (Term.tvs_of w) bound))
    in
    let plain = List.map ~f:(fun t -> (t, [])) in
    let arrays = arrays_indexed_by x body in
    let same_array =
      List.filter_map reads ~f:(fun (a, i) ->
          if List.mem arrays a ~equal:Stdlib.( = ) then Some i else None)
    in
    let same_sort =
      List.filter_map reads ~f:(fun (a, i) ->
          if
            List.exists arrays ~f:(fun a' ->
                Stdlib.( = ) (Term.sort_of a) (Term.sort_of a'))
          then Some i
          else None)
    in
    let empty, chained, matched, matched_sort =
      match elem_of_seq sort with
      | Some se ->
          ( [ T_seq.mk_empty se ],
            (if with_extra && !chain_concat_candidates then
               chain_concat_candidates_for ~whole_chains ~whole ~bound x se
                 body
             else [])
            @ extra_rule_candidates ~with_extra ~whole x se body,
            concat_matches ~same_array:true ~others x se ~reads body,
            concat_matches ~same_array:false ~others x se ~reads body )
      | None -> ([], [], [], [])
    in
    let by_size_b =
      List.stable_sort ~compare:(fun (t1, _) (t2, _) ->
          Int.compare (Term.ast_size t1) (Term.ast_size t2))
    in
    let extras =
      if with_extra then
        List.take (List.filter ~f:fits (plain (extra sort))) max_extra_terms
      else []
    in
    dedup_terms
    @@ List.take
      (List.filter ~f:fits
      @@ dedup_terms
      @@ plain chained
      @ by_size_b matched
      @ plain (by_size same_array)
      @ by_size_b matched_sort
      @ plain (by_size same_sort)
      @ plain (by_size pool)
      @ plain empty)
      max_terms_per_binder
    @ extras
  in
  let rec go ~pos ~bound phi =
    match phi with
    | Formula.Atom _ | Formula.LetRec _ | Formula.LetFormula _ -> phi
    | Formula.UnaryOp (Formula.Not, p, _) ->
        Formula.mk_neg (go ~pos:(not pos) ~bound p)
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
        Formula.mk_binop op (go ~pos ~bound p) (go ~pos ~bound q)
    | Formula.BinaryOp (Formula.Imply, p, q, _) ->
        Formula.mk_binop Formula.Imply
          (go ~pos:(not pos) ~bound p)
          (go ~pos ~bound q)
    | Formula.BinaryOp ((Formula.Iff | Formula.Xor), _, _, _) -> phi
    | Formula.Bind (binder, senv, body, _) -> (
        let bound =
          Set.union bound (Set.Poly.of_list (List.map senv ~f:fst))
        in
        let body = go ~pos ~bound body in
        let sound =
          match binder with
          | Formula.Exists -> pos
          | Formula.Forall -> not pos
          | Formula.Random _ -> false
        in
        (* the pointwise definitions of this binder's arrays, only for a
           positive existential and only with [pointwise_array_witnesses] *)
        let pointwise =
          if
            !pointwise_array_witnesses
            && Stdlib.( = ) binder Formula.Exists
            && pos
          then
            List.filter_map senv ~f:(fun (x, s) ->
                match
                  pointwise_witness_candidates ~free:(Lazy.force whole_free) x
                    s body
                with
                | [] -> None
                | ts -> Some (x, ts))
          else []
        in
        let pointwise_of x =
          Option.value ~default:[]
            (List.Assoc.find pointwise x ~equal:Ast.Ident.tvar_equal)
        in
        let seqs, others =
          List.partition_tf senv ~f:(fun (x, s) ->
              Option.is_some (elem_of_seq s)
              || !seq_array_view_candidates
                 && Stdlib.( = ) binder Formula.Exists
                 && array_view_sort ~pool s
              || not (List.is_empty (pointwise_of x)))
        in
        let keep () = Formula.mk_bind binder senv body in
        let spent =
          match budget with Some left -> !left <= 0 | None -> false
        in
        (* once the budget is spent the binder is left as it is, without
           computing its candidates: leaving a quantifier is exact, and the
           candidates were the cost -- on an instantiated map clause, about a
           fifth of a second per binder over thousands of binders *)
        if (not sound) || List.is_empty seqs || spent then keep ()
        else
          let choices =
            List.map seqs ~f:(fun (x, s) ->
                List.map
                  (match s with
                  | T_array.SArray (_, se) ->
                      (* an array binder: only the views and the pointwise
                         definitions, kept where they mention nothing bound
                         here (a pool term is ground in the whole formula, but
                         a binder may reuse a name) *)
                      List.filter_map
                        ((if !seq_array_view_candidates then
                            array_view_candidates ~pool se
                          else [])
                        @ pointwise_of x)
                        ~f:(fun t ->
                          if Set.is_empty (Set.inter (Term.tvs_of t) bound)
                          then
                            (* a total lambda is no witness in every model:
                               guarded by the ranges the body reads [x] in *)
                            Option.map (guard_array_witness ~body x t)
                              ~f:(fun t -> (t, []))
                          else None)
                  | _ ->
                      let cs, secs =
                        instr_time (fun () ->
                            candidates
                              ~with_extra:(Stdlib.( = ) binder Formula.Exists)
                              ~bound ~others x s body)
                      in
                      instr_candidates_s := !instr_candidates_s +. secs;
                      cs)
                  ~f:(fun (t, binds) -> ((x, t), binds)))
          in
          if List.exists choices ~f:List.is_empty then keep ()
          else
            (* each instance substitutes its sequence terms and the
               bindings their matches gave, a variable bound by two matches
               differently keeping neither, and stays quantified over the
               rest of [others] *)
            let instance choice =
              let seq_sub = List.map choice ~f:fst in
              let binds = List.concat_map choice ~f:snd in
              let binds =
                List.filter binds ~f:(fun (v, w) ->
                    List.for_all binds ~f:(fun (v', w') ->
                        (not (Ast.Ident.tvar_equal v v')) || Stdlib.( = ) w w'))
                |> List.dedup_and_sort ~compare:(fun (v1, _) (v2, _) ->
                    Ast.Ident.tvar_compare v1 v2)
              in
              let rest =
                List.filter others ~f:(fun (y, _) ->
                    not
                      (List.exists binds ~f:(fun (v, _) ->
                           Ast.Ident.tvar_equal v y)))
              in
              let inst =
                Formula.subst (Map.Poly.of_alist_exn (seq_sub @ binds)) body
              in
              (* an array view substituted: its reads written without the
                 array, an equivalence ([reduce_view_reads]) *)
              let inst =
                if List.exists seq_sub ~f:(fun (_, t) -> view_rooted t) then
                  reduce_view_reads inst
                else inst
              in
              Formula.mk_bind_if_bounded binder rest inst
            in
            let instances =
              instances_within ?budget
                (product ~limit:max_instances_per_quantifier choices)
                ~build:instance
            in
            observe "seq"
              (List.map2_exn seqs choices ~f:(fun (x, _) c -> (x, List.length c)))
              instances;
            match binder with
            | Formula.Exists -> Formula.or_of instances
            | _ -> Formula.and_of instances)
  in
  go ~pos:true ~bound:Set.Poly.empty phi

(** [phi] with every sequence binder that can be instantiated soundly for
    validity instantiated; the result [phi'] satisfies: [phi'] valid implies
    [phi] valid.  [rounds] passes are made, each drawing its candidate terms
    from the instances of the previous one as well as from [phi], so that a
    term one hypothesis's instance builds ([unit y ++ t], say) can
    instantiate another; only the last pass's result is returned, and every
    pass instantiates [phi] itself, so each is sound on its own.  With
    [max_nodes], the passes together stop adding instances to a quantifier
    once the instances they have built total that many nodes
    ([instances_within]), a quantifier met after that is left as it is, and
    no further pass is made: the last pass made is returned, which is sound
    for the same reason as any pass.  The later pass draws its candidates
    from the earlier one's instances, so an earlier pass that filled the
    budget would give it a pool as large as that output; on an instantiated
    map clause a second pass over a pool of about a thousand terms took
    seconds per binder over some 1,500 binders.  Without [max_nodes], every
    quantifier takes up to [max_instances_per_quantifier] instances in every
    pass, as it always has. *)
let instantiate ?extra ?max_nodes ?(rounds = 2) phi =
  let free = Formula.tvs_of phi in
  let budget = Option.map max_nodes ~f:ref in
  let exhausted () =
    match budget with Some left -> !left <= 0 | None -> false
  in
  let rec loop n source =
    let pool = ground_sequences ~free source in
    let reads = reads_of ~pool source in
    let phi' = instantiate_with ?extra ?budget ~pool ~reads phi in
    if n <= 1 || exhausted () then phi'
    else loop (n - 1) (Formula.mk_and phi phi')
  in
  match instr_file with
  | None -> loop rounds phi
  | Some _ ->
      instr_candidates_s := 0.;
      let r, secs = instr_time (fun () -> loop rounds phi) in
      instr_line
        (sprintf "inst\tsecs=%.4f\tcand=%.4f\tin=%d\tout=%d" secs
           !instr_candidates_s (Formula.ast_size phi) (Formula.ast_size r));
      r

(** Variants of the sequence terms of [phi] with their variables replaced by
    PARTNERS, offered as extra candidates for a sequence binder.  Two free
    variables [v] and [w] of one sort are partners when some atom of [phi]
    (under a binder or not) mentions exactly those two free variables of
    that sort -- [10 * nth w j = nth v j], [v = 10 * w], [len v = len w].
    Why: a conclusion [exists s. R(s, v)] about a sequence [v] the clause
    builds as [unit a ++ b] is typically witnessed by the sequence built the
    same way from what [a] and [b] are related to ([unit a' ++ b'], with
    [a = 10 * a'] and [b] ten times [b'] elementwise), a term the clause
    never writes; on a Rust-derived input the right witness was of exactly
    that shape and was among no other candidate list.  Any term is a sound
    instance, so this only decides which instances are tried.  At most
    [max_partner_variants] variants per term, the identity excluded. *)
let max_partner_variants = 8

let partner_variants phi =
  let free = Formula.tvs_of phi in
  let atoms =
    let acc = ref [] in
    let rec walk = function
      | Formula.Atom (a, _) -> acc := a :: !acc
      | Formula.UnaryOp (_, p, _) -> walk p
      | Formula.BinaryOp (_, p, q, _) ->
          walk p;
          walk q
      | Formula.Bind (_, _, p, _) -> walk p
      | Formula.LetRec _ | Formula.LetFormula _ -> ()
    in
    walk phi;
    !acc
  in
  let partners =
    List.concat_map atoms ~f:(fun a ->
        let env =
          Set.to_list (Atom.term_sort_env_of a)
          |> List.filter ~f:(fun (v, _) -> Set.mem free v)
        in
        List.concat_map env ~f:(fun (v, sv) ->
            match
              List.filter env ~f:(fun (w, sw) ->
                  Stdlib.( = ) sv sw && not (Ast.Ident.tvar_equal v w))
            with
            | [ (w, _) ]
              when List.count env ~f:(fun (_, s) -> Stdlib.( = ) s sv) = 2 ->
                [ ((v, sv), Term.mk_var w sv) ]
            | _ -> []))
  in
  let partners_of v =
    dedup_terms
    @@ List.filter_map partners ~f:(fun ((v', _), w) ->
        if Ast.Ident.tvar_equal v v' then Some w else None)
  in
  let seqs = ground_sequences ~free phi in
  dedup_terms
  @@ List.concat_map seqs ~f:(fun t ->
      match flatten_concat t with
      | _ :: _ :: _ ->
          let choices =
            Set.to_list (Term.tvs_of t)
            |> List.filter_map ~f:(fun v ->
                match partners_of v with
                | [] -> None
                | ws ->
                    let sort = Term.sort_of (List.hd_exn ws) in
                    Some
                      (List.map (Term.mk_var v sort :: ws) ~f:(fun w -> (v, w))))
          in
          if List.is_empty choices then []
          else
            product ~limit:(max_partner_variants + 1) choices
            |> List.filter_map ~f:(fun sub ->
                let sub =
                  List.filter sub ~f:(fun (v, w) ->
                      match w with
                      | Term.Var (w, _, _) -> not (Ast.Ident.tvar_equal v w)
                      | _ -> true)
                in
                if List.is_empty sub then None
                else Some (Term.subst (Map.Poly.of_alist_exn sub) t))
      | _ -> [])

(** Integer binders instantiated where that only STRENGTHENS the validity
    question, applied to a clause whose sequence binders are already
    instantiated, as a second attempt when that alone was not shown valid.

    The clause [phi] is in negation normal form, so a hypothesis
    [forall j. 0 <= j < len s => psi(j)] of a premise reads as a positive
    [exists j. 0 <= j /\ j < len s /\ not psi(j)], and so does a conclusion's
    existential.  Three steps, each giving [phi'] with [phi' => phi] valid:
    - a universal reached from the root through conjunctions and
      disjunctions alone has its variables replaced by fresh free variables,
      which is exact, since validity is truth for every value of the free
      variables;
    - such an existential over integers is replaced by the disjunction of
      its instances, each of which implies it;
    - any existential still left there is replaced by [false], which implies
      it.
    So only a VALID answer may be read, as for the sequence step.  The
    result binds nothing, which is the point: a solver asked about reads of
    sequences under an integer hypothesis over their indices left such a
    question undecided at two minutes, while the instantiated,
    quantifier-free question was decided in under a second.

    Which terms.  For an index variable [j] read as [nth s (j + c)], the
    terms that name a position the clause reads: [u - len p - c] for every
    read [nth t u] of the clause where [s] is an operand of the
    concatenation [t] and [p] the operands before it; [len p - c] for every
    unit operand of [s] itself; and [0 .. n-1] less [c] when [s] has a
    literal length [n <= 4].  For a variable [x] occurring as [unit x], the
    elements of the unit sequences of the clause.  With [equated], also
    [t - c] for every equation or disequation [x + c = t] (or [t = x + c])
    of the body whose [t] mentions nothing bound -- the value a case split
    singles out, such as the sentinel index [-1] of a cell universal read
    back from a sequence, whose body is [false] there.  With
    [offset_int_candidates] set, also, after all of those, [t - len u] and
    [t + len u] for a variable used in a read index or an extraction bound,
    [t] a non-literal index or extraction bound of the clause and [len u] a
    length it mentions.  Two rounds, the second
    drawing on the terms the first round's instances introduce (a fresh
    variable of a conclusion's universal, say).  By default each round
    instantiates the clause itself, so an existential nested inside another
    is never instantiated and is dropped.  With [nested], the second round
    instantiates the FIRST round's result instead, whose existentials are
    the ones the first round's instances exposed -- one level deeper, as in a
    cell universal over two positions, whose premise is two nested
    existentials.  That result implies the clause once its fresh variables
    are read as universals again (each replaced a universal reached through
    conjunctions and disjunctions alone, and moving such a universal back
    out over the formula around it is an equivalence), so the second round's
    instances do too.  At most
    [max_int_instances] instances per quantifier; the bounds are a choice,
    not a measurement.  The terms are relevant by construction -- each
    names a position or element the clause already reads -- and that is
    what keeps the question small: offering every integer term of the
    clause instead was measured to give a query of megabytes that the
    solver did not decide. *)
let max_int_instances = 32

(* Whether an existential over an element of a sort variable or an
   uninterpreted sort is instantiated at the indices of the reads of the same
   array (see [instantiate_int]) rather than replaced by [false].  Set by the
   coordinator from its configuration; process-wide, as the question it
   answers is. *)
let instantiate_element_binders = ref false

(* Whether an integer binder used as a read index or a bound of an extraction
   is also offered the positions [t - len u] and [t + len u], where [t] is an
   index or extraction bound the clause reads outside every binder (not a
   literal) and [u] a sequence whose length it mentions there -- the position
   of a read of a concatenation [u ++ w] carried over to [w], or back, which a
   lemma stated over prefixes needs at the goal's own read (a prefix lemma for
   [x ++ y] instantiated at [i - len x] to reach the goal's [nth (x ++ y) i]).
   These come after the candidates of the other rules and at most
   [max_offset_int_candidates] of them.  Set by the coordinator from its
   configuration; process-wide, as [instantiate_element_binders] is. *)
let offset_int_candidates = ref false

let max_offset_int_candidates = 8

(* Whether an integer binder [x] read as an array index, [a[x + d]] with [a]
   and [d] mentioning nothing bound, is also offered [u - d] for every read
   [a[u]] of the same array the clause makes outside every binder -- the
   index a premise's witness names.  What it is for: a goal [exists j. f[j] =
   i] whose [f] is a join of two index maps, [ite (j < n) f1[j] (f2[j - n] +
   m)], is witnessed by the [k] of a premise [exists k. f1[k] = i] (or [k + n]
   of [exists k. f2[k] = i - m]); once the premise is instantiated and its
   witness made a fresh variable by the first round, the second round sees
   the read [f1[k]], and no other rule offers [k], since [j] is read by no
   sequence and equated to nothing.  Only for a binder the earlier rules
   offer nothing, at most [max_array_read_int_candidates] of them, the reads
   of each array of the body taken in turns.  Any integer term is
   a sound instance, so this only chooses which.  Set by the coordinator from
   its configuration; process-wide, as [offset_int_candidates] is. *)
let array_read_int_candidates = ref false

let max_array_read_int_candidates = 8

(* Whether an existential over an index map, an array [Int -> Int], is also
   offered the shifts [lambda k. k + len u] by the lengths the clause mentions
   outside every binder, and the identity (with [instantiate_element_binders],
   which is what instantiates array binders at all).  What it is for: a
   filter's [produces] relates the visited items to the inner sequence [s]
   through an index map [f]; after one accepted item [x] following refused
   items [t], [s] is [t ++ [x]] and [f] maps the one visited position to [len
   t], a shift no other rule offers -- the clause mentions no array of that
   sort, and the constant array at a dummy value serves only when [t] is
   empty.  At most [max_index_map_shift_candidates] shifts.  Each instance
   implies the existential, so this only chooses which.  Set by the
   coordinator from its configuration; process-wide. *)
let index_map_shift_candidates = ref false

let max_index_map_shift_candidates = 6

(* Whether an existential over an index map, an array [Int -> Int], is also
   offered the joins [lambda k. ite (k < c) g[k] (h[k - c] + d)] of two index
   maps [g], [h] free in the clause (with [instantiate_element_binders]), [c]
   and [d] the lengths of proper prefixes of two different concatenations the
   binder's body mentions outside every binder.  What it is for: the
   transitivity of a filter's [produces], whose index map for the visited
   items [ab ++ bc] over the inner sequence [s1 ++ s2] is the premises' maps
   [f1] (for [ab]) and [f2] (for [bc]) joined at [c = len ab], the second
   shifted by [d = len s1].  The input states that join as a [lambda] in a
   lemma, but the lemma's applications are beta-reduced before the
   instantiation sees them, so no rule finds the term in the clause.  At most
   [max_index_map_join_candidates] joins.  Each instance implies the
   existential, so this only chooses which.  Set by the coordinator from its
   configuration; process-wide. *)
let index_map_join_candidates = ref false

let max_index_map_join_candidates = 8

(* Whether an integer binder is also offered the integers in [-8, 8] that
   satisfy every top-level conjunct of its body mentioning it alone, when there
   are at most four: a binder over the positions of a sequence of literal
   length, [exists j. 0 <= j < 1 /\ f[j] = i], which no read or equation
   names.  Each instance implies the existential, so this only chooses
   which.  Set by the coordinator from its configuration; process-wide. *)
let literal_range_int_candidates = ref false

(* Whether the chain-focused and associativity-matched forms instantiate their
   integer binders as the deep forms do ([instantiate_int ~equated ~nested]):
   the second round instantiating the first's result, so that an existential
   exposed only once an outer binder is instantiated -- the [exists j. f[j] =
   i] of a goal whose index map [f] the first round chose -- is instantiated
   rather than dropped; and the first round keeps each existential beside its
   instances ([keep_first]), an equivalent formula, so that the second offers
   it the terms the first round's instances introduce -- a premise
   instantiated at the goal's position, which is a fresh variable of an index
   map's instance.  A focused form holds one witness, so the nested round
   stays small where the deep form's, over every witness, was measured past
   what the solver decides within its budget.  Each instance implies its
   existential either way.  Set by the coordinator; process-wide. *)
let nested_focus_forms = ref false

(* Whether, with [instantiate_element_binders], an element binder that is an
   argument of a constructor at an array index, [r[c(.., x, ..)]], is also
   offered the argument at the same place of the same constructor at that
   index of a read of [r] outside the quantifier.  What it is for: the laws
   over a closure's postcondition -- its history invariant, Creusot's
   [precise] -- quantify over the two states of a [mut c d] the
   postcondition is read at, and the clause reads it at [mut(s, s')]; the
   plain rule offers only an index that is the binder itself.  Each instance
   implies its existential.  Set by the coordinator; process-wide. *)
let element_candidates_through_constructors = ref false

(* Whether an existential that also binds a [Bool] is instantiated, the
   [Bool] at [true] and [false], rather than replaced by [false] for binding
   a sort no rule offers anything.  What it is for: a law over a closure's
   postcondition quantifies over its result, [post(mut c d, e, b) =>
   hist(c, d)], and the clause needs it at a [b] it reads.  Both values
   together are the binder's whole domain.  Set by the coordinator;
   process-wide. *)
let bool_binder_candidates = ref false

(* Whether the forms that split every read of a concatenation by index also
   split every prefix of a concatenation, [extract (a ++ b) 0 k], by where [k]
   falls ([Ast.Evaluator.rewrite_seq_prefix_over_concat]).  The rewrite is an
   equivalence in every model, so a form rewritten by it asks the same question.
   Set by the coordinator from its configuration; process-wide, as
   [offset_int_candidates] is. *)
let split_seq_prefix_over_concat = ref false

(* Whether that split is confined to the chain-focused and
   associativity-matched forms ([split_prefixes ~focus:true]).  Contract: with
   it set, [split_prefixes] without [~focus] is the identity.  Why: a deep
   form holds every instance of every binder, and splitting all of its
   prefixes of concatenations (hundreds of distinct ones) was measured to
   triple its size, past what the solver decides within its budget, while a
   focused form holds one witness and a few law instances, a few kilobytes,
   where the split is what lets the solver decide a goal over a prefix of the
   witness [x0 ++ x1].  The split is an equivalence wherever it is applied,
   so this only chooses which questions carry it.  Set by the coordinator;
   process-wide, as [split_seq_prefix_over_concat] is. *)
let split_seq_prefix_focus_only = ref false

let split_prefixes ?(focus = false) phi =
  if !split_seq_prefix_over_concat && (focus || not !split_seq_prefix_focus_only)
  then Ast.Evaluator.rewrite_seq_prefix_over_concat phi
  else phi

(* Whether the offset positions of [offset_int_candidates] are built only
   from the lengths of CHAIN OPERANDS: the operands (of the concatenation
   chain) of the middle argument of either application of a pair of ground
   applications [h(s, u1, m)], [h(m, u2, e)] of the piece whose inner
   arguments agree, the pair a transitivity witness [u1 ++ u2] is built from.
   A prefix lemma over that witness reaches a read of it at [t] through
   [t - len u1], and no other length is needed for it; offering every length
   the piece mentions was measured to cost more solver time than the
   instances save.  Fewer instances of the same kind, so each is still sound.
   Set by the coordinator; process-wide, as [offset_int_candidates] is. *)
let offset_int_candidates_chain_only = ref false

(** the operands of the middle arguments of the chained pairs of ground
    applications of [phi] (see [offset_int_candidates_chain_only]) *)
let chain_operands phi =
  let free = Formula.tvs_of phi in
  let apps =
    List.filter (select_chains phi) ~f:(fun (h, args) ->
        List.for_all (h :: args) ~f:(fun t ->
            Set.is_subset (Term.tvs_of t) ~of_:free))
  in
  dedup_terms
  @@ List.concat_map apps ~f:(fun (h, a1) ->
      let n = List.length a1 in
      let j = n / 2 in
      if
        n mod 2 = 0 || j = 0
        || Option.is_none (elem_of_seq (Term.sort_of (List.nth_exn a1 j)))
      then []
      else
        List.concat_map apps ~f:(fun (h', a2) ->
            if
              Stdlib.( = ) h h'
              && List.length a2 = n
              && List.equal Stdlib.( = ) (List.drop a1 (j + 1)) (List.take a2 j)
            then
              flatten_concat (List.nth_exn a1 j)
              @ flatten_concat (List.nth_exn a2 j)
            else []))

(** The first [max] terms of [offsets], in order, that mention no variable of
    [bound] and are not [Stdlib.( = )] to an element of [existing]; each
    offset comes with its free variables ([Term.tvs_of], forced only when
    the offset is reached).

    Contract: when [offsets] is free of repetitions and [existing] has no two
    elements [Stdlib.compare] finds equal (both hold of a [dedup_terms]
    result), the terms returned are
    [List.take (List.filter (dedup_terms (List.filter ts ~f:free)) ~f:(fun t
    -> not (List.mem existing t ~equal:Stdlib.( = )))) max], with [ts] the
    offsets' terms and [free] the test on [bound]: that is how
    [instantiate_int] chose them before.  The [dedup_terms] is the identity
    on a sublist of a list free of repetitions; membership in [existing] is
    [Stdlib.( = )] asked of the one element [Stdlib.compare] finds equal, if
    any, since a term [=] to another is [compare]-equal to it; and filtering
    stops at [max] terms.  Why: offsets run to thousands on a Rust-derived
    clause, and the earlier form re-took every offset's free variables,
    re-hashed every offset and scanned [existing] once per offset, for each
    integer existential, which was about a third of the instantiation's
    time there. *)
let select_offsets ~max ~bound ~existing offsets =
  let existing_tbl = Hashtbl.PolyDeep.create () in
  List.iter existing ~f:(fun e -> Hashtbl.set existing_tbl ~key:e ~data:e);
  let in_existing t =
    match Hashtbl.find existing_tbl t with
    | Some e -> Stdlib.( = ) e t
    | None -> false
  in
  let rec take k acc = function
    | [] -> List.rev acc
    | _ when k <= 0 -> List.rev acc
    | (t, tvs) :: rest ->
        if Set.is_empty (Set.inter (Lazy.force tvs) bound) && not (in_existing t)
        then take (k - 1) (t :: acc) rest
        else take k acc rest
  in
  take max [] offsets

(** whether an existential's binders are all of sorts no instantiation rule
    here offers terms for and that a solver's matching handles on its own: no
    integer, Boolean, sequence or array binder (an uninterpreted sort, a sort
    variable, a datatype).  Such an existential is, in a validity question, a
    premise universal over opaque values -- a law of an uninterpreted
    relation (reflexivity, transitivity, a postcondition implying a history
    invariant) -- which [instantiate_int ~keep_scalar:true] keeps as it is
    instead of dropping it. *)
let scalar_only senv =
  List.for_all senv ~f:(fun (_, s) ->
      not
        (Stdlib.( = ) s T_int.SInt
        || Stdlib.( = ) s T_bool.SBool
        || Stdlib.( = ) s T_real.SReal
        || Option.is_some (elem_of_seq s)
        || match s with T_array.SArray _ -> true | _ -> false))

(* Whether [instantiate_int] reads each [nth] of its source once.  The result is
   the same either way; the switch exists so that a test can compare the two. *)
let instantiate_int_dedup_reads = ref true

(* Whether [instantiate_int] keys the fresh variables of a universal by the
   universal's structure ([Hashtbl.PolyDeep]) rather than by its printed form.
   The two keys agree wherever two universals that print alike are equal, which
   is every case met so far, and then the fresh variables drawn, their order and
   the result are the same.  Where two different universals print alike the
   structural key gives each its own fresh variables, which is the reading the
   skolemisation needs (sharing them between two different universals of one
   disjunction weakens it).  Why: printing every distinct universal of every
   piece's deep form once per form was 40% of the integer step on a
   Rust-derived loop-body clause of 95 pieces whose premise instances ran to
   100,000-270,000 nodes, about 8 s of a 120 s budget under load.  The switch
   exists so that a test can compare the two keys. *)
let instantiate_int_skolem_by_structure = ref true

(* Whether [instantiate_int], inside a replay of fresh names
   ([Ast.Ident.with_replayed_fresh_names]), reuses the instances it built for
   an integer existential when the same existential is met again with the same
   candidates, the same node budget left and the replay at the same position
   ([instantiated_with_memo]).  Set by the coordinator from its configuration;
   process-wide, as the other instantiation switches are.  What it is for: the
   first deep forms of the pieces of one clause, built one after another in one
   replay scope for grouping, share their premise, and the instances of its
   existentials are the same formulas in every piece; on a Rust-derived clause
   of 64 pieces the integer step built those instances (14,000 nodes to
   307,000) once per piece, 11 s of a 120 s budget. *)
let share_replayed_int_instances = ref false

(* the memo's counts since the process started: reuses, and instances built
   with the memo consulted *)
let int_memo_hits = ref 0
let int_memo_misses = ref 0

(* entries stored at one replay position (their building drew replayed
   names), and builds not stored because a process-global counter moved *)
let int_memo_positional = ref 0
let int_memo_unstored = ref 0

(* per domain: the replay scope the table is for, and the table, keyed by the
   existential, its candidates, the budget left and the replay position, with
   the instances built, the budget left after them and the number of names
   drawn *)
let int_memo_key :
    (string option ref
    * ( Formula.t * (Ast.Ident.tvar * Term.t) list list * int option * int,
        Formula.t list * int option * int )
      Hashtbl.t)
    Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> (ref None, Hashtbl.PolyDeep.create ()))

(* this domain's memo emptied, which only frees what it holds: an emptied
   memo builds what it would have reused *)
(* with COAR_INT_MEMO_STATS set, the memo's counts so far go to stderr when
   it is emptied and after every 25th consultation *)
let int_memo_stats = lazy (Option.is_some (Sys.getenv "COAR_INT_MEMO_STATS"))

let print_int_memo_stats () =
  if Lazy.force int_memo_stats then
    eprintf "int-memo hits=%d misses=%d positional=%d unstored=%d\n%!"
      !int_memo_hits !int_memo_misses !int_memo_positional !int_memo_unstored

let reset_int_memo () =
  print_int_memo_stats ();
  let current, table = Stdlib.Domain.DLS.get int_memo_key in
  current := None;
  Hashtbl.clear table

(** [instantiated_with_memo ~phi ~choices ~budget compute] is [compute ()], the
    instances of the existential [phi] at the candidates [choices] built under
    the node budget [budget] (which [compute] lowers), or a stored copy of
    them.

    Contract: the result, the budget left afterwards and the names every later
    draw gives are those [compute ()] would give.  The instances built for an
    existential are a function of the existential, its candidates, the budget
    left (which decides how many are built) and the fresh names drawn while
    building them; a stored entry is used only when the first three are equal
    and the replay is at the same position in the same scope, so the replayed
    draws would give the same names -- or, for an entry whose building drew no
    name at all, at any position, since nothing it built was named by the
    replay -- and an entry is stored only when every
    name drawn while building it was a replayed one (no process-global counter
    moved, in this domain or another), so that nothing else is drawn that a
    reuse would skip.  On reuse the budget is set to what it was left at and
    the replay is moved on by the number of names drawn.  Outside a replay, or
    with the switch off, [compute ()] alone. *)
let instantiated_with_memo ~phi ~choices ~budget compute =
  if not !share_replayed_int_instances then compute ()
  else
    match Ast.Ident.replay_position () with
    | None -> compute ()
    | Some (scope, pos) -> (
        let current, table = Stdlib.Domain.DLS.get int_memo_key in
        if not (Option.equal String.equal !current (Some scope)) then (
          Hashtbl.clear table;
          current := Some scope);
        if (!int_memo_hits + !int_memo_misses) mod 25 = 24 then
          print_int_memo_stats ();
        let left = Option.map budget ~f:( ! ) in
        (* an entry whose building drew no name at all is stored at position
           [-1] and serves every position: what it built cannot depend on
           where the replay stood *)
        let anywhere = (phi, choices, left, -1) and here = (phi, choices, left, pos) in
        match
          match Hashtbl.find table anywhere with
          | Some _ as e -> e
          | None -> Hashtbl.find table here
        with
        | Some (instances, left', draws) ->
            incr int_memo_hits;
            (match (budget, left') with Some b, Some l -> b := l | _ -> ());
            if draws > 0 then Ast.Ident.skip_replayed_fresh_names draws;
            instances
        | None ->
            incr int_memo_misses;
            let global0 = Ast.Ident.fresh_stamp () - pos in
            let instances = compute () in
            (match Ast.Ident.replay_position () with
            | Some (scope', pos') when String.equal scope scope' ->
                if Ast.Ident.fresh_stamp () - pos' <> global0 then
                  incr int_memo_unstored
                else
                  let draws = pos' - pos in
                  if draws > 0 then incr int_memo_positional;
                  Hashtbl.set table
                    ~key:(if draws = 0 then anywhere else here)
                    ~data:(instances, Option.map budget ~f:( ! ), draws)
            | _ -> ());
            instances)

(* [instantiate_int]'s result implies [phi]: an existential over integers is
   replaced by its instances and any other by [false], each of which implies
   it.  With [keep_scalar], an existential [scalar_only] accepts is left as it
   is instead (by both passes and by the final [drop]), which is exact. *)
let instantiate_int ?(equated = false) ?(nested = false) ?(keep_first = false)
    ?(keep_scalar = false) ?max_nodes phi =
  (* one budget for both passes: the second instantiates the first's
     instances when [nested] is set, so the two multiply *)
  let budget = Option.map max_nodes ~f:ref in
  let skolems = Hashtbl.create (module String) in
  (* with [instantiate_int_skolem_by_structure], the fresh variables keyed by
     the universal itself *)
  let skolems_by_structure = Hashtbl.PolyDeep.create () in
  let skolemized = Hashtbl.PolyDeep.create () in
  (* [Formula.str_of] of each universal met, remembered by the universal's
     structure: printing is a function of the structure, and the instances
     of one body repeat the universals that do not mention the instantiated
     variable, so the same universal was printed once per instance and per
     round, a few seconds on a Rust-derived clause *)
  let printed = Hashtbl.PolyDeep.create () in
  let by_structure = !instantiate_int_skolem_by_structure in
  (* the fresh variables of a universal are fixed by the universal, so that
     the two rounds agree on them *)
  let rec skolemize phi =
    match phi with
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
        Formula.mk_binop op (skolemize p) (skolemize q)
    | Formula.Bind (Formula.Forall, senv, body, _) ->
        let fresh () =
          List.map senv ~f:(fun (x, s) ->
              (x, Term.mk_var (Ast.Ident.mk_fresh_tvar ()) s))
        in
        if by_structure then (
          (* the result too, by the universal's structure: a second
             universal equal to one already skolemized gets the same fresh
             variables, and every universal nested in it was met (and given
             its variables) the first time, so its result is the first
             one's and no name is drawn either way.  The instances of one
             body repeat the universals that do not mention the
             instantiated variable, and each was substituted afresh. *)
          match Hashtbl.find skolemized phi with
          | Some r -> r
          | None ->
              let sub =
                Hashtbl.find_or_add skolems_by_structure phi ~default:fresh
              in
              let r = skolemize (Formula.subst (Map.Poly.of_alist_exn sub) body) in
              Hashtbl.set skolemized ~key:phi ~data:r;
              r)
        else
          let key =
            Hashtbl.find_or_add printed phi ~default:(fun () ->
                Formula.str_of phi)
          in
          let sub = Hashtbl.find_or_add skolems key ~default:fresh in
          skolemize (Formula.subst (Map.Poly.of_alist_exn sub) body)
    | _ -> phi
  in
  (* the subterms of [phi] outside every binder, entering the formulas
     embedded in terms (the conditions of an if-then-else, which is how a
     split read of a concatenation is written) but no quantifier, array
     lambda or let in them *)
  let collect ?(atom = fun _ -> None) phi ~f =
    let acc = ref [] in
    let rec term t =
      (match f t with Some x -> acc := x :: !acc | None -> ());
      match t with
      | Term.FunApp (T_bool.Formula p, [], _) -> formula p
      | Term.FunApp ((T_array.ALambda _ | T_bool.Formula _), _, _)
      | Term.LetTerm _ | Term.Var _ ->
          ()
      | Term.FunApp (_, args, _) -> List.iter args ~f:term
    and formula = function
      | Formula.Atom ((Atom.App (_, args, _) as a), _) ->
          (match atom a with Some x -> acc := x :: !acc | None -> ());
          List.iter args ~f:term
      | Formula.Atom _ -> ()
      | Formula.UnaryOp (_, p, _) -> formula p
      | Formula.BinaryOp (_, p, q, _) ->
          formula p;
          formula q
      | Formula.Bind _ | Formula.LetRec _ | Formula.LetFormula _ -> ()
    in
    formula phi;
    List.rev !acc
  in
  let offset x = function
    | Term.Var (y, _, _) when Ast.Ident.tvar_equal x y -> Some Z.zero
    | Term.FunApp
        ( T_int.Add,
          ( [ Term.Var (y, _, _); Term.FunApp (T_int.Int c, [], _) ]
          | [ Term.FunApp (T_int.Int c, [], _); Term.Var (y, _, _) ] ),
          _ )
      when Ast.Ident.tvar_equal x y ->
        Some c
    | Term.FunApp
        ( T_int.Sub,
          [ Term.Var (y, _, _); Term.FunApp (T_int.Int c, [], _) ],
          _ )
      when Ast.Ident.tvar_equal x y ->
        Some (Z.neg c)
    | _ -> None
  in
  (* a linear normal form, so that one position reached two ways is one
     candidate; a term outside linear integer arithmetic is only simplified *)
  let norm t =
    try
      Ast.AffineTerm.mk_int_term
        (Ast.Normalizer.linear_int_monomials_of (Ast.Value.Int Z.one) t)
    with exn_ when not (Timer.is_async exn_) -> Ast.Evaluator.simplify_term t
  in
  let minus t c = norm (T_int.mk_sub t (T_int.mk_int c)) in
  let len_of se ops =
    List.fold ops ~init:(T_int.zero ()) ~f:(fun acc o ->
        T_int.mk_add acc (T_seq.mk_len se o))
  in
  let candidates ~reads ~units ~offsets ~source ~bound x body =
    let at_index =
      collect body ~f:(function
        | Term.FunApp (T_seq.SqNth se, [ s; i ], _) -> (
            match offset x i with
            | Some c when Set.is_empty (Set.inter (Term.tvs_of s) bound) ->
                Some (se, s, c)
            | _ -> None)
        | _ -> None)
      |> List.concat_map ~f:(fun (se, s, c) ->
          let ops = flatten_concat s in
          let from_reads =
            List.concat_map reads ~f:(fun (s', u) ->
                let ops' = flatten_concat s' in
                List.filter_mapi ops' ~f:(fun p o ->
                    if Stdlib.( = ) o s then
                      Some (minus (T_int.mk_sub u (len_of se (List.take ops' p))) c)
                    else None))
          in
          let unit_positions =
            List.filter_mapi ops ~f:(fun p o ->
                match o with
                | Term.FunApp (T_seq.SqUnit _, [ _ ], _) ->
                    Some (minus (len_of se (List.take ops p)) c)
                | _ -> None)
          in
          let literal =
            match Ast.Evaluator.seq_len_of s with
            | Some n when Z.leq n (Z.of_int 4) ->
                List.init (Z.to_int n) ~f:(fun k ->
                    T_int.mk_int Z.(of_int k - c))
            | _ -> []
          in
          from_reads @ unit_positions @ literal)
    in
    let as_element =
      if
        Set.exists
          (Formula.filtered_terms_of body ~f:(function
            | Term.FunApp (T_seq.SqUnit _, [ Term.Var (y, _, _) ], _) ->
                Ast.Ident.tvar_equal x y
            | _ -> false))
          ~f:(fun _ -> true)
      then units
      else []
    in
    (* the other side of an equation or disequation between the variable
       (up to a constant offset) and a term that mentions nothing bound: the
       value a case split in the body singles out, such as the sentinel
       position of a cell read back from a sequence *)
    let as_equated =
      if not equated then []
      else
        collect body ~f:(fun _ -> None) ~atom:(function
          | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ a; b ], _)
            when Stdlib.( = ) (Term.sort_of a) T_int.SInt -> (
              let free t = Set.is_empty (Set.inter (Term.tvs_of t) bound) in
              match (offset x a, offset x b) with
              | Some c, None when free b -> Some (minus b c)
              | None, Some c when free a -> Some (minus a c)
              | _ -> None)
          | _ -> None)
    in
    (* Any integer term is a sound instance of an existential here, since
       each instance implies it and the result only has to strengthen the
       clause; the rule below only chooses which terms, and adds them after
       every other rule's so that none of those is displaced. *)
    let offers_offsets =
      let is_position =
        let mentions t = Set.mem (Term.tvs_of t) x in
        not
        @@ List.is_empty
        @@ collect body ~f:(function
          | Term.FunApp (T_seq.SqNth _, [ _; i ], _) when mentions i -> Some ()
          | Term.FunApp (T_seq.SqExtract _, [ _; o; l ], _)
            when mentions o || mentions l ->
              Some ()
          | _ -> None)
      in
      is_position
    in
    (* [array_read_int_candidates]: for a read [a[x + d]] of the body ([a]
       and [d] mentioning nothing bound), the indices [u - d] of the reads
       [a[u]] of the same array in [source] outside every binder *)
    let as_array_index =
      lazy (
      if not !array_read_int_candidates then []
      else
        let free t = Set.is_empty (Set.inter (Term.tvs_of t) bound) in
        let shifts =
          collect body ~f:(function
            | Term.FunApp (T_array.ASelect _, [ a; i ], _)
              when free a && Set.mem (Term.tvs_of i) x -> (
                match norm (T_int.mk_sub i (Term.mk_var x T_int.SInt)) with
                | d when free d && not (Set.mem (Term.tvs_of d) x) -> Some (a, d)
                | _ -> None
                | exception exn_ when not (Timer.is_async exn_) -> None)
            | _ -> None)
        in
        if List.is_empty shifts then []
        else
          let reads_of_arrays =
            collect source ~f:(function
              | Term.FunApp (T_array.ASelect _, [ a; u ], _)
                when Stdlib.( = ) (Term.sort_of u) T_int.SInt && free u ->
                  Some (a, u)
              | _ -> None)
            (* reads at a variable first: a premise's witness, made a fresh
               variable by the first round, is read there, while a read at
               a compound index is an instance an earlier rule built *)
            |> List.partition_tf ~f:(function
              | _, Term.Var _ -> true
              | _ -> false)
            |> fun (vars, others) -> vars @ others
          in
          (* one list per read of the body, taken in turns, so that the
             reads of one array do not fill the bound before another's are
             offered (a joined map reads both of its parts) *)
          let per_shift =
            List.map shifts ~f:(fun (a, d) ->
                List.filter_map reads_of_arrays ~f:(fun (a', u) ->
                    if Stdlib.( = ) a a' then Some (norm (T_int.mk_sub u d))
                    else None))
          in
          let rec interleave = function
            | [] -> []
            | ls ->
                List.filter_map ls ~f:List.hd
                @ interleave
                    (List.filter_map ls ~f:(fun l ->
                         match List.tl l with
                         | Some (_ :: _ as t) -> Some t
                         | _ -> None))
          in
          List.take
            (dedup_terms (interleave per_shift))
            max_array_read_int_candidates)
    in
    (* [literal_range_int_candidates]: the integers in [-8, 8] that satisfy
       every top-level conjunct of the body mentioning [x] and no other
       variable, when there are at most four -- a binder ranging over the
       positions of a sequence of literal length, such as the one visited
       item of a filter's step *)
    let as_literal_range =
      if not !literal_range_int_candidates then []
      else
        let own =
          List.filter (Formula.conjuncts_list_of body) ~f:(fun c ->
              let vs = Formula.tvs_of c in
              Set.length vs = 1 && Set.mem vs x
              && List.is_empty (Formula.quantified_sort_env_of c |> Set.to_list))
        in
        if List.is_empty own then []
        else
          let holds v c =
            Formula.is_true
              (Ast.Evaluator.simplify
                 (Formula.subst (Map.Poly.singleton x (T_int.mk_int (Z.of_int v))) c))
          in
          let vs =
            List.filter (List.range (-8) 9) ~f:(fun v ->
                List.for_all own ~f:(holds v))
          in
          if List.length vs <= 4 then
            List.map vs ~f:(fun v -> T_int.mk_int (Z.of_int v))
          else []
    in
    let existing =
      dedup_terms (at_index @ as_element @ as_equated @ as_literal_range)
    in
    (* only for a binder no other rule offers anything: one read by a
       sequence already has the positions of those reads, and offering it
       every index of an array as well was seen to triple the instances of
       a clause's premises without proving more *)
    let existing =
      if List.is_empty existing then dedup_terms (Lazy.force as_array_index)
      else existing
    in
    existing
    @
    if offers_offsets then
      select_offsets ~max:max_offset_int_candidates ~bound ~existing offsets
    else []
  in
  (* An array read decomposed into its root variable and its indices, the
     outermost last: [select (select a i) j] is [(a, [i; j])]. *)
  let rec select_chain = function
    | Term.FunApp (T_array.ASelect _, [ a; i ], _) ->
        Option.map (select_chain a) ~f:(fun (r, is) -> (r, is @ [ i ]))
    | Term.Var (r, _, _) -> Some (r, [])
    | _ -> None
  in
  let chains_of phi =
    collect phi ~f:(function
      | Term.FunApp (T_array.ASelect _, _, _) as t -> (
          match select_chain t with Some (_, []) | None -> None | c -> c)
      | _ -> None)
  in
  (* Candidates for an element of a sort variable or an uninterpreted sort,
     which nothing can count: the indices at the same position of a read of
     the same array outside the quantifier.  A trait predicate over a
     quantified sort is such an array, and a law stated about it -- the
     transitivity of [produces] -- reaches a clause as an existential whose
     witnesses are the states the clause already reads it at, e.g. the
     middle state [y] of [produces x s1 y /\ produces y s2 z]. *)
  let element_candidates ~chains ~bound x body =
    let is_x = function
      | Term.Var (y, _, _) -> Ast.Ident.tvar_equal x y
      | _ -> false
    in
    let free t = Set.is_empty (Set.inter (Term.tvs_of t) bound) in
    List.concat_map (chains_of body) ~f:(fun (r, is) ->
        List.concat
        @@ List.mapi is ~f:(fun k i ->
            if is_x i then
              List.filter_map chains ~f:(fun (r', is') ->
                  if Ast.Ident.tvar_equal r r' && List.length is' > k then
                    let t = List.nth_exn is' k in
                    if free t then Some t else None
                  else None)
            else
              (* [element_candidates_through_constructors]: [x] an argument
                 of a constructor at an index, [r[c(.., x, ..)]], is offered
                 the argument at the same place of the same constructor at
                 that index of a read of [r] outside the quantifier -- a law
                 over a closure's states [mut c d] read at [mut(s, s')] *)
              match i with
              | Term.FunApp (T_dt.DTCons (name, _, _), args, _)
                when !element_candidates_through_constructors ->
                  List.concat
                  @@ List.mapi args ~f:(fun p a ->
                      if not (is_x a) then []
                      else
                        List.filter_map chains ~f:(fun (r', is') ->
                            if Ast.Ident.tvar_equal r r' && List.length is' > k
                            then
                              match List.nth_exn is' k with
                              | Term.FunApp (T_dt.DTCons (name', _, _), args', _)
                                when String.equal name name'
                                     && List.length args' = List.length args ->
                                  let t = List.nth_exn args' p in
                                  if free t then Some t else None
                              | _ -> None
                            else None))
              | _ -> []))
    |> dedup_terms
  in
  let is_element_sort = function
    | Sort.SVar _ | T_dt.SUS _ -> !instantiate_element_binders
    | _ -> false
  in
  let is_array_sort = function
    | T_array.SArray _ -> !instantiate_element_binders
    | _ -> false
  in
  (* Candidates for an array binder: the arrays of its sort the clause
     mentions outside the quantifier.  An array a clause states by an equation
     is removed before this by the one-point rule. *)
  let array_candidates ~source ~bound ~body x sort =
    collect source ~f:(fun t ->
        if
          Stdlib.( = ) (Term.sort_of t) sort
          && Set.is_empty (Set.inter (Term.tvs_of t) bound)
        then Some t
        else None)
    |> dedup_terms
    |> fun ts ->
    List.take ts 4
    @
    (* and a constant array, which serves when the body reads the binder only
       where it is overwritten, as a call's visited-items array extended by a
       store at the positions it reads *)
    (* not a constant array, which a model's carrier need not hold, but a
       fresh array, read universally *)
    (match sort with
    | T_array.SArray _ -> [ fresh_array_witness sort ]
    | _ -> [])
    @ (* [index_map_shift_candidates]: for an index map [Int -> Int], the
       shifts [lambda k. k + len u] by the length of a sequence the clause
       mentions outside every binder -- the map of a visited suffix of [u ++
       v] into [u ++ v], which a filter or a map that has just produced one
       item over an inner sequence [t ++ [x]] needs ([t] the items refused
       before it) -- and the identity *)
    (match sort with
    | T_array.SArray (T_int.SInt, T_int.SInt) when !index_map_shift_candidates
      ->
        let shift d =
          let k = Ast.Ident.mk_fresh_tvar () in
          T_array.mk_lambda (k, T_int.SInt) T_int.SInt
            (match d with
            | None -> Term.mk_var k T_int.SInt
            | Some d -> T_int.mk_add (Term.mk_var k T_int.SInt) d)
        in
        (* the lengths of the proper prefixes of every concatenation the
           clause (or the binder's own body) mentions with nothing bound,
           then the lengths it states *)
        let free u = Set.is_empty (Set.inter (Term.tvs_of u) bound) in
        let prefix_lens phi =
          collect phi ~f:(function
            | Term.FunApp (T_seq.SqConcat se, _, _) as u when free u ->
                let ops = flatten_concat u in
                Some
                  (List.init
                     (List.length ops - 1)
                     ~f:(fun p -> norm (len_of se (List.take ops (p + 1)))))
            | _ -> None)
          |> List.concat
        in
        let lens =
          dedup_terms
          @@ prefix_lens body
          @ prefix_lens source
          @ collect source ~f:(function
              | Term.FunApp (T_seq.SqLen _, [ u ], _) as l when free u -> Some l
              | _ -> None)
        in
        List.map (List.take lens max_index_map_shift_candidates) ~f:(fun l ->
            shift (Some l))
        @ [ shift None ]
        |> List.filter_map ~f:(guard_array_witness ~body x)
    | _ -> [])
    @
    (* [index_map_join_candidates]: for an index map [Int -> Int], the joins
       of two free index maps at the length of a prefix of one concatenation
       of the binder's body, the second shifted by the length of a prefix of
       another *)
    match sort with
    | T_array.SArray (T_int.SInt, T_int.SInt) when !index_map_join_candidates
      ->
        let free u = Set.is_empty (Set.inter (Term.tvs_of u) bound) in
        (* [collect] does not look under a binder, and here both the
           concatenations (under the goal's own universal) and the free maps
           (under the premises' existentials) are found there: this one
           enters binders and keeps a found term none of whose variables a
           binder met on the way binds *)
        let collect_free phi ~f =
          let acc = ref [] in
          let rec term inner t =
            (match f t with
            | Some x when Set.is_empty (Set.inter (Term.tvs_of x) inner) ->
                acc := x :: !acc
            | _ -> ());
            match t with
            | Term.FunApp (T_bool.Formula p, [], _) -> formula inner p
            | Term.FunApp ((T_array.ALambda _ | T_bool.Formula _), _, _)
            | Term.LetTerm _ | Term.Var _ ->
                ()
            | Term.FunApp (_, args, _) -> List.iter args ~f:(term inner)
          and formula inner = function
            | Formula.Atom (Atom.App (_, args, _), _) ->
                List.iter args ~f:(term inner)
            | Formula.Atom _ -> ()
            | Formula.UnaryOp (_, p, _) -> formula inner p
            | Formula.BinaryOp (_, p, q, _) ->
                formula inner p;
                formula inner q
            | Formula.Bind (_, senv, p, _) ->
                formula
                  (Set.union inner (Set.Poly.of_list (List.map senv ~f:fst)))
                  p
            | Formula.LetRec _ | Formula.LetFormula _ -> ()
          in
          formula Set.Poly.empty phi;
          List.rev !acc
        in
        let prefix_lengths u =
          match u with
          | Term.FunApp (T_seq.SqConcat se, _, _) ->
              let ops = flatten_concat u in
              List.init
                (List.length ops - 1)
                ~f:(fun p -> norm (len_of se (List.take ops (p + 1))))
          | _ -> []
        in
        let is_concat = function
          | Term.FunApp (T_seq.SqConcat _, _, _) -> true
          | _ -> false
        in
        (* the inner sequences: free concatenations the binder's body reads
           at a read of the binder, [nth (p ++ q) x[i]]; the shift is the
           length of a proper prefix of one of them.  Only for a block of one
           binder, which is what the goal's index map is once its inner
           sequence has been instantiated; a lemma's block, which binds both
           maps it joins, gets none, as its own maps are what it is
           instantiated at *)
        let x_of_binder =
          match Set.to_list bound with [ x ] -> Some x | _ -> None
        in
        let inner_seqs =
          match x_of_binder with
          | None -> []
          | Some x ->
              collect_free body ~f:(function
                | Term.FunApp
                    ( T_seq.SqNth _,
                      [ u; Term.FunApp (T_array.ASelect _, [ Term.Var (y, _, _); _ ], _) ],
                      _ )
                  when is_concat u && free u && Ast.Ident.tvar_equal x y ->
                    Some u
                | _ -> None)
              |> dedup_terms
        in
        (* the visited sequences: every other free concatenation of the body;
           the cut is the length of a proper prefix of one of them *)
        let visited =
          if List.is_empty inner_seqs then []
          else
            collect_free body ~f:(function
              | Term.FunApp (T_seq.SqConcat _, _, _) as u
                when free u && not (List.mem inner_seqs u ~equal:Stdlib.( = ))
                ->
                  Some u
              | _ -> None)
            |> dedup_terms
        in
        let maps =
          if List.is_empty visited then []
          else
            collect_free source ~f:(fun t ->
                match t with
                | Term.Var _ when Stdlib.( = ) (Term.sort_of t) sort && free t
                  ->
                    Some t
                | _ -> None)
            |> dedup_terms
        in
        let join g h c d =
          let k = Ast.Ident.mk_fresh_tvar () in
          let kv = Term.mk_var k T_int.SInt in
          let rd a i = T_array.mk_select T_int.SInt T_int.SInt a i in
          T_array.mk_lambda (k, T_int.SInt) T_int.SInt
            (T_bool.ifte (Formula.lt kv c) (rd g kv)
               (T_int.mk_add (rd h (T_int.mk_sub kv c)) d))
        in
        List.concat_map visited ~f:(fun v ->
            List.concat_map (prefix_lengths v) ~f:(fun c ->
                List.concat_map inner_seqs ~f:(fun u ->
                    List.concat_map (prefix_lengths u) ~f:(fun d ->
                        List.concat_map maps ~f:(fun g ->
                            List.filter_map maps ~f:(fun h ->
                                if Stdlib.( = ) g h then None
                                else Some (join g h c d)))))))
        |> List.filter_map ~f:(guard_array_witness ~body x)
        |> fun ts -> List.take ts max_index_map_join_candidates
    | _ -> []
  in
  let rec inst ~keep ~reads ~units ~offsets ~chains ~source phi =
    match phi with
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
        Formula.mk_binop op
          (inst ~keep ~reads ~units ~offsets ~chains ~source p)
          (inst ~keep ~reads ~units ~offsets ~chains ~source q)
    | Formula.Bind (Formula.Exists, senv, _, _)
      when !instantiate_element_binders
           && List.exists senv ~f:(fun (_, s) -> is_array_sort s)
           && Stdlib.( <> ) phi
                (Ast.Evaluator.elim_onepoint_and_split_binders phi) ->
        (* the one-point rule first: an array the body equates to a term is
           that term, exactly *)
        inst ~keep ~reads ~units ~offsets ~chains ~source
          (Ast.Evaluator.elim_onepoint_and_split_binders phi)
    | Formula.Bind (Formula.Exists, senv, _, _)
      when keep_scalar && scalar_only senv ->
        phi
    | Formula.Bind (Formula.Exists, senv, body, _) ->
        if
          not
            (List.for_all senv ~f:(fun (_, s) ->
                 Stdlib.( = ) s T_int.SInt || is_element_sort s
                 || is_array_sort s
                 || (!bool_binder_candidates && Stdlib.( = ) s T_bool.SBool)))
        then if keep then phi else Formula.mk_false ()
        else
          let bound = Set.Poly.of_list (List.map senv ~f:fst) in
          let choices =
            Common.PhaseTime.with_phase "int-candidates" @@ fun () ->
            List.map senv ~f:(fun (x, s) ->
                List.map
                  (if is_element_sort s then
                     element_candidates ~chains ~bound x body
                   else if Stdlib.( = ) s T_bool.SBool then
                     [ T_bool.mk_true (); T_bool.mk_false () ]
                   else if is_array_sort s then
                     array_candidates ~source ~bound ~body x s
                   else candidates ~reads ~units ~offsets ~source ~bound x body)
                  ~f:(fun t -> (x, t)))
          in
          if List.exists choices ~f:List.is_empty then
            if keep then phi else Formula.mk_false ()
          else
            let instances =
              Common.PhaseTime.with_phase "int-instances" @@ fun () ->
              instantiated_with_memo ~phi ~choices ~budget @@ fun () ->
              instances_within ?budget
                (product ~limit:max_int_instances choices)
                ~build:(fun sub ->
                  Formula.subst (Map.Poly.of_alist_exn sub) body)
            in
            observe "int"
              (List.map2_exn senv choices ~f:(fun (x, _) c -> (x, List.length c)))
              instances;
            (* with [keep], the existential itself beside its instances,
               an equivalent formula, so that the nested round can offer
               it the terms the first round's instances introduce *)
            Formula.or_of (if keep then phi :: instances else instances)
    | _ -> phi
  in
  let rec drop phi =
    match phi with
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
        Formula.mk_binop op (drop p) (drop q)
    | Formula.Bind (Formula.Exists, senv, _, _)
      when keep_scalar && scalar_only senv ->
        phi
    | Formula.Bind (Formula.Exists, _, _, _) -> Formula.mk_false ()
    | _ -> phi
  in
  let base = Common.PhaseTime.with_phase "int-skolemize" @@ fun () -> skolemize phi in
  let pass ?(keep = false) ?(target = base) source =
    Common.PhaseTime.with_phase "int-pass" @@ fun () ->
    let reads =
      collect source ~f:(function
        | Term.FunApp (T_seq.SqNth _, [ s; u ], _) -> Some (s, u)
        | _ -> None)
    in
    (* each read once, first occurrences in order: every use below
       ([candidates]' positions read off them, [positions]) keeps the first
       occurrence of what it builds, and a repeated read builds only what its
       first occurrence built, so the candidates are the same; the nested
       pass's source holds the first pass's instances, which repeat the
       premises' reads once per instance, and [candidates] scans every read
       for every binder *)
    let reads = if !instantiate_int_dedup_reads then dedup_terms reads else reads in
    let units =
      dedup_terms
      @@ collect source ~f:(function
        | Term.FunApp (T_seq.SqUnit _, [ e ], _)
          when Stdlib.( = ) (Term.sort_of e) T_int.SInt ->
            Some e
        | _ -> None)
    in
    (* the positions [t - len u] and [t + len u], with [t] an index or an
       extraction bound read outside every binder (reads first) and [u] a
       sequence whose length occurs there; nothing unless switched on *)
    let offsets =
      if not !offset_int_candidates then []
      else
        let is_literal = function
          | Term.FunApp (T_int.Int _, [], _) -> true
          | _ -> false
        in
        let positions =
          dedup_terms
          @@ List.filter ~f:(Fn.non is_literal)
          @@ List.map reads ~f:snd
             @ List.concat
                 (collect source ~f:(function
                   | Term.FunApp (T_seq.SqExtract _, [ _; o; l ], _) ->
                       Some [ o; l ]
                   | _ -> None))
        in
        let lens =
          dedup_terms
          @@ collect source ~f:(function
            | Term.FunApp (T_seq.SqLen se, [ u ], _) -> Some (se, u)
            | _ -> None)
        in
        let lens =
          if not !offset_int_candidates_chain_only then lens
          else
            let operands = chain_operands base in
            List.filter lens ~f:(fun (_, u) ->
                List.mem operands u ~equal:Stdlib.( = ))
        in
        dedup_terms
        @@ List.concat_map positions ~f:(fun t ->
            List.concat_map lens ~f:(fun (se, u) ->
                [
                  norm (T_int.mk_sub t (T_seq.mk_len se u));
                  norm (T_int.mk_add t (T_seq.mk_len se u));
                ]))
    in
    (* each offset with its free variables, computed when first asked *)
    let offsets = List.map offsets ~f:(fun t -> (t, lazy (Term.tvs_of t))) in
    let chains = chains_of source in
    let r =
      Common.PhaseTime.with_phase "int-inst" @@ fun () ->
      inst ~keep ~reads ~units ~offsets ~chains ~source target
    in
    Common.PhaseTime.with_phase "int-skolemize" @@ fun () -> skolemize r
  in
  let first = pass ~keep:(nested && keep_first) base in
  let source = Formula.mk_and base first in
  let r = if nested then pass ~target:first source else pass source in
  Common.PhaseTime.with_phase "int-drop" @@ fun () -> drop (skolemize r)

(* Whether each piece asked by [prove_valid] and [prove_valid_deep] has its
   positive universals replaced by fresh free variables
   ([skolemize_positive_universals]) before any of its forms is built.  Set by
   the coordinator from its configuration; process-wide, as
   [instantiate_element_binders] is. *)
let skolemize_positive_universals_before_instantiation = ref false

(** [phi], in negation normal form, with every universal reached from the
    root through conjunctions, disjunctions and other such universals alone
    replaced by its body with its variables renamed to fresh free variables.
    Nothing under an existential, a negation, an implication, an [iff]/[xor],
    a let or an embedded formula term is touched.

    Contract, for VALIDITY only: [phi] is valid exactly when the result is.
    Such a universal can be moved out to the root over the conjunctions and
    disjunctions around it (its variables occur nowhere else once renamed),
    and a formula [forall x. psi] is valid exactly when [psi[c/x]] is, [c]
    fresh.  Nothing else may be read: the result is not equivalent to [phi]
    in a model, so a countermodel of it (or of anything built from it) says
    nothing about [phi] beyond what a countermodel of [phi]'s matrix would.
    Each occurrence gets its own fresh variables: two different universals of
    one disjunction must not share them, as [forall x. A(x) \/ forall y. B(y)]
    is weaker than [forall x. A(x) \/ B(x)].

    What it buys: [instantiate] draws its candidate terms only from terms
    that mention no enclosing binder, so a clause whose conclusion is
    [forall a b. P(a) /\ Q(b) => exists s. R(s)] -- or whose premise is an
    existential, which negation normal form turns into such a universal --
    never offers [a ++ b], nor the instance of a premise law at [(a, b)] that
    would write it, as a witness for [s]; with [a] and [b] free both are
    candidates. *)
let skolemize_positive_universals phi =
  let rec go phi =
    match phi with
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
        Formula.mk_binop op (go p) (go q)
    | Formula.Bind (Formula.Forall, senv, body, _) ->
        let sub =
          List.map senv ~f:(fun (x, s) ->
              (x, Term.mk_var (Ast.Ident.mk_fresh_tvar ()) s))
        in
        go (Formula.subst (Map.Poly.of_alist_exn sub) body)
    | _ -> phi
  in
  go phi

(* Whether each piece has its cancellation-forced sequence binders
   eliminated ([cancel_forced_sequence_binders]) before any of its forms is
   built.  Set by the coordinator from its configuration; process-wide, as
   the switch above is. *)
let cancel_forced_sequence_binders_before_instantiation = ref false

let eq_sides = function
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _) ->
      Some (a, b)
  | _ -> None

let neq_sides = function
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ a; b ], _), _)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _),
        _ ) ->
      Some (a, b)
  | _ -> None

(** [piece], a disjunction, with every sequence binder [x] of an existential
    that the piece's own disequations force eliminated by its forced value.
    The binder is forced when the existential's body has a top-level conjunct
    [p ++ x = q] (either side; [x ++ p = q] likewise) and the piece has a
    top-level disjunct [p ++ u != q] ([u ++ p != q] respectively; either
    side), where [p], [q] and [u] mention no variable bound at the
    existential, the operands being compared modulo associativity of
    concatenation and the empty sequence.  The existential then becomes its
    instance at [u], still quantified over its other binders; this is
    repeated while some binder is forced, so an instance can force the next.

    Contract: the result is EQUIVALENT to [piece] in every model, not only a
    strengthening.  In a model where [p ++ u = q] holds, the conjunct gives
    [p ++ x = p ++ u], which by cancellation of a common prefix ([s ++ v =
    s ++ w] iff [v = w]; of a common suffix likewise) forces [x = u] for every
    value of the binders around, since [p], [q] and [u] do not depend on
    them; so the existential is equivalent there to its instance at [u].  In
    a model where [p ++ u = q] fails the disjunct [p ++ u != q] makes both
    [piece] and the result true.  Equivalence holds pointwise under the
    disjunct's failure, so the replacement is sound whatever the polarity of
    the position and whatever connectives and binders it is reached
    through; a binder shadowing a variable of [p], [q] or [u] is excluded by
    the bound check, and inner binders are renamed by the (capture-avoiding)
    substitution.

    What it buys: a premise [exists s1 s2 s3. p1 ++ s2 = q1 /\ p2 ++ s3 = q2
    /\ ...], whose disequations the clause states as other disjuncts, had its
    three sequence binders offered 4, 8 and 8 candidates, 32 instances kept,
    each then instantiated over integers; on a Rust-derived clause that one
    existential was most of a two-megabyte question.  Substitution of a
    disequated definition misses it because [q] is a tuple projection, not a
    variable. *)
let cancel_forced_sequence_binders piece =
  let diseqs =
    List.filter_map (Formula.disjuncts_list_of piece) ~f:neq_sides
    |> List.concat_map ~f:(fun (a, b) -> [ (a, b); (b, a) ])
    |> List.map ~f:(fun (a, b) -> (flatten_concat a, flatten_concat b))
  in
  let disjoint t bound = Set.is_empty (Set.inter (Term.tvs_of t) bound) in
  let rec is_prefix p l =
    match (p, l) with
    | [], _ -> Some l
    | x :: p', y :: l' when Stdlib.( = ) x y -> is_prefix p' l'
    | _ -> None
  in
  let is_var x = function
    | Term.Var (y, _, _) -> Ast.Ident.tvar_equal x y
    | _ -> false
  in
  (* the value one conjunct forces [x] to, with [x] the last operand of one
     side ([left], cancelling a common prefix) or its first ([not left],
     cancelling a common suffix) *)
  let forced ~bound x se conj =
    let side ~left ops q =
      match ops with
      | [] -> None
      | _ ->
          let at_end = if left then List.last_exn ops else List.hd_exn ops in
          let p = if left then List.drop_last_exn ops else List.tl_exn ops in
          if
            (not (is_var x at_end))
            || not (List.for_all p ~f:(fun t -> disjoint t bound))
          then None
          else
            List.find_map diseqs ~f:(fun (a', b') ->
                if not (Stdlib.( = ) b' q) then None
                else
                  let rest =
                    if left then is_prefix p a'
                    else
                      Option.map ~f:List.rev
                        (is_prefix (List.rev p) (List.rev a'))
                  in
                  match rest with
                  | Some us ->
                      let u = concat_of se us in
                      if disjoint u bound then Some u else None
                  | None -> None)
    in
    match eq_sides conj with
    | None -> None
    | Some (a, b) ->
        List.find_map [ (a, b); (b, a) ] ~f:(fun (lhs, rhs) ->
            if not (disjoint rhs bound) then None
            else
              let ops = flatten_concat lhs and q = flatten_concat rhs in
              match side ~left:true ops q with
              | Some u -> Some u
              | None -> side ~left:false ops q)
  in
  let rec go ~bound phi =
    match phi with
    | Formula.UnaryOp (Formula.Not, p, _) -> Formula.mk_neg (go ~bound p)
    | Formula.BinaryOp
        (((Formula.And | Formula.Or | Formula.Imply) as op), p, q, _) ->
        Formula.mk_binop op (go ~bound p) (go ~bound q)
    | Formula.Bind (Formula.Exists, senv, body, _) ->
        let bound =
          Set.union bound (Set.Poly.of_list (List.map senv ~f:fst))
        in
        let rec resolve senv body =
          match
            List.find_map senv ~f:(fun (x, s) ->
                match elem_of_seq s with
                | None -> None
                | Some se ->
                    List.find_map (Formula.conjuncts_list_of body)
                      ~f:(forced ~bound x se)
                    |> Option.map ~f:(fun u -> (x, u)))
          with
          | None -> Formula.mk_bind_if_bounded Formula.Exists senv body
          | Some (x, u) ->
              resolve
                (List.filter senv ~f:(fun (y, _) ->
                     not (Ast.Ident.tvar_equal x y)))
                (Formula.subst (Map.Poly.singleton x u) body)
        in
        resolve senv (go ~bound body)
    | Formula.Bind (((Formula.Forall | Formula.Random _) as b), senv, body, _)
      ->
        let bound =
          Set.union bound (Set.Poly.of_list (List.map senv ~f:fst))
        in
        Formula.mk_bind b senv (go ~bound body)
    | _ -> phi
  in
  if List.is_empty diseqs then piece else go ~bound:Set.Poly.empty piece

(** [piece] as the forms of [prove_valid] and [prove_valid_deep] start from:
    [skolemize_positive_universals] applied when its switch is on, then
    [cancel_forced_sequence_binders] when its switch is on, once per piece,
    so that every form of the piece names its fresh variables alike; [piece]
    itself when both are off. *)
let prepare_piece piece =
  let piece =
    if !skolemize_positive_universals_before_instantiation then
      skolemize_positive_universals piece
    else piece
  in
  if !cancel_forced_sequence_binders_before_instantiation then
    cancel_forced_sequence_binders piece
  else piece

(* Whether [prove_valid] also asks each piece's [witness_form], after every
   other form.  Set by the coordinator from its configuration; process-wide,
   as [instantiate_element_binders] is. *)
let witness_forms = ref false

(* the variables of [phi] that occur outside every array lambda (entering
   formulas embedded in terms) *)
let tvs_outside_lambdas phi =
  let acc = ref Set.Poly.empty in
  let rec term = function
    | Term.Var (x, _, _) -> acc := Set.add !acc x
    | Term.FunApp (T_array.ALambda _, _, _) -> ()
    | Term.FunApp (T_bool.Formula p, [], _) -> formula p
    | Term.FunApp (_, args, _) -> List.iter args ~f:term
    | Term.LetTerm (_, _, def, body, _) ->
        term def;
        term body
  and formula = function
    | Formula.Atom (Atom.App (_, args, _), _) -> List.iter args ~f:term
    | Formula.Atom _ -> ()
    | Formula.UnaryOp (_, p, _) -> formula p
    | Formula.BinaryOp (_, p, q, _) ->
        formula p;
        formula q
    | Formula.Bind (_, _, p, _) -> formula p
    | Formula.LetRec _ | Formula.LetFormula _ -> ()
  in
  formula phi;
  !acc

(** A strengthening of [phi] shaped for the solver's own instantiation
    (e-matching).  After the exact rewrites
    ([Evaluator.elim_onepoint_and_split_binders]) have written a witness
    array as a lambda over the variables it depends on, two steps at every
    existential of the negation normal form:
    - a bound variable occurring only inside array lambdas is replaced by a
      fresh free variable.  This STRENGTHENS the formula:
      [forall zs. exists x. psi(zs, x)] becomes [psi(zs, y)] with [y] free,
      whose validity is [forall y zs. psi(zs, y)], which implies the
      original (take [x := y] for any [y]).  What it buys: the solver is no
      longer asked for an instance of a variable no trigger can bind -- the
      part of a pointwise-defined array outside its range, which any value
      serves;
    - an integer bound variable [x] occurring, outside every lambda, in an
      argument [t] of a constructor or in an array index, where [t] is not
      [x] itself but isolates it with coefficient one ([x - 1], say), is
      renamed by [x := e(m)] for a fresh bound [m], [e] solving [t = m] for
      [x].  With coefficient one, [m |-> e(m)] is a bijection of the
      integers, so the step is EXACT; the argument then reads [m] and can be
      matched against a ground term, which an arithmetic term cannot.
    Every step is exact or strengthens an existential at positive polarity
    (negation normal form has no other), so a proof that the result is
    valid is a proof that [phi] is valid.  Nothing else may be read from it:
    a countermodel of the result need not be one of [phi]. *)
let witness_form phi =
  (* integer arithmetic in a linear normal form, simplified so that
     [(1 - (0 - m)) - 1] reads [m] rather than [m * 1]; anything outside
     linear integer arithmetic is kept *)
  let norm_arith t =
    match t with
    | Term.FunApp ((T_int.Add | T_int.Sub | T_int.Neg), _, _) -> (
        try
          Ast.Evaluator.simplify_term
          @@ Ast.AffineTerm.mk_int_term
               (Ast.Normalizer.linear_int_monomials_of (Ast.Value.Int Z.one) t)
        with exn_ when not (Timer.is_async exn_) -> t)
    | _ -> t
  in
  let rec int_args acc t =
    match t with
    | Term.FunApp (T_array.ALambda _, _, _) -> acc
    | Term.FunApp (((T_dt.DTCons _ | T_array.ASelect _) as sym), args, _) ->
        let here =
          List.filteri args ~f:(fun k a ->
              (match sym with T_array.ASelect _ -> k = 1 | _ -> true)
              && Stdlib.( = ) (Term.sort_of a) T_int.SInt
              && not (Term.is_var a))
        in
        List.fold args ~init:(acc @ here) ~f:int_args
    | Term.FunApp (T_bool.Formula _, _, _) -> acc
    | Term.FunApp (_, args, _) -> List.fold args ~init:acc ~f:int_args
    | _ -> acc
  in
  let rec atoms_terms acc = function
    | Formula.Atom (Atom.App (_, args, _), _) -> acc @ args
    | Formula.Atom _ -> acc
    | Formula.UnaryOp (_, p, _) -> atoms_terms acc p
    | Formula.BinaryOp (_, p, q, _) -> atoms_terms (atoms_terms acc p) q
    | Formula.Bind (_, _, p, _) -> atoms_terms acc p
    | Formula.LetRec _ | Formula.LetFormula _ -> acc
  in
  let rec go phi =
    match phi with
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
        Formula.mk_binop op (go p) (go q)
    | Formula.Bind (Formula.Forall, senv, body, info) ->
        Formula.mk_bind_if_bounded ~info Formula.Forall senv (go body)
    | Formula.Bind (Formula.Exists, senv, body, info) ->
        let body = go body in
        let outside = tvs_outside_lambdas body in
        let used = Formula.fvs_of body in
        let senv, sub =
          List.fold senv ~init:([], []) ~f:(fun (keep, sub) (x, s) ->
              if Set.mem used x && not (Set.mem outside x) then
                (keep, (x, Term.mk_var (Ast.Ident.mk_fresh_tvar ()) s) :: sub)
              else ((x, s) :: keep, sub))
        in
        let senv = List.rev senv in
        let body = Formula.subst (Map.Poly.of_alist_exn sub) body in
        let args = List.fold (atoms_terms [] body) ~init:[] ~f:int_args in
        let senv, body =
          List.fold senv ~init:([], body) ~f:(fun (keep, body) (x, s) ->
              if Stdlib.( <> ) s T_int.SInt then ((x, s) :: keep, body)
              else
                let occurs t = Set.mem (Term.tvs_of t) x in
                let is_target = function
                  | Term.Var (y, _, _) -> Ast.Ident.tvar_equal x y
                  | _ -> false
                in
                let m = Ast.Ident.mk_fresh_tvar () in
                match
                  List.find_map args ~f:(fun t ->
                      if occurs t then
                        Ast.Evaluator.isolate_target ~is_target ~occurs t
                          (Term.mk_var m T_int.SInt)
                      else None)
                with
                | Some e ->
                    ( (m, s) :: keep,
                      Formula.map_term ~f:norm_arith
                        (Formula.subst (Map.Poly.singleton x e) body) )
                | None -> ((x, s) :: keep, body))
        in
        Formula.mk_bind_if_bounded ~info Formula.Exists (List.rev senv) body
    | _ -> phi
  in
  go
  @@ Ast.Evaluator.elim_onepoint_and_split_binders
  @@ Ast.Evaluator.simplify (Formula.nnf_of phi)

(* Whether [prove_valid] also asks each piece's [drop_array_hypotheses_form],
   after every other form, the witness form included.  Set by the coordinator
   from its configuration; process-wide, as [witness_forms] is. *)
let drop_array_hypotheses = ref false

(** [Some] strengthening of [phi] with the disjuncts of its negation normal
    form that read as universally quantified hypotheses over arrays or
    sequences removed, and [None] when there is no such disjunct (or nothing
    else is left), so that no question is asked twice.

    The test, on each top-level disjunct [d] of the negation normal form
    (after the exact rewrites [Evaluator.elim_onepoint_and_split_binders]):
    [d] is dropped exactly when it is an existential binding at least one
    variable of array or sequence sort AND a universal quantifier occurs
    somewhere in its body (formulas embedded in terms included).  That is
    the shape a premise [forall a i. H(a, i) -> exists j. G(a, j)] takes
    once negated -- [exists a i. H(a, i) /\ forall j. not G(a, j)], an
    exists-forall alternation the solver's instantiation cannot decide.  An
    existential over an array whose body is quantifier-free or existential
    only (a premise over a witness sequence fixed pointwise, say) is kept:
    the solver decides such a disjunct by e-matching, and on the input this
    form was built for such disjuncts are needed for validity -- dropping
    them as well turns a valid question into one with a countermodel.  The
    goal is kept whenever it binds no array or sequence at an
    exists-forall alternation; a goal that does (an array witness still
    bound around a universal) is dropped with the hypotheses, the form is
    then not valid, and nothing is lost but the question.

    Soundness: in negation normal form a validity question is a disjunction,
    and removing a disjunct can only make it false in more models, so the
    result implies [phi]; a proof that it is valid is a proof that [phi] is.
    The converse fails, so only a proof may be read from it, never a
    countermodel.  What it buys: a hypothesis irrelevant to why the piece
    holds, but quantified over an array at an alternation, made the solver
    give up on a piece that it proves at once without it. *)
let drop_array_hypotheses_form phi =
  let binds_collection =
    List.exists ~f:(fun (_, s) ->
        Term.is_array_sort s || Option.is_some (elem_of_seq s))
  in
  let rec has_forall_term = function
    | Term.Var _ -> false
    | Term.FunApp (T_bool.Formula p, args, _) ->
        has_forall p || List.exists args ~f:has_forall_term
    | Term.FunApp (_, args, _) -> List.exists args ~f:has_forall_term
    | Term.LetTerm (_, _, def, body, _) ->
        has_forall_term def || has_forall_term body
  and has_forall = function
    | Formula.Atom (Atom.App (_, args, _), _) ->
        List.exists args ~f:has_forall_term
    | Formula.Atom _ -> false
    | Formula.UnaryOp (_, p, _) -> has_forall p
    | Formula.BinaryOp (_, p, q, _) -> has_forall p || has_forall q
    | Formula.Bind (Formula.Forall, _, _, _) -> true
    | Formula.Bind (_, _, p, _) -> has_forall p
    | Formula.LetRec _ | Formula.LetFormula _ -> false
  in
  let is_array_hypothesis = function
    | Formula.Bind (Formula.Exists, senv, body, _) ->
        binds_collection senv && has_forall body
    | _ -> false
  in
  let disjuncts =
    Formula.disjuncts_list_of
    @@ Ast.Evaluator.elim_onepoint_and_split_binders
    @@ Ast.Evaluator.simplify (Formula.nnf_of phi)
  in
  let kept = List.filter disjuncts ~f:(Fn.non is_array_hypothesis) in
  if List.length kept = List.length disjuncts || List.is_empty kept then None
  else Some (Formula.or_of kept)

(** [Some] strengthening of [phi] with every top-level disjunct of its
    negation normal form that binds a variable of array or sequence sort
    removed, whatever its body is, and [None] when there is no such disjunct
    or nothing else is left.  It differs from [drop_array_hypotheses_form] in
    dropping also the existentials whose body is quantifier-free: the
    negation of a premise lemma [forall h x y k. G(h, x, y, k)] over
    sequences.  Such a disjunct, handed to the solver, is a universally
    quantified axiom over sequences, which it may instantiate without end
    even when the piece holds without it (a length identity that only the
    ground disjuncts carry, say).

    Soundness: as for [drop_array_hypotheses_form], the result implies
    [phi], so only a proof may be read from it. *)
let ground_core_form phi =
  let binds_collection =
    List.exists ~f:(fun (_, s) ->
        Term.is_array_sort s || Option.is_some (elem_of_seq s))
  in
  let is_collection_binder = function
    | Formula.Bind (_, senv, _, _) -> binds_collection senv
    | _ -> false
  in
  let disjuncts =
    Formula.disjuncts_list_of
    @@ Ast.Evaluator.elim_onepoint_and_split_binders
    @@ Ast.Evaluator.simplify (Formula.nnf_of phi)
  in
  let kept = List.filter disjuncts ~f:(Fn.non is_collection_binder) in
  if List.length kept = List.length disjuncts || List.is_empty kept then None
  else Some (Formula.or_of kept)

(* ===== Chain-focused and associativity-matched forms (begin) =====

   Two further forms of a piece, each asked only after every other form of
   [prove_valid] has failed, and each a STRENGTHENING of the piece, so that a
   proof of validity of either is one of the piece and nothing else may be
   read from it.  Both work on the piece in negation normal form, where every
   binder is at positive polarity, and both write each existential that binds
   a sequence as chosen instances of it -- each instance implies the
   existential -- or, when no instance is chosen, as [false], which implies
   anything.  Existentials over other sorts and universals are left as they
   are, so the question may still be quantified over integers and elements;
   a universal over a sequence stays bound, and such a form is refused like
   any other that binds a sequence.

   What both buy is SIZE.  A goal about a relation [R] (an array read as a
   chain of [select]s) whose premises chain two applications [R(a, u, b)] and
   [R(b, w, c)], and a premise law stating transitivity
   [R(a, u, b) /\ R(b, w, c) => R(a, u ++ w, c)], is valid at one witness and
   one law instance; the plain instantiation offers that witness among up to
   ten candidates and the law at up to thirty-two tuples, and the solver was
   observed to leave the result undecided at 60 s where the question with
   the one witness and the one law instance is decided in a fraction of a
   second.

   - The chain-focused form ([chain_focus_forms]): for a positive sequence
     existential [exists x. ... R(a', x, c') ...] and a pair of ground
     applications [R(s, u, m)], [R(m, w, e)] of the piece (the chain
     [chain_concat_candidates_for] reads), [x] is instantiated at [u ++ w]
     alone, and a sequence existential that two of its body's applications
     of [R] match onto the pair (the negated law, in normal form) at the
     tuple the match gives alone.  One form per pair, pairs whose endpoints
     are the goal's own first, at most [max_focus_forms].
   - The associativity-matched form ([assoc_match_forms]): a positive
     sequence existential whose body applies [R] with argument [v ++ t] at
     the middle position ([v] bound by it) and a pair [R(a, u, b)],
     [R(b, w, c)] as above whose start matches the application's start and
     whose end matches its end (a bound end variable is bound to [c]): the
     operands of [u ++ w] are matched against [v ++ t] modulo associativity,
     [v] taking what is left once [t]'s operands are matched from the end,
     each of [t]'s operands matched structurally (a [unit e] binding [e]).
     The existential is instantiated at that match alone, and the law at the
     pair.  This is the re-establishment of a property stated over what an
     iterator has produced, at a state one step later: the witness is the
     longer prefix [u ++ w'], which the clause never writes.

   Each form is given twice: as built, with the integer quantifiers left to
   the solver, and then with them instantiated, reads of concatenations
   split, as [instantiate_deep] does after its sequence step.  Set by the
   coordinator from its configuration; process-wide, as the other switches
   of this module are. *)
let chain_focus_forms = ref false
let chain_assoc_match_forms = ref false
let max_focus_forms = 4
let max_law_instances = 4

let is_seq_sort s = Option.is_some (elem_of_seq s)

let or_of_nonempty = function [] -> None | fs -> Some (Formula.or_of fs)

(** the concatenation of [ts] nested to the right, [empty] for none *)
let concat_right se ts =
  match List.rev ts with
  | [] -> T_seq.mk_empty se
  | last :: ops ->
      List.fold ops ~init:last ~f:(fun acc op -> T_seq.mk_concat se op acc)

(** the applications of [phi] (as [select_chains] lists them) that mention
    only free variables of [phi] *)
let ground_apps phi =
  let free = Formula.tvs_of phi in
  List.filter (select_chains phi) ~f:(fun (h, args) ->
      List.for_all (h :: args) ~f:(fun t ->
          Set.is_subset (Term.tvs_of t) ~of_:free))

(** the pairs [(h, j, a1, a2)] of applications [h(a1)] and [h(a2)] of
    [apps] of one odd arity [2j + 1], [j > 0], whose middle argument is a
    sequence, with the arguments after the middle of [a1] those before the
    middle of [a2] (compared syntactically) *)
let chained_app_pairs apps =
  List.concat_map apps ~f:(fun (h, a1) ->
      let n = List.length a1 in
      let j = n / 2 in
      if n mod 2 = 0 || j = 0 || not (is_seq_sort (Term.sort_of (List.nth_exn a1 j)))
      then []
      else
        List.filter_map apps ~f:(fun (h', a2) ->
            if
              Stdlib.( = ) h h'
              && List.length a2 = n
              && List.equal Stdlib.( = ) (List.drop a1 (j + 1)) (List.take a2 j)
            then Some (h, j, a1, a2)
            else None))

(* Whether [match_pattern] also matches a concatenation modulo
   associativity (see [match_concat_operands]).  Set by the coordinator from
   its configuration ([matched_instance_assoc_open_no_unknown_query]);
   process-wide, as [matched_instance_forms] is. *)
let assoc_concat_matching = ref false

let is_concat_term = function
  | Term.FunApp (T_seq.SqConcat _, [ _; _ ], _) -> true
  | _ -> false

(** first-order matching of the pattern [p] against the term [t], the
    variables of [vars] being the pattern's; [sub] extended, or [None].
    With [assoc] (default [!assoc_concat_matching]), a pattern that is a
    concatenation and that does not match the concatenation [t]
    syntactically is matched modulo associativity of concatenation
    ([match_concat_operands]); a substitution found that way makes
    the instantiated pattern EQUAL to [t] in every model (both sides
    flatten to the same operands), so every instance it yields is an
    instance of the pattern's quantifier as any other is. *)
let rec match_pattern ?(assoc = !assoc_concat_matching) ~vars sub p t =
  let plain =
    match (p, t) with
    | Term.Var (v, _, _), _ when Set.mem vars v -> (
        match Map.Poly.find sub v with
        | Some t' -> if Stdlib.( = ) t' t then Some sub else None
        | None ->
            if Stdlib.( = ) (Term.sort_of p) (Term.sort_of t) then
              Some (Map.Poly.set sub ~key:v ~data:t)
            else None)
    | Term.FunApp (f, ps, _), Term.FunApp (g, ts, _)
      when Stdlib.( = ) f g && List.length ps = List.length ts ->
        List.fold2_exn ps ts ~init:(Some sub) ~f:(fun acc p t ->
            Option.bind acc ~f:(fun sub -> match_pattern ~assoc ~vars sub p t))
    | _ -> if Stdlib.( = ) p t then Some sub else None
  in
  match plain with
  | Some _ -> plain
  | None
    when assoc && is_concat_term p && is_concat_term t
         && Stdlib.( = ) (Term.sort_of p) (Term.sort_of t) ->
      match_concat_operands ~vars sub (flatten_concat p) (flatten_concat t)
  | None -> None

(** the operands [ps] of a flattened pattern concatenation matched in order
    against the operands [ts] of a flattened term: a sequence variable of
    [vars] stands for a run of one or more consecutive operands, the shortest
    run first; one already bound must equal the run its own operands flatten
    to; any other operand is matched against exactly one operand by
    [match_pattern].  The first match found, or [None].  Exact in the sense
    [match_pattern] states: the bound pattern and the term have the same
    operands in the same order.  Why neither an empty run nor a term that is
    not a concatenation: [s1 ++ s2] would then match every sequence term of
    the piece, with [s1] empty, and on a Rust-derived piece those matches
    crowded out of the per-existential cut the one a transitivity law needed,
    so that its matched form, proved with the switch off, was no longer
    proved. *)
and match_concat_operands ~vars sub ps ts =
  match ps with
  | [] -> if List.is_empty ts then Some sub else None
  | Term.Var (v, s, _) :: ps' when Set.mem vars v && Option.is_some (elem_of_seq s)
    -> (
      match Map.Poly.find sub v with
      | Some value ->
          let vs = flatten_concat value in
          let k = List.length vs in
          if
            List.length ts >= k
            && List.equal Stdlib.( = ) vs (List.take ts k)
          then match_concat_operands ~vars sub ps' (List.drop ts k)
          else None
      | None ->
          let se = Option.value_exn (elem_of_seq s) in
          List.find_map
            (List.range 1 (List.length ts + 1))
            ~f:(fun k ->
              match_concat_operands ~vars
                (Map.Poly.set sub ~key:v ~data:(concat_of se (List.take ts k)))
                ps' (List.drop ts k)))
  | p :: ps' -> (
      match ts with
      | [] -> None
      | t :: ts' ->
          Option.bind (match_pattern ~assoc:true ~vars sub p t) ~f:(fun sub ->
              match_concat_operands ~vars sub ps' ts'))

let match_patterns ~vars sub ps ts =
  if List.length ps <> List.length ts then None
  else
    List.fold2_exn ps ts ~init:(Some sub) ~f:(fun acc p t ->
        Option.bind acc ~f:(fun sub -> match_pattern ~vars sub p t))

(** [exists senv. body] instantiated by [sub] (a substitution of some of
    [senv]), the variables it leaves still bound; [None] when it leaves a
    sequence variable *)
let instance_of senv body sub =
  let rest = List.filter senv ~f:(fun (x, _) -> not (Map.Poly.mem sub x)) in
  if List.exists rest ~f:(fun (_, s) -> is_seq_sort s) then None
  else Some (Formula.mk_exists_if_bounded rest (Formula.subst sub body))

(** the instances of [exists senv. body] at which two applications of the
    pair's relation in [body] match the pair [h(a1)], [h(a2)] (the law
    instance the pair calls for), at most [max_law_instances] *)
let law_instances (h, _, a1, a2) senv body =
  let vars = Set.Poly.of_list (List.map senv ~f:fst) in
  let apps =
    List.filter (select_chains body) ~f:(fun (h', args) ->
        Stdlib.( = ) h h' && List.length args = List.length a1)
  in
  List.concat_map apps ~f:(fun (_, p1) ->
      List.filter_map apps ~f:(fun (_, p2) ->
          Option.bind
            (Option.bind (match_patterns ~vars Map.Poly.empty p1 a1) ~f:(fun sub ->
                 match_patterns ~vars sub p2 a2))
            ~f:(instance_of senv body)))
  |> List.dedup_and_sort ~compare:Stdlib.compare
  |> Fn.flip List.take max_law_instances

(** [phi] (in negation normal form) with every existential that binds a
    sequence replaced by [pick senv body] when that gives a formula, and by
    [false] otherwise; the picked formula is treated the same way.  A
    strengthening whenever each picked formula implies its existential. *)
let focus_seq_existentials ~pick phi =
  let rec go phi =
    match phi with
    | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
        Formula.mk_binop op (go p) (go q)
    | Formula.Bind (Formula.Exists, senv, body, _)
      when List.exists senv ~f:(fun (_, s) -> is_seq_sort s) -> (
        match pick senv body with Some f -> go f | None -> Formula.mk_false ())
    | Formula.Bind (((Formula.Exists | Formula.Forall) as b), senv, body, _) ->
        Formula.mk_bind b senv (go body)
    | _ -> phi
  in
  go phi

(** the positive existentials of [phi] (negation normal form) that bind a
    sequence, each with the variables bound around it *)
let seq_existentials phi =
  let acc = ref [] in
  let rec go ~bound = function
    | Formula.BinaryOp ((Formula.And | Formula.Or), p, q, _) ->
        go ~bound p;
        go ~bound q
    | Formula.Bind (((Formula.Exists | Formula.Forall) as b), senv, body, _) ->
        if
          Stdlib.( = ) b Formula.Exists
          && List.exists senv ~f:(fun (_, s) -> is_seq_sort s)
        then acc := (bound, senv, body) :: !acc;
        go ~bound:(Set.union bound (Set.Poly.of_list (List.map senv ~f:fst))) body
    | _ -> ()
  in
  go ~bound:Set.Poly.empty phi;
  List.rev !acc

let same_binders senv senv' =
  List.equal (fun (x, _) (y, _) -> Ast.Ident.tvar_equal x y) senv senv'

(** a focused form given as built and then with its integer binders
    instantiated and its reads of concatenations split *)
let focused_variants ?(keep_scalar = false) focused =
  let instantiated ~keep_scalar =
    lazy
      (Ast.Evaluator.simplify
      @@ Ast.Evaluator.rewrite_seq_read_over_concat
      @@ split_prefixes ~focus:true
      @@ instantiate_int ~equated:!nested_focus_forms
           ~nested:!nested_focus_forms ~keep_first:!nested_focus_forms
           ~keep_scalar
      @@ Ast.Evaluator.simplify
      @@ Formula.nnf_of (right_nest_concats (Lazy.force focused)))
  in
  [
    lazy (right_nest_concats (Lazy.force focused));
    instantiated ~keep_scalar:false;
  ]
  (* with [keep_scalar], a third variant: the second with the premise laws
     over opaque values kept quantified rather than dropped
     ([instantiate_int ~keep_scalar]).  Why: the second variant is
     quantifier-free, which is what lets the solver decide it, but a step
     that needs a law of an uninterpreted relation at a term only the
     instantiation creates (a history invariant carried from the start to
     the state after a call: transitivity through the pushed state) is then
     invalid as asked; with those laws kept the solver instantiates them
     itself, and the sequence and integer binders it does not handle are
     still instantiated.  Keeping a disjunct is exact, so the variant implies
     the focused form as the second does. *)
  @ if keep_scalar then [ instantiated ~keep_scalar:true ] else []

(* Whether the chain-focused form also fills the OTHER sequence binders of
   the existential it focuses, by the push witnesses [push_witnesses] reads
   off its body.  Set by the coordinator from its configuration
   ([chain_focus_push_witnesses_no_unknown_query]); process-wide, as
   [chain_focus_forms] is. *)
let chain_focus_push_witnesses = ref false

(** For the chain-focused existential [exists senv. body] of [piece] whose
    binder [x] is instantiated at the chain term [s ++ ...] ([s] the chain
    pair's first middle argument), instances of its OTHER sequence binders:
    a binder [y] of sort [Seq ey] that a conjunct of [body] reads at [x]'s
    length, [t = seq.nth y (seq.len x)] (either way round, [t] mentioning no
    variable of [senv]), is instantiated at [a ++ unit t], where [a] is a
    variable of sort [Seq ey] free in [piece] whose length a top-level
    disjunct of [piece] relates to [s]'s alone (the disjunct mentions
    [seq.len a] and [seq.len s] and no other variable; the first such
    disjunct), or failing that the [u] of a conjunct [seq.nth y 0 =
    seq.nth u 0] of [body] with [u] free of [senv].  [None] when some other
    sequence binder gets no instance.

    Why: a loop that keeps a history as several sequences restates it under
    one existential after each step, [exists s accs fs. R(iter, s, it') /\
    accs[len s] = acc' /\ fs[len s] = g' /\ ...], with [len accs = len s + 1]
    and [len fs = len s + 1].  The witness is the previous history pushed
    once -- [s0 ++ unit x], [accs0 ++ unit acc'], [fs0 ++ unit g'] -- and the
    three must come from the same previous history, which the premise's
    length equations [len accs0 = len s0 + 1] tie together: a clause that
    restates the invariant several times (one copy per path into the loop
    head) has several such histories, equal only at their ends.  The chain
    pair gives [s0 ++ unit x] alone, and an instance that leaves [accs] and
    [fs] bound is not formed, so without these the focused form drops the
    existential.

    Contract: each returned term is of its binder's sort and mentions no
    variable of [senv]; nothing is claimed of its meaning, since an instance
    of an existential at any terms implies it. *)
let push_witnesses ~piece ~x ~s senv body =
  let bound = Set.Poly.of_list (List.map senv ~f:fst) in
  let free = Formula.tvs_of piece in
  let closed t = Set.is_empty (Set.inter (Term.tvs_of t) bound) in
  let is_var v = function
    | Term.Var (y, _, _) -> Ast.Ident.tvar_equal v y
    | _ -> false
  in
  let len_of v = function
    | Term.FunApp (T_seq.SqLen _, [ a ], _) -> is_var v a
    | _ -> false
  in
  let rec subterms t =
    t
    :: (match t with
       | Term.FunApp (_, ts, _) -> List.concat_map ts ~f:subterms
       | _ -> [])
  in
  let mentions_len d v =
    Set.exists (Formula.terms_of d) ~f:(fun t ->
        List.exists (subterms t) ~f:(len_of v))
  in
  let eq_sides = function
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ l; r ], _), _) ->
        Some (l, r)
    | _ -> None
  in
  let conjuncts = Formula.conjuncts_list_of body in
  let last_elem y =
    List.find_map conjuncts ~f:(fun c ->
        Option.bind (eq_sides c) ~f:(fun (l, r) ->
            let read = function
              | Term.FunApp (T_seq.SqNth _, [ a; i ], _) ->
                  is_var y a && len_of x i
              | _ -> false
            in
            if read l && closed r then Some r
            else if read r && closed l then Some l
            else None))
  in
  let first_elem_seq y =
    List.find_map conjuncts ~f:(fun c ->
        Option.bind (eq_sides c) ~f:(fun (l, r) ->
            let at0 = function
              | Term.FunApp (T_seq.SqNth _, [ a; i ], _) when T_int.is_zero i ->
                  Some a
              | _ -> None
            in
            match (at0 l, at0 r) with
            | Some a, Some u when is_var y a && closed u -> Some u
            | Some u, Some a when is_var y a && closed u -> Some u
            | _ -> None))
  in
  let partner ey =
    match s with
    | Term.Var (sv, _, _) ->
        List.find_map (Formula.disjuncts_list_of piece) ~f:(fun d ->
            let vs = Formula.tvs_of d in
            if Set.length vs = 2 && Set.mem vs sv && mentions_len d sv then
              match Set.to_list (Set.remove vs sv) with
              | [ a ] when Set.mem free a && mentions_len d a ->
                  List.find_map
                    (Set.to_list (Formula.term_sort_env_of d))
                    ~f:(fun (v, srt) ->
                      if
                        Ast.Ident.tvar_equal v a
                        && Stdlib.( = ) srt (T_seq.mk_seq_sort ey)
                      then Some (Term.mk_var a srt)
                      else None)
              | _ -> None
            else None)
    | _ -> None
  in
  List.filter senv ~f:(fun (y, srt) ->
      (not (Ast.Ident.tvar_equal x y)) && is_seq_sort srt)
  |> List.map ~f:(fun (y, srt) ->
      let ey = Option.value_exn (elem_of_seq srt) in
      Option.bind (last_elem y) ~f:(fun t ->
          Option.map
            (match partner ey with Some a -> Some a | None -> first_elem_seq y)
            ~f:(fun a -> (y, T_seq.mk_concat ey a (T_seq.mk_unit ey t)))))
  |> Option.all

(** the chain-focused forms of [piece] (see above).  With [~pushed_only]
    (and [chain_focus_push_witnesses] set), instead only the variant with the
    opaque laws kept ([focused_variants ~keep_scalar]) of each focus whose
    existential [push_witnesses] filled, at most [max_pushed_forms] of them:
    the forms [piece_forms_with_first] asks first under that switch. *)
let max_pushed_forms = 2

let chain_focus_forms_of ?(pushed_only = false) piece =
  let piece = Formula.nnf_of piece in
  let pairs = chained_app_pairs (ground_apps piece) in
  (* the focused formula, and whether push witnesses filled its
     existential *)
  let focus_of (x, t, ((_, j, a1, _) as pair)) =
    let pushed = ref false in
    let f =
      focus_seq_existentials piece ~pick:(fun senv body ->
          if List.exists senv ~f:(fun (y, _) -> Ast.Ident.tvar_equal x y) then
            let sub = Map.Poly.singleton x t in
            let sub =
              if not !chain_focus_push_witnesses then sub
              else
                match
                  push_witnesses ~piece ~x ~s:(List.nth_exn a1 j) senv body
                with
                | Some (_ :: _ as binds) ->
                    pushed := true;
                    List.fold binds ~init:sub ~f:(fun m (y, w) ->
                        Map.Poly.set m ~key:y ~data:w)
                | Some [] | None -> sub
            in
            instance_of senv body sub
          else or_of_nonempty (law_instances pair senv body))
    in
    (f, !pushed)
  in
  let chosen =
    List.concat_map (seq_existentials piece) ~f:(fun (outer, senv, body) ->
        let bound = Set.union outer (Set.Poly.of_list (List.map senv ~f:fst)) in
        List.concat_map senv ~f:(fun (x, s) ->
            match elem_of_seq s with
            | None -> []
            | Some se ->
                List.concat_map (select_chains body) ~f:(fun (h, gargs) ->
                    List.concat
                    @@ List.mapi gargs ~f:(fun j g ->
                        match g with
                        | Term.Var (y, _, _) when Ast.Ident.tvar_equal x y ->
                            let gs = List.take gargs j
                            and ge = List.drop gargs (j + 1) in
                            if
                              List.exists (gs @ ge) ~f:(fun t ->
                                  not (Set.is_empty (Set.inter (Term.tvs_of t) bound)))
                            then []
                            else
                              List.filter_map pairs ~f:(fun ((h', j', a1, a2) as p) ->
                                  if Stdlib.( = ) h h' && j = j' then
                                    let t =
                                      concat_right se
                                        (flatten_concat (List.nth_exn a1 j)
                                        @ flatten_concat (List.nth_exn a2 j))
                                    in
                                    let first =
                                      List.equal Stdlib.( = ) (List.take a1 j) gs
                                      && List.equal Stdlib.( = )
                                           (List.drop a2 (j + 1)) ge
                                    in
                                    Some (first, (x, t, p))
                                  else None)
                        | _ -> []))))
  in
  let firsts, rest = List.partition_tf chosen ~f:fst in
  List.map (firsts @ rest) ~f:snd
  |> List.dedup_and_sort ~compare:(fun (x, t, _) (y, u, _) ->
      Stdlib.compare (Ast.Ident.name_of_tvar x, t) (Ast.Ident.name_of_tvar y, u))
  |> Fn.flip List.take max_focus_forms
  |> fun cs ->
  if pushed_only then
    if not !chain_focus_push_witnesses then []
    else
      List.filter_map cs ~f:(fun c ->
          let x, _, _ = c in
          let f, pushed = focus_of c in
          if pushed then (
            observe "chain-focus-push" [ (x, 1) ] [ f ];
            List.last (focused_variants ~keep_scalar:true (Lazy.from_val f)))
          else None)
      |> Fn.flip List.take max_pushed_forms
  else
    List.concat_map cs ~f:(fun c ->
        let x, _, _ = c in
        focused_variants
          (lazy
            (let f = fst (focus_of c) in
             observe "chain-focus" [ (x, 1) ] [ f ];
             f)))

(** the associativity-matched forms of [piece] (see above) *)
let assoc_match_forms_of piece =
  let piece = Formula.nnf_of piece in
  let pairs = chained_app_pairs (ground_apps piece) in
  let is_var v = function
    | Term.Var (y, _, _) -> Ast.Ident.tvar_equal v y
    | _ -> false
  in
  let matches (_, senv, body) =
    let vars = Set.Poly.of_list (List.map senv ~f:fst) in
    List.concat_map (select_chains body) ~f:(fun (h, pargs) ->
        let n = List.length pargs in
        let j = n / 2 in
        if n mod 2 = 0 || j = 0 then []
        else
          let ops = flatten_concat (List.nth_exn pargs j) in
          let heads =
            List.filter_map senv ~f:(fun (v, s) ->
                match (elem_of_seq s, ops) with
                | Some se, _ :: _ :: _ when is_var v (List.hd_exn ops) ->
                    Some (v, se, true, List.tl_exn ops)
                | Some se, _ :: _ :: _ when is_var v (List.last_exn ops) ->
                    Some (v, se, false, List.drop_last_exn ops)
                | _ -> None)
          in
          List.concat_map heads ~f:(fun (v, se, at_head, t) ->
              List.filter_map pairs ~f:(fun ((h', j', a1, a2) as pair) ->
                  if not (Stdlib.( = ) h h' && j = j') then None
                  else
                    let us =
                      flatten_concat (List.nth_exn a1 j)
                      @ flatten_concat (List.nth_exn a2 j)
                    in
                    let k = List.length t in
                    let m = List.length us - k in
                    if m < 0 then None
                    else
                      let vt, matched =
                        if at_head then (List.take us m, List.drop us m)
                        else (List.drop us k, List.take us k)
                      in
                      let sub =
                        Option.bind
                          (match_patterns ~vars Map.Poly.empty (List.take pargs j)
                             (List.take a1 j))
                          ~f:(fun sub ->
                            Option.bind
                              (match_patterns ~vars sub
                                 (List.drop pargs (j + 1))
                                 (List.drop a2 (j + 1)))
                              ~f:(fun sub -> match_patterns ~vars sub t matched))
                      in
                      Option.bind sub ~f:(fun sub ->
                          match_pattern ~vars sub (Term.mk_var v (T_seq.SSeq se))
                            (concat_right se vt))
                      |> Option.map ~f:(fun sub -> (m > 0, (senv, sub, pair))))))
    (* an existential that is itself the law for the pair is instantiated
       by [law_instances] in every form, and matching it here only repeats
       that instance *)
    |> List.filter ~f:(fun (_, (_, _, pair)) ->
        List.is_empty (law_instances pair senv body))
  in
  (* matches that give [v] some operand of the pair first: an empty [v] is
     a sound instance but restates a premise *)
  let nonempty, empty =
    List.partition_tf ~f:fst (List.concat_map (seq_existentials piece) ~f:matches)
  in
  List.map (nonempty @ empty) ~f:snd
  |> List.fold ~init:[] ~f:(fun acc ((senv, sub, _) as c) ->
      if
        List.exists acc ~f:(fun (senv', sub', _) ->
            same_binders senv senv' && Map.Poly.equal Stdlib.( = ) sub sub')
      then acc
      else c :: acc)
  |> List.rev
  |> Fn.flip List.take max_focus_forms
  |> List.concat_map ~f:(fun (senv0, sub, pair) ->
      focused_variants
        (lazy
          (let f =
             focus_seq_existentials piece ~pick:(fun senv body ->
                 if same_binders senv senv0 then instance_of senv body sub
                 else or_of_nonempty (law_instances pair senv body))
           in
           observe "assoc-match"
             (List.map (Map.Poly.keys sub) ~f:(fun x -> (x, 1)))
             [ f ];
           f)))

(* ===== Chain-focused and associativity-matched forms (end) ===== *)

(* ===== The matched-instance form (begin) =====

   Further forms of a piece, asked FIRST among the piece's forms when
   [matched_instance_forms] is set: the form below, the same with the
   existentials over no array or sequence kept beside their instances, and,
   for a piece after the first of its clause, the form of the piece with the
   earlier pieces as hypotheses ([with_earlier_pieces]) in two rounds.  In
   negation normal form every binder of
   a validity question is at positive polarity once its positive universals
   are skolemized, and each existential is either the negation of a premise
   (a lemma the program states, an invariant's universal) or a goal's
   witness.  The form replaces EVERY positive existential, whatever the sort
   of its binders, by the disjunction of its instances at the substitutions
   found by one round of first-order matching (E-matching without a solver):
   each subterm of the existential's body that mentions a binder is matched
   against each ground subterm of the piece -- a term all of whose variables
   are free in the piece, taken from the piece and from its reads of
   concatenations split ([Evaluator.rewrite_seq_read_over_concat]) -- and the
   matches of several subterms are combined where they agree
   ([matched_substitutions]), up to [max_matched_instances] complete ones
   (every binder given a term); an existential with none is replaced by
   [false].

   Sound for validity only, as the chain-focused forms are: an instance
   implies its existential and [false] implies anything, so the form implies
   the piece; a countermodel of the form says nothing about the piece.

   What it buys is a question with no quantifier over a sequence that holds
   exactly the lemma instances the goal's terms call for.  The shape it was
   built for: a goal about the [k]-th element of a concatenation [x ++ y]
   and of the joined chain [x' ++ y'[1..]], with a history lemma
   [forall h x y k. h ++ (x ++ y)[0..k] = ...] and a chain lemma
   [forall x y k. (x ++ y[1..])[k] = ...] among the premises.  The goal
   writes [h ++ (x ++ y)[0..k]] and [(x' ++ y'[1..])[k]] literally, so
   matching the lemmas' left-hand sides against them gives the instances;
   the premise universals over indices are matched at the goal's reads
   ([s[k]]) the same way.  The deep forms offer those instances among
   hundreds of others (a question of about half a megabyte that the solver
   did not decide in 20 s), and the ground core without them is not valid. *)

let matched_instance_forms = ref false

(* The largest estimated size, in formula nodes, of the instances one
   matched-instance form may build, when [Some n]; unbounded when [None].
   The estimate is the sum, over every existential the form instantiates,
   of its number of instances times its body's [Formula.ast_size], taken
   BEFORE the instances are built, so a form past the bound costs no more
   than the matching that chose its substitutions.  Such a form is not
   built: [matched_instance_form] raises [Matched_form_too_large] and the
   callers that ask the forms in order ([matched_forms],
   [prove_valid_deep]) skip it as they skip an undecided one.  Skipping a
   form loses a proof and never asserts anything, since every form only
   strengthens its piece.  Why a bound: on a Rust-derived piece of about
   43,000 characters whose existentials each matched a few dozen
   instances, the form reached three million characters and took 13-19 s
   to build, while every other matched form over the same corpus was under
   200,000 characters.  Set by the coordinator from its configuration;
   process-wide, as [matched_instance_forms] is. *)
let max_matched_form_size : int option ref = ref None

(* Whether [matched_instance_form] tests its size bound for an existential
   before ranking that existential's substitutions
   ([rank_by_ground_agreement]) rather than after.  The ranking only
   permutes the substitutions, so the number of instances the cuts after it
   keep -- and hence the estimate and whether the bound is passed -- is known
   before it: when the bound is passed the form raises [Matched_form_too_large]
   with the same estimate either way, and otherwise the ranking runs as
   before, so the result is the same; only the time to reach the raise
   changes.  Why: on a chain-join form whose simplified focused formula was
   1.5 million nodes, the ranking of 21 substitutions (each pattern of the
   existential's body substituted and looked up among the ground terms) took
   170 s of CPU before the bound, which two instances of that body pass at
   once, discarded the form.  Set by the coordinator; process-wide, as
   [max_matched_form_size] is. *)
let matched_bound_before_ranking = ref false

exception Matched_form_too_large

(* the estimate of the last matched-instance form built (or abandoned), for
   a census *)
let last_matched_form_estimate = ref 0

(** [form] forced, or [None] when it is a matched-instance form past
    [max_matched_form_size] *)
let skip_too_large form =
  lazy (try Some (Lazy.force form) with Matched_form_too_large -> None)

(* Whether [matched_instance_form] skips the substitution search of an
   existential met once its pass's instance budget ([per_pass]) is spent.
   Exact: with the budget spent, the general branch takes no substitution
   whatever the search returns ([List.take subs 0]), so the bound test, the
   estimate, the census line and the instances are those of an empty list,
   and the existential becomes [false] (or stays beside nothing, with
   [keep_all] or [keep_scalar]); the search itself draws no fresh name and
   changes no state the form reads.  So the form built is the same formula,
   with the same fresh names, and only the time to build it changes.  Why:
   on the elimination questions of a Rust-derived coroutine input, the words
   route spent 209 s, of which 146 s went to 10,790 searches made after
   their pass's budget of 64 instances was spent, against 35 s for the
   1,804 searches whose answer was used.
   Set by the preprocessor from its configuration; process-wide, as the
   other switches of this module are. *)
let skip_spent_budget_searches = ref false

(* how many searches [skip_spent_budget_searches] skipped, in this process;
   read by the tests *)
let skipped_spent_searches = ref 0

let max_matched_instances = 8
let max_partial_matches = 64
let max_matched_instances_per_pass = 64
let max_match_steps = 20000

(** the function applications of [phi] (and of [phi] with its reads of
    concatenations split) all of whose variables are free in [phi], other
    than embedded formulas: the applications [Formula.filtered_terms_of]
    visits (it does not enter an array lambda's body, and enters an embedded
    formula but not the arguments beside it) whose [Term.tvs_of] is a subset
    of [Formula.tvs_of phi].  The result is a sorted list without
    duplicates. *)
let ground_funapps_quadratic phi =
  let free = Formula.tvs_of phi in
  let f = function
    | Term.FunApp (T_bool.Formula _, _, _) -> false
    | Term.FunApp _ as t -> Set.is_subset (Term.tvs_of t) ~of_:free
    | _ -> false
  in
  Set.to_list
  @@ Set.union
       (Formula.filtered_terms_of ~f phi)
       (Formula.filtered_terms_of ~f
          (Ast.Evaluator.rewrite_seq_read_over_concat phi))

(* [ground_collect ~free ~acc phi] adds to [acc] the applications
   [Formula.filtered_terms_of ~f phi] returns for the test [f] of
   [ground_funapps_quadratic], each once per occurrence, in one bottom-up
   pass.  Each node's free variables outside [free] are computed once from
   its children's, following [Term.tvs_of], [Atom.tvs_of] and
   [Formula.tvs_of] case by case (an array lambda and a let remove their
   binder, a quantifier and a recursive definition theirs, an uninterpreted
   function variable counts unless it is a defined function); a node passes
   the test exactly when that set is empty, since [tvs t \ free] is empty iff
   [tvs t] is a subset of [free], and the set difference commutes with the
   binder removals.  Under an array lambda nothing is collected, as
   [filtered_terms_of] does not descend there, but the outside-[free]
   variables are still computed, since the lambda itself is tested.  The
   traversal is the tree, as [filtered_terms_of]'s is; the cost per node is
   one union of the children's outside-[free] sets, which hold only
   variables bound somewhere in [phi], instead of a whole [Term.tvs_of] of
   the node, which made the test quadratic in the nesting depth. *)
let ground_collect ~free ~acc phi =
  let outside x = not (Set.mem free x) in
  let union_list = function
    | [] -> Set.Poly.empty
    | [ s ] -> s
    | ss -> Set.Poly.union_list ss
  in
  let rec term ~collect t =
    match t with
    | Term.Var (x, _, _) ->
        if outside x then Set.Poly.singleton x else Set.Poly.empty
    | Term.FunApp (T_bool.Formula psi, args, _) ->
        union_list (formula ~collect psi :: List.map args ~f:(term ~collect:false))
    | Term.FunApp (T_array.ALambda ((x, _), _), args, _) ->
        let b =
          union_list
            (List.map args ~f:(fun a -> Set.remove (term ~collect:false a) x))
        in
        if collect && Set.is_empty b then acc := t :: !acc;
        b
    | Term.FunApp (fsym, args, _) ->
        let bs = List.map args ~f:(term ~collect) in
        let bs =
          match fsym with
          | FVar (x, _, _)
            when (not (Hash_set.Poly.mem defined_fvars x)) && outside x ->
              Set.Poly.singleton x :: bs
          | _ -> bs
        in
        let b = union_list bs in
        if collect && Set.is_empty b then acc := t :: !acc;
        b
    | Term.LetTerm (x, _, def, body, _) ->
        Set.union (term ~collect def) (Set.remove (term ~collect body) x)
  and atom ~collect = function
    | Atom.True _ | Atom.False _ -> Set.Poly.empty
    | Atom.App (pred, args, _) ->
        let bp =
          match pred with
          | Predicate.Fixpoint def ->
              Set.diff
                (formula ~collect def.body)
                (Set.add
                   (Set.Poly.of_list (List.map ~f:fst def.args))
                   (Ast.Ident.pvar_to_tvar def.name))
          | _ -> Set.Poly.empty
        in
        union_list (bp :: List.map args ~f:(term ~collect))
  and formula ~collect = function
    | Formula.Atom (a, _) -> atom ~collect a
    | Formula.UnaryOp (Formula.Not, p, _) -> formula ~collect p
    | Formula.BinaryOp (_, p, q, _) ->
        let bp = formula ~collect p in
        Set.union bp (formula ~collect q)
    | Formula.Bind (_, senv, p, _) ->
        Set.diff (formula ~collect p) (Set.Poly.of_list (List.map senv ~f:fst))
    | Formula.LetRec (funcs, p, _) ->
        let bp = formula ~collect p in
        Set.diff
          (union_list
             (bp
             :: List.map funcs ~f:(fun def ->
                 Set.diff
                   (formula ~collect def.body)
                   (Set.Poly.of_list (List.map ~f:fst def.args)))))
          (Set.Poly.of_list
             (List.map funcs ~f:(fun def -> Ast.Ident.pvar_to_tvar def.name)))
    | Formula.LetFormula (x, sort, def, body, info) ->
        (* as [Formula.filtered_terms_of] reads it: the let term over the
           body as a term; its free variables are [Formula.tvs_of]'s, the
           body as a term having the body's *)
        term ~collect
          (Term.mk_let_term ~info x sort def (T_bool.of_formula body))
  in
  ignore (formula ~collect:true phi : Ast.Ident.tvar Set.Poly.t)

(** [ground_funapps_quadratic phi], computed by [ground_collect] in one pass
    over [phi] and one over its read-split form: the same list. *)
let ground_funapps_one_pass phi =
  let free = Formula.tvs_of phi in
  let acc = ref [] in
  ground_collect ~free ~acc phi;
  ground_collect ~free ~acc (Ast.Evaluator.rewrite_seq_read_over_concat phi);
  Set.to_list (Set.Poly.of_list !acc)

(* Whether [ground_funapps] is [ground_funapps_one_pass] rather than
   [ground_funapps_quadratic]; the two return the same list.  Set by the
   coordinator from its configuration; process-wide, as
   [max_matched_form_size] is. *)
let ground_funapps_linear = ref false

(* the CPU seconds spent in [ground_funapps] and its calls, for a census *)
let ground_funapps_cpu = ref 0.
let ground_funapps_calls = ref 0

(* called with each formula [ground_funapps] is given, for a census that
   compares the two implementations on real inputs *)
let ground_funapps_observer : (Formula.t -> unit) option ref = ref None

let ground_funapps phi =
  Option.iter !ground_funapps_observer ~f:(fun f -> f phi);
  let t0 = Stdlib.Sys.time () in
  let r =
    if !ground_funapps_linear then ground_funapps_one_pass phi
    else ground_funapps_quadratic phi
  in
  let dt = Stdlib.Sys.time () -. t0 in
  ground_funapps_cpu := !ground_funapps_cpu +. dt;
  incr ground_funapps_calls;
  (* a row of the phase report (CPU seconds), named by the implementation,
     so a run shows which one it used and what it cost *)
  if !Common.PhaseTime.on then
    Common.PhaseTime.add
      (if !ground_funapps_linear then "ground-funapps-one-pass-cpu"
       else "ground-funapps-quadratic-cpu")
      dt;
  r

(* Whether [matched_substitutions] falls back to substitutions that leave
   scalar binders out (its [open_scalars]).  Set by the coordinator with
   [assoc_concat_matching]; process-wide. *)
let open_scalar_matches = ref false

(** the complete substitutions of [senv] found by matching the subterms of
    [body] that mention a variable of [senv] against [ground]: a depth-first
    search over the patterns, most constrained first (fewest matching ground
    terms), each pattern either taken at one of its matches that agrees with
    the substitution so far or skipped; at most [max_matched_instances]
    complete substitutions, in the order found, and at most
    [max_match_steps] steps of the search.  Taking patterns jointly rather
    than merging matches pairwise is what keeps the substitutions
    consistent: a premise over several of the binders fixes them together
    ([R(a, x, b)] against [R(a, s, b)]), and the goal's terms then fix the
    rest.
    With [open_scalars] (default [!open_scalar_matches]), no complete
    substitution found and at least one binder of an array or sequence sort
    in [senv], the search is run once more and also keeps, at each leaf, a
    substitution that gives a term to every binder of an array or sequence
    sort, the others left out; of those, only the maximal ones (no other kept
    substitution extends one) are returned, those fixing the most binders
    first, at most [max].  The caller must keep the binders a substitution
    leaves out bound, as [matched_instance_form] does; an instance with those
    still existential implies the existential as a complete one does. *)
let matched_substitutions ?(extra = []) ?(max = max_matched_instances)
    ?(open_scalars = !open_scalar_matches) ~ground senv body =
  let vars = Set.Poly.of_list (List.map senv ~f:fst) in
  let patterns =
    Set.to_list
    @@ Formula.filtered_terms_of body ~f:(function
      | Term.FunApp (T_bool.Formula _, _, _) -> false
      | Term.FunApp _ as t -> not (Set.is_empty (Set.inter (Term.tvs_of t) vars))
      | _ -> false)
  in
  let equal_sub = Map.Poly.equal Stdlib.( = ) in
  let candidates =
    List.filter_map patterns ~f:(fun p ->
        match
          List.rev
          @@ List.fold ~init:[] ~f:(fun acc m ->
                 if List.exists acc ~f:(equal_sub m) then acc else m :: acc)
          @@ List.filter ~f:(Fn.non Map.Poly.is_empty)
          @@ List.filter_map ground ~f:(fun g ->
                 match_pattern ~vars Map.Poly.empty p g)
        with
        | [] -> None
        | ms -> Some (List.take ms max_partial_matches))
    |> List.sort ~compare:(fun a b -> Int.compare (List.length a) (List.length b))
  in
  (* each binder's extra terms, one group per binder, tried before the matched
     patterns: the search takes each group before skipping it, so a binder a
     pattern fixes first could never take its extra term *)
  let candidates =
    List.filter_map senv ~f:(fun (x, _) ->
        match
          List.filter_map extra ~f:(fun (y, t) ->
              if Ast.Ident.tvar_equal x y then Some (Map.Poly.singleton x t)
              else None)
        with
        | [] -> None
        | ms -> Some ms)
    @ candidates
  in
  let complete s = Set.for_all vars ~f:(Map.Poly.mem s) in
  let merge s1 s2 =
    if
      Map.Poly.for_alli s2 ~f:(fun ~key ~data ->
          match Map.Poly.find s1 key with
          | Some t -> Stdlib.( = ) t data
          | None -> true)
    then
      Some
        (Map.Poly.merge s1 s2 ~f:(fun ~key:_ -> function
           | `Left t | `Right t | `Both (t, _) -> Some t))
    else None
  in
  let found = ref [] and steps = ref 0 in
  let record s =
    if not (List.exists !found ~f:(equal_sub s)) then found := s :: !found
  in
  let rec search sub = function
    | _ when List.length !found >= max || !steps >= max_match_steps
      ->
        ()
    | _ when complete sub -> record sub
    | [] -> ()
    | ms :: rest ->
        incr steps;
        List.iter ms ~f:(fun m ->
            match merge sub m with
            | Some sub' when Map.Poly.length sub' > Map.Poly.length sub ->
                search sub' rest
            | _ -> ());
        search sub rest
  in
  search Map.Poly.empty candidates;
  (* the binders a partial substitution must fix: a binder of an array or
     sequence sort left bound is what the forms exist to remove *)
  let collection =
    List.filter_map senv ~f:(fun (x, s) ->
        if Term.is_array_sort s || is_seq_sort s then Some x else None)
  in
  if (not open_scalars) || List.is_empty collection || not (List.is_empty !found)
  then List.rev !found
  else
    let partial_ok sub =
      (not (Map.Poly.is_empty sub))
      && List.for_all collection ~f:(Map.Poly.mem sub)
    in
    let leaves = ref [] and steps = ref 0 in
    let keep s =
      if partial_ok s && not (List.exists !leaves ~f:(equal_sub s)) then
        leaves := s :: !leaves
    in
    let rec search_open sub = function
      | _ when List.length !leaves >= max_partial_matches
               || !steps >= max_match_steps ->
          ()
      | [] -> keep sub
      | ms :: rest ->
          incr steps;
          List.iter ms ~f:(fun m ->
              match merge sub m with
              | Some sub' when Map.Poly.length sub' > Map.Poly.length sub ->
                  search_open sub' rest
              | _ -> ());
          search_open sub rest
    in
    search_open Map.Poly.empty candidates;
    let extends big small =
      Map.Poly.length big > Map.Poly.length small
      && Map.Poly.for_alli small ~f:(fun ~key ~data ->
             match Map.Poly.find big key with
             | Some t -> Stdlib.( = ) t data
             | None -> false)
    in
    let leaves = List.rev !leaves in
    (* most binders fixed first (stable, so in the order found among equals):
       the substitution a proof needs is the one the most ground terms agree
       on, and the cut at [max] must not take the loosest ones first *)
    List.take
      (List.stable_sort
         (List.filter leaves ~f:(fun s ->
              not (List.exists leaves ~f:(fun b -> extends b s))))
         ~compare:(fun a b -> Int.compare (Map.Poly.length b) (Map.Poly.length a)))
      max

(* Whether the matched-instance forms also offer a sequence binder the
   candidates its element equations name ([element_equation_candidates_for]).
   Set by the coordinator from its configuration; process-wide, as
   [matched_instance_forms] is. *)
let matched_instance_element_candidates = ref false

(* at most this many element-equation candidates per binder *)
let max_element_candidates = 8

(** candidates for the sequence binder [x] (element sort [se]) of a positive
    existential whose binders are [bound], read off the element equations of
    its [body]: for each conjunct [seq.nth x i = t] (either way round) at the
    top of [body]'s conjunction, [t] mentioning no variable of [bound], the
    one-element sequence [seq.unit t], and then [u ++ seq.unit t] for each
    sequence [u] of [x]'s sort that is free in [whole] (a variable, a
    skolemized premise witness among them) or a ground function application
    of [ground]; units first, at most [max_element_candidates] in all, in
    the order found.

    Contract: each candidate is a term of [x]'s sort all of whose variables
    are free in [whole] -- nothing is claimed of its meaning, since an
    instance at any term implies the existential; so offering these changes
    which instances the matched-instance form asks, never its soundness.

    What it buys: an existential introduction whose witness is built from the
    element the goal fixes and is written nowhere in the piece.  A chain of
    states [fs] with [fs[0] = f] and [len fs = 1 + len v], [v] empty, has the
    witness [seq.unit f] (an iterator's [produces] at the start of a loop),
    and the same chain after one step has [fs' = fs ++ seq.unit f'] (the loop
    body, [fs] the invariant's witness); no pattern of the body matches
    either, because neither term occurs in the piece. *)
let element_equation_candidates_for ~whole ~ground ~bound x se body =
  let is_x = function
    | Term.Var (y, _, _) -> Ast.Ident.tvar_equal x y
    | _ -> false
  in
  let closed t = Set.is_empty (Set.inter (Term.tvs_of t) bound) in
  let elem_of_eq = function
    | Formula.Atom
        (Atom.App (Predicate.Psym T_bool.Eq, [ l; r ], _), _) -> (
        match (l, r) with
        | Term.FunApp (T_seq.SqNth _, [ s; _ ], _), t when is_x s && closed t
          ->
            Some t
        | t, Term.FunApp (T_seq.SqNth _, [ s; _ ], _) when is_x s && closed t
          ->
            Some t
        | _ -> None)
    | _ -> None
  in
  let elems =
    List.dedup_and_sort ~compare:Stdlib.compare
      (List.filter_map (Formula.conjuncts_list_of body) ~f:elem_of_eq)
  in
  if List.is_empty elems then []
  else
    let sort = T_seq.mk_seq_sort se in
    let prefixes =
      (Set.to_list (Formula.term_sort_env_of whole)
      |> List.filter_map ~f:(fun (y, s) ->
             if Stdlib.( = ) s sort && not (Set.mem bound y) then
               Some (Term.mk_var y s)
             else None))
      @ List.filter ground ~f:(fun t ->
            closed t && Stdlib.( = ) (Term.sort_of t) sort)
    in
    let units = List.map elems ~f:(T_seq.mk_unit se) in
    List.take
      (units
      @ List.concat_map prefixes ~f:(fun u ->
            List.map units ~f:(T_seq.mk_concat se u)))
      max_element_candidates

(* Whether the matched-instance forms also offer a sequence binder the joins
   of two chains that share an end element ([chain_join_candidates_for]).
   Set by the coordinator from its configuration; process-wide. *)
let matched_instance_chain_join_candidates = ref false

(* Whether [chain_join_candidates_for] also joins two chains whose shared end
   element is written as a direct equation [u[i] = w[0]] (either way round)
   rather than through a common term.  Set by the coordinator from its
   configuration; process-wide.  Off by default. *)
let chain_join_direct_reads = ref false

(* at most this many chain-join candidates per binder *)
let max_chain_join_candidates = 4

(** candidates for the sequence binder [x] (element sort [se]) of a positive
    existential whose binders are [bound] and whose [body] reads [x] by
    [seq.nth]: two sequences [u] and [w] of [x]'s sort, free in [whole]
    (mentioning no variable of [bound]), whose elements [whole] equates to a
    common term [m] -- [u[i] = m] with [i] not the literal [0], and
    [w[0] = m], each atom an equation or a disequation (a premise of the
    piece is a disequation) -- give the joins

      u ++ extract w 1 (len w - 1)      and      extract u 0 i ++ w,

    [u]'s first then [w]'s first, at most [max_chain_join_candidates]; with
    [chain_join_direct_reads], also the joins of [u] and [w] for each atom
    [u[i] = w[0]] (the common term being one of the reads themselves).

    Contract: each candidate is a term of [x]'s sort all of whose variables
    are free in [whole]; nothing is claimed of its meaning, since an instance
    at any term implies the existential, so offering these changes which
    instances are asked, never soundness.

    What it buys: a chain of states [fs] (the closure states of an iterator
    adapter's [produces], [len fs = len v + 1], [fs[0]] the start and
    [fs[len v]] the end) proved for [v = ab ++ bc] from the chains of the two
    halves, which share the middle state ([fab[len ab] = b = fbc[0]]): the
    witness drops one copy of the shared state, and no pattern of the piece
    writes it, the chain rule's concatenation [fab ++ fbc] being one element
    too long. *)
let chain_join_candidates_for ~whole ~bound x se body =
  let sort = T_seq.mk_seq_sort se in
  let closed t = Set.is_empty (Set.inter (Term.tvs_of t) bound) in
  let reads_x =
    not
      (Set.is_empty
         (Formula.filtered_terms_of body ~f:(function
           | Term.FunApp (T_seq.SqNth _, [ Term.Var (y, _, _); _ ], _) ->
               Ast.Ident.tvar_equal x y
           | _ -> false)))
  in
  if not reads_x then []
  else
    (* an atom under another binder of [whole] may mention that binder; only
       terms over [whole]'s free variables are candidates *)
    let free = Formula.tvs_of whole in
    let closed t = closed t && Set.is_subset (Term.tvs_of t) ~of_:free in
    let read_eq (a, b) =
      let one l r =
        match l with
        | Term.FunApp (T_seq.SqNth _, [ u; i ], _)
          when Stdlib.( = ) (Term.sort_of u) sort && closed u && closed i
               && closed r ->
            Some (u, i, r)
        | _ -> None
      in
      List.filter_opt [ one a b; one b a ]
    in
    let atoms =
      List.concat_map
        (Set.to_list
           (let pos, neg = Formula.atoms_of whole in
            Set.union pos neg))
        ~f:(fun atm ->
          match atm with
          | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ a; b ], _) ->
              read_eq (a, b)
          | _ -> [])
    in
    let starts =
      List.filter atoms ~f:(fun (_, i, _) -> T_int.is_zero i)
    and ends = List.filter atoms ~f:(fun (_, i, _) -> not (T_int.is_zero i)) in
    let one = T_int.mk_int Z.one in
    let join (u, i) w =
      [
        T_seq.mk_concat se u
          (T_seq.mk_extract se w one (T_int.mk_sub (T_seq.mk_len se w) one));
        T_seq.mk_concat se (T_seq.mk_extract se u (T_int.zero ()) i) w;
      ]
    in
    let joins =
      List.concat_map ends ~f:(fun (u, i, m) ->
          List.concat_map starts ~f:(fun (w, _, m') ->
              if Stdlib.( = ) m m' && not (Stdlib.( = ) u w) then join (u, i) w
              else []))
    in
    (* with [chain_join_direct_reads], also the joins whose shared element is
       written as one equation [u[i] = w[0]] between the two reads, with no
       common term: what the pairs above become once the middle state, a
       field of a tuple, is a variable that the one-point rule replaced by
       one of the two reads *)
    let direct =
      if not !chain_join_direct_reads then []
      else
        List.concat_map ends ~f:(fun (u, i, m) ->
            match m with
            | Term.FunApp (T_seq.SqNth _, [ w; j ], _)
              when T_int.is_zero j
                   && Stdlib.( = ) (Term.sort_of w) sort
                   && not (Stdlib.( = ) u w) ->
                join (u, i) w
            | _ -> [])
    in
    List.take (dedup_terms (joins @ direct)) max_chain_join_candidates

(* Whether the matched-instance forms also offer an integer binder the last
   index [len s - 1] of each sequence its body bounds it by
   ([last_index_candidates_for]).  Set by the coordinator; process-wide. *)
let matched_instance_last_index_candidates = ref false

(* Whether the matched-instance forms also ask [matched_instance_form] with
   [collections_only] (see there), after the forms without it.  Set by the
   coordinator; process-wide. *)
let matched_instance_collections_only = ref false

(* at most this many last-index candidates per binder *)
let max_last_index_candidates = 4

(** candidates for the integer binder [k] of a positive existential whose
    binders are [bound]: [len s - 1] for each [seq.len s] of its [body] with
    [s] mentioning no variable of [bound], at most
    [max_last_index_candidates], in the order found.

    Contract: each candidate is an integer term free in the piece, so an
    instance at it implies the existential; only which instances are asked
    changes.

    What it buys: a premise [forall k. 0 <= k < len v => step(k)] (in the
    piece, the disjunct [exists k. 0 <= k < len v /\ not step(k)]) whose
    instance at the last index proves a goal about the end of the chain
    (a count after the loop equals the length): [len v - 1] is written
    nowhere in the piece, and the offsets [t - len u] do not reach it. *)
let last_index_candidates_for ~bound _k body =
  let closed t = Set.is_empty (Set.inter (Term.tvs_of t) bound) in
  let lens =
    Set.to_list
    @@ Formula.filtered_terms_of body ~f:(function
      | Term.FunApp (T_seq.SqLen _, [ s ], _) -> closed s
      | _ -> false)
  in
  List.take
    (dedup_terms
       (List.map lens ~f:(fun l -> T_int.mk_sub l (T_int.mk_int Z.one))))
    max_last_index_candidates

(** candidates for the sequence binder [x] of a positive existential whose
    binders are [bound], read off the pointwise definition in its [body]: a
    conjunct [forall k. ... \/ x[k] = a[k - o]] (either way round, [k] an
    integer, [o] not mentioning [k]) names [a] at offset [o]; each [a] named
    at offset 0 is a candidate, and so is [a ++ b] for each [b] named at the
    offset [len a].  [a] and [b] must mention no variable of [bound].

    Contract as for [element_equation_candidates_for]: a term of [x]'s sort,
    closed in the piece, so offering it changes which instances are asked and
    never their soundness.

    What it buys: a lemma's conclusion states its concatenation pointwise
    ([len v = len a + len b], [v[k] = a[k]] below [len a], [v[k] = b[k - len
    a]] above), and a caller's goal writes [a ++ b]; the only pattern of [v]
    is [len v], which matches every length in the piece, so the instance the
    definition forces is one among many and, under a budget, often not
    taken. *)
let pointwise_definition_candidates_for ~bound x se body =
  let is_x = function
    | Term.Var (y, _, _) -> Ast.Ident.tvar_equal x y
    | _ -> false
  in
  let closed t = Set.is_empty (Set.inter (Term.tvs_of t) bound) in
  let source k d =
    (* [x[k] = a[i]] with [i = k - o]: [(a, o)] *)
    let of_read xk ai =
      match (xk, ai) with
      | ( Term.FunApp (T_seq.SqNth _, [ s; Term.Var (k', _, _) ], _),
          Term.FunApp (T_seq.SqNth _, [ a; i ], _) )
        when is_x s && Ast.Ident.tvar_equal k k' && closed a
             && not (Set.mem (Term.tvs_of a) k) ->
          let is_k = function
            | Term.Var (k'', _, _) -> Ast.Ident.tvar_equal k k''
            | _ -> false
          in
          (* the offset read syntactically: [k], [k - o], [k + -o], [-o + k] *)
          let o =
            match i with
            | _ when is_k i -> Some (T_int.zero ())
            | Term.FunApp (T_int.Sub, [ k'; o ], _) when is_k k' -> Some o
            | Term.FunApp (T_int.Add, [ k'; Term.FunApp (T_int.Neg, [ o ], _) ], _)
              when is_k k' ->
                Some o
            | Term.FunApp (T_int.Add, [ Term.FunApp (T_int.Neg, [ o ], _); k' ], _)
              when is_k k' ->
                Some o
            | _ -> None
          in
          Option.bind o ~f:(fun o ->
              if Set.mem (Term.tvs_of o) k || not (closed o) then None
              else Some (a, Ast.Evaluator.simplify_term o))
      | _ -> None
    in
    match d with
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ l; r ], _), _) -> (
        match of_read l r with Some _ as s -> s | None -> of_read r l)
    | _ -> None
  in
  let sources =
    List.concat_map (Formula.conjuncts_list_of body) ~f:(function
      | Formula.Bind (Formula.Forall, [ (k, _) ], d, _) ->
          List.filter_map (Formula.disjuncts_list_of d) ~f:(source k)
      | _ -> [])
  in
  let is_zero o = Stdlib.( = ) o (Ast.Evaluator.simplify_term (T_int.zero ())) in
  let prefixes =
    List.filter_map sources ~f:(fun (a, o) -> if is_zero o then Some a else None)
  in
  let joined =
    List.concat_map prefixes ~f:(fun a ->
        let la = Ast.Evaluator.simplify_term (T_seq.mk_len se a) in
        List.filter_map sources ~f:(fun (b, o) ->
            if Stdlib.( = ) o la then Some (T_seq.mk_concat se a b) else None))
  in
  List.take (dedup_terms (joined @ prefixes)) max_element_candidates

(** [subs] (substitutions of the binders [senv] of an existential whose body
    is [body]) ordered first by whether one of the body's patterns -- its
    function applications mentioning a binder -- turns into a term of
    [ground] that satisfies [prefer] (none does by default), then by how
    many distinct terms of [ground] the patterns turn into, most first, the order found kept among
    equals.  Only an order: which
    substitution an instance is made at never affects soundness.  What it
    buys: the search returns its complete substitutions in the order its
    depth-first walk meets them, so the one every ground fact agrees with (a
    chain of states the premises fix at both ends, and the input sequence the
    history concatenation names) can come after one that a single length
    pattern admits *)
let rank_by_ground_agreement ?(prefer = fun _ -> false) ~ground senv body
    subs =
  let vars = Set.Poly.of_list (List.map senv ~f:fst) in
  let patterns =
    Set.to_list
    @@ Formula.filtered_terms_of body ~f:(function
      | Term.FunApp (T_bool.Formula _, _, _) -> false
      | Term.FunApp _ as t -> not (Set.is_empty (Set.inter (Term.tvs_of t) vars))
      | _ -> false)
  in
  let ground = Set.Poly.of_list ground in
  let score sub =
    (* distinct terms: an instance that maps two binders to one term (a
       transitivity law at [a = b]) writes the same ground term twice and is
       no stronger for it *)
    let hits =
      List.dedup_and_sort ~compare:Stdlib.compare
      @@ List.filter_map patterns ~f:(fun p ->
             let t = Term.subst sub p in
             if Set.mem ground t then Some t else None)
    in
    ((if List.exists hits ~f:prefer then 1 else 0), List.length hits)
  in
  List.map subs ~f:(fun sub -> (score sub, sub))
  |> List.stable_sort ~compare:(fun ((a1, a2), _) ((b1, b2), _) ->
         match Int.compare b1 a1 with 0 -> Int.compare b2 a2 | c -> c)
  |> List.map ~f:snd

(* the number of instances the [collections_only] form makes per existential,
   the best-ranked ones ([rank_by_ground_agreement]): with all eight a
   matched instance set at once, Z3 left a from_iter loop piece undecided at
   20 s, and the one instance every ground fact agrees with, asked alone,
   was proved at once *)
let collections_only_instances = 1

(** the matched-instance form of [piece] (see above).  With [keep_scalar],
    an existential that binds no array or sequence is kept beside its
    instances instead of being replaced by them, so that the solver may still
    instantiate it (the form then implies the piece all the same, and is
    implied by the form without [keep_scalar]).  With [collections_only],
    an existential that binds no array or sequence is left as it is, with no
    instance beside it: only the blocks binding a collection are
    instantiated, each at its [collections_only_instances] best-ranked
    substitutions ([rank_by_ground_agreement]) (the result implies the piece,
    as each instance implies its existential), so a premise universal over indices stays a universal the
    solver instantiates at the skolem constant the goal's instance leaves,
    which a matched instance, chosen before that constant exists, cannot be.
    With [prefer], each existential's substitutions are searched up to
    [max_partial_matches] and the [per_existential] best by
    [rank_by_ground_agreement ~prefer] are taken.
    With [rounds] = [n] > 1,
    the first [n - 1] rounds keep every existential beside its instances and
    then skolemize the positive universals the instances brought to the top
    ([skolemize_positive_universals]), so that the next round matches against
    the fresh constants too: a goal [exists w. ... /\ forall k. G(w, k)]
    instantiated at [w := t] leaves [forall k. G(t, k)], whose [k] a premise
    universal over indices can then be instantiated at.  The last round's
    instances have their positive universals skolemized too unless
    [skolemize_last] is false (then a universal the solver is to instantiate
    stays).  At most [per_pass] instances are made in one pass.  Each step is
    a strengthening (an instance implies its existential; a positive
    universal not under an existential is valid exactly when its instance at
    a fresh constant is), so the result implies the piece.  Raises
    [Matched_form_too_large] as soon as the estimated size of its instances
    passes [max_size] ([max_matched_form_size] by default; see there). *)
let matched_instance_form ?(keep_scalar = false) ?(collections_only = false)
    ?prefer ?(rounds = 1)
    ?(per_pass = max_matched_instances_per_pass) ?(skolemize_last = true)
    ?(keep_as_is = []) ?(per_existential = max_matched_instances)
    ?(max_size = !max_matched_form_size) ?(between = Fn.id) piece =
  (* the estimated size of the instances built so far, over every pass *)
  let estimate = ref 0 in
  last_matched_form_estimate := 0;
  let binds_collection =
    List.exists ~f:(fun (_, s) -> Term.is_array_sort s || is_seq_sort s)
  in
  let ph = Common.PhaseTime.with_phase in
  let pass ~keep_all phi =
    let phi = ph "mf-nnf" (fun () -> Formula.nnf_of phi) in
    let whole = phi in
    let whole_chains = lazy (ph "mf-chains" (fun () -> select_chains whole)) in
    !clause_trace
      (lazy (sprintf "matched form: pass on %d nodes" (Formula.ast_size phi)));
    let ground = ph "mf-ground" (fun () -> ground_funapps phi) in
    !clause_trace
      (lazy (sprintf "matched form: %d ground terms" (List.length ground)));
    let bound_of senv = Set.Poly.of_list (List.map senv ~f:fst) in
    (* a sequence binder is offered the chain rule's concatenations
       ([chain_concat_candidates_for]): a transitivity premise's witness
       [x0 ++ x1] is written nowhere in the piece, so no pattern can match
       it.  With [matched_instance_element_candidates], the concatenation a
       pointwise definition in the body forces
       ([pointwise_definition_candidates_for]) is offered beside them, and
       the candidates its element equations name
       ([element_equation_candidates_for]) only to fill the places the
       matches leave: the search takes a binder's extra terms before its
       patterns, so a unit or a one-step extension offered with the others
       would crowd out a match the piece does write *)
    let extra_of candidates senv body =
      List.concat_map senv ~f:(fun (x, s) ->
          match elem_of_seq s with
          | None -> []
          | Some se ->
              List.map
                (candidates ~bound:(bound_of senv) x se body)
                ~f:(fun t -> (x, t)))
    in
    let subs_of senv body =
      let chain =
        extra_of (chain_concat_candidates_for ~whole ~whole_chains) senv body
        @ (if !matched_instance_last_index_candidates then
             List.concat_map senv ~f:(fun (k, s) ->
                 if Term.is_int_sort s then
                   List.map
                     (last_index_candidates_for ~bound:(bound_of senv) k body)
                     ~f:(fun t -> (k, t))
                 else [])
           else [])
        @
        if !matched_instance_element_candidates then
          extra_of
            (fun ~bound x se body ->
              pointwise_definition_candidates_for ~bound x se body)
            senv body
        else []
      in
      let search_max =
        if Option.is_some prefer then Int.max per_existential max_partial_matches
        else per_existential
      in
      let base =
        matched_substitutions ~extra:chain ~max:search_max ~ground senv body
      in
      if
        (not !matched_instance_element_candidates)
        || List.length base >= per_existential
      then base
      else
        match
          extra_of (element_equation_candidates_for ~whole ~ground) senv body
        with
        | [] -> base
        | elems ->
            let equal_sub = Map.Poly.equal Stdlib.( = ) in
            let more =
              List.filter
                (matched_substitutions ~extra:(chain @ elems)
                   ~max:per_existential ~ground senv body)
                ~f:(fun s -> not (List.mem base s ~equal:equal_sub))
            in
            List.take (base @ more) per_existential
    in
    (* instances nest (an instance's body may hold further existentials,
       instantiated in turn), so a pass makes at most [per_pass] of them in
       all *)
    let budget = ref per_pass in
    let rec go phi =
      match phi with
      | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, _) ->
          Formula.mk_binop op (go p) (go q)
      | Formula.Bind (Formula.Exists, senv, _, _)
        when collections_only && not (binds_collection senv) ->
          phi
      | Formula.Bind (Formula.Exists, senv, _, _)
        when !skip_spent_budget_searches && !budget <= 0 ->
          (* the general branch below with no substitution taken, which is
             what it takes once the budget is spent (see
             [skip_spent_budget_searches]) *)
          incr skipped_spent_searches;
          observe "matched-instance"
            (List.map senv ~f:(fun (x, _) -> (x, 0)))
            [];
          if keep_all || (keep_scalar && not (binds_collection senv)) then
            Formula.or_of [ phi ]
          else Formula.or_of []
      | Formula.Bind (Formula.Exists, senv, body, _) ->
          !clause_trace
            (lazy
              (sprintf "matched form: existential over %d nodes"
                 (Formula.ast_size body)));
          let subs =
            ph
              (if !budget <= 0 then "mf-subs-spent" else "mf-subs")
              (fun () -> subs_of senv body)
          in
          !clause_trace
            (lazy (sprintf "matched form: %d substitutions" (List.length subs)));
          (* the bound tested before the ranking: the number the cuts below
             keep is that of the unranked list, the ranking being a
             permutation, so this raises exactly when the test after the
             cuts would, with the same estimate *)
          (if !matched_bound_before_ranking then
             let kept =
               let n = List.length subs in
               let n =
                 if collections_only then Int.min n collections_only_instances
                 else
                   match prefer with
                   | None -> n
                   | Some _ -> Int.min n per_existential
               in
               Int.min n (Int.max 0 !budget)
             in
             if kept > 0 then
               match max_size with
               | Some bound
                 when !estimate + (kept * Formula.ast_size body) > bound ->
                   estimate := !estimate + (kept * Formula.ast_size body);
                   last_matched_form_estimate := !estimate;
                   raise Matched_form_too_large
               | _ -> ());
          let subs =
            if collections_only then
              List.take
                (rank_by_ground_agreement ~ground senv body subs)
                collections_only_instances
            else
              match prefer with
              | None -> subs
              | Some prefer ->
                  List.take
                    (rank_by_ground_agreement ~prefer ~ground senv body subs)
                    per_existential
          in
          !clause_trace (lazy "matched form: substitutions ranked");
          let subs = List.take subs (max 0 !budget) in
          budget := !budget - List.length subs;
          if not (List.is_empty subs) then (
            estimate := !estimate + (List.length subs * Formula.ast_size body);
            last_matched_form_estimate := !estimate;
            match max_size with
            | Some bound when !estimate > bound -> raise Matched_form_too_large
            | _ -> ());
          observe "matched-instance"
            (List.map senv ~f:(fun (x, _) -> (x, List.length subs)))
            [];
          let instances =
            (* a substitution of [open_scalar_matches] leaves some scalar
               binders out; they stay bound around the instance *)
            List.map subs ~f:(fun sub ->
                let rest =
                  List.filter senv ~f:(fun (x, _) -> not (Map.Poly.mem sub x))
                in
                Formula.mk_exists_if_bounded rest (go (Formula.subst sub body)))
          in
          if keep_all || (keep_scalar && not (binds_collection senv)) then
            Formula.or_of (phi :: instances)
          else Formula.or_of instances
      | Formula.Bind (b, senv, body, _) -> Formula.mk_bind b senv (go body)
      | _ -> phi
    in
    if List.is_empty keep_as_is then go phi
    else
      (* a top-level disjunct of [keep_as_is] is left as it is; its terms are
         still among the ground terms the others are matched against *)
      let kept = List.map keep_as_is ~f:Formula.nnf_of in
      Formula.or_of
        (List.map (Formula.disjuncts_list_of phi) ~f:(fun d ->
             if List.mem kept d ~equal:Stdlib.( = ) then d else go d))
  in
  let rec loop n phi =
    if n <= 1 then
      if skolemize_last then
        let p = ph "mf-pass" (fun () -> pass ~keep_all:false phi) in
        ph "mf-skolem" (fun () -> skolemize_positive_universals p)
      else ph "mf-pass" (fun () -> pass ~keep_all:false phi)
    else
      let p = ph "mf-pass" (fun () -> between (pass ~keep_all:true phi)) in
      let p = ph "mf-mid-simplify" (fun () -> Ast.Evaluator.simplify p) in
      loop (n - 1) (ph "mf-skolem" (fun () -> skolemize_positive_universals p))
  in
  let instantiated = loop rounds piece in
  !clause_trace
    (lazy
      (sprintf "matched form: instantiated, %d nodes"
         (Formula.ast_size instantiated)));
  let result =
    let r =
      ph "mf-read-split" (fun () ->
          Ast.Evaluator.rewrite_seq_read_over_concat instantiated)
    in
    ph "mf-final-simplify" (fun () -> Ast.Evaluator.simplify r)
  in
  !clause_trace (lazy "matched form: read split and simplified");
  result

(** [piece] with each earlier piece [e] of the same clause beside it as a
    hypothesis: the disjunct [exists xs. not e'], where [e'] is the
    disjunction of the disjuncts of [e] that [piece] does not have and [xs]
    the variables free in [e'] and not in [piece].

    Sound when every piece of [earlier] is valid, which [prove_valid]
    requires before it answers that the clause is: each [e] is valid, so
    [not e] holds in no model; where the disjuncts [e] shares with [piece]
    are false, [e'] is then true for every value of [xs], so the added
    disjunct is false there, and [piece] and the result are valid together.
    By induction over the order of the pieces, every piece is then valid.
    What it buys: a clause whose conclusion is [A /\ B], with [A] a lemma
    [B] follows from ([B] the existential introduction of what [A] states
    with its witness named), can be proved piece by piece only when [B]'s
    pieces see [A]; the matched-instance form then instantiates the
    hypothesis at the terms [B]'s goal mentions. *)
let rec with_earlier_pieces ~earlier piece =
  if List.is_empty earlier then piece
  else Formula.or_of (piece :: earlier_hypotheses ~earlier piece)

(** the disjuncts [with_earlier_pieces] adds to [piece], one per earlier
    piece that has a disjunct [piece] lacks *)
and earlier_hypotheses ~earlier piece =
    let own = Formula.disjuncts_list_of piece in
    let fv = Formula.tvs_of piece in
      List.filter_map earlier ~f:(fun e ->
          let rest =
            List.filter (Formula.disjuncts_list_of e) ~f:(fun d ->
                not (List.mem own d ~equal:Stdlib.( = )))
          in
          if List.is_empty rest then None
          else
            let e' = Formula.or_of rest in
            let xs =
              Set.to_list (Formula.term_sort_env_of e')
              |> List.filter ~f:(fun (x, _) -> not (Set.mem fv x))
              |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) ->
                     Stdlib.compare x y)
            in
            Some
              (Formula.mk_exists_if_bounded xs
                 (Formula.nnf_of (Formula.negate e'))))

(** first-order matching of the formula [p] against [f], the variables of
    [vars] being the pattern's: the same connectives and predicates, the
    arguments matched by [match_pattern], and a binder of [p] matched to the
    binder of [f] at the same position (same sort), which does not enter the
    result; [sub] extended, or [None] *)
let rec match_formula ~vars sub p f =
  match (p, f) with
  | ( Formula.Atom
        (Atom.App ((Predicate.Psym (T_bool.Eq | T_bool.Neq) as pp), [ a; b ], _), _),
      Formula.Atom (Atom.App (fp, [ c; d ], _), _) )
    when Stdlib.( = ) pp fp -> (
      (* an equation matches either orientation *)
      match match_patterns ~vars sub [ a; b ] [ c; d ] with
      | Some _ as r -> r
      | None -> match_patterns ~vars sub [ a; b ] [ d; c ])
  | Formula.Atom (Atom.App (pp, pa, _), _), Formula.Atom (Atom.App (fp, fa, _), _)
    when Stdlib.( = ) pp fp ->
      match_patterns ~vars sub pa fa
  | Formula.Atom ((Atom.True _ | Atom.False _) as a, _), Formula.Atom (b, _) ->
      if Stdlib.( = ) a b then Some sub else None
  | Formula.UnaryOp (o, p1, _), Formula.UnaryOp (o', f1, _)
    when Stdlib.( = ) o o' ->
      match_formula ~vars sub p1 f1
  | Formula.BinaryOp (o, p1, p2, _), Formula.BinaryOp (o', f1, f2, _)
    when Stdlib.( = ) o o' ->
      Option.bind (match_formula ~vars sub p1 f1) ~f:(fun sub ->
          match_formula ~vars sub p2 f2)
  | Formula.Bind (b, senv, p1, _), Formula.Bind (b', senv', f1, _)
    when Stdlib.( = ) b b'
         && List.length senv = List.length senv'
         && List.for_all2_exn senv senv' ~f:(fun (_, s) (_, s') ->
                Stdlib.( = ) s s') ->
      let bound = List.map senv ~f:fst in
      let sub_b =
        List.fold2_exn senv senv' ~init:sub ~f:(fun sub (x, s) (y, _) ->
            Map.Poly.set sub ~key:x ~data:(Term.mk_var y s))
      in
      Option.map
        (match_formula
           ~vars:(Set.union vars (Set.Poly.of_list bound))
           sub_b p1 f1)
        ~f:(fun sub' ->
          List.fold bound ~init:sub' ~f:(fun acc x ->
              match Map.Poly.find sub x with
              | Some t -> Map.Poly.set acc ~key:x ~data:t
              | None -> Map.Poly.remove acc x))
  | _ -> None

(** [earlier_hypotheses] with each earlier piece [e] first ALIGNED with
    [piece]: a substitution [sigma] of [e]'s own variables (those not free in
    [piece]) is sought that maps [e]'s disjuncts, one by one, onto disjuncts
    [piece] has ([match_formula]; each disjunct taken at its first consistent
    match, in order); the disjuncts so matched are dropped, and the hypothesis
    is [exists u. not (e'' sigma)], [e''] the disjuncts left and [u] the own
    variables [sigma] leaves unmapped.

    Sound when [e] is valid, as for [with_earlier_pieces]: [e] is valid for
    every value of its own variables, so [e sigma] is valid; where every
    disjunct of [piece] is false, so are the dropped ones (they are disjuncts
    of [piece] under [sigma]), so [e'' sigma] holds for every [u] and the
    hypothesis is false.  What it buys over [earlier_hypotheses]: two pieces
    of one clause whose premises repeat each other up to a renaming of the
    clause's variables (two conclusions stated under separate universals)
    give a hypothesis with no premise left in it, often binding nothing or a
    single index -- a question a solver instantiates by itself. *)
let aligned_hypotheses ~earlier piece =
  let own_disjs = Formula.disjuncts_list_of piece in
  let fv = Formula.tvs_of piece in
  List.filter_map earlier ~f:(fun e ->
      let rest =
        List.filter (Formula.disjuncts_list_of e) ~f:(fun d ->
            not (List.mem own_disjs d ~equal:Stdlib.( = )))
      in
      let own =
        Set.filter (Formula.tvs_of (Formula.or_of rest)) ~f:(fun x ->
            not (Set.mem fv x))
      in
      let sigma, left =
        List.fold rest ~init:(Map.Poly.empty, []) ~f:(fun (sigma, left) d ->
            match
              List.find_map own_disjs ~f:(fun d' ->
                  match_formula ~vars:own sigma d d')
            with
            | Some sigma' -> (sigma', left)
            | None -> (sigma, d :: left))
      in
      match List.rev left with
      | [] -> None
      | left ->
          let e'' = Formula.subst sigma (Formula.or_of left) in
          let u =
            Set.to_list (Formula.term_sort_env_of e'')
            |> List.filter ~f:(fun (x, _) ->
                   Set.mem own x && not (Map.Poly.mem sigma x))
            |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) ->
                   Stdlib.compare x y)
          in
          Some
            (Formula.mk_exists_if_bounded u
               (Formula.nnf_of (Formula.negate e''))))

(* The per-pass instance budget of the earlier-pieces form, when [Some n]
   ([max_matched_instances_per_pass] otherwise), and whether that form aligns
   the earlier pieces with the piece ([aligned_hypotheses]) instead of binding
   their own variables ([earlier_hypotheses]).  Set by the coordinator from
   its configuration; process-wide, as [matched_instance_forms] is. *)
let matched_instance_hyp_budget : int option ref = ref None
let matched_instance_aligned_hyps = ref false

(** the earlier-pieces form of [piece].  By default [with_earlier_pieces] in
    two rounds of [matched_instance_form].  With
    [matched_instance_aligned_hyps], the piece's own matched-instance form in
    one round that keeps the universals its instances bring (the goal's
    index), beside its [aligned_hypotheses] left as they are, so that an
    index a hypothesis still binds and the goal's universal index are left
    for the solver to pair; the hypotheses' terms are matched against all the
    same (the joined witness a goal needs is often written only there).
    Every other existential of the piece is replaced by its instances, which
    keeps the question free of the premise quantifiers a solver was seen to
    wander in; this form comes twice, first with one instance per existential
    (the first the search finds) and then with the usual number, because the
    extra instances were seen to stop the solver where the first alone
    decided the question.  Either way at most [matched_instance_hyp_budget]
    instances a pass.  A list of forms, to be asked in order. *)
let earlier_pieces_form ?(aligned = !matched_instance_aligned_hyps)
    ?(hyp_budget = !matched_instance_hyp_budget) ~earlier piece =
  let per_pass = hyp_budget in
  if aligned then
    let hyps = aligned_hypotheses ~earlier piece in
    let form per_existential =
      lazy
        (matched_instance_form ?per_pass ~skolemize_last:false ~keep_as_is:hyps
           ~per_existential
           (prepare_piece (Formula.or_of (piece :: hyps))))
    in
    [ form 1; form max_matched_instances ]
  else
    [
      lazy
        (matched_instance_form ~rounds:2 ?per_pass
           (prepare_piece (with_earlier_pieces ~earlier piece)));
    ]

(* [nth s j] split over [s = a ++ b] as [Evaluator.seq_read_over_concat]
   does, and further, inside a branch whose guard puts the index in range, a
   read of an extraction taken to a read of the extracted sequence:
   [nth (extract t o n) i = nth t (o + i)] whenever [0 <= i < len (extract t o
   n)] -- that guard forces [0 <= o], [n > 0] and [o + i < len t], so both
   reads are in range and equal in every model.  So the rewrite is exact under
   the guard the branch carries, and only applied there. *)
let rec read_over_concat_through_extract se a b j =
  let branch_read s i =
    match s with
    | Term.FunApp (T_seq.SqUnit _, [ e ], _) -> e
    | Term.FunApp (T_seq.SqConcat _, [ s1; s2 ], _) ->
        read_over_concat_through_extract se s1 s2 i
    | Term.FunApp (T_seq.SqExtract _, [ t; o; _ ], _) ->
        T_seq.mk_nth se t (T_int.mk_add o i)
    | _ -> T_seq.mk_nth se s i
  in
  let la = T_seq.mk_len se a and lb = T_seq.mk_len se b in
  T_bool.mk_if_then_else
    (T_bool.of_formula
    @@ Formula.and_of [ Formula.leq (T_int.zero ()) j; Formula.lt j la ])
    (branch_read a j)
    (T_bool.mk_if_then_else
       (T_bool.of_formula
       @@ Formula.and_of
            [ Formula.leq la j; Formula.lt j (T_int.mk_add la lb) ])
       (branch_read b (T_int.mk_sub j la))
       (T_seq.mk_nth se (T_seq.mk_concat se a b) j))

(* the splits the chain-join form applies between its two rounds: reads of a
   concatenation by [read_over_concat_through_extract], prefixes of one by
   [Evaluator.rewrite_seq_prefix_over_concat]; both exact *)
let join_splits phi =
  Ast.Evaluator.rewrite_seq_prefix_over_concat
    (Formula.map_term phi ~f:(function
      | Term.FunApp
          (T_seq.SqNth se, [ Term.FunApp (T_seq.SqConcat _, [ a; b ], _); j ], _)
        ->
          read_over_concat_through_extract se a b j
      | t -> t))

(* Whether the chain-join forms instantiate the existentials left after the
   goal's instance at their two best substitutions by
   [rank_by_ground_agreement], preferring an instance that writes a term
   mentioning a constant the goal's skolemization introduced, with no
   existential kept beside its instance.  Set by the coordinator;
   process-wide. *)
let chain_join_focused = ref false

(** the chain-join forms of a prepared [piece]: for each positive existential
    binding sequences of which one has a chain join
    ([chain_join_candidates_for]), the piece with that existential replaced
    by its instance at the join (its other sequence binders at their chain
    concatenation, [chain_concat_candidates_for], or the existential is left
    out), every other existential binding a sequence replaced by its
    law instances at the piece's chained pairs ([law_instances]) or [false],
    as the chain-focused forms do; then the positive universals the instance
    exposed (the goal's per-index conjunct) skolemized, the remaining
    existentials instantiated by matching ([matched_instance_form], which now
    sees the fresh index in the split reads); the reads and prefixes of the
    concatenations in the goal's instance are split first ([join_splits]),
    so that a read [fs[k]] of the joined chain is a read of
    one half, the shape a premise is stated in.  Each picked formula implies
    its existential and every split is exact, so each form is a
    strengthening of [piece].  At most [max_focus_forms].

    The joins are offered here and not among the candidates of the plain
    matched-instance forms: there they give the chain's binder instances it
    had none of, and a piece's form grew tenfold (35 K to 303 K characters)
    with no piece proved by it. *)
(* The size, in formula nodes, past which a chain-join form
   ([chain_join_forms_of]) is not built: the focused formula, the piece with
   each joined existential instantiated and the others replaced by the
   transitivity-law instances over every chained pair, is measured before it
   is simplified and matched, and one past this raises
   [Matched_form_too_large], which the callers skip as an undecided form.
   [None], the default, builds every one.  Skipping a form only loses a
   proof.  Why: the law instances are taken over every pair, so on large
   Rust-derived pieces the focused formula, and the simplification and the
   matching run on it before the instance estimate of
   [max_matched_form_size] is reached, held the verdict for more than 200 s
   with no question asked.  Set by the coordinator; process-wide, as
   [max_matched_form_size] is. *)
let max_chain_join_focus_size : int option ref = ref None

let chain_join_forms_of ?(per_existential = 1)
    ?(per_pass = max_matched_instances_per_pass) piece =
  let piece = Formula.nnf_of piece in
  let whole_chains = lazy (select_chains piece) in
  let pairs = chained_app_pairs (ground_apps piece) in
  let subs =
    List.filter_map (seq_existentials piece) ~f:(fun (outer, senv, body) ->
        let bound = Set.union outer (Set.Poly.of_list (List.map senv ~f:fst)) in
        let joined = ref false in
        let pick (x, s) =
          match elem_of_seq s with
          | None -> None
          | Some se -> (
              match chain_join_candidates_for ~whole:piece ~bound x se body with
              | t :: _ ->
                  joined := true;
                  Some (x, t)
              | [] -> (
                  match
                    chain_concat_candidates_for ~whole_chains ~whole:piece ~bound
                      x se body
                  with
                  | t :: _ -> Some (x, t)
                  | [] -> None))
        in
        let seqs = List.filter senv ~f:(fun (_, s) -> is_seq_sort s) in
        let picked = List.filter_map seqs ~f:pick in
        if !joined && List.length picked = List.length seqs then
          Some (senv, Map.Poly.of_alist_exn picked)
        else None)
  in
  List.take subs max_focus_forms
  |> List.map ~f:(fun (senv0, sub) ->
      lazy
        (let f =
           focus_seq_existentials piece ~pick:(fun senv body ->
               if same_binders senv senv0 then
                 Option.map (instance_of senv body sub) ~f:(fun g ->
                     join_splits (right_nest_concats g))
               else
                 or_of_nonempty
                   (List.concat_map pairs ~f:(fun pair ->
                        law_instances pair senv body)))
         in
         !clause_trace
           (lazy (sprintf "chain-join form: focused built, %d nodes" (Formula.ast_size f)));
         (match !max_chain_join_focus_size with
         | Some bound ->
             let size = Formula.ast_size f in
             !clause_trace
               (lazy (sprintf "chain-join form: focused (size %d)" size));
             if size > bound then raise Matched_form_too_large
         | None -> ());
         observe "chain-join" (List.map (Map.Poly.keys sub) ~f:(fun x -> (x, 1))) [ f ];
         if !chain_join_focused then
           let step name g =
             !clause_trace
               (lazy
                 (sprintf "chain-join form: %s, %d nodes" name
                    (Formula.ast_size g)));
             g
           in
           let nf = step "nnf" (Formula.nnf_of f) in
           let sk = step "skolemized" (skolemize_positive_universals nf) in
           let fresh = Set.diff (Formula.tvs_of sk) (Formula.tvs_of nf) in
           let prefer t = not (Set.is_empty (Set.inter (Term.tvs_of t) fresh)) in
           step "final simplify"
           @@ Ast.Evaluator.simplify
           (* two instances per existential: the goal's index read splits
              into a read of each half of the join, and a transitivity law
              is needed at the state of the second half while the first
              half's state comes from its own premise; with one, the
              instance taken was the first half's and the piece was not
              proved *)
           @@ step "matched"
           @@ matched_instance_form ~skolemize_last:false ~per_existential:2
                ~per_pass ~keep_scalar:false ~prefer
           @@ step "first simplify"
           @@ Ast.Evaluator.simplify sk
         else
         Ast.Evaluator.simplify
         @@ matched_instance_form ~skolemize_last:false ~per_existential
              ~per_pass ~keep_scalar:true
         @@ Ast.Evaluator.simplify
         @@ Formula.nnf_of
         @@ skolemize_positive_universals f))

(** the matched-instance forms of a prepared [piece], in the order they are
    asked: its [matched_instance_form], the same keeping its scalar binders,
    and, when [earlier] (the pieces before it in the same clause) is not
    empty, its [earlier_pieces_form] ([aligned] and [hyp_budget] default to
    the process-wide switches).  Each is a strengthening of [piece]; the
    earlier-pieces forms only under the hypothesis that every piece of
    [earlier] is valid, so a caller may read a proof by one of them only as
    part of proving every piece of the clause, as [prove_valid] and
    [prove_valid_deep] do.  A form past [max_matched_form_size] is forced to
    [None], which the callers skip. *)
let matched_forms ?aligned ?hyp_budget ~earlier piece =
  List.map ~f:skip_too_large
  @@ [
       lazy (matched_instance_form piece);
       lazy (matched_instance_form ~keep_scalar:true piece);
     ]
  @ (if !matched_instance_collections_only then
       [ lazy (matched_instance_form ~collections_only:true piece) ]
     else [])
  @ (if !matched_instance_chain_join_candidates then chain_join_forms_of piece
     else [])
  @
  if List.is_empty earlier then []
  else earlier_pieces_form ?aligned ?hyp_budget ~earlier piece

(* ===== The matched-instance form (end) ===== *)

let max_pieces = 64

(* Whether [pieces] keeps every conjunct's pieces however many there are.  A
   conjunction's pieces are the union of its sides' pieces, so their number
   grows only by addition (at most one per leaf of the conjunction tree, each
   side's count already bounded); the cap of [max_pieces] is needed for the
   product a disjunction's distribution makes, not for this.  Without the
   switch a conjunction whose sides give more than [max_pieces] pieces
   together is kept whole, so one more conjunct in a clause's conclusion can
   turn tens of small questions into one question holding them all: on a
   Rust-derived loop-body clause whose conclusion splits into 42 + 32 pieces
   the whole 19,000-node conjunction became one piece, whose instantiated
   form reached 4.6 million nodes and was left undecided, where the pieces
   are each proved in a fraction of a second.  With the switch a disjunction
   whose distribution would pass the bound is split along one side, as
   [pointwise_concat_candidates] has it, also when that is off: otherwise a
   side that is no longer kept whole could make its disjunction one piece
   where the switch off split it, so the switch never gives fewer pieces. *)
let uncapped_conjunction_pieces = ref false

(** formulas whose conjunction is equivalent to [phi] in every model: a
    conjunction is split into its conjuncts and a disjunction distributed
    over its disjuncts' pieces, stopping (and keeping the formula whole)
    where the number of pieces would exceed [max_pieces].  Exact, so each
    piece is a question of its own and [phi] is valid exactly when every
    piece is.  What it buys: a clause whose premise is a case split reads,
    in its disjunctive form, as [not premise \/ (not case1 /\ ... /\ not
    casen)]; on a Rust-derived input the solver left such a clause, asked
    whole, undecided after 120 seconds, while its pieces, each instantiated
    on its own terms, were decided in under a second each. *)
(** With [pointwise_concat_candidates] set, a disjunction [p \/ q] whose
    distribution would give more than [max_pieces] pieces is split along the
    side with more pieces only, the other side kept whole in each: [p \/ q]
    is equivalent to the conjunction of [p_i \/ q] when [p] is to the
    conjunction of the [p_i], so this is exact as well, and gives at most
    [max_pieces] pieces (each side's list is at most that long).  Why: a
    clause whose conclusion is a conjunction of several goals beside a few
    case splits was otherwise asked whole, every goal at once. *)
let one_side_pieces p ps q qs =
  if List.length ps >= List.length qs then
    List.map ps ~f:(fun p -> Formula.mk_or p q)
  else List.map qs ~f:(fun q -> Formula.mk_or p q)

let rec pieces phi =
  match phi with
  | Formula.BinaryOp (Formula.And, p, q, _) -> (
      let ps = pieces p and qs = pieces q in
      match List.length ps + List.length qs with
      | n when n <= max_pieces || !uncapped_conjunction_pieces -> ps @ qs
      | _ -> [ phi ])
  | Formula.BinaryOp (Formula.Or, p, q, _) ->
      let ps = pieces p and qs = pieces q in
      if List.length ps * List.length qs <= max_pieces then
        List.concat_map ps ~f:(fun p ->
            List.map qs ~f:(fun q -> Formula.mk_or p q))
      else if !pointwise_concat_candidates || !uncapped_conjunction_pieces then
        one_side_pieces p ps q qs
      else [ phi ]
  | _ -> [ phi ]

(** A piece with its sequence binders instantiated (with [extra]
    candidates for its positive sequence existentials, if given), then its
    integer binders ([instantiate_int]), then every read of a concatenation
    split by index, which is exact.  A strengthening of the piece, as each
    step is, and quantifier-free outside embedded formulas.  [max_nodes]
    bounds the instances each instantiation step builds, as [instantiate]
    describes; absent, nothing is bounded but the per-quantifier limits. *)
(* Raised by [instantiate_deep_unsimplified ~max_int_input:n] when the formula
   its integer step would instantiate is past [n] nodes; the form is then not
   built ([piece_forms] skips it as it skips a form forced to [None]). *)
exception Deep_form_too_large

(* With COAR_CHECK_INT_MEMO set (a diagnostic for a whole run, never for a
   measurement: every form is built twice), each deep form built inside a
   replay with [share_replayed_int_instances] on is also built with it off,
   from the same replay position and process-global counters, and the two are
   compared; one line per form goes to stderr, [int-memo-check equal] or
   [int-memo-check DIFFERENT]. *)
let int_memo_check = lazy (Option.is_some (Sys.getenv "COAR_CHECK_INT_MEMO"))

let int_memo_check_counters =
  Ast.Ident.
    [
      tvar_count;
      dontcare_count;
      dummy_tvar_count;
      svar_count;
      evar_count;
      rvar_count;
      pvar_count;
      parameter_cout;
      head_arg_count;
    ]

(* [build ()] with the memo on, after a build with it off from the same fresh
   names, the two compared (see [int_memo_check]); outside a replay
   [build ()] alone.  Rewinds the process-global counters, so it is safe only
   while no other domain draws fresh names. *)
let checked_against_unshared build =
  match Ast.Ident.replay_position () with
  | None -> build ()
  | Some (_, pos) ->
      let saved = List.map int_memo_check_counters ~f:Atomic.get in
      let rewind () =
        List.iter2_exn int_memo_check_counters saved ~f:Atomic.set;
        match Ast.Ident.replay_position () with
        | Some (_, pos') -> Ast.Ident.skip_replayed_fresh_names (pos - pos')
        | None -> ()
      in
      let unshared =
        share_replayed_int_instances := false;
        Exn.protect
          ~f:(fun () -> Result.try_with build)
          ~finally:(fun () -> share_replayed_int_instances := true)
      in
      (match unshared with
      | Error e when Timer.is_async e -> raise e
      | _ -> ());
      rewind ();
      let shared = Result.try_with build in
      let same =
        match (unshared, shared) with
        | Ok a, Ok b -> Stdlib.( = ) a b
        | Error a, Error b -> Stdlib.( = ) (Exn.to_string a) (Exn.to_string b)
        | _ -> false
      in
      eprintf "int-memo-check %s\n%!" (if same then "equal" else "DIFFERENT");
      Result.ok_exn shared

(* [?mid_size]: when given, called on the formula the integer step would
   instantiate (whether or not a gate is set), and its result is the size the
   [max_int_input] gate compares in place of [Formula.ast_size]; it may raise
   to abandon the build.  [instantiate_deep_shaped] uses it to gate a build
   that stands for another formula, and to inspect that stage. *)
let instantiate_deep_unsimplified ?extra ?equated ?max_nodes ?max_int_input
    ?mid_size ?(split_reads = true) piece =
  let gate phi =
    let size =
      match mid_size with
      | Some f -> lazy (f phi)
      | None -> lazy (Formula.ast_size phi)
    in
    if Option.is_some mid_size then ignore (Lazy.force size : int);
    match max_int_input with
    | Some n when Lazy.force size > n -> raise Deep_form_too_large
    | _ -> phi
  in
  let step name phi =
    !clause_trace
      (lazy (sprintf "deep form: %s (size %d)" name (Formula.ast_size phi)));
    phi
  in
  let ph name f x = Common.PhaseTime.with_phase name (fun () -> f x) in
  let build () =
    (if split_reads then ph "deep-rewrite" Ast.Evaluator.rewrite_seq_read_over_concat
     else Fn.id)
    @@ step "prefixes split"
    @@ ph "deep-split" split_prefixes
    @@ step "integer binders instantiated"
    @@ ph "deep-int" (instantiate_int ?equated ?nested:equated ?max_nodes)
    @@ gate
    @@ step "simplified"
    @@ ph "deep-simplify" Ast.Evaluator.simplify
    @@ Formula.nnf_of
    @@ step "sequence binders instantiated"
    @@ ph "deep-seq" (fun p -> right_nest_concats (instantiate ?extra ?max_nodes p)) piece
  in
  let build () =
    if Lazy.force int_memo_check && !share_replayed_int_instances then
      checked_against_unshared build
    else build ()
  in
  match instr_file with
  | None -> build ()
  | Some _ ->
      let r, secs = instr_time build in
      instr_line
        (sprintf "deep\tsecs=%.4f\tin=%d\tout=%d" secs (Formula.ast_size piece)
           (Formula.ast_size r));
      r

(** [instantiate_deep_unsimplified] is [instantiate_deep] without its last
    step, the [Ast.Evaluator.simplify] of the result, which is kept apart so
    that [PieceGroups] can simplify the part several pieces share once.

    [split_reads] (default [true]) is the read-over-concatenation split
    ([Ast.Evaluator.rewrite_seq_read_over_concat]); it is an identity, so with
    [~split_reads:false] the result is the same formula up to equivalence.  The
    split exists for a solver asked about a read of a concatenation under a
    quantified hypothesis over the parts, so a caller that keeps only
    quantifier-free results has no use for it, and it is costly there: on a
    Rust-derived clause whose instantiated piece reads concatenations of
    literals, the split took the formula from 50 thousand to 290 thousand
    nodes and the final simplification then to 6.2 million, in 45 s of CPU,
    where the same piece without the split simplifies in 0.02 s. *)
let instantiate_deep ?extra ?equated ?max_nodes ?split_reads piece =
  let r =
    instantiate_deep_unsimplified ?extra ?equated ?max_nodes ?split_reads piece
  in
  Common.PhaseTime.with_phase "deep-final-simplify" @@ fun () ->
  Ast.Evaluator.simplify r

(* ---------------------------------------------------------------------------
   One deep form per shape.  The pieces of a clause that distributes its
   conclusion over case splits are [R \/ L_1], ..., [R \/ L_k]: one premise
   part [R] and a few small quantifier-free literals [L_i] that pick a case.
   Their first deep forms were built one by one, each instantiating [R] again;
   on a Rust-derived loop-body clause 55 of 64 pieces came in families of
   eight sharing [R], each form 139,000-307,000 nodes and about a second to
   build under load.

   [share_deep_shapes] builds the deep form of [R \/ H], [H] a placeholder
   atom, once per family and replay position, and gives each piece that form
   with [H] replaced by its own literals as the simplification leaves them.
   It applies only to a literal that no step of the deep form reads: no
   subterm of a sequence, array, sort-variable or uninterpreted sort, no
   embedded formula, no lambda, no binder.  Every step of the deep form is
   then a map over the disjuncts whose choices (candidates, budgets, fresh
   names) are read off the rest of the formula only, except the
   simplification, which merges the comparisons of one pair of terms across
   disjuncts and orders them by their pairs; a piece whose literals compare a
   pair a top-level atom of [R]'s form also compares, or equal one of its
   disjuncts, or are not all such comparisons, is built as without the switch
   ([deep_shape_fill] puts the literals back where that ordering puts them).
   Contract (checked by a property test, and in a run by
   COAR_CHECK_DEEP_SHAPES): the form returned is the formula
   [instantiate_deep_unsimplified] builds without the switch, the same
   formula and not only an equivalent one, so every question asked of it is
   the same; the fresh names it draws and the replay position it leaves are
   those of that build; [Deep_form_too_large] is raised exactly when that
   build raises it. *)
let share_deep_shapes = ref false

(* counts since the process started: forms reused, forms built for sharing,
   pieces built without sharing because a check declined them *)
let deep_shape_hits = ref 0
let deep_shape_builds = ref 0
let deep_shape_declined = ref 0

let deep_shape_stats =
  lazy (Option.is_some (Sys.getenv "COAR_DEEP_SHAPE_STATS"))

let print_deep_shape_stats () =
  if Lazy.force deep_shape_stats then
    eprintf "deep-shape hits=%d builds=%d declined=%d\n%!" !deep_shape_hits
      !deep_shape_builds !deep_shape_declined

(* a nullary predicate variable no input spells: an atom every step of the
   deep form passes through unchanged *)
let deep_shape_hole =
  Formula.mk_atom
    (Atom.mk_pvar_app (Ast.Ident.Pvar "#deep_shape_hole") [] [])

let is_deep_shape_hole phi = Stdlib.( = ) phi deep_shape_hole

(* a sort no candidate collector of the deep form reads a term of *)
let deep_shape_inert_sort s =
  Option.is_none (elem_of_seq s)
  && match s with T_array.SArray _ | Sort.SVar _ | T_dt.SUS _ -> false | _ -> true

(* the length of a sequence variable, [seq.len v]: inert under the checks of
   [deep_shape_lengths_fit] *)
let deep_shape_len_var = function
  | Term.FunApp (T_seq.SqLen _, [ Term.Var (v, _, _) ], _) -> Some v
  | _ -> None

let rec deep_shape_inert_term t =
  Option.is_some (deep_shape_len_var t)
  || deep_shape_inert_sort (Term.sort_of t)
  &&
  match t with
  | Term.Var _ -> true
  | Term.FunApp ((T_bool.Formula _ | T_array.ALambda _), _, _) -> false
  | Term.FunApp (_, args, _) -> List.for_all args ~f:deep_shape_inert_term
  | Term.LetTerm _ -> false

(** Whether a top-level disjunct of a piece is a literal no step of the deep
    form reads: a theory atom, or its negation, over terms of inert sorts
    built without binders. *)
let deep_shape_inert_disjunct = function
  | Formula.Atom (Atom.App (Predicate.Psym _, args, _), _)
  | Formula.UnaryOp
      (Formula.Not, Formula.Atom (Atom.App (Predicate.Psym _, args, _), _), _)
    ->
      List.for_all args ~f:deep_shape_inert_term
  | _ -> false

(* the variables [v] of the lengths [seq.len v] a formula mentions *)
let deep_shape_len_vars phi =
  Set.to_list
  @@ Set.Poly.filter_map
       (Formula.filtered_terms_of phi ~f:(fun t ->
            Option.is_some (deep_shape_len_var t)))
       ~f:deep_shape_len_var

(* Whether a piece's literals that mention lengths [seq.len v] ([vs] their
   variables) leave every list the deep form's steps read as it is, given the
   formula [mid] the integer step instantiates and the premise part [rest].
   A length is read by two rules only: the offsets [t - len u], [t + len u]
   ([offset_int_candidates]), whose lengths are taken in order of first
   occurrence and cut at a bound, so a literal met earlier would reorder them;
   and the shifts of an index map ([index_map_shift_candidates]).  With the
   offsets restricted to the operands of chained relation reads
   ([offset_int_candidates_chain_only]), a length of a [v] that occurs in no
   array read of [mid] is filtered out wherever it occurs: the operands are
   arguments of array reads, and the integer instances of later rounds put
   integer terms, never [v], in a read's argument.  And [v] must occur free in
   [rest], so that the pool of ground sequences, a set, is the same. *)
(* a mutant switch for the test: [false] skips the check below *)
let deep_shape_length_check = ref true

let deep_shape_lengths_fit ~vs ~rest ~read_vars =
  (not !deep_shape_length_check)
  || List.is_empty vs
  || (not !index_map_shift_candidates)
     && ((not !offset_int_candidates) || !offset_int_candidates_chain_only)
     &&
     let free = Formula.tvs_of (Formula.or_of rest) in
     List.for_all vs ~f:(fun v -> Set.mem free v && not (Set.mem read_vars v))

(* the variables of the array reads of [mid], anywhere in it *)
let deep_shape_read_vars mid =
  Set.Poly.union_list
  @@ List.map ~f:Term.tvs_of @@ Set.to_list
  @@ Formula.filtered_terms_of mid ~f:(function
    | Term.FunApp (T_array.ASelect _, _, _) -> true
    | _ -> false)

(* the unordered pair of terms a comparison atom groups by in the
   simplification of a disjunction *)
let deep_shape_pair = function
  | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _)
    when Predicate.is_negatable_psym psym ->
      Some (t1, t2)
  | _ -> None

let deep_shape_pairs_meet (a1, a2) (b1, b2) =
  (Stdlib.( = ) a1 b1 && Stdlib.( = ) a2 b2)
  || (Stdlib.( = ) a1 b2 && Stdlib.( = ) a2 b1)

(* what the shared build saw of the formula its integer step instantiates:
   [None] when that formula was [true] (no placeholder), else its top-level
   disjuncts other than the placeholder *)
type deep_shape_mid = {
  others : Formula.t list option;
  draws_to_mid : int;
  read_vars : Ast.Ident.tvar Set.Poly.t;
      (* the variables of its array reads, for [deep_shape_lengths_fit] *)
  elems : int;  (* its top-level disjuncts, the placeholder included *)
  map_keys : (Term.t * Term.t) list;
      (* the term pairs of the comparisons that lead it, in its order *)
  hole_index : int;  (* the placeholder's place among its disjuncts *)
}

exception Deep_shape_declined

(* per domain: the replay scope the table is for, and the table, keyed by the
   premise part, the options and the replay position (-1: built without
   drawing a name), with the shared form, what it saw at its middle stage and
   the names it drew *)
let deep_shape_key :
    (string option ref
    * ( Formula.t list * bool option * int option * int option * int,
        Formula.t * deep_shape_mid * int )
      Hashtbl.t)
    Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> (ref None, Hashtbl.PolyDeep.create ()))

let reset_deep_shapes () =
  print_deep_shape_stats ();
  let current, table = Stdlib.Domain.DLS.get deep_shape_key in
  current := None;
  Hashtbl.clear table

(* [mid] checked against a piece's simplified literals [lits]: [`Declined]
   when the simplification of the whole piece could have merged one of them
   with a disjunct of the premise part, else the size the integer step's gate
   would see for the whole piece *)
let deep_shape_fit mid lits =
  match mid.others with
  | None -> `Size 1 (* [true]: the whole piece's formula is [true] too *)
  | Some others ->
      let other_pairs = List.filter_map others ~f:deep_shape_pair in
      if
        List.exists lits ~f:(fun l -> Option.is_none (deep_shape_pair l))
        || List.exists lits ~f:(fun l ->
            List.mem others l ~equal:Stdlib.( = )
            ||
            match deep_shape_pair l with
            | None -> false
            | Some p -> List.exists other_pairs ~f:(deep_shape_pairs_meet p))
      then `Declined
      else
        let all = others @ lits in
        match all with
        | [] -> `Size 1
        | _ ->
            `Size
              (List.sum (module Int) all ~f:Formula.ast_size
              + List.length all - 1)

(* The form the unshared build gives, from the shared [form], what the shared
   build saw at its middle stage [mid], and the piece's simplified literals
   [lits] (comparisons, each grouped by its pair of terms, in the order the
   simplification of a disjunction puts them).  The simplification of the
   whole piece would have put the literals' comparisons among the premise
   part's leading comparisons, ordered by descending pair as it orders them,
   and the placeholder's place among its other disjuncts held nothing; every
   later step maps each top-level disjunct of that stage to one subformula in
   place, under the same left-nested chain of disjunctions.  So the shared
   form is cut into its [mid.elems] blocks along that chain, the placeholder's
   block is dropped and the literals are merged in among the leading blocks by
   their pairs, and the blocks are chained again.  [None] when the form does
   not have that shape. *)
let deep_shape_fill form mid lits =
  if Formula.is_true form then Some form
  else
    let rec peel f k acc =
      if k = 0 then Some (f :: acc)
      else
        match f with
        | Formula.BinaryOp (Formula.Or, l, r, _) -> peel l (k - 1) (r :: acc)
        | _ -> None
    in
    match peel form (mid.elems - 1) [] with
    | None -> None
    | Some blocks ->
        let n_map = List.length mid.map_keys in
        if
          List.length blocks <> mid.elems
          || mid.hole_index < n_map
          || not (is_deep_shape_hole (List.nth_exn blocks mid.hole_index))
        then None
        else
          let leading, after = List.split_n blocks n_map in
          let after = List.filteri after ~f:(fun i _ -> i + n_map <> mid.hole_index) in
          let keyed_lits =
            (* [deep_shape_fit] declined any literal without a pair *)
            List.filter_map lits ~f:(fun l ->
                Option.map (deep_shape_pair l) ~f:(fun k -> (k, l)))
          in
          (* both lists in descending order of their pairs *)
          let rec merge xs ys =
            match (xs, ys) with
            | [], r | r, [] -> List.map r ~f:snd
            | ((kx, x) :: xs'), ((ky, y) :: ys') ->
                if Stdlib.compare kx ky >= 0 then x :: merge xs' ys
                else y :: merge xs ys'
          in
          match merge (List.zip_exn mid.map_keys leading) keyed_lits @ after with
          | [] -> Some (Formula.mk_false ())
          | b :: bs -> Some (List.fold bs ~init:b ~f:Formula.mk_or)

(** [instantiate_deep_unsimplified ?equated ?max_nodes ?max_int_input piece],
    with [share_deep_shapes] on inside a replay of fresh names, built through
    the premise part's shared form as described above; otherwise the plain
    build. *)
let instantiate_deep_shaped ?equated ?max_nodes ?max_int_input piece =
  let plain () =
    instantiate_deep_unsimplified ?equated ?max_nodes ?max_int_input piece
  in
  if not !share_deep_shapes then plain ()
  else
    match Ast.Ident.replay_position () with
    | None -> plain ()
    | Some (scope, pos0) -> (
        let declined why =
          incr deep_shape_declined;
          !clause_trace (lazy ("deep shape: declined, " ^ why));
          plain ()
        in
        let lits, rest =
          List.partition_tf (Formula.disjuncts_list_of piece)
            ~f:deep_shape_inert_disjunct
        in
        (* the literals as the simplification of the whole piece leaves
           them: it simplifies each disjunct alone and then merges the
           comparisons of one pair of terms, which [deep_shape_fit] checks
           do not meet the premise part's *)
        let stamp0 = Ast.Ident.fresh_stamp () in
        let lits =
          if List.is_empty lits then []
          else
            (* beside the placeholder, so that the merge of a disjunction
               (which also orients each comparison) applies even to a single
               literal, as it does in the whole piece *)
            List.filter ~f:(Fn.non is_deep_shape_hole)
            @@ Formula.disjuncts_list_of
                 (Ast.Evaluator.simplify
                    (Formula.or_of
                       (List.map lits ~f:Formula.nnf_of @ [ deep_shape_hole ])))
        in
        let constant f = Formula.is_true f || Formula.is_false f in
        let len_vars = deep_shape_len_vars (Formula.or_of lits) in
        match Ast.Ident.replay_position () with
        | Some (_, pos1) when Ast.Ident.fresh_stamp () <> stamp0 ->
            (* never seen: the inert literals have no lambda to rename *)
            Ast.Ident.skip_replayed_fresh_names (pos0 - pos1);
            declined "a literal drew a name"
        | _ when List.exists lits ~f:constant -> declined "a constant literal"
        | _ -> (
            let current, table = Stdlib.Domain.DLS.get deep_shape_key in
            if not (Option.equal String.equal !current (Some scope)) then (
              print_deep_shape_stats ();
              Hashtbl.clear table;
              current := Some scope);
            let key0 = (rest, equated, max_nodes, max_int_input) in
            let with_pos (r, e, m, i) p = (r, e, m, i, p) in
            let finish form mid ~draws =
              match
                if
                  deep_shape_lengths_fit ~vs:len_vars ~rest
                    ~read_vars:mid.read_vars
                then deep_shape_fit mid lits
                else `Declined
              with
              | `Declined -> None
              | `Size s -> (
                  match max_int_input with
                  | Some n when s > n ->
                      Ast.Ident.skip_replayed_fresh_names mid.draws_to_mid;
                      raise Deep_form_too_large
                  | _ -> (
                      match deep_shape_fill form mid lits with
                      | None -> None
                      | Some f ->
                          Ast.Ident.skip_replayed_fresh_names draws;
                          Some f))
            in
            match
              match Hashtbl.find table (with_pos key0 (-1)) with
              | Some _ as e -> e
              | None -> Hashtbl.find table (with_pos key0 pos0)
            with
            | Some (form, mid, draws) -> (
                match finish form mid ~draws with
                | Some f ->
                    incr deep_shape_hits;
                    !clause_trace (lazy "deep shape: reused");
                    f
                | None -> declined "merge or placeholder (reuse)")
            | None -> (
                (* build the premise part's form, gated and checked at its
                   middle stage for THIS piece's literals *)
                let mid = ref None in
                let mid_size phi =
                  let ds = Formula.disjuncts_list_of phi in
                  let others =
                    if Formula.is_true phi then None
                    else if List.count ds ~f:is_deep_shape_hole <> 1 then
                      raise Deep_shape_declined
                    else Some (List.filter ds ~f:(Fn.non is_deep_shape_hole))
                  in
                  let map_keys =
                    List.filter_map ~f:Fn.id
                    @@ List.take_while ~f:Option.is_some
                    @@ List.map ds ~f:deep_shape_pair
                  in
                  let hole_index =
                    Option.value_map ~default:(-1) ~f:fst
                      (List.findi ds ~f:(fun _ d -> is_deep_shape_hole d))
                  in
                  let draws_to_mid =
                    match Ast.Ident.replay_position () with
                    | Some (_, p) -> p - pos0
                    | None -> 0
                  in
                  let m =
                    {
                      others;
                      draws_to_mid;
                      read_vars = deep_shape_read_vars phi;
                      elems = List.length ds;
                      map_keys;
                      hole_index;
                    }
                  in
                  mid := Some m;
                  if
                    not
                      (deep_shape_lengths_fit ~vs:len_vars ~rest
                         ~read_vars:m.read_vars)
                  then raise Deep_shape_declined;
                  match deep_shape_fit m lits with
                  | `Declined -> raise Deep_shape_declined
                  | `Size s -> s
                in
                let global0 = Ast.Ident.fresh_stamp () - pos0 in
                let rewind () =
                  match Ast.Ident.replay_position () with
                  | Some (_, p) -> Ast.Ident.skip_replayed_fresh_names (pos0 - p)
                  | None -> ()
                in
                match
                  Common.PhaseTime.with_phase "deep-shape-build" @@ fun () ->
                  instantiate_deep_unsimplified ?equated ?max_nodes
                    ?max_int_input ~mid_size
                    (Formula.or_of (rest @ [ deep_shape_hole ]))
                with
                | exception Deep_shape_declined ->
                    rewind ();
                    declined "merge or placeholder (middle stage)"
                | form -> (
                    let draws =
                      match Ast.Ident.replay_position () with
                      | Some (_, p) -> p - pos0
                      | None -> 0
                    in
                    let mid = Option.value_exn !mid in
                    (* stored only when every name it drew was a replayed one,
                       so that a reuse that moves the replay on by [draws]
                       leaves every later draw as the build would *)
                    (match Ast.Ident.replay_position () with
                    | Some (scope', p) when String.equal scope scope' ->
                        if Ast.Ident.fresh_stamp () - p = global0 then
                          Hashtbl.set table
                            ~key:(with_pos key0 (if draws = 0 then -1 else pos0))
                            ~data:(form, mid, draws)
                    | _ -> ());
                    incr deep_shape_builds;
                    !clause_trace
                      (lazy
                        (sprintf
                           "deep shape: built (%d literals, premise part of \
                            %d disjuncts, %d nodes, hash %d, position %d)"
                           (List.length lits) (List.length rest)
                           (List.sum (module Int) rest ~f:Formula.ast_size)
                           (Hashtbl.hash (List.map rest ~f:Formula.str_of))
                           pos0));
                    (* [finish] moves the replay on by the draws again *)
                    rewind ();
                    match finish form mid ~draws with
                    | Some f -> f
                    | None ->
                        (* the placeholder was absorbed by a later step *)
                        declined "placeholder absorbed"))))

(* With COAR_CHECK_DEEP_SHAPES set (a diagnostic for a whole run, never for a
   measurement: every first deep form is built twice), each one built with
   [share_deep_shapes] on inside a replay is also built with it off, from the
   same replay position and counters, and the two are compared as formulas
   (and by the exception raised, and by the replay position); one line per form goes
   to stderr, [deep-shape-check equal] or [deep-shape-check DIFFERENT]. *)
let deep_shape_check = lazy (Option.is_some (Sys.getenv "COAR_CHECK_DEEP_SHAPES"))

let instantiate_deep_first ?equated ?max_nodes ?max_int_input piece =
  let shaped () =
    instantiate_deep_shaped ?equated ?max_nodes ?max_int_input piece
  in
  if not (Lazy.force deep_shape_check && !share_deep_shapes) then shaped ()
  else
    match Ast.Ident.replay_position () with
    | None -> shaped ()
    | Some (_, pos) ->
        let saved = List.map int_memo_check_counters ~f:Atomic.get in
        let rewind () =
          List.iter2_exn int_memo_check_counters saved ~f:Atomic.set;
          match Ast.Ident.replay_position () with
          | Some (_, pos') -> Ast.Ident.skip_replayed_fresh_names (pos - pos')
          | None -> ()
        in
        let unshared =
          share_deep_shapes := false;
          Exn.protect
            ~f:(fun () ->
              Result.try_with (fun () ->
                  instantiate_deep_unsimplified ?equated ?max_nodes
                    ?max_int_input piece))
            ~finally:(fun () -> share_deep_shapes := true)
        in
        (match unshared with
        | Error e when Timer.is_async e -> raise e
        | _ -> ());
        let pos_unshared = Ast.Ident.replay_position () in
        rewind ();
        let shared = Result.try_with shaped in
        let same =
          (match (unshared, shared) with
          | Ok a, Ok b -> Stdlib.( = ) a b
          | Error a, Error b -> Stdlib.( = ) (Exn.to_string a) (Exn.to_string b)
          | _ -> false)
          && Option.equal
               (fun (s, p) (s', p') -> String.equal s s' && p = p')
               pos_unshared (Ast.Ident.replay_position ())
        in
        eprintf "deep-shape-check %s\n%!" (if same then "equal" else "DIFFERENT");
        Result.ok_exn shared

(** The forms of a piece asked before its plain sequence instantiation:
    [instantiate_deep] without partner variants and then, when the piece has
    any, with them.  Partner variants are offered only in the second form
    because each one is a further instance of every positive sequence
    existential, and on an input that needed none of them they tripled the
    size of the question and left it undecided. *)
let deep_forms_with_first ?equated ?max_nodes ?max_int_input piece =
  let variants = partner_variants piece in
  let with_partners =
    if List.is_empty variants then []
    else
      [
        lazy
          (Ast.Evaluator.simplify
          @@ instantiate_deep_unsimplified ?equated ?max_nodes ?max_int_input
             ~extra:(fun sort ->
               List.filter variants ~f:(fun t ->
                   Stdlib.( = ) (Term.sort_of t) sort))
             piece);
      ]
  in
  let first =
    lazy (instantiate_deep_first ?equated ?max_nodes ?max_int_input piece)
  in
  (first, lazy (Ast.Evaluator.simplify (Lazy.force first)) :: with_partners)

(** [deep_forms_with_first] also returns the first form before its last
    [Ast.Evaluator.simplify], as a lazy value the first form is computed from,
    so that forcing both builds the instantiation once. *)
let deep_forms ?equated ?max_nodes piece =
  snd (deep_forms_with_first ?equated ?max_nodes piece)

(* Whether [prove_valid] first asks a clause of several pieces through one
   instantiation of the whole clause ([shared_pieces]) before instantiating
   each piece on its own.  Set by the coordinator from its configuration;
   process-wide, as [instantiate_element_binders] is. *)
let share_premise_instances = ref false

(** The pieces of [nnf] (a clause in negation normal form, simplified, as
    [prove_valid] splits it) instantiated ONCE: [instantiate_deep] of the
    whole clause as [prepare_piece] leaves it, then [pieces] of the result.

    Contract, for VALIDITY only: every returned formula valid implies [nnf]
    valid.  [prepare_piece] keeps validity, [instantiate_deep] strengthens,
    and [pieces] is exact, so the conjunction of the result is equivalent to
    a strengthening of [nnf]; nothing may be read from a countermodel.  The
    result is quantifier-free outside embedded formulas, as
    [instantiate_deep]'s is, which is what makes splitting it afterwards
    exact rather than a further choice of instances.

    Its candidate terms are drawn from the whole clause, so they are those of
    every piece together (each binder still offered at most
    [max_terms_per_binder]); the instances are therefore not in general the
    ones a piece asked alone would get, which is why [prove_valid] falls back
    to the pieces when this does not prove the clause.

    Why: a clause whose distribution over its case splits gives many pieces
    repeats the premise disjuncts in each, and each piece's own instantiation
    builds them again.  What it was measured to do, on a Rust-derived
    loop-body clause of 64 pieces: building the forms took 1.5 s of CPU
    against 28.5 s for the pieces one by one, but the split of the
    instantiated clause gave 57 pieces of about 2.3 MB each (the pieces' own
    forms are at most 1.8 MB, and 8 of them simplify to [true]), because the
    larger pool gives more instances and the case splits are no longer
    isolated; of three sampled, two were proved by a solver in 2-3 s and the
    first was undecided at 20 s, where the pieces' own first forms are
    proved at once.  Hence off by default. *)
let shared_pieces nnf = pieces (instantiate_deep (prepare_piece nnf))

(** Whether some form of [forms] is proved: each is forced and given to
    [ask] in order, stopping at the first answered [`Valid] (a form forced to
    [None] is skipped), as [List.exists] would.  With [second_pass =
    Some (deferred, ask_long)], [ask] is meant to be a short-budget asker:
    when no form is proved in that pass, the forms whose answer [deferred]
    selects (the ones that ran out of the short budget) are asked again, in
    their original order, with [ask_long], stopping at the first [`Valid].
    Only [`Valid] is read, so the second pass changes when a proof is found,
    never whether one is sound; and a form that needs the long budget is
    still asked with it.  Each form is forced at most once, in the same order
    as with [second_pass = None].  With [true_forms_proved] set, a form that
    is literally [true] counts as answered [`Valid] without being asked
    ([proved_by_syntax]). *)

let force_traced form =
  if not (Lazy.is_val form) then !clause_trace (lazy "building a form");
  let started = Common.Clock.now_float () in
  let r = Lazy.force form in
  !form_built_trace
    (Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) started))
    r;
  r

(* Whether a form that is literally [true] is taken as proved without being
   asked ([first_proved_with]).  Set by the coordinator from its configuration
   ([ladder_proof_shortcuts_no_unknown_query]); process-wide, as the other form
   switches are.  [false] asks it like any other form. *)
let true_forms_proved = ref false

(* How many forms [first_proved_with] took as proved because they were
   literally [true], in this process; read by the tests *)
let true_forms_taken = ref 0

(* [true] when [form] is literally [true] and [true_forms_proved] is set.
   Exact: [true] is valid in every model, so the only answers an asker could
   give it other than [`Valid] are ones that say nothing about the form -- a
   budget cut, a refusal past a deadline, a killed copy.  Such a form reached
   the external solver's retry ([undecided_piece_prover]) as its largest
   built form, which spent a process start to have [(assert false)] proved. *)
let proved_by_syntax form =
  !true_forms_proved && Formula.is_true form
  && (incr true_forms_taken;
      true)

(* [?on_timeout]: asked once, right after the first form whose question ran
   out of its budget (and, with [second_pass], between the two passes when a
   form was deferred), before any later form; a [true] proves the piece.
   Used to ask a proof-only attempt that is cheap where the forms are not
   ([lemma_after_form_timeout]); it must answer [true] only for a valid
   piece.  Without it the forms are asked exactly as before. *)
let first_proved_with ?(proved_by_syntax = fun _ -> false) ~force ?second_pass
    ?on_timeout ~ask forms =
  let tried = ref false in
  let after_timeout () =
    match on_timeout with
    | Some attempt when not !tried ->
        tried := true;
        attempt ()
    | _ -> false
  in
  match second_pass with
  | None ->
      List.exists forms ~f:(fun form ->
          match force form with
          | Some form when proved_by_syntax form -> true
          | Some form -> (
              match ask form with
              | `Valid -> true
              | `Timeout -> after_timeout ()
              | _ -> false)
          | None -> false)
  | Some (deferred, ask_long) ->
      let retry = ref [] in
      List.exists forms ~f:(fun form ->
          match force form with
          | Some form when proved_by_syntax form -> true
          | Some form -> (
              match ask form with
              | `Valid -> true
              | r ->
                  if deferred r then retry := form :: !retry;
                  false)
          | None -> false)
      || ((not (List.is_empty !retry)) && after_timeout ())
      || List.exists (List.rev !retry) ~f:(fun form ->
             match ask_long form with `Valid -> true | _ -> false)

let first_proved ?second_pass ~ask forms =
  first_proved_with ~force:Lazy.force ?second_pass ~ask forms

(* [first_proved] over formulas, each form's build traced ([force_traced]) *)
let first_proved_formula ?second_pass ?on_timeout ~ask forms =
  first_proved_with ~proved_by_syntax ~force:force_traced ?second_pass
    ?on_timeout ~ask forms

(* Whether [prove_valid] also asks each piece, after every other form (the
   grouped question of [PieceGroups] included, which is asked before any
   piece's own forms), its [contextual_ite_form].  Set by the coordinator from
   its configuration; process-wide, as [witness_forms] is.  The coordinator
   sets it only together with the process-wide [Evaluator.contextual_ite] off,
   so that every other form is the one asked without the contextual rewrite. *)
let contextual_ite_extra_form = ref false

(** [Some] form of a prepared [piece] with the contextual [ite] rule
    ([Evaluator.elim_onepoint_and_split_binders_contextual]) applied before
    and after its plain sequence instantiation, and [None] when that is
    literally the plain form [plain] (so that no question is asked twice).

    Contract: the result implies [piece] in every model -- the contextual
    rewrite is an equivalence in every model and the instantiation a
    strengthening -- so a proof of its validity is one of [piece]'s, and
    nothing may be read from a countermodel.  Asked as the last form of a
    piece, it can only turn a piece no other form proves into a proved one:
    every piece proved with [contextual_ite_extra_form] off is proved, by the
    same question, with it on (up to the names of fresh variables the form
    draws when it is forced, which a later piece's forms are then built
    with, and which rename a question without changing it).  What it buys: the rewrite drops a bound array
    the array-read one-point rule left only in the else branch of a lambda,
    which the plain form still binds; applied in place to every form instead,
    it changed the forms the grouped questions are built from, and on a
    Rust-derived call-site input the grouped questions then proved 8 pieces
    where without it they proved 21. *)
let contextual_ite_form ~plain piece =
  let f =
    Ast.Evaluator.elim_onepoint_and_split_binders_contextual
    @@ right_nest_concats
    @@ instantiate
         (Ast.Evaluator.elim_onepoint_and_split_binders_contextual piece)
  in
  if Stdlib.( = ) f plain then None else Some f

(* Whether [piece_forms_with_first] builds a piece's plain sequence
   instantiation only when it is forced (see there).  Set by the coordinator
   from its configuration; process-wide, as the other form switches are. *)
let lazy_plain_form = ref false

(** The forms [prove_valid] asks of one piece, in the order it asks them:
    [prepare_piece], then its [matched_instance_form] when that switch is
    on, its [deep_forms], its plain sequence instantiation,
    and the switched-on further forms, [contextual_ite_form] last.
    The plain form is built first, before
    the deep ones, so that the fresh names those draw do not rename its query;
    the others are built only when forced.  A form forced to [None] is
    skipped. *)
(* The node budget of the plain and deep instantiations [piece_forms] builds
   for one piece ([instantiate]'s and [instantiate_int]'s [max_nodes]); [None],
   the default, bounds nothing but the per-quantifier limits.  Set by the
   coordinator from its configuration; process-wide, as
   [max_matched_form_size] is.  A bounded instantiation is still a
   strengthening of the piece (a quantifier met after the budget is left as it
   is), so the bound can only lose a proof.  Why: the first deep form of a
   piece of a Rust-derived clause was seen to take more than a minute to build
   with no question asked, the time in polymorphic comparison inside the
   instantiation, which is what stopped the verdict on that input. *)
let piece_max_nodes : int option ref = ref None

(* The size, in formula nodes, past which a piece's deep form is not built
   when the formula its integer step would instantiate exceeds it
   ([instantiate_deep_unsimplified]'s [max_int_input]); [None], the default,
   builds every deep form.  Not building a form only loses a proof.  Why: the
   integer step on a sequence-instantiated form of 80,000 and 270,000 nodes did
   not return in 45-70 s, which stopped the verdict, while every deep form a
   question proved on the same inputs was under 20,000 nodes as asked.  Set by
   the coordinator; process-wide, as [piece_max_nodes] is. *)
let piece_max_int_input_nodes : int option ref = ref None

let piece_forms_with_first_lead ?(earlier = []) piece =
  let max_nodes = !piece_max_nodes in
  let earlier_pieces = earlier in
  let step name = !clause_trace (lazy ("piece forms: " ^ name)) in
  let piece = prepare_piece piece in
  step "prepared";
  (* with [lazy_plain_form], the plain instantiation is built when its turn
     to be asked comes (or the contextual-ite form compares against it), and
     not when the piece's forms are listed; the forms and their order are
     the same.  Why: the forms are listed for every piece of a clause before
     its first forms are grouped, and on a clause of twelve history pieces
     the plain instantiations, which come after the deep forms and are
     rarely reached, took two to three seconds each under load, most of a
     120 s budget with the questions taking under a second in all *)
  let plain = lazy (right_nest_concats (instantiate ?max_nodes piece)) in
  if not !lazy_plain_form then (
    ignore (Lazy.force plain : Formula.t);
    step "plain instantiation built");
  let witness = if !witness_forms then [ lazy (witness_form piece) ] else [] in
  let drop =
    if !drop_array_hypotheses then [ lazy (drop_array_hypotheses_form piece) ]
    else []
  in
  (* with [chain_focus_push_witnesses], the chain-focused forms whose
     existential the push witnesses filled, with the opaque laws kept,
     first: a few kilobytes each, and on a loop's history step they are the
     forms that decide, while the forms before them run to their budget *)
  let pushed =
    if !chain_focus_push_witnesses then
      chain_focus_forms_of ~pushed_only:true piece
    else []
  in
  (* the chain-focused and associativity-matched forms, last *)
  let focused =
    (if !chain_focus_forms then chain_focus_forms_of piece else [])
    @ if !chain_assoc_match_forms then assoc_match_forms_of piece else []
  in
  step "focused forms listed";
  (* the matched-instance form, first: it is small, and a piece it proves
     costs no deep form *)
  let matched =
    if !matched_instance_forms then matched_forms ~earlier:earlier_pieces piece
    else []
  in
  step "matched forms listed";
  (* the contextual-ite form, after every other one *)
  let contextual =
    if !contextual_ite_extra_form then
      [ lazy (contextual_ite_form ~plain:(Lazy.force plain) piece) ]
    else []
  in
  let first, deep =
    deep_forms_with_first ?max_nodes ?max_int_input:!piece_max_int_input_nodes
      piece
  in
  step "deep forms listed";
  let deep =
    List.map deep ~f:(fun form ->
        lazy (try Some (Lazy.force form) with Deep_form_too_large -> None))
  in
  (* which kind each form of the list below is, by position: a trace reader
     can then name the form a question proved *)
  step
    (sprintf
       "order pushed %d, matched %d, deep %d, plain 1, witness %d, drop %d, \
        focused %d, contextual %d"
       (List.length pushed) (List.length matched) (List.length deep)
       (List.length witness) (List.length drop) (List.length focused)
       (List.length contextual));
  ( first,
    List.map pushed ~f:(Lazy.map ~f:Option.some)
    @ matched @ deep
    @ List.map (plain :: witness) ~f:(Lazy.map ~f:Option.some)
    @ drop
    @ List.map focused ~f:(Lazy.map ~f:Option.some)
    @ contextual,
    List.length pushed + List.length matched )

(** [piece_forms_with_first_lead piece] is [(first, forms, n)]: [forms] the
    forms [prove_valid] asks of [piece] in order, [first] the first DEEP form
    before its last [Ast.Evaluator.simplify] (a lazy value the deep form in
    [forms] is forced from, so forcing both builds the instantiation once), and
    [n] the number of forms that come before the deep ones (the push-witness
    and matched-instance forms), none of which forces [first]. *)
let piece_forms_with_first ?earlier piece =
  let first, forms, _ = piece_forms_with_first_lead ?earlier piece in
  (first, forms)

(** [piece_forms_with_first] also returns the piece's first form before its
    last [Ast.Evaluator.simplify] (the first of [piece_forms] is that
    simplification of it, forced from the same lazy value). *)
let piece_forms ?earlier piece = snd (piece_forms_with_first ?earlier piece)

(* Whether [prove_valid] asks the first forms of a clause's pieces in groups
   ([PieceGroups]) before asking them one by one.  Set by the coordinator from
   its configuration; process-wide, as [instantiate_element_binders] is. *)
let group_piece_forms = ref false

(* Whether [PieceGroups] groups the pieces' first forms before their last
   simplification and simplifies each grouped question once, instead of
   grouping the simplified forms.  Set by the coordinator; process-wide. *)
let share_piece_simplify = ref false

(* A last attempt at a piece no form proved, after its last form
   ([prove_valid], [PieceGroups]): [Some prove] asks [prove] about the piece's
   largest form built so far ([best_built_form]), and a [true] proves the
   piece; [None], the default, asks nothing more.  Set by the coordinator from
   its configuration (an external solver's proof); process-wide, as
   [group_piece_forms] is, so it applies to every [prove_valid] once set.
   Contract asked of [prove]: [true] only when its argument is valid in every
   model.  Every form implies its piece, so the piece is then valid, and
   [prove] is never asked for a refutation. *)
let undecided_piece_prover : (Formula.t -> bool) option ref = ref None

(* [lemma_application_prover]: asked about a piece (the piece itself, not a
   form) after every form and [undecided_piece_prover] have failed; [None],
   the default, asks nothing.  Set by the coordinator
   ([lemma_application_ms_no_unknown_query]); process-wide.  Contract asked of
   it: [true] only when the piece is valid in every model.  Asked last, it can
   only add a proof. *)
let lemma_application_prover : (Formula.t -> bool) option ref = ref None

(* [lemma_before_retry]: ask [lemma_application_prover] before
   [undecided_piece_prover] instead of after it.  Each reads only a proof, so
   the order changes what a piece costs and never what is proved of it.  Set by
   the coordinator ([lemma_application_before_cvc5_no_unknown_query]);
   process-wide. *)
let lemma_before_retry = ref false

(* [lemma_after_form_timeout]: ask [lemma_application_prover] as soon as one
   of a piece's forms has run out of its budget, before the piece's later
   forms, instead of only after all of them.  Each reads only a proof, so the
   order changes what a piece costs and never what is proved of it; and the
   attempt is made only on a piece that has already cost a form's whole
   budget, so a piece some form proves before any timeout is asked exactly as
   without the switch.  Why: on a Rust-derived iterator law the route proves
   in a few seconds, three of the piece's thirteen forms each ran to their
   10 s budget (34 s of the piece's 37 s) before the route was reached.  Set by
   the coordinator ([lemma_application_after_form_timeout_no_unknown_query]);
   process-wide. *)
let lemma_after_form_timeout = ref false

(* The budget of the caller of [prove_valid], for the two last attempts
   ([lemma_application_prover], [undecided_piece_prover]).  Each prover is set
   once per process with a budget of its own (the external solver's is
   seconds), so a caller that runs under a budget of its own -- a stage of the
   ladder with a per-question cap and a whole budget -- bounds its questions
   through its [ask] but not those attempts: on a Rust-derived bit-set input
   the early point pin, documented as 1 s per question and 10 s in all, spent
   about 28 s of its 32-38 s in seven external-solver retries asked from
   [proved_at].  [with_last_attempt_budget within f] runs [f] with [within]
   (the caller's remaining per-question budget in ms, [None] once spent) in
   force in this domain: an attempt is not started when [within ()] is
   [None], and a prover reading [last_attempt_ms] gets at most what [within]
   gives.  Only proofs are read from either attempt, so a bound can only
   leave a piece undecided, never change what is proved.  Outside such a
   scope, nothing changes. *)
let last_attempt_budget_key : (unit -> int option) option Stdlib.Domain.DLS.key
    =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let with_last_attempt_budget within f =
  let old = Stdlib.Domain.DLS.get last_attempt_budget_key in
  Stdlib.Domain.DLS.set last_attempt_budget_key (Some within);
  Exn.protect ~f ~finally:(fun () ->
      Stdlib.Domain.DLS.set last_attempt_budget_key old)

(** [ms] bounded by the budget in force ([with_last_attempt_budget]): [Some
    ms] outside a scope, [None] when the scope's budget is spent, and
    otherwise the smaller of [ms] and what is left. *)
let last_attempt_ms ms =
  match Stdlib.Domain.DLS.get last_attempt_budget_key with
  | None -> Some ms
  | Some within -> Option.map (within ()) ~f:(Int.min ms)

let last_attempt_allowed () =
  match Stdlib.Domain.DLS.get last_attempt_budget_key with
  | None -> true
  | Some within -> Option.is_some (within ())

(* How many pieces [undecided_piece_prover] was asked about, and proved, in
   this process; read by the coordinator's trace and the tests *)
let undecided_piece_asked = ref 0
let undecided_piece_proved = ref 0

(** The largest (in formula nodes) of [forms] that has been built, i.e. forced
    to [Some] form, and [None] when none has.  Size stands for the number of
    instances, which is what a form is grown by.  Forces nothing. *)
let best_built_form forms =
  List.filter_map forms ~f:(fun form ->
      if Lazy.is_val form then Lazy.force form else None)
  |> List.fold ~init:None ~f:(fun best f ->
         match best with
         | Some (_, n) when n >= Formula.ast_size f -> best
         | _ -> Some (f, Formula.ast_size f))
  |> Option.map ~f:fst

(* Whether a form is asked, before itself, as the three cases of the position
   of an index against the prefix of a concatenation it reads
   ([index_split_candidates]).  Set by the coordinator from its configuration
   ([case_split_index_forms_no_unknown_query]); process-wide, as
   [witness_forms] is. *)
let case_split_index_forms = ref false

(* When [Some r], [index_cases_outcome] asks a candidate split only when each
   of its three case questions is at most [r] times the form's AST size, and
   skips it, asking nothing, otherwise.  Set by the coordinator from its
   configuration ([case_split_index_max_size_ratio_no_unknown_query]) and
   reset with the other switches; process-wide, as [case_split_index_forms]
   is.  [None] asks every candidate.

   Why: the cases pay where deciding the index decides the guards of most of
   the form's reads, and then each case question is a small part of the form
   (on a Rust-derived fold over a mapped iterator, 1-3% of the size of the
   two largest forms, with most [ite] terms gone, each decided in 0.1-0.2 s).
   Where the reads the case decides are a small part of the form, each case
   question keeps 86-100% of the form's size and most of its [ite] terms,
   and was proved about as slowly as the whole (10.6-14.3 s each against
   11 s for the form), so asking by cases tripled the piece's cost.  The size
   test tells the two apart before any question, independently of the
   machine's load, which a short case budget does not. *)
let index_case_max_size_ratio : float option ref = ref None

(* at most this many forms of one piece are asked by cases, and each by at
   most this many candidate splits *)
let max_case_split_forms = 2
let max_case_split_candidates = 2

(** The splits [prove_by_index_cases] offers for a form [phi]: the pairs
    [(i, u)] of an index [i] and a sequence term [u] such that [phi] reads
    [seq.nth (u ++ w) i], [i] being [t] or [t + c] with [t] an integer
    variable free in [phi] and [c] an integer literal, and [u ++ w] mentioning
    only variables free in [phi] ([u] all operands of the chain but the
    last); distinct pairs, the largest offset [c] first (ties in the order
    [phi] lists its terms), at most [max_case_split_candidates].

    Why: a loop step that extends a history by one element is checked at a
    skolemized position [k] of the extended history [h ++ unit e], reading it
    at [k] and at [k + 1]: below the last position the premise's universal at
    [k] gives the step, at the last one the step's own facts do.  Each such
    read is an [ite] on [k + c < len h] once reads over concatenations are
    split, a form holds several of them, and the solver was seen to time out
    at 20 s on the whole form (and on its case [k < len h]) while deciding
    each of the cases [k + 1 < len h], [k + 1 = len h], [k + 1 > len h] in
    about 2 s or less.  The read at the larger offset is the one whose
    boundary separates the premise's positions from the step's, hence the
    order. *)
let index_split_candidates phi =
  let free = Formula.tvs_of phi in
  let offset_of = function
    | Term.Var (t, T_int.SInt, _) when Set.mem free t -> Some Z.zero
    | Term.FunApp
        ( T_int.Add,
          ( [ Term.Var (t, T_int.SInt, _); Term.FunApp (T_int.Int c, [], _) ]
          | [ Term.FunApp (T_int.Int c, [], _); Term.Var (t, T_int.SInt, _) ] ),
          _ )
      when Set.mem free t ->
        Some c
    | _ -> None
  in
  Formula.filtered_terms_of phi ~f:(function
    | Term.FunApp
        (T_seq.SqNth _, [ (Term.FunApp (T_seq.SqConcat _, _, _) as s); i ], _)
      ->
        Option.is_some (offset_of i) && Set.is_subset (Term.tvs_of s) ~of_:free
    | _ -> false)
  |> Set.to_list
  |> List.filter_map ~f:(function
    | Term.FunApp (T_seq.SqNth se, [ s; i ], _) -> (
        match (offset_of i, List.rev (flatten_concat s)) with
        | Some c, _ :: (_ :: _ as rev_prefix) ->
            Some (c, (i, concat_of se (List.rev rev_prefix)))
        | _ -> None)
    | _ -> None)
  |> List.stable_sort ~compare:(fun (c1, _) (c2, _) -> Z.compare c2 c1)
  |> List.map ~f:snd
  |> List.remove_consecutive_duplicates ~equal:Stdlib.( = )
  |> List.fold ~init:[] ~f:(fun acc p ->
         if List.mem acc p ~equal:Stdlib.( = ) then acc else acc @ [ p ])
  |> Fn.flip List.take max_case_split_candidates

(** [phi] (a disjunction) with the length of a sequence variable replaced,
    in every top-level disjunct but one, by what that one disjunct, a
    disequation [len v != e] (up to a linear rearrangement: [len v] with
    coefficient 1 or -1 in a linear integer disequation), says it is
    elsewhere; disjunct by disjunct in order, each disequation read off the
    formula as the earlier ones left it, one whose [e] mentions [len v] left
    alone.  Exact: [len v != e \/ psi(len v)] and [len v != e \/ psi(e)]
    agree in every model, since where the first disjunct is false [len v] is
    [e].  Replaced everywhere, embedded guards of [ite]s included, and only
    when no binder of [phi] binds a variable of [len v] or [e], so that each
    occurrence replaced is the one the disjunct speaks of.
    Why: a history's lengths are tied by premises such as [len accs = len s
    + 1], and a case literal or an [ite] guard over one length is decided by
    the contextual rule only once both are written over the same one. *)
let subst_length_equations phi =
  let is_len_var = function
    | Term.FunApp (T_seq.SqLen _, [ Term.Var _ ], _) -> true
    | _ -> false
  in
  let equation = function
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ l; r ], _), _)
      when Stdlib.( = ) (Term.sort_of l) T_int.SInt -> (
        let monomials c =
          Ast.Normalizer.linear_int_monomials_of (Ast.Value.Int c)
            (T_int.mk_sub l r)
        in
        match monomials Z.one with
        | exception exn_ when not (Timer.is_async exn_) -> None
        | m ->
            Map.Poly.to_alist m
            |> List.find_map ~f:(fun (k, v) ->
                   match (k, v) with
                   | Some t, Ast.Value.Int c
                     when is_len_var t
                          && (Z.equal c Z.one || Z.equal c Z.minus_one) ->
                       (* [t] with coefficient -1, so that [t] is the rest *)
                       let m =
                         if Z.equal c Z.one then monomials Z.minus_one else m
                       in
                       let e =
                         Ast.AffineTerm.mk_int_term (Map.Poly.remove m (Some t))
                       in
                       if
                         Set.is_empty
                           (Term.filtered_terms_of e ~f:(fun u ->
                                Stdlib.( = ) u t))
                       then Some (t, e)
                       else None
                   | _ -> None))
    | _ -> None
  in
  let bound = bound_vars_of phi in
  let rebound t e =
    Set.exists (Set.union (Term.tvs_of t) (Term.tvs_of e)) ~f:(Set.mem bound)
  in
  let ds = Formula.disjuncts_list_of phi in
  List.fold (List.range 0 (List.length ds)) ~init:ds ~f:(fun ds j ->
      match equation (List.nth_exn ds j) with
      | Some (t, e) when not (rebound t e) ->
          List.mapi ds ~f:(fun k d ->
              if k = j then d
              else
                Formula.map_term d ~f:(fun u ->
                    if Stdlib.( = ) u t then e else u))
      | _ -> ds)
  |> Formula.or_of

(** the question of one case: [phi \/ lit] with every [ite] whose guard
    the case decides replaced by its branch (the contextual rule of
    [Ast.Evaluator.elim_onepoint_and_split_binders_contextual], under which
    [phi]'s context holds [not lit]), after the lengths the premises equate
    are written over one ([subst_length_equations]) and each prefix of a
    concatenation is split on where it ends
    ([Ast.Evaluator.rewrite_seq_prefix_over_concat]: the visited prefix
    [extract (h ++ unit e) 0 k] of a history, which the case decides), and
    then simplified; equivalent to [phi
    \/ lit] in every model.  Why: the case is asked so that the solver need
    not split the reads' guards itself, and a form whose guards are left in
    place was seen to take 6 s in a separate solver process and to run out of
    the 10 s budget in process. *)
let case_form phi lit =
  Ast.Evaluator.simplify
  @@ Ast.Evaluator.elim_onepoint_and_split_binders_contextual
  @@ Ast.Evaluator.rewrite_seq_prefix_over_concat
  @@ subst_length_equations
  @@ Formula.mk_or phi (Formula.mk_atom lit)

(** [phi] proved by cases on [i] against [len u] for one of
    [index_split_candidates phi]: [phi \/ i >= len u], [phi \/ i != len u]
    and [phi \/ i <= len u] each asked, in that order, stopping at the first
    not proved; a candidate all of whose three are proved proves [phi], the
    three cases [i < len u], [i = len u], [i > len u] covering every model.
    Only a proof is read.

    [`Proved] when some candidate's three cases are proved; [`Undecided] as
    soon as a case question is answered neither valid nor invalid (a timeout
    or an unknown), with no later case or candidate asked; [`Not_proved]
    otherwise.  Contract: [`Proved] only from three [`Valid] answers.

    With [index_case_max_size_ratio] set to [Some r], a candidate is asked
    only when each of its three case questions has an AST size
    ([Formula.ast_size]) at most [r] times [phi]'s; the three are then built
    before the first is asked, and a candidate failing the test is skipped
    without any question, as one whose cases are not proved.  So the test
    only removes case questions: when every candidate is skipped the
    outcome is [`Not_proved] and the form is asked whole. *)
let index_cases_outcome ~ask phi =
  let size = lazy (Formula.ast_size phi) in
  let rec candidates = function
    | [] -> `Not_proved
    | (i, u) :: rest -> (
        let se = Option.value_exn (elem_of_seq (Term.sort_of u)) in
        let len = T_seq.mk_len se u in
        let lits =
          [ T_int.mk_geq i len; T_bool.mk_neq i len; T_int.mk_leq i len ]
        in
        let rec cases = function
          | [] -> `Proved
          | form :: more -> (
              match ask (Lazy.force form) with
              | `Valid -> cases more
              | `Invalid _ -> `Not_proved
              | _ -> `Undecided)
        in
        let asked forms =
          !clause_trace
            (lazy
              (sprintf "index cases: %s against seq.len %s" (Term.str_of i)
                 (Term.str_of u)));
          match cases forms with
          | `Not_proved -> candidates rest
          | (`Proved | `Undecided) as r -> r
        in
        match !index_case_max_size_ratio with
        | None -> asked (List.map lits ~f:(fun lit -> lazy (case_form phi lit)))
        | Some ratio ->
            let forms = List.map lits ~f:(case_form phi) in
            let sizes = List.map forms ~f:Formula.ast_size in
            let bound = ratio *. Float.of_int (Lazy.force size) in
            if List.for_all sizes ~f:(fun n -> Float.(of_int n <= bound)) then
              asked (List.map forms ~f:Lazy.from_val)
            else (
              !clause_trace
                (lazy
                  (sprintf
                     "index cases: %s against seq.len %s skipped, case sizes \
                      %s of %d above ratio %g"
                     (Term.str_of i) (Term.str_of u)
                     (String.concat ~sep:"/" (List.map sizes ~f:Int.to_string))
                     (Lazy.force size) ratio));
              candidates rest))
  in
  candidates (index_split_candidates phi)

(** Whether [index_cases_outcome] proves [phi]. *)
let prove_by_index_cases ~ask phi =
  match index_cases_outcome ~ask phi with `Proved -> true | _ -> false

(* When [Some ask_short], the case questions of [ask_with_index_cases] are
   asked with [ask_short] instead of the piece's own [ask]: an asker with a
   shorter budget, answering [`Valid] only for a proof, [`Invalid ()] only for a
   countermodel and [`Undecided] otherwise (out of its budget included).  Set
   by the coordinator around its sequence instantiation from its
   configuration ([case_split_index_budget_no_unknown_query]) and reset to
   [None] with the other switches; process-wide, as [case_split_index_forms]
   is.  [None] asks the cases as the form is asked.

   Why: a case question can decide and still be slow.  On a Rust-derived
   loop-step clause whose whole form a solver proves in about 11 s, each of
   its three cases was also proved, in 10.6-14.3 s each, so asking by cases
   tripled the clause's cost and the stop-at-undecided guard never fired
   (every case decided); while on the input the cases are for every case
   question decides in 0.1-0.2 s.  A short case budget turns a slow case
   into an undecided one, which the guard then reads as "ask the form
   whole", at the cost of that budget once per piece.  Only the time a proof
   is found at changes: a proof by cases is still three [`Valid] answers,
   and a form not proved by cases is asked whole with its own budget. *)
let index_case_ask :
    (Formula.t -> [ `Valid | `Invalid of unit | `Undecided ]) option ref =
  ref None

(** [ask] wrapped so that the first [max_case_split_forms] forms with a split
    candidate are asked by cases ([index_cases_outcome]) before being asked
    whole: a proof by cases is a proof of the form, and a form not so proved
    is asked as it would have been.  Once a case question is left undecided,
    no further case question is asked through this [ask] (one piece's forms):
    the forms are then asked only whole, as without the cases.  The case
    questions are asked with [index_case_ask] when that is set (a shorter
    budget, so that a slow case counts as undecided), and with [ask]
    otherwise.
    Why: a case question that does not decide runs to the full question
    budget, and on a Rust-derived input whose piece no case split proves the
    two forms' four candidates cost 1 s for each case refuted and 10 s for
    each that ran out, about 23 s in front of the whole forms' own questions,
    while on the input the cases are for every case question decided within
    5 s and the first candidate tried proved its form.  Asks the same
    questions as before wherever every case question decides (within the
    case budget, when [index_case_ask] sets one). *)
let ask_with_index_cases ~ask =
  let split = ref 0 in
  let stalled = ref false in
  let outcome phi =
    match !index_case_ask with
    | None -> index_cases_outcome ~ask phi
    | Some ask_short -> index_cases_outcome ~ask:ask_short phi
  in
  fun phi ->
    if
      (not !stalled)
      && !split < max_case_split_forms
      && not (List.is_empty (index_split_candidates phi))
    then (
      incr split;
      match outcome phi with
      | `Proved -> `Valid
      | `Not_proved -> ask phi
      | `Undecided ->
          stalled := true;
          !clause_trace
            (lazy "index cases: a case left undecided, no more cases asked");
          ask phi)
    else ask phi

(* How many pieces [piece_proved] found proved by its lead stage ([lead > 0])
   in this process; read by the coordinator's trace and by the tests *)
let lead_forms_unasked_proved = ref 0

(** Whether a piece whose forms are [forms] is proved: [first_proved_formula],
    and when that fails, [undecided_piece_prover] (when set) on
    [best_built_form].  Adds a question after every other one of the piece, so
    it cannot lose a proof [first_proved_formula] gives, and its proof is one
    of a form, hence of the piece.

    With [lead = n > 0], the first [n] forms (the push-witness and
    matched-instance forms, which come first in [piece_forms]) are asked as a
    stage of their own before the rest, without [lemma_after_form_timeout]'s
    attempt after a form that ran out of its budget; the attempt is made, at
    most once as before, among the remaining forms.  So the forms asked and
    their order are those of [lead = 0] (with [second_pass], each stage makes
    its own two passes), only the point at which the lemma route is tried
    moves after the lead forms, and only proofs are read either way.
    [best_built_form] is taken over all [forms]. *)
let piece_proved ?second_pass ?piece ?(lead = 0) ~ask forms =
  let ask_first =
    if !case_split_index_forms then ask_with_index_cases ~ask else ask
  in
  let lemma_tried = ref false in
  let lemma () =
    match (!lemma_application_prover, piece) with
    | Some prove, Some piece when not !lemma_tried && last_attempt_allowed ()
      ->
        lemma_tried := true;
        prove piece
    | _ -> false
  in
  let on_timeout =
    if !lemma_after_form_timeout then Some lemma else None
  in
  let lead_forms, rest = List.split_n forms (max lead 0) in
  ((not (List.is_empty lead_forms))
   && Common.PhaseTime.with_phase "group-lead-forms" (fun () ->
          first_proved_formula ?second_pass ~ask:ask_first lead_forms)
   && (incr lead_forms_unasked_proved;
       true))
  || first_proved_formula ?second_pass ?on_timeout ~ask:ask_first rest
  || (!lemma_before_retry && lemma ())
  || (match !undecided_piece_prover with
     | None -> false
     | Some _ when not (last_attempt_allowed ()) -> false
     | Some prove -> (
         match best_built_form forms with
         | None -> false
         | Some form when proved_by_syntax form -> true
         | Some form ->
             incr undecided_piece_asked;
             !clause_trace
               (lazy
                 (sprintf "undecided piece: its largest form (size %d) asked once more"
                    (Formula.ast_size form)));
             let proved = prove form in
             if proved then incr undecided_piece_proved;
             !clause_trace
               (lazy
                 (sprintf "undecided piece: %s"
                    (if proved then "proved by the last attempt" else "still undecided")));
             proved))
  || ((not !lemma_before_retry) && lemma ())

(* What the grouping did in this process: grouped questions asked, how many of
   them were proved, and how many pieces those proved.  Read by the coordinator
   for its trace; written only here. *)
let group_questions_asked = ref 0
let group_questions_proved = ref 0
let group_pieces_proved = ref 0

(* How many grouped questions [group_question_max_nodes] kept from being asked
   in this process; read by the tests *)
let group_questions_skipped = ref 0

(* The size, in formula nodes, past which a grouped question of [PieceGroups]
   is not asked: the question is built (and simplified, with
   [share_piece_simplify]) as it would be asked, and when it is larger the
   group's pieces are asked their own forms at once, exactly as when the
   grouped question is asked and not proved.  [None], the default, asks every
   grouped question.  Not asking it changes which questions are asked and never
   which answer is read: only a proof of a grouped question is ever read, and
   every piece it would have proved is still asked its own forms.  Why: on a
   Rust-derived input the first forms of nine pieces, each an integer step that
   turned about ten thousand nodes into a quarter of a million, made a grouped
   question of 570,000 nodes, which Z3 held for 44 s under a 10 s budget, after
   which the run had no time left for the per-piece forms that prove it; the
   grouped questions proved on the same inputs were under 90,000 nodes.  Set
   by the coordinator from its configuration; process-wide, as
   [group_piece_forms] is. *)
let group_question_max_nodes : int option ref = ref None

(* Whether [PieceGroups.prove] lists each piece's forms and builds its first
   form with the fresh names replayed from one scope per clause
   ([Ast.Ident.with_replayed_fresh_names]), so that the pieces' first forms
   name the instances of the premise they share alike and the grouping finds
   that common part without renaming it.  Set by the coordinator from its
   configuration; process-wide, as [group_piece_forms] is.  Why: on a
   Rust-derived loop-body clause of 79 pieces each first form drew 180-500
   fresh names of its own, nearly all in the premise's 269,000-node instance,
   so the grouping renamed three quarters of every form back into the first
   one's names before it could see what they share, 7-13 s under load.  With
   the names replayed the renaming is skipped: what two first forms share is
   then spelled alike, and the grouping compares them as they are. *)
let replay_piece_names = ref false

(* Whether [PieceGroups.prove] lets a piece join any open group rather than
   only the group of the pieces just before it.  Set by the coordinator from
   its configuration; process-wide, as [group_piece_forms] is.  Why: a
   loop-body clause's pieces fall into a few families with different
   premise instances (about 268,000, 108,000 and 100,000 nodes on a
   Rust-derived input), interleaved in the clause's order, so grouping only
   consecutive pieces closed a group at every change of family: 18 grouped
   questions, each re-simplifying, converting and asking the family's common
   part, where three would do. *)
let group_open_pieces = ref false

(* Whether [PieceGroups.prove] asks a piece's forms that come before its deep
   forms (the push-witness and matched-instance forms) before it builds the
   deep first form the grouping compares, and leaves a piece one of them proves
   out of every group.  A piece they do not prove is grouped as before, its
   per-piece forms then starting after them, so no question is asked twice.
   Each answer read is a proof of a form, hence of its piece, so what a proof
   shows is unchanged; only which questions are asked, and when, changes.  Why:
   on a Rust-derived loop clause of twelve pieces each deep first form took
   about a second to build at idle and three under load, eleven of the twelve
   pieces were then proved by their matched-instance form (a few thousand
   nodes, answered in 0.1-0.2 s), and the grouped questions over the deep
   forms proved two.  On the consecutive path only, unless
   [lead_forms_under_open_grouping] is set too.  Set by the coordinator from
   its configuration; process-wide, as [group_piece_forms] is. *)
let lead_forms_before_grouping = ref false

(* Whether [lead_forms_before_grouping] also acts with [group_open_pieces]:
   each piece is then listed for open grouping as the consecutive path lists
   it, a piece its lead forms prove joining no group and a member listed again
   after its group's question fails starting after the lead forms it already
   had asked.  Off, the open path asks no lead stage: every piece is listed by
   its first form and grouped, and a piece asked alone is asked its forms in
   [piece_forms]'s order, as when [lead_forms_before_grouping] is off.  Ignored
   while [lead_forms_for_unasked_groups] is set, which decides the open path's
   lead forms by itself, and while [lead_forms_open_min_nodes] is set, which
   leads only the groups past its bound.  Contract as [lead_forms_before_grouping]'s: only a
   proof of a form is read, and no question is asked twice.  Why off: on one
   Rust-derived counter clause the lead stage proved six pieces before
   grouping where the grouped and per-piece questions ran to the cap, while
   on a Rust-derived map clause its proofs, 0.7-2.2 s each over about 24
   pieces, displaced cheaper grouped questions over the same pieces, and the
   file, at the edge of its budget, lost answers.  Set by the
   coordinator from its configuration; process-wide. *)
let lead_forms_under_open_grouping = ref false

(* How many pieces [lead_forms_before_grouping] settled before grouping in
   this process; read by the coordinator's trace and by the tests *)
let lead_forms_pieces_proved = ref 0

(* Whether, with [group_open_pieces], the lead forms of a piece (its
   push-witness and matched-instance forms, before its deep ones) are asked
   as a stage of their own ([piece_proved]'s [lead]) exactly for the pieces
   whose first form no grouped question is asked about: the members of a
   group whose question is past [group_question_max_nodes], a group of one,
   and a piece with no first form to group on.  Every other piece is listed
   and grouped as with [lead_forms_before_grouping] off, so a group within
   the bound is asked as it is then, its pieces never asked a lead form
   before its question; [lead_forms_before_grouping] and
   [lead_forms_under_open_grouping] do not act on the open path while this is
   set.  It acts whether or not those are set.

   Contract.  Only a proof of a form, which implies its piece, is read.  No
   question is asked twice: a piece's lead forms and the rest of its forms
   are a split of the one list [piece_forms] gives, asked in that order.
   Cost: the pieces affected are asked the same forms in the same order as
   without the switch, since the lead forms come first in [piece_forms]
   anyway; what moves is the lemma route's one attempt
   ([lemma_after_form_timeout]), which is made after the lead forms rather
   than right after the first of them to run out of its budget, so a piece
   costs at most its lead forms' questions before that attempt.  Why: on a
   Rust-derived counter clause the grouped question over five pieces was
   459,038 nodes and was skipped by the bound, and the sixth piece, a group of
   one, had a matched-instance form time out at 10 s; the lemma route tried
   next ran for 60 s without a proof, where the piece's next matched-instance
   forms proved it (the lead stage before grouping, which asks them without
   that attempt, proved all six pieces at about 8 s each), while on another
   Rust-derived clause the same lead stage before grouping displaced ten
   cheap grouped proofs and cost 17-52 s.  Set by the coordinator from its
   configuration; process-wide, as [group_piece_forms] is. *)
let lead_forms_for_unasked_groups = ref false

(* With [group_open_pieces], the size, in formula nodes, past which a grouped
   question is judged unlikely to pay: a group of two or more pieces whose
   grouped question (built, and simplified with [share_piece_simplify], as it
   would be asked) has more nodes is not asked, and its members are asked
   alone with their lead forms (the push-witness and matched-instance forms)
   as a stage of their own ([piece_proved]'s [lead]).  Every other group is
   asked its grouped question first, exactly as with the switch off, and a
   group of one or a piece with no first form is asked its forms as then.
   While it is [Some _] the open path asks no lead stage before grouping
   ([lead_forms_under_open_grouping] is not read), so the lead forms move
   only for the members of a group past the bound.  It acts beside
   [group_question_max_nodes] and [lead_forms_for_unasked_groups]: a group
   past either bound is not asked, and its members are led when it is past
   this one or when that switch is set.  [None], the default, changes
   nothing.

   Contract.  Only a proof of a form, which implies its piece, is read, and
   no question is asked twice: a member's lead forms and the rest of its
   forms are a split of the one list [piece_forms] gives, asked in that
   order.  What moves is which questions are asked: the grouped question of
   a large group is not, and the lemma route's one attempt
   ([lemma_after_form_timeout]) is made after a led member's lead forms.

   Why a size and not a count: on a Rust-derived counter clause seven
   pieces made a grouped question of about 428,000 nodes that proved
   nothing in about 90 s while the pieces' lead forms proved six of them in
   about 45 s; on a Rust-derived bit-set clause 128 pieces fell into two
   small grouped questions that proved them all in seconds, where asking
   every piece's lead forms first cost 129 serial questions.  A solver-free
   count of the grouped questions the Rust-derived inputs build found the
   ones past 380,000 nodes on four files only, so the size of the question,
   which is built anyway, is the shape that separates the two cases.  Set by the coordinator from
   its configuration; process-wide, as [group_piece_forms] is. *)
let lead_forms_open_min_nodes : int option ref = ref None

(* How many groups [lead_forms_open_min_nodes] led in this process; read by
   the coordinator's trace and by the tests *)
let lead_forms_open_gated_groups = ref 0

(* Whether, with [group_open_pieces] and [replay_piece_names], the top-level
   disjuncts of the pieces' first forms are interned per clause: a disjunct
   structurally equal to one an earlier piece of the clause had is replaced by
   that one's entry, physically.  The lists compared, kept and asked are equal
   to those without it disjunct for disjunct, so every comparison answers the
   same, the groups are the same and each grouped question is the same
   formula; only the sharing changes.  Why: the members of one family spell
   their shared premise instance alike but build it afresh, so joining a piece
   compared each of its ~1,000 common disjuncts structurally twice (the
   intersection, then the residue) and the grouped question's residues a third
   time, 7-12 s of a loop-body clause's 95 pieces; interned, each disjunct is
   compared structurally once (against the intern table), and the tables of the
   intersection and the residue hash and compare interned entries by a number
   ([PieceGroups.entry]'s [id]), which is exact because the intern table gives
   structurally equal disjuncts one entry. *)
let intern_piece_disjuncts = ref true

(** Several pieces' first forms asked as one question.

    The situation.  A clause [b1 \/ ... \/ bm \/ (h1 /\ ... /\ hn)] in
    disjunctive form splits into pieces [b1 \/ ... \/ bm \/ hk]: every piece
    repeats the premise disjuncts.  Each piece is prepared and instantiated on
    its own, so its first form is [S_k \/ R_k], where [S_k] is the premise
    part as instantiated for that piece and [R_k] the rest; the [S_k] of two
    pieces are typically the same formula up to the names of the fresh free
    variables each piece's own skolemization and instantiation drew.  On a
    Rust-derived loop-body clause of 64 pieces, pieces 16 and 17 have first
    forms of 1,043 top-level disjuncts each, 1,042 of which are equal up to such
    a renaming, and each was asked of the solver separately at about 3.6 s.

    The question.  For a group of pieces with first forms [F_1 ... F_n]:
    - [G_k] is [F_k] with an injective renaming [rho_k] of the free variables
      of [F_k] that are not free in the clause, chosen so that as many of
      [G_k]'s top-level disjuncts as possible are literally disjuncts of
      [G_1] ([align]; [rho_1] is the identity);
    - [C] is the multiset of top-level disjuncts common to every [G_k], and
      [R_k] the rest of [G_k]'s;
    - the question is [\/ C \/ (/\_k \/ R_k)].

    Contract, for VALIDITY only: the question valid implies every [F_k]
    valid, hence, by [prove_valid]'s contract for a form, every piece valid.
    (1) Renaming the free variables of a formula injectively, without capture
    ([Formula.subst] renames a binder a replacement would be captured by),
    keeps its validity: validity is truth under every assignment to the free
    variables, and an injective renaming is a bijection between the
    assignments.  So [G_k] is valid exactly when [F_k] is.  The clause's own
    free variables are not renamed, and the targets are fresh variables of
    [F_1] that [F_k] does not otherwise use freely ([align] checks both).
    (2) A conjunction is valid exactly when each conjunct is, whatever free
    variables the conjuncts share, so [/\_k G_k] is valid exactly when every
    [G_k] is.  (3) [G_k] is [\/ C \/ \/ R_k] up to associativity and
    commutativity of [\/], and [/\_k (X \/ Y_k)] is [X \/ /\_k Y_k] by
    distributivity; both hold in every model, so the question is equivalent
    to [/\_k G_k].  Only a [`Valid] answer is read: a countermodel of the
    question is one of some [G_k], which is a renamed form, and a form's
    countermodel says nothing about its piece.

    What it cannot lose.  The [F_k] are the very first forms [piece_forms]
    builds, forced here instead of in [first_proved]; when the grouped
    question is not proved, each piece of the group is asked its forms, the
    first one being the same value, exactly as without grouping.  So grouping
    only adds a question in front; it changes when an answer is found, and it
    can cost the time of the grouped question, never an answer the per-piece
    questions give -- up to the fresh names of forms built after the first,
    which are drawn at other points of the name counter than without
    grouping, and which rename a question without changing it.

    Which pieces form a group: consecutive ones, while the common part stays
    at least half of what it was ([min_common_share]) and the pieces' residues
    together stay no larger than it ([max_residue_share]), so that the
    grouped question is at most about twice the size of one form.  A piece
    that does not fit starts the next group; a group of one is not asked as a
    group.  None of this affects soundness; it bounds the size of what is
    asked.

    With [share_piece_simplify] set, the [F_k] above are the first forms
    before their last [Ast.Evaluator.simplify] (the [U_k], with [F_k] the
    simplification of [U_k]), and the question asked is the simplification
    of the question built from them, so that the disjuncts the pieces share
    are simplified once per group rather than once per piece.  The contract
    is kept: [Ast.Evaluator.simplify] returns a formula equivalent to its
    argument in every model under every assignment (the variables it
    introduces are bound), so the question asked is equivalent to
    [/\_k rho_k(U_k)], which by (1)-(3) is valid exactly when every [U_k]
    is, that is, exactly when every [F_k] is.  So the shared result is
    equivalent, in every model, to the conjunction of the renamed
    per-piece simplifications [rho_k(F_k)] -- what the question without the
    switch is equivalent to -- though it is not the same formula, which is
    why it is a switch of its own.  A piece whose group is not proved is
    asked its own forms, whose first is still [F_k], forced only then.  Why:
    on a Rust-derived loop-body clause of 56 non-trivial pieces, the last
    simplification of the pieces' first forms (up to 1.8 MB each) took 30.7 s
    of CPU against 9.4 s for everything before it, and simplifying the
    grouped questions instead took 1.3 s; the renaming is
    found on the unsimplified forms exactly as on the simplified ones (the
    signature and literal comparison below are syntactic and need no
    simplified input). *)
module PieceGroups = struct
  (* the variables of [phi] in [cands], with their sorts, in order of first
     occurrence *)
  let in_order ~cands phi =
    let seen = Hash_set.Poly.create () in
    (* the variables met that are not in [cands], so that [cands] is asked
       about each variable once rather than at each of its occurrences *)
    let others = Hash_set.Poly.create () in
    let acc = ref [] in
    Formula.iter_term phi ~f:(function
      | Term.Var (x, s, _)
        when (not (Hash_set.mem seen x)) && not (Hash_set.mem others x) ->
          if Set.mem cands x then (
            Hash_set.add seen x;
            acc := (x, s) :: !acc)
          else Hash_set.add others x
      | _ -> ());
    List.rev !acc

  (* the free variables of [form] a renaming may touch: those not in [keep] *)
  let renameable ~keep form = Set.diff (Formula.tvs_of form) keep

  (* A disjunct's signature, which a disjunct keeps under a renaming of the
     variables in [cands]: its size and the sorts of those variables in order
     of first occurrence; and those variables.  Two disjuncts with one
     signature are only candidates for being one disjunct renamed: the
     matching below is a heuristic for choosing the renaming, and what is
     common is decided afterwards by literal equality. *)
  let signature ~cands d =
    let vs = in_order ~cands d in
    ((Formula.ast_size d, List.map vs ~f:snd), List.map vs ~f:fst)

  (** the signatures of a reference form's disjuncts, each with the queue of
      the variable lists of the reference disjuncts that have it, in order *)
  let ref_keys_of ~keep form =
    let cands = renameable ~keep form in
    let ref_keys = Hashtbl.Poly.create () in
    List.iter (List.rev (Formula.disjuncts_list_of form)) ~f:(fun d ->
        let k, vs = signature ~cands d in
        Hashtbl.update ref_keys k ~f:(function
          | None -> [ vs ] | Some l -> vs :: l));
    ref_keys

  (** [form] renamed towards the reference whose signatures are [ref_keys]
      ([ref_keys_of]): each disjunct of [form], in order, is matched to the
      first unused reference disjunct of its signature, and its renameable
      variables are mapped positionally to that disjunct's, provided the
      mapping stays a function and injective; a match that would break either
      is skipped.  The renaming is applied, by capture-avoiding substitution,
      only if no target is also a free variable of [form] left unrenamed, so
      that it is injective on the free variables of [form]; otherwise [form]
      is returned as it is.  Either way the result is [form] under an
      injective renaming of free variables outside [keep], returned with the
      renaming as [(from, to, sort)] triples.  Cost: one traversal of [form]
      per disjunct and one substitution of the whole; a key built by renaming
      every disjunct instead cost about 0.5 s per 1.8 MB form. *)
  let align_with_renaming ~keep ~ref_keys form =
    let cands = renameable ~keep form in
    let avail = Hashtbl.copy ref_keys in
    let rho = Hashtbl.Poly.create () in
    let used = Hash_set.Poly.create () in
    let sorts = Hashtbl.Poly.create () in
    List.iter (Formula.disjuncts_list_of form) ~f:(fun d ->
        let vs = in_order ~cands d in
        List.iter vs ~f:(fun (x, s) -> Hashtbl.set sorts ~key:x ~data:s);
        let k = (Formula.ast_size d, List.map vs ~f:snd) in
        match Hashtbl.find avail k with
        | Some (ws :: rest) ->
            let pairs = List.zip_exn (List.map vs ~f:fst) ws in
            let fits =
              List.for_all pairs ~f:(fun (v, w) ->
                  match Hashtbl.find rho v with
                  | Some w' -> Ast.Ident.tvar_equal w w'
                  | None -> not (Hash_set.mem used w))
              (* two positions of this disjunct must not ask one variable for
                 two targets, nor two variables for one *)
              && List.for_all pairs ~f:(fun (v, w) ->
                     List.for_all pairs ~f:(fun (v', w') ->
                         Bool.equal
                           (Ast.Ident.tvar_equal v v')
                           (Ast.Ident.tvar_equal w w')))
            in
            if fits then (
              Hashtbl.set avail ~key:k ~data:rest;
              List.iter pairs ~f:(fun (v, w) ->
                  if not (Hashtbl.mem rho v) then (
                    Hashtbl.set rho ~key:v ~data:w;
                    Hash_set.add used w)))
        | _ -> ());
    let unrenamed = Set.filter cands ~f:(fun x -> not (Hashtbl.mem rho x)) in
    if Hashtbl.is_empty rho || Hash_set.exists used ~f:(Set.mem unrenamed)
    then (form, [])
    else
      let pairs =
        List.filter_map (Hashtbl.to_alist rho) ~f:(fun (v, w) ->
            if Ast.Ident.tvar_equal v w then None
            else Option.map (Hashtbl.find sorts v) ~f:(fun s -> (v, w, s)))
      in
      let sub =
        Map.Poly.of_alist_exn
        @@ List.map pairs ~f:(fun (v, w, s) -> (v, Term.mk_var w s))
      in
      (Formula.subst sub form, pairs)

  let align ~keep ~ref_keys form = fst (align_with_renaming ~keep ~ref_keys form)

  let size_of = List.sum (module Int) ~f:Formula.ast_size

  (* the multiset intersection of [xs] and [ys], in the order of [xs] *)
  let inter xs ys =
    let count = Hashtbl.PolyDeep.create () in
    List.iter ys ~f:(fun y -> Hashtbl.update count y ~f:(function
      | None -> 1 | Some n -> n + 1));
    List.filter xs ~f:(fun x ->
        match Hashtbl.find count x with
        | Some n when n > 0 -> Hashtbl.set count ~key:x ~data:(n - 1); true
        | _ -> false)

  (* [ys] less the multiset [xs] *)
  let minus ys xs =
    let count = Hashtbl.PolyDeep.create () in
    List.iter xs ~f:(fun x -> Hashtbl.update count x ~f:(function
      | None -> 1 | Some n -> n + 1));
    List.filter ys ~f:(fun y ->
        match Hashtbl.find count y with
        | Some n when n > 0 -> Hashtbl.set count ~key:y ~data:(n - 1); false
        | _ -> true)

  (* A top-level disjunct carried with its [Formula.ast_size] and its
     [Hashtbl.PolyDeep] hash, each computed at most once.  The grouping loop
     below compares every new piece's disjuncts with the common part and
     re-summed the size of every member's disjuncts at each new piece, so
     with the sizes and hashes recomputed it was quadratic in the group: on a
     Rust-derived clause whose pieces' first forms ran to megabytes, the
     re-summed sizes and the re-hashed disjuncts took about a fifth of the
     whole run.  Invariant: [size] and [hash] are those of [d]. *)
  (* [id]: -1, or, for an entry interned by [intern_piece_disjuncts], a number
     no other interned entry of the clause has; interned entries are equal
     exactly when their ids are, since the intern table gives structurally
     equal disjuncts one entry.  A table never holds both kinds. *)
  type entry = { d : Formula.t; size : int Lazy.t; hash : int Lazy.t; id : int }

  let entry d =
    {
      d;
      size = lazy (Formula.ast_size d);
      hash = lazy (Hashtbl.PolyDeep.hashable.hash d);
      id = -1;
    }

  let interned_entry id d = { (entry d) with id }

  let entries_of ds = List.map ds ~f:entry
  let formulas_of es = List.map es ~f:(fun e -> e.d)
  let size_of_entries = List.sum (module Int) ~f:(fun e -> Lazy.force e.size)

  (* the table [inter_entries] and [minus_entries] use: the hash and the
     comparison of [Hashtbl.PolyDeep] on the entries' formulas, so the same
     buckets and the same answers as [inter] and [minus] *)
  let entry_hashable : entry Base.Hashable.t =
    {
      Base.Hashable.hash =
        (fun e -> if e.id >= 0 then e.id else Lazy.force e.hash);
      compare =
        (fun e1 e2 ->
          if e1.id >= 0 && e2.id >= 0 then Int.compare e1.id e2.id
          else Stdlib.compare e1.d e2.d);
      sexp_of_t = (fun _ -> Sexp.Atom "<entry>");
    }

  (* [inter] on entries: [formulas_of (inter_entries xs ys)] is
     [inter (formulas_of xs) (formulas_of ys)], and the entries kept are
     those of [xs] *)
  let inter_entries xs ys =
    let count = Hashtbl.Using_hashable.create ~hashable:entry_hashable () in
    List.iter ys ~f:(fun y -> Hashtbl.update count y ~f:(function
      | None -> 1 | Some n -> n + 1));
    List.filter xs ~f:(fun x ->
        match Hashtbl.find count x with
        | Some n when n > 0 -> Hashtbl.set count ~key:x ~data:(n - 1); true
        | _ -> false)

  (* [minus] on entries, in the same sense as [inter_entries] *)
  let minus_entries ys xs =
    let count = Hashtbl.Using_hashable.create ~hashable:entry_hashable () in
    List.iter xs ~f:(fun x -> Hashtbl.update count x ~f:(function
      | None -> 1 | Some n -> n + 1));
    List.filter ys ~f:(fun y ->
        match Hashtbl.find count y with
        | Some n when n > 0 -> Hashtbl.set count ~key:y ~data:(n - 1); false
        | _ -> true)

  (* [(inter_entries xs ys, minus_entries ys (inter_entries xs ys))] in one
     pass over each list: the counts [inter_entries] builds over [ys] are
     decremented by the entries of [xs] it keeps, so what is matched of each
     key is the count it lost, and [minus_entries] removes exactly that many
     of the key's first occurrences in [ys] *)
  let inter_minus_entries xs ys =
    let count = Hashtbl.Using_hashable.create ~hashable:entry_hashable () in
    List.iter ys ~f:(fun y -> Hashtbl.update count y ~f:(function
      | None -> 1 | Some n -> n + 1));
    let matched = Hashtbl.Using_hashable.create ~hashable:entry_hashable () in
    let inter =
      List.filter xs ~f:(fun x ->
          match Hashtbl.find count x with
          | Some n when n > 0 ->
              Hashtbl.set count ~key:x ~data:(n - 1);
              Hashtbl.update matched x ~f:(function None -> 1 | Some m -> m + 1);
              true
          | _ -> false)
    in
    let rest =
      List.filter ys ~f:(fun y ->
          match Hashtbl.find matched y with
          | Some m when m > 0 -> Hashtbl.set matched ~key:y ~data:(m - 1); false
          | _ -> true)
    in
    (inter, rest)

  (* An upper bound on [size_of_entries (inter_entries xs ys)] read off the
     entries' cached hashes alone: the sizes of the entries of [xs] whose hash
     some entry of [ys] has.  Every entry [inter_entries] keeps is one of
     them, since it is equal to an entry of [ys] and equal entries hash
     alike; no structural comparison is made *)
  let inter_size_bound xs ys =
    let hashes = Hash_set.create (module Int) in
    List.iter ys ~f:(fun y -> Hash_set.add hashes (Lazy.force y.hash));
    List.sum (module Int) xs ~f:(fun x ->
        if Hash_set.mem hashes (Lazy.force x.hash) then Lazy.force x.size else 0)

  let min_common_share = 2 (* the common part may shrink to 1/2 of itself *)
  let max_residue_share = 1 (* residues together at most 1x the common part *)

  (** the grouped question of renamed forms whose top-level disjuncts are
      [disjs] with common part [common] *)
  let question common disjs =
    Formula.or_of
      (common
      @ [ Formula.and_of
            (List.map disjs ~f:(fun ds -> Formula.or_of (minus ds common))) ])

  (* [question] on entries: [question_entries common disjs] is
     [question (formulas_of common) (List.map disjs ~f:formulas_of)] *)
  let question_entries common disjs =
    Formula.or_of
      (formulas_of common
      @ [ Formula.and_of
            (List.map disjs ~f:(fun ds ->
                 Formula.or_of (formulas_of (minus_entries ds common)))) ])

  (** [`Valid] when every piece of [ps] is proved -- by the grouped question
      of its group, or else by one of its own [piece_forms] -- and
      [`Undecided] at the first piece that is not, as [prove_valid]'s
      per-piece loop.  [keep] is the clause's free variables. *)
  let prove ?second_pass ~ask ~keep ps =
    (* each piece with the pieces before it, for [piece_forms]'s hypotheses *)
    let ps = List.mapi ps ~f:(fun k p -> (List.take ps k, p)) in
    (* with [replay_piece_names], the scope every piece's forms are listed
       and its first form built in ([with_replayed_fresh_names]) *)
    let scope =
      if !replay_piece_names then Some (Ast.Ident.fresh_replay_scope ())
      else None
    in
    let in_scope : 'a. (unit -> 'a) -> 'a =
     fun f ->
      match scope with
      | Some scope -> Ast.Ident.with_replayed_fresh_names ~scope f
      | None -> f ()
    in
    (* [members] are the group's pieces, each with its forms, its first
       form's top-level disjuncts (renamed towards the first member's) and
       their total size; [common] is their common part, the fold of
       [inter_entries] over the members' disjuncts from the first member's,
       which [go] has kept as the group grew *)
    (* [unasked_lead]: the members are asked their lead forms as a stage of
       their own ([piece_proved]'s [lead], [lead_forms_for_unasked_groups])
       when no grouped question is asked about them: a group of one, or a
       question past [group_question_max_nodes] *)
    (* [lead_bound]: [lead_forms_open_min_nodes] on the open path; a group
       whose question is past it is not asked and its members are asked
       their lead forms as a stage of their own *)
    let ask_group ?(unasked_lead = false) ?lead_bound members common =
      let proved_alone ~lead (forms, _, _, piece) =
        let forms, n = Lazy.force forms in
        piece_proved ?second_pass ~piece
          ~lead:(if lead then n else 0) ~ask forms
      in
      match members with
      | [] -> true
      | [ member ] -> proved_alone ~lead:unasked_lead member
      | _ :: _ :: _ ->
          let disjs = List.map members ~f:(fun (_, ds, _, _) -> ds) in
          let q =
            Common.PhaseTime.with_phase "group-question-build" @@ fun () ->
            let q = question_entries common disjs in
            if !share_piece_simplify then Ast.Evaluator.simplify q else q
          in
          let each_piece ~lead =
            Common.PhaseTime.with_phase "group-each-piece" @@ fun () ->
            List.for_all members ~f:(proved_alone ~lead)
          in
          let size = lazy (Formula.ast_size q) in
          let past_lead_bound =
            match lead_bound with
            | Some bound -> Lazy.force size > bound
            | None -> false
          in
          if past_lead_bound then incr lead_forms_open_gated_groups;
          match !group_question_max_nodes with
          | Some bound when Lazy.force size > bound ->
              incr group_questions_skipped;
              !clause_trace
                (lazy
                  (sprintf
                     "grouped question over %d pieces not asked: %d nodes, \
                      past the bound %d"
                     (List.length members) (Lazy.force size) bound));
              each_piece ~lead:(unasked_lead || past_lead_bound)
          | _ when past_lead_bound ->
              incr group_questions_skipped;
              !clause_trace
                (lazy
                  (sprintf
                     "grouped question over %d pieces not asked: %d nodes, \
                      past the lead bound %d; its pieces asked their lead \
                      forms first"
                     (List.length members) (Lazy.force size)
                     (Option.value_exn lead_bound)));
              Common.PhaseTime.with_phase "group-lead-gate" @@ fun () ->
              each_piece ~lead:true
          | _ ->
              incr group_questions_asked;
              !clause_trace
                (lazy
                  (sprintf "grouped question over %d pieces"
                     (List.length members)));
              if
                first_proved_formula ?second_pass ~ask
                  [ Lazy.from_val (Some q) ]
              then (
                incr group_questions_proved;
                group_pieces_proved :=
                  !group_pieces_proved + List.length members;
                true)
              else each_piece ~lead:false
    in
    (* a piece's forms and the first form the grouping compares, built in
       [in_scope] *)
    let first_form_of ~forms unsimplified =
      if !share_piece_simplify then
        try Some (Lazy.force unsimplified) with Deep_form_too_large -> None
      else match forms with f :: _ -> Lazy.force f | [] -> None
    in
    (* also the number of lead forms at the head of the forms *)
    let first_form (earlier, piece) =
      !clause_trace (lazy "a piece's first form, for grouping");
      Common.PhaseTime.with_phase "group-first-form" @@ fun () ->
      in_scope @@ fun () ->
      let unsimplified, forms, n = piece_forms_with_first_lead ~earlier piece in
      (forms, first_form_of ~forms unsimplified, n)
    in
    (* With [lead_forms_before_grouping]: [`Proved] when one of the piece's
       forms before its deep ones proves it, asked before the deep first form
       is built; otherwise [`Forms (rest, first, n, 0)] with [first] the first
       form [first_form] gives, [rest] the forms after the [n] already asked
       (the forms [first_form] lists with their first [n] dropped).  Without
       the switch, or with [stage] false, always [`Forms (forms, first, 0, l)]
       for [(forms, first, l) = first_form ep], [l] the lead forms at the
       head of [forms], none of them asked.  Both grouping paths list their
       pieces through it; the open path passes [stage] true only under
       [lead_forms_under_open_grouping]. *)
    (* the lead stage stops at the first piece its forms do not prove: the
       pieces after it are listed as without the switch.  So a clause the
       switch cannot settle costs at most that one piece's lead forms more
       than without it (asked anyway, after its group's question, unless
       the group proves it), where asking every piece's lead forms first
       would ask those of pieces never reached once one piece fails *)
    let lead_open = ref true in
    let lead_or_first_form ?(stage = true) ((earlier, piece) as ep) =
      if not (stage && !lead_forms_before_grouping && !lead_open) then
        let forms, first, n = first_form ep in
        `Forms (forms, first, 0, n)
      else
        let unsimplified, forms, n =
          Common.PhaseTime.with_phase "group-first-form" @@ fun () ->
          in_scope @@ fun () -> piece_forms_with_first_lead ~earlier piece
        in
        let lead, rest = List.split_n forms n in
        if
          (not (List.is_empty lead))
          && Common.PhaseTime.with_phase "group-lead-forms" (fun () ->
                 (* asked as [piece_proved] asks a piece's forms, with the
                    index cases when that switch is on *)
                 let ask =
                   if !case_split_index_forms then ask_with_index_cases ~ask
                   else ask
                 in
                 first_proved_formula ?second_pass ~ask lead)
        then (
          incr lead_forms_pieces_proved;
          !clause_trace (lazy "a piece proved by a form before its deep ones, not grouped");
          `Proved)
        else (
          lead_open := false;
          !clause_trace (lazy "a piece's first form, for grouping");
          `Forms
            ( rest,
              (Common.PhaseTime.with_phase "group-first-form" @@ fun () ->
               in_scope @@ fun () -> first_form_of ~forms:rest unsimplified),
              List.length lead,
              0 ))
    in
    (* the group being collected, newest member first, with its reference's
       disjunct keys and its common part.  The common part is
       [List.fold ~init:d_1 ~f:inter_entries [d_1; ...; d_k]] for the
       members' disjuncts [d_i] in order, as [ask_group] needs it, since
       [inter_entries d_1 d_1] is [d_1]. *)
    let rec go group ref_keys common = function
      | [] -> ask_group (List.rev group) common
      | (earlier, piece) :: rest -> (
          match lead_or_first_form (earlier, piece) with
          | `Proved -> go group ref_keys common rest
          | `Forms (forms, first, _, _) ->
          let start () =
            match first with
            | None ->
                (* nothing to group on: this piece is asked alone *)
                piece_proved ?second_pass ~piece ~ask forms
                && go [] (Hashtbl.Poly.create ()) [] rest
            | Some f ->
                let disjs = entries_of (Formula.disjuncts_list_of f) in
                go
                  [ (Lazy.from_val (forms, 0), disjs, lazy (size_of_entries disjs), piece) ]
                  (ref_keys_of ~keep f) disjs rest
          in
          match (group, first) with
          | [], _ -> start ()
          | _, None -> ask_group (List.rev group) common && start ()
          | _, Some f ->
              let disjs, total, common', c =
                Common.PhaseTime.with_phase "group-align" @@ fun () ->
                let disjs =
                  if !replay_piece_names then entries_of (Formula.disjuncts_list_of f)
                  else
                    entries_of (Formula.disjuncts_list_of (align ~keep ~ref_keys f))
                in
                let total = lazy (size_of_entries disjs) in
                let common' = inter_entries common disjs in
                (disjs, total, common', size_of_entries common')
              in
              (* the sum over the new piece and every member of its size less
                 [c], each member's size summed once when it joined *)
              let residue =
                List.sum (module Int) (total :: List.map group ~f:(fun (_, _, t, _) -> t))
                  ~f:(fun s -> Lazy.force s - c)
              in
              if
                c > 0
                && c * min_common_share >= size_of_entries common
                && residue <= c * max_residue_share
              then go ((Lazy.from_val (forms, 0), disjs, total, piece) :: group) ref_keys common' rest
              else ask_group (List.rev group) common && start ())
    in
    (* With [group_open_pieces]: every piece joins the first open group, in
       the order the groups were opened, that the criterion above admits it
       to, and opens a group of its own when none does; the groups are asked
       when every piece has its first form, in the order they were opened.
       The question of a group is the one [ask_group] asks of consecutive
       members, so what a proof shows is unchanged: the grouped question
       implies each member's first form, whichever pieces lie between them.
       With [replay_piece_names] the forms are compared as they are, since
       the pieces name the instances they share alike; otherwise each is
       renamed towards the reference of the group it is tried against.
       With [lead_forms_before_grouping] and [lead_forms_under_open_grouping]
       (and [lead_forms_for_unasked_groups] off) a piece is listed as [go]
       lists it (by [lead_or_first_form]): one its lead forms prove joins no
       group, and a member listed again after its group's question fails
       starts after the lead forms it already had asked.  Otherwise no lead
       stage is asked before grouping; with [lead_forms_open_min_nodes] the
       members of a group past its bound are asked their lead forms in
       place of the group's question. *)
    let go_open () =
      (* each open group: its members newest first, its reference's keys,
         its common part *)
      let groups = ref [] (* the oldest group first *) in
      (* [intern_piece_disjuncts]: the entry of every disjunct met so far in
         the clause's first forms, by structure *)
      let interning = !intern_piece_disjuncts && !replay_piece_names in
      let interned = Hashtbl.PolyDeep.create () in
      let try_join (earlier, piece) =
        match
          lead_or_first_form
            ~stage:
              (!lead_forms_under_open_grouping
              && (not !lead_forms_for_unasked_groups)
              && Option.is_none !lead_forms_open_min_nodes)
            (earlier, piece)
        with
        | `Proved -> `Proved
        | `Forms (forms, None, _, n) -> `Alone (forms, n, piece)
        | `Forms (forms, Some f, asked, n) ->
            (* the forms of a member are listed again, in the same scope,
               only if its group's question is not proved, so that a member
               keeps its residue and not its whole first form; the [asked]
               lead forms already asked of it are not listed again, and [n]
               lead forms not yet asked stay at the head of the list *)
            let forms_again =
              lazy
                (let forms, _, _ = first_form (earlier, piece) in
                 (List.drop forms asked, n))
            in
            let as_built =
              lazy
                (if interning then
                   List.map (Formula.disjuncts_list_of f) ~f:(fun d ->
                       Hashtbl.find_or_add interned d ~default:(fun () ->
                           interned_entry (Hashtbl.length interned) d))
                 else entries_of (Formula.disjuncts_list_of f))
            in
            let entries_towards ref_keys =
              if !replay_piece_names then Lazy.force as_built
              else
                entries_of (Formula.disjuncts_list_of (align ~keep ~ref_keys f))
            in
            let accepts (members, ref_keys, common) =
              let disjs = entries_towards ref_keys in
              let total = lazy (size_of_entries disjs) in
              (* the criterion below holds of [c] only if it holds of any
                 bound above [c], so a group the hash bound already fails is
                 passed over without comparing a disjunct *)
              let admits c =
                c > 0
                && c * min_common_share >= size_of_entries common
                && List.sum (module Int)
                     (total :: List.map members ~f:(fun (_, _, t, _) -> t))
                     ~f:(fun s -> Lazy.force s - c)
                   <= c * max_residue_share
              in
              if not (admits (inter_size_bound common disjs)) then None
              else
              let common', residue_entries = inter_minus_entries common disjs in
              let c = size_of_entries common' in
              let residue =
                List.sum (module Int)
                  (total :: List.map members ~f:(fun (_, _, t, _) -> t))
                  ~f:(fun s -> Lazy.force s - c)
              in
              if
                c > 0
                && c * min_common_share >= size_of_entries common
                && residue <= c * max_residue_share
              then
                (* [disjs] kept as its residue beside the common part it was
                   compared with: [common'] is a sub-multiset of [common],
                   whose entries it shares, and of [disjs], so the residue
                   against any later common part (a sub-multiset of
                   [common']) is this residue with what [common'] has and
                   that one lacks *)
                let kept = residue_entries @ common' in
                Some ((forms_again, kept, total, piece) :: members, ref_keys, common')
              else None
            in
            Common.PhaseTime.with_phase "group-join" @@ fun () ->
            let rec place = function
              | [] -> None
              | g :: rest -> (
                  match accepts g with
                  | Some g' -> Some (g' :: rest)
                  | None -> Option.map (place rest) ~f:(fun rest' -> g :: rest'))
            in
            (match place !groups with
            | Some gs -> groups := gs
            | None ->
                let disjs =
                  if interning then Lazy.force as_built
                  else entries_of (Formula.disjuncts_list_of f)
                in
                groups :=
                  !groups
                  @ [ ( [ (Lazy.from_val (forms, n), disjs, lazy (size_of_entries disjs), piece) ],
                        ref_keys_of ~keep f,
                        disjs ) ]);
            `Grouped
      in
      let unasked_lead = !lead_forms_for_unasked_groups in
      List.for_all ps ~f:(fun ep ->
          match try_join ep with
          | `Alone (forms, n, piece) ->
              piece_proved ?second_pass ~piece
                ~lead:(if unasked_lead then n else 0) ~ask forms
          | `Grouped | `Proved -> true)
      && List.for_all !groups ~f:(fun (members, _, common) ->
             ask_group ~unasked_lead ?lead_bound:!lead_forms_open_min_nodes
               (List.rev members) common)
    in
    if !group_open_pieces then go_open ()
    else go [] (Hashtbl.Poly.create ()) [] ps
end

(** [`Valid] when every clause is shown valid -- by [already_valid] (its
    index), or by [ask] answering [`Valid], for every one of its [pieces]
    (taken of its negation normal form), on one of the piece's forms: its
    [piece_forms], in order: its [deep_forms], then its plain sequence
    instantiation, and last,
    when [witness_forms] is set, its [witness_form], and after it, when
    [drop_array_hypotheses] is set and it removes anything, its
    [drop_array_hypotheses_form], and after it, when [chain_focus_forms]
    or [chain_assoc_match_forms] is set, the forms of [chain_focus_forms_of]
    and then [assoc_match_forms_of], and last, when
    [contextual_ite_extra_form] is set and it changes anything, its
    [contextual_ite_form] -- and [`Undecided]
    otherwise.  Every form is a strengthening of the piece, so
    any one answered valid proves it; there is deliberately no refuting
    answer, since a countermodel of a form is not one of the clause.  A
    form is asked only when every form before it failed, so adding forms
    cannot lose an answer the plain instantiation gives.  The quantifier-free
    forms come first because a solver answers them either way in about a
    second, where the plain form, still quantified over integers, was left
    undecided at its budget on the clauses the deep forms were built for.
    Nothing is asked when [enabled] is false.  [second_pass] makes the asks
    of each piece two-pass, as [first_proved] describes.  With
    [share_premise_instances] set, a clause of more than one piece is first
    asked as its [shared_pieces], each one form; every one [`Valid] proves
    the clause, and otherwise the pieces are asked as above, so the switch
    adds questions before the others and cannot lose an answer they give.
    With [group_piece_forms] set, the pieces of a clause of more than one are
    asked through [PieceGroups.prove], which asks groups of their first forms
    as one question before each piece's forms.  A piece none of its forms
    proves is given to [undecided_piece_prover] when that is set
    ([piece_proved]).

    With [schedule], the clauses not [already_valid] are asked smallest
    first by [Formula.ast_size] (ties in their order), every one of them
    whatever the others' answers, and [proved i] is called for each clause
    [i] shown valid; [`Valid] still means every clause is shown valid, now
    or by [already_valid].  Without it the clauses are asked in order up to
    the first not shown valid, and [proved] is not called. *)
let prove_valid ?second_pass ?(schedule = false) ?(proved = fun _ -> ())
    ~enabled ~already_valid ~ask clauses =
  let prove_clause i c =
    let started = Common.Clock.now_float () in
    let nnf, ps =
      Common.PhaseTime.with_phase "clause-split" @@ fun () ->
      let nnf = Ast.Evaluator.simplify (Formula.nnf_of c) in
      (nnf, pieces nnf)
    in
    (let secs =
       Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) started)
     in
     !clause_trace
       (lazy
         (sprintf "clause %d: %d pieces, split in %.2f s" i
            (List.length ps) secs)));
    (* the clause instantiated once and split, first; a form of it not
       proved sends the clause to its pieces, as with the switch off *)
    (!share_premise_instances
    && List.length ps > 1
    && List.for_all (shared_pieces nnf) ~f:(fun q ->
           first_proved_formula ?second_pass ~ask [ Lazy.from_val (Some q) ]))
    ||
    if !group_piece_forms && List.length ps > 1 then
      (* the integer step's memo holds this clause's instances, and the
         deep-shape table its shared forms; nothing reuses them once its
         pieces are proved or given up *)
      Exn.protect
        ~finally:(fun () ->
          reset_int_memo ();
          reset_deep_shapes ())
        ~f:(fun () ->
          PieceGroups.prove ?second_pass ~ask ~keep:(Formula.tvs_of nnf) ps)
    else
      List.for_alli ps ~f:(fun k piece ->
          piece_proved ?second_pass ~piece ~ask
            (piece_forms ~earlier:(List.take ps k) piece))
  in
  if not enabled then `Undecided
  else if not schedule then
    if List.for_alli clauses ~f:(fun i c -> already_valid i || prove_clause i c)
    then `Valid
    else `Undecided
  else
    let open_ =
      List.filter_mapi clauses ~f:(fun i c ->
          if already_valid i then None else Some (Formula.ast_size c, i, c))
      |> List.stable_sort ~compare:(fun (a, _, _) (b, _, _) -> Int.compare a b)
    in
    (* every open clause is asked, so [List.map] and not [for_all] *)
    let results =
      List.map open_ ~f:(fun (_, i, c) ->
          let ok = prove_clause i c in
          if ok then proved i;
          ok)
    in
    if List.for_all results ~f:Fn.id then `Valid else `Undecided

(** Two further forms of a quantifier-free form [form] (a disjunction, as
    [instantiate_deep] leaves it), asked when [form] itself is not proved,
    for the case where the form says what a sequence IS rather than what it
    holds.  A candidate read back from sequence cells may state a whole
    sequence at the sentinel -- [t = seq.store s i 0] -- and its instance then
    sits in a premise, so the form has a disjunct [t != seq.store s i 0]
    beside a conclusion that reads [t] ([seq.nth t j = seq.nth s j]).  A
    solver asked that meets [seq.store] only through its expansion into
    [seq.extract] and [seq.++] at the solver boundary, and was observed to
    answer neither way at 10 s on exactly this frame form.

    The first form rewrites [form] exactly:
    - for a disjunct [x != e] with [x] a sequence variable not occurring in
      [e], every OTHER disjunct has [x] replaced by [e] -- [x != e \/ psi(x)]
      and [x != e \/ psi(e)] are equivalent, since where the first disjunct
      is false [x] is [e];
    - then every read of a store in a top-level disjunct whose index the
      other disjuncts put inside the sequence is split on whether it is the
      written index ([Evaluator.rewrite_seq_read_over_write]), which is exact
      where the range holds.  [entails] decides the range and may say no
      whenever it likes, but its yes must be sound; [range_entails] is the
      intended one.
    The second form keeps only the disjuncts of the first that mention no
    [seq.store] and no [seq.extract], which strengthens it (a disjunction is
    implied by any of its sub-disjunctions), and is the question with the
    write gone altogether once the reads are split.

    Contract: each returned form implies [form] (the first is equivalent to
    it), so a proof of either is a proof of [form]; nothing may be read from
    a countermodel.  Only a disequation, never an equation, is substituted:
    [x = e \/ psi(x)] is not [x = e \/ psi(e)]. *)
let seq_var_diseq d =
  let pick a b =
    match a with
    | Term.Var (x, srt, _)
      when Option.is_some (elem_of_seq srt) && not (Set.mem (Term.tvs_of b) x)
      ->
        Some (x, b)
    | _ -> None
  in
  match d with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ a; b ], _), _)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _),
        _ ) -> (
      match pick a b with Some r -> Some r | None -> pick b a)
  | _ -> None

let substitute_disequated_sequences phi =
  let rec go ds substituted =
    match
      List.find_mapi ds ~f:(fun k d ->
          match seq_var_diseq d with
          | Some (x, e)
            when not (List.mem substituted x ~equal:Ast.Ident.tvar_equal) ->
              Some (k, x, e)
          | _ -> None)
    with
    | None -> ds
    | Some (k, x, e) ->
        let sub = Map.Poly.singleton x e in
        go
          (List.mapi ds ~f:(fun k' d -> if k = k' then d else Formula.subst sub d))
          (x :: substituted)
  in
  Formula.or_of (go (Formula.disjuncts_list_of phi) [])

let mentions_write phi =
  Set.exists (Formula.funsyms_of phi) ~f:(function
    | T_seq.SqStore _ | T_seq.SqExtract _ -> true
    | _ -> false)

(** An [entails] for [frame_forms]: whether [assumptions] give [goal], asked
    of [check_valid] with only the conjuncts of [assumptions] that are
    quantifier-free and read, write or build no sequence and hold no
    if-then-else ([seq.len] of anything may occur).  Dropping conjuncts
    weakens the hypothesis, so a yes stays sound, and the question left is
    linear arithmetic over lengths, which a solver decides at once. *)
let range_entails ~check_valid assumptions goal =
  let usable a =
    Formula.is_quantifier_free a
    && Set.for_all (Formula.funsyms_of a) ~f:(function
         | T_seq.SqNth _ | T_seq.SqStore _ | T_seq.SqExtract _
         | T_seq.SqConcat _ | T_seq.SqUnit _ | T_bool.IfThenElse
         | T_bool.Formula _ ->
             false
         | _ -> true)
  in
  let premises =
    List.filter ~f:usable
    @@ Formula.conjuncts_list_of (Formula.nnf_of assumptions)
  in
  check_valid (Formula.mk_imply (Formula.and_of premises) goal)

let frame_forms ~entails form =
  if not (mentions_write form) then []
  else
    let exact =
      lazy
        (Ast.Evaluator.simplify
        @@ Ast.Evaluator.rewrite_seq_read_over_write ~entails
        @@ substitute_disequated_sequences form)
    in
    let core =
      lazy
        (Formula.or_of
        @@ List.filter ~f:(Fn.non mentions_write)
        @@ Formula.disjuncts_list_of (Lazy.force exact))
    in
    [ exact; core ]

(* An instantiated form asked for validity, with the variables its top-level
   disequations define substituted away and the result simplified.  A form a
   premise universal was instantiated in states the premise's facts as
   disjuncts [x != t] of one disjunction (the negated premise), and
   [forall x. (x != t \/ R(x))] is [R(t)] for [x] not in [t]
   ([Evaluator.subst_var_definitions], exact for validity); simplification
   can then act on the composed terms.  Why it is worth asking that instead:
   on a composition clause the form says [t = store s i 0], [u = store t i 0]
   and asks for [u = store s i 0] (among other facts), which the
   simplifier's store-over-store rule closes once [t] and [u] are
   substituted, while left to the solver it is a sequence entailment whose
   answer depends on the solver's search: Z3 5.1.0 did not decide it in 20 s
   on its default random seed, and both 5.1.0 and 4.15.2 decided the bare
   lemma [store (store s i 0) i 0 = store s i 0] on only about half of the
   seeds tried, the rest timing out.  Returns [form] itself when no
   definition applies, so the question asked is then the unchanged one. *)
let substitute_form_definitions form =
  let form' = Ast.Evaluator.subst_var_definitions form in
  if phys_equal form' form then form else Ast.Evaluator.simplify form'

(** [`Valid] when every one of [phi]'s [pieces] is answered [`Valid] by [ask]
    on one of its [deep_forms] (with the [equated] and [nested] candidates),
    and otherwise [`Unproved ms] with [ms] the models [ask] returned for the
    forms it refuted.  [also form] gives further forms asked, in order, when
    [form] is not proved; each must imply [form] ([frame_forms] is one such
    supplier), so the contract below is unchanged.  Unlike [prove_valid], the plain sequence instantiation
    is not asked: it keeps the integer binders, and a clause checked by the
    validator is typically quantified over integers only -- a candidate read
    back from sequence cells is a universal over a sequence's positions -- so
    the plain form would be the very query this exists to avoid.

    Every form asked is quantifier-free outside embedded formulas and is a
    strengthening of its piece ([form => piece] is valid once the form's
    fresh variables are read as universals), so [`Valid] means [phi] is
    valid.  Nothing else may be read: [ms] are models of the NEGATED FORMS,
    which are weaker than the negated [phi], so none of them need be a
    counterexample to [phi] -- they are returned only to be checked against
    [phi] ([decide_clause]).  The asks stop at the first piece no form
    proves.

    [max_nodes] is passed to [deep_forms] and so bounds the instances each
    form is built from; absent, as for the coordinator's ladder, the forms
    are exactly those built without it.  A caller that may leave [phi]
    unproved -- a solution checker, which then reports the constraint
    unchecked -- passes it so that building a form cannot exhaust memory;
    a bounded form is still a strengthening of its piece, so [`Valid] keeps
    its meaning, but it may keep sequence binders the budget left
    uninstantiated, so it need not be quantifier-free.

    [matched], when [Some (aligned, hyp_budget)], also asks each piece its
    [matched_forms] (the two settings passed on), the forms the zero-unknown
    verdict proves a piece with when [matched_instance_forms] is on; they are
    not bounded by [max_nodes], whose instance counts they bound themselves,
    and each is passed through [rewrite_matched] before it is asked, which
    must return a formula implying its argument (an equivalence, such as
    [Ast.Evaluator.elim_onepoint_and_split_binders], which the verdict's
    questions go through).  The pieces are then not asked in one sweep but
    in rounds, a piece not proved being deferred rather than ending the
    attempt:
    - round 1, every piece in order, its matched-instance forms by [ask],
      the earlier-pieces forms taking as [earlier] the pieces PROVED SO FAR;
    - then, while a round proves something, each deferred piece by
      [ask_long] (default [ask]): its earlier-pieces forms again whenever
      more pieces have been proved since they were last built, and failing
      that its two plain matched forms, its [deep_forms] and their [also]
      forms.
    Why rounds: a piece whose goal is the existential introduction of a
    lemma another piece states can be proved only with that piece as a
    hypothesis, and the order [pieces] returns need not put it first; on a
    Rust-derived constraint of eleven pieces the second piece was proved
    only once the other nine were.  And why the matched forms first, by a
    short [ask]: they are small and decided in about a second when they
    decide at all, where a deep form of one piece was 74,000 nodes and
    undecided at its whole budget.
    Soundness: an earlier-pieces form is a strengthening of its piece under
    the hypothesis that the pieces it takes as hypotheses are valid; each of
    those was proved before it, and [`Valid] is returned only when every
    piece is proved, so by induction over the order the pieces were PROVED
    every hypothesis is discharged and every piece is valid.  A model of
    such a form's negation is a model of a question weaker than [not phi]
    under an unproved hypothesis, returned only to be checked against [phi],
    as the others are.  With [matched] absent the pieces are asked in one
    sweep as before, [ask_long] unused.

    [subst_definitions] (default [false]) passes every form through
    [substitute_form_definitions] before it is asked: a question valid
    exactly when the form is, so [`Valid] keeps its meaning, and a model of
    its negation extends to one of the form's negation (each eliminated
    variable taking its definition's value), so [ms] keep theirs. *)
let prove_valid_deep ?(also = fun _ -> []) ?max_nodes ?matched
    ?(rewrite_matched = Fn.id) ?ask_long ?(subst_definitions = false) ~ask phi
    =
  let refuted = ref [] in
  let proves_by ask form =
    match ask (if subst_definitions then substitute_form_definitions form else form) with
    | `Valid -> true
    | `Invalid m ->
        refuted := m :: !refuted;
        false
    | `Undecided -> false
  in
  let ps = pieces (Ast.Evaluator.simplify (Formula.nnf_of phi)) in
  let deep_by ask piece =
    List.exists (deep_forms ~equated:true ?max_nodes piece) ~f:(fun form ->
        let form = Lazy.force form in
        proves_by ask form
        || List.exists (also form) ~f:(fun f -> proves_by ask (Lazy.force f)))
  in
  match matched with
  | None ->
      if List.for_all ps ~f:(fun piece -> deep_by ask (prepare_piece piece))
      then `Valid
      else `Unproved (List.rev !refuted)
  | Some (aligned, hyp_budget) ->
      let ask_long = Option.value ask_long ~default:ask in
      (* a form forced to [None] (past [max_matched_form_size]) is skipped
         as an undecided one is *)
      let by ask form =
        match Lazy.force form with
        | Some f -> proves_by ask (rewrite_matched f)
        | None -> false
      in
      (* [proved]: the raw pieces proved so far, in the order they were *)
      let proved = ref [] in
      let earlier () = List.rev !proved in
      let prove_piece (raw, _) = proved := raw :: !proved in
      let items = List.map ps ~f:(fun raw -> (raw, prepare_piece raw)) in
      let deferred =
        List.filter items ~f:(fun ((_, piece) as item) ->
            if
              List.exists
                (matched_forms ~aligned ~hyp_budget ~earlier:(earlier ()) piece)
                ~f:(by ask)
            then (
              prove_piece item;
              false)
            else true)
      in
      (* the number of pieces proved when each deferred piece's
         earlier-pieces forms were last built *)
      let tried_with = Hashtbl.Poly.create () in
      let round deferred ~f =
        let progress = ref false in
        let left =
          List.filter deferred ~f:(fun item ->
              if f item then (
                prove_piece item;
                progress := true;
                false)
              else true)
        in
        (!progress, left)
      in
      let with_hypotheses ((raw, piece) as _item) =
        let n = List.length !proved in
        (not (Option.equal Int.equal (Hashtbl.find tried_with raw) (Some n)))
        && (not (List.is_empty !proved))
        &&
        (Hashtbl.set tried_with ~key:raw ~data:n;
         List.exists
           (List.map ~f:skip_too_large
              (earlier_pieces_form ~aligned ~hyp_budget ~earlier:(earlier ())
                 piece))
           ~f:(by ask_long))
      in
      let alone (_, piece) =
        List.exists
          (List.map ~f:skip_too_large
             [
               lazy (matched_instance_form piece);
               lazy (matched_instance_form ~keep_scalar:true piece);
             ])
          ~f:(by ask_long)
        || deep_by ask_long piece
      in
      let rec loop deferred =
        if List.is_empty deferred then true
        else
          let progress, deferred = round deferred ~f:with_hypotheses in
          if progress then loop deferred
          else
            let progress, deferred = round deferred ~f:alone in
            progress && loop deferred
      in
      if loop deferred then `Valid else `Unproved (List.rev !refuted)

(** Whether a clause [phi] has a counterexample, answered as a satisfiability
    question about its negation: [`Unsat] when [phi] is valid, [`Sat m] with
    [m] a model of [not phi].  The questions, in order:
    - [prove_valid_deep ~ask:ask_form]: [`Unsat] when it proves [phi];
    - otherwise the refuters: [ask_pinned m] for each model [m] of a refuted
      form -- the negation of [phi] with [phi]'s free variables fixed to
      their values in [m]; a model of THAT is a model of [not phi], so its
      [`Sat] is returned as the counterexample, and [m] itself never is --
      then each of [bounded] in order, which the caller must make questions
      every model of which is a model of [not phi] (the negation with the
      free sequences fixed to literals of a small length, say).  The first
      [`Sat] is returned and [ask_full] is then NOT asked;
    - only when no refuter answers [`Sat], [ask_full ()], the unrewritten
      question, whose answer (decided or not) is returned as it is.
    So [`Unsat] is returned only when [phi] is valid (a form proved it, or
    the full question said so), and [`Sat] only with a model of [not phi],
    provided [ask_pinned] and [bounded] keep their contracts.  When the
    stubs are consistent -- no refuter satisfiable for a valid [phi] -- the
    answer agrees with the full question's wherever that is decided; which
    counterexample is returned for an invalid [phi] is the first refuter's,
    not the full question's. *)
(* The refuters are tried BEFORE the unrewritten question, and that order is
   the point.  A wrong candidate is the common case in a CEGIS loop, and for
   one the instantiated forms are satisfiable and prove nothing; the refuters
   are then cheap -- the negation with every free variable pinned to a model
   of an instantiated form, or with every free sequence a literal of a small
   length -- and a satisfiable answer of either is a model of the negation
   itself, so a counterexample.  The unrewritten question is the expensive
   one: with a premise universal over positions it was measured at 40-136 s a
   question on a Rust-derived slice loop, and asking it first for every wrong
   candidate made this whole route slower than not taking it.  It is asked
   only when no refuter finds a counterexample. *)
let decide_clause ?subst_definitions ~ask_form ~ask_full ~ask_pinned
    ?(bounded = []) phi =
  match prove_valid_deep ?subst_definitions ~ask:ask_form phi with
  | `Valid -> `Unsat
  | `Unproved form_models -> (
      let refuters =
        List.map form_models ~f:(fun m () -> ask_pinned m) @ bounded
      in
      match
        List.find_map refuters ~f:(fun ask ->
            match ask () with `Sat m' -> Some m' | _ -> None)
      with
      | Some m' -> `Sat m'
      | None -> ask_full ())

(* ===== Matched-instance forms asked through their words (begin) ===== *)

(** [word_forms ?two_rounds_first piece]: the forms of a prepared [piece]
    that a validity question through its words is asked of, in order: the
    forms of [matched_forms ~earlier:[]], then the matched-instance form of
    two rounds of matching (the second round against the ground terms the
    first round's instances write).  Each implies [piece] in every model.

    With [two_rounds_first], the two-round form comes first and the plain
    one-round form ([matched_instance_form piece], the head of
    [matched_forms]) is built and asked only when the two-round form is not
    built (past [max_matched_form_size]).  Why that loses no proof the
    one-round form gives: the two-round form's first pass makes the same
    substitutions as the one-round form's only pass (same formula, same
    ground terms, same budget) and keeps the existentials beside their
    instances, which the second pass then instantiates again; so every
    disjunct the one-round form puts in place of an existential is among
    those the two-round form puts there (simplification and skolemization
    between the passes are equivalences up to fresh names), and the
    one-round form implies the two-round one: valid only if it is.  The
    words question of a form is not monotone in the same way, so what the
    order gives up is only a proof the solver finds through the smaller
    form's words and not the larger one's -- which never happened on the
    input it was written for, where the one-round words question of a bit
    set's obligation ran out of its 10 s and the two-round one was proved in
    0.6 s. *)
let word_forms ?(two_rounds_first = false) piece =
  let two = skip_too_large (lazy (matched_instance_form ~rounds:2 piece)) in
  let plain = matched_forms ~earlier:[] piece in
  if not two_rounds_first then plain @ [ two ]
  else
    match plain with
    | [] -> [ two ]
    | one :: rest ->
        two
        :: lazy (match Lazy.force two with Some _ -> None | None -> Lazy.force one)
        :: rest

(** [valid_by_word_forms ?two_rounds_first ~ask phi]: [true] when every
    piece of [phi] ([pieces], after the exact one-point rule) is shown valid
    by [ask] on the piece itself or on one of its [word_forms]; [ask] is
    called only on quantifier-free forms that read an integer as a word
    ([Z3interface.reads_int_as_word]) and must answer [`Valid] only for a
    valid formula.  Contract: [true] implies [phi] valid in every model --
    the pieces' conjunction is equivalent to [phi], [prepare_piece] keeps
    validity, and each form implies its piece.  [false] says nothing.  A
    piece no form of which reads an integer as a word stops the search at
    once, asking nothing more. *)
(* the form [ask] of the words route: the form after the exact one-point
   rule, asked only when it is quantifier-free and reads an integer as a
   word *)
let word_ask_form ~ask c =
  let c =
    Common.PhaseTime.with_phase "w-form-onepoint" (fun () ->
        Ast.Evaluator.elim_onepoint_and_split_binders c)
  in
  if
    Z3Smt.Z3interface.reads_int_as_word c
    && Set.is_empty (Formula.quantified_sort_env_of c)
  then ask c
  else `Unknown "not a quantifier-free word question"

(* whether one piece (not yet prepared) is proved through its words: the
   prepared piece itself, then its [word_forms], the first proved form
   deciding *)
let word_piece_proved ?two_rounds_first ~ask p =
  let p = Common.PhaseTime.with_phase "w-prepare" (fun () -> prepare_piece p) in
  first_proved_formula ~ask:(word_ask_form ~ask)
    (lazy (Some p) :: word_forms ?two_rounds_first p)

let valid_by_word_forms ?two_rounds_first ?(note = fun _ -> ()) ~ask phi =
  let phi =
    Common.PhaseTime.with_phase "w-onepoint" (fun () ->
        Ast.Evaluator.elim_onepoint_and_split_binders phi)
  in
  let ps = pieces phi in
  let n = List.length ps in
  List.for_alli ps ~f:(fun k p ->
      let size = Formula.ast_size p in
      if not (Z3Smt.Z3interface.reads_int_as_word p) then (
        note (sprintf "piece %d of %d (size %d): reads no word" (k + 1) n size);
        false)
      else
        let proved = word_piece_proved ?two_rounds_first ~ask p in
        note
          (sprintf "piece %d of %d (size %d): %s" (k + 1) n size
             (if proved then "proved" else "not proved"));
        proved)

(** [pieces_with_residual phi]: the pieces of [phi], exactly the list
    [pieces phi] (same formulas, same order), and a function that, given one
    flag per piece in that order, returns a formula equivalent in every model
    to the conjunction of the flagged pieces ([true] when none is flagged).

    Why it is exact, case by case, following [pieces]: a conjunction's pieces
    are its sides' pieces in turn, so the flagged ones are the flagged ones of
    each side and their conjunction is the conjunction of each side's
    residual.  A distributed disjunction [p \/ q] has the pieces [p_i \/ q_j]
    (for each [i], each [j]); the conjunction of the flagged ones is, by
    distributivity, [/\_i (p_i \/ /\_{j flagged with i} q_j)], grouped by
    the side with fewer pieces so that each of that side's pieces is written
    once.  A disjunction split along one side ([one_side_pieces]) has the
    pieces [p_i \/ q] (or [p \/ q_j]), whose flagged conjunction is
    [(/\_{i flagged} p_i) \/ q].  A formula kept whole is its own piece.

    What it buys: a question whose pieces were proved in part needs only the
    rest asked, and the rest written this way keeps a shared premise once
    instead of once per remaining piece. *)
let rec pieces_with_residual phi :
    Formula.t list * (bool list -> Formula.t) =
  let whole = ([ phi ], function [ true ] -> phi | _ -> Formula.mk_true ()) in
  let some_flag = List.exists ~f:Fn.id in
  match phi with
  | Formula.BinaryOp (Formula.And, p, q, _) -> (
      let ps, rp = pieces_with_residual p and qs, rq = pieces_with_residual q in
      match List.length ps + List.length qs with
      | n when n <= max_pieces || !uncapped_conjunction_pieces ->
          let np = List.length ps in
          ( ps @ qs,
            fun flags ->
              let fp, fq = List.split_n flags np in
              Formula.and_of
                ((if some_flag fp then [ rp fp ] else [])
                @ if some_flag fq then [ rq fq ] else []) )
      | _ -> whole)
  | Formula.BinaryOp (Formula.Or, p, q, _) ->
      let ps, _ = pieces_with_residual p and qs, _ = pieces_with_residual q in
      let np = List.length ps and nq = List.length qs in
      if np * nq <= max_pieces then
        ( List.concat_map ps ~f:(fun p -> List.map qs ~f:(fun q -> Formula.mk_or p q)),
          fun flags ->
            (* flags.(i * nq + j) for the piece [p_i \/ q_j] *)
            let fa = Array.of_list flags in
            let flag i j = fa.((i * nq) + j) in
            if np <= nq then
              Formula.and_of
                (List.filter_mapi ps ~f:(fun i p_i ->
                     let js =
                       List.filter_mapi qs ~f:(fun j q_j ->
                           if flag i j then Some q_j else None)
                     in
                     if List.is_empty js then None
                     else Some (Formula.mk_or p_i (Formula.and_of js))))
            else
              Formula.and_of
                (List.filter_mapi qs ~f:(fun j q_j ->
                     let is =
                       List.filter_mapi ps ~f:(fun i p_i ->
                           if flag i j then Some p_i else None)
                     in
                     if List.is_empty is then None
                     else Some (Formula.mk_or (Formula.and_of is) q_j))) )
      else if !pointwise_concat_candidates || !uncapped_conjunction_pieces then
        let kept xs flags =
          Formula.and_of
            (List.filter_map (List.zip_exn xs flags) ~f:(fun (x, f) ->
                 if f then Some x else None))
        in
        if np >= nq then
          ( one_side_pieces p ps q qs,
            fun flags -> Formula.mk_or (kept ps flags) q )
        else
          ( one_side_pieces p ps q qs,
            fun flags -> Formula.mk_or p (kept qs flags) )
      else whole
  | _ -> whole

(** [words_by_pieces ?two_rounds_first ~ask phi]: the words route of
    [valid_by_word_forms] taken over every piece of [phi], each piece tried
    exactly as there (the piece itself, then its [word_forms]; a piece that
    reads no word is not tried).  Returns [`Proved] when every piece is
    proved; [`Rest psi] when some but not all are and [psi], equivalent in
    every model to the conjunction of the pieces not proved
    ([pieces_with_residual]), is smaller ([Formula.ast_size]) than [phi];
    and [`Ask_whole] otherwise -- no piece proved, or a rest no smaller than
    the question.  Why the size test: the pieces are taken after the
    one-point rule, which can grow a formula, and a distributed disjunction's
    rest writes one side's pieces once per piece of the other they are kept
    with; on a Rust-derived bit-set input two rests were 18,104 and 18,484
    nodes for questions of 5,170 and 940, and asking the question itself is
    exactly as good a proof.

    Contract: [`Proved] implies [phi] valid in every model (as for
    [valid_by_word_forms]); with [`Rest psi], [phi] is valid exactly when
    [psi] is -- the pieces' conjunction is equivalent to [phi] (after the
    exact one-point rule), the proved pieces are valid, and [psi] is
    equivalent to the conjunction of the others -- so a proof of [psi] by
    any route is a proof of [phi], and a countermodel of [psi] is one of
    [phi].  [`Ask_whole] says nothing. *)
let words_by_pieces ?two_rounds_first ?(note = fun _ -> ()) ~ask phi =
  let question_size = Formula.ast_size phi in
  let phi =
    Common.PhaseTime.with_phase "w-onepoint" (fun () ->
        Ast.Evaluator.elim_onepoint_and_split_binders phi)
  in
  let ps, residual = pieces_with_residual phi in
  let n = List.length ps in
  let remaining =
    List.mapi ps ~f:(fun k p ->
        let size = Formula.ast_size p in
        if not (Z3Smt.Z3interface.reads_int_as_word p) then (
          note (sprintf "piece %d of %d (size %d): reads no word" (k + 1) n size);
          true)
        else
          let proved = word_piece_proved ?two_rounds_first ~ask p in
          note
            (sprintf "piece %d of %d (size %d): %s" (k + 1) n size
               (if proved then "proved" else "not proved"));
          not proved)
  in
  if not (List.exists remaining ~f:Fn.id) then `Proved
  else if List.for_all remaining ~f:Fn.id then `Ask_whole
  else
    let psi = residual remaining in
    if Formula.ast_size psi < question_size then `Rest psi
    else (
      note
        (sprintf "rest of size %d not smaller than the question (%d)"
           (Formula.ast_size psi) question_size);
      `Ask_whole)

(* ===== Matched-instance forms asked through their words (end) ===== *)
