(* Forward application of a guarded hypothesis at the points its guard holds,
   for a validity question of the zero-unknown verdict.

   The question.  A piece [phi] is valid exactly when its negation
   [N = nnf (not phi)] is unsatisfiable.  [N] is a conjunction of FACTS
   (quantifier-free conjuncts) and HYPOTHESES (conjuncts [forall xs. d_1 \/ ...
   \/ d_n]).  A called function's contract read through a relation is such a
   hypothesis: [forall v. not R(e, v) \/ (wi = v div 64 /\ m = 1 << (v mod 64))]
   says what the call returned at every [v] the relation [R(e, .)] holds at,
   and a fact [R(e, x)] says where it holds.

   The rule.  A GUARD of a hypothesis is a disjunct that is a negated
   Bool-valued term [not B(xs)] mentioning a binder ([B] a read of a relation:
   a [select] chain, a Boolean function application).  Every fact [B(ts)] of
   the opposite polarity is matched against it ([SeqInstantiation.match_pattern],
   first-order and syntactic), and the substitutions that bind every binder
   give instances [d_1 theta \/ ... \/ d_n theta], each a consequence of [N].
   A disjunct whose negation is itself a fact, or that the facts over its own
   variables refute ([valid] proves [not (facts /\ e)]), is dropped; when one
   disjunct is left it is a consequence of [N] and its conjuncts become new
   facts, and when none is left [N] is unsatisfiable and [phi] is valid.  At
   most [max_rounds] rounds (a new fact can be a guard's match), at most
   [max_instances] instances per hypothesis and round, [max_questions]
   questions in all.  Only proofs of validity are read.  With
   [theory_facts_only], a form whose derived facts are all relation reads
   ([relation_read_fact]) is not returned.

   The form.  Before the rule the free variables of a single-constructor
   datatype (a tuple, a record) that the piece reads through a selector are
   split into their fields ([Evaluator.split_single_cons_free_vars]), which is
   an identity under the universal closure of a validity question.  The form
   returned is [new_facts => phi_split]: every new fact follows from the
   negation of [phi_split], so the form is valid exactly when [phi] is.

   Why.  A Rust-derived postcondition ([contains] of a bit set: the word and
   the mask a call returned, read through a tuple, and the relation that fixes
   the element's index) was left undecided at 30 s by Z3 asked whole, with the
   tuples split, and with the contract's instance added as the implication it
   is (its guard still to be discharged); it was decided in 0.2-0.3 s with the
   tuples split AND the instance's conclusion asserted as a fact. *)
open Core
open Ast
open Ast.LogicOld

let max_rounds = 3
let max_instances = 16
let max_questions = 48

(** a literal read as [(b, polarity)] when it is a Boolean term [b] compared
    with a Boolean constant ([b = true], [b != false], their negations), the
    polarity being whether it says [b] holds *)
let rec bool_term_lit = function
  | Formula.UnaryOp (Formula.Not, f, _) ->
      Option.map (bool_term_lit f) ~f:(fun (b, pol) -> (b, not pol))
  | Formula.Atom (Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as p), [ t1; t2 ], _), _)
    -> (
      let eq = match p with T_bool.Eq -> true | _ -> false in
      let const t =
        if T_bool.is_true t then Some true
        else if T_bool.is_false t then Some false
        else None
      in
      match (const t1, const t2) with
      | None, Some c -> Some (t1, Bool.(c = eq))
      | Some c, None -> Some (t2, Bool.(c = eq))
      | _ -> None)
  | _ -> None

(** whether a derived fact is only a read of a relation: a Boolean term that is
    a [select] chain, a variable or a function application, said to hold or to
    fail.  A form whose derived facts are all such reads is the question plus
    ground atoms of the relations its own hypotheses are guarded by, the
    instances E-matching reaches from those guards as triggers; measured over
    five Rust-derived inputs, no such form was decided where the question
    alone was not, and the ones left undecided were undecided questions (or,
    once, a question decided in 0.5 s that the added atoms made a timeout),
    while the forms that decided what the question alone did not all derived
    a fact with arithmetic content (a call's word and mask at the index its
    relation holds at). *)
let relation_read_fact f =
  match bool_term_lit f with
  | Some (b, _) -> (
      match b with
      | Term.Var _ -> true
      | Term.FunApp ((T_array.ASelect _ | FVar _ | FunCall _), _, _) -> true
      | _ -> false)
  | None -> false

let is_collection_sort s =
  Term.is_array_sort s || SeqInstantiation.is_seq_sort s

(** the hypotheses whose binders are all of a non-collection sort, with their
    guards: [(senv, body, guards)], each guard the Boolean term [b] of a
    disjunct saying [not b] that mentions a binder *)
let hypotheses conjuncts =
  List.filter_map conjuncts ~f:(function
    | Formula.Bind (Formula.Forall, senv, body, _)
      when (not (List.is_empty senv))
           && List.for_all senv ~f:(fun (_, s) -> not (is_collection_sort s)) ->
        let vars = Set.Poly.of_list (List.map senv ~f:fst) in
        let guards =
          List.filter_map (Formula.disjuncts_list_of body) ~f:(fun d ->
              match bool_term_lit d with
              | Some (b, false)
                when not (Set.is_empty (Set.inter vars (Term.tvs_of b))) ->
                  Some b
              | _ -> None)
        in
        if List.is_empty guards then None else Some (senv, body, guards)
    | _ -> None)

(** the substitutions of all of [senv] obtained by matching each guard against
    a fact that says its term holds, at most [max_instances] *)
let instances ~facts senv guards =
  let vars = Set.Poly.of_list (List.map senv ~f:fst) in
  let holds =
    List.filter_map facts ~f:(fun f ->
        match bool_term_lit f with Some (b, true) -> Some b | _ -> None)
  in
  let rec go sub = function
    | [] -> [ sub ]
    | g :: rest ->
        List.concat_map holds ~f:(fun b ->
            match
              SeqInstantiation.match_pattern ~assoc:false ~vars sub g b
            with
            | Some sub -> go sub rest
            | None -> [])
  in
  go Map.Poly.empty guards
  |> List.filter ~f:(fun sub ->
         Set.for_all vars ~f:(fun v -> Map.Poly.mem sub v))
  |> List.dedup_and_sort ~compare:Stdlib.compare
  |> fun subs -> List.take subs max_instances

let questions_asked = ref 0

(* the last form [form] returned, with the split question and the facts it
   derived, for the dump of [form_valid_forked] *)
let last_form : (Formula.t * Formula.t * Formula.t list) option ref = ref None

let dump_count = Atomic.make 0

(* trace every question the rule asks, with its disjunct *)
let trace_questions = ref false

(** [`Proved] when the negation of [phi] is refuted by the rule alone,
    [`Form psi] with [psi] the strengthened question ([new_facts => phi], after
    the split) when the rule derived a fact, [`None] otherwise.  [valid psi]
    must be [true] only when [psi] is valid. *)
let form ?(trace = fun (_ : string lazy_t) -> ()) ?(theory_facts_only = false)
    ~valid phi =
  let senv = Map.Poly.of_alist_reduce (Set.to_list (Formula.term_sort_env_of phi))
      ~f:(fun a _ -> a) in
  let _, phi, nsplit =
    Evaluator.split_single_cons_free_vars ~selected_only:true senv phi
  in
  let n = Evaluator.simplify @@ Formula.nnf_of (Formula.negate phi) in
  let conjuncts = Formula.conjuncts_list_of n in
  let hyps = hypotheses conjuncts in
  if List.is_empty hyps then `None
  else
    let asked = ref 0 in
    let facts0 = List.filter conjuncts ~f:Formula.is_quantifier_free in
    (* [facts] imply [not e]: syntactically (the negation is a fact, or a
       linear bound the facts' bounds imply: [Evaluator.ctx_entails], whose
       [true] is never wrong), and otherwise asked of [valid] beside the facts
       over [e]'s own variables (a refutation from some of the facts is one
       from all) *)
    let cheap facts e =
      let neg = Evaluator.simplify (Formula.nnf_of (Formula.negate e)) in
      Formula.is_false e
      || List.mem facts neg ~equal:Stdlib.( = )
      || (match bool_term_lit e with
         | Some (b, pol) ->
             List.exists facts ~f:(fun f ->
                 match bool_term_lit f with
                 | Some (b', pol') -> Bool.(pol <> pol') && Stdlib.( = ) b b'
                 | None -> false)
         | None -> false)
      || Evaluator.ctx_entails facts (Evaluator.ctx_ge_facts facts) neg
    in
    let asked_refuted facts e =
      let vs = Formula.tvs_of e in
      let fs =
        List.filter facts ~f:(fun f -> Set.is_subset (Formula.tvs_of f) ~of_:vs)
      in
      (not (List.is_empty fs))
      && !asked < max_questions
      && (incr asked;
          incr questions_asked;
          let r = valid (Formula.negate (Formula.and_of (e :: fs))) in
          if !trace_questions then
            trace
              (lazy
                (sprintf "guarded facts: asked %s beside %d facts: %b"
                   (Formula.str_of e) (List.length fs) r));
          r)
    in
    (* the disjuncts of [inst] the facts do not refute, or [None] once two
       are left (no fact can come of it, so nothing more is asked) *)
    let left_of facts inst =
      let ds =
        List.filter (Formula.disjuncts_list_of inst) ~f:(fun e ->
            not (cheap facts e))
      in
      if List.exists ds ~f:Formula.is_true then None
      else
        let rec go left = function
          | [] -> Some left
          | e :: rest ->
              if asked_refuted facts e then go left rest
              else if List.length left >= 1 then None
              else go [ e ] rest
        in
        match ds with [ e ] -> Some [ e ] | _ -> go [] ds
    in
    let tried = ref [] in
    let rec round k facts derived =
      if k > max_rounds then `Facts derived
      else
        let progress = ref false in
        let result =
          List.fold_until hyps ~init:(facts, derived)
            ~finish:(fun acc -> `Facts acc)
            ~f:(fun (facts, derived) (senv, body, guards) ->
              let subs = instances ~facts senv guards in
              let rec over facts derived = function
                | [] -> Continue_or_stop.Continue (facts, derived)
                | sub :: more ->
                    let inst =
                      Evaluator.simplify @@ Formula.nnf_of
                      @@ Formula.subst sub body
                    in
                    if List.mem !tried inst ~equal:Stdlib.( = ) then
                      over facts derived more
                    else (
                      tried := inst :: !tried;
                      match left_of facts inst with
                      | Some [] -> Continue_or_stop.Stop `Proved
                      | Some [ e ] ->
                          let fresh =
                            List.filter (Formula.conjuncts_list_of e)
                              ~f:(fun c ->
                                Formula.is_quantifier_free c
                                && not (List.mem facts c ~equal:Stdlib.( = )))
                          in
                          if not (List.is_empty fresh) then progress := true;
                          over (facts @ fresh) (derived @ fresh) more
                      | _ -> over facts derived more)
              in
              over facts derived subs)
        in
        match result with
        | `Proved -> `Proved
        | `Facts (facts, derived) ->
            if !progress then round (k + 1) facts derived else `Facts derived
    in
    let r = round 1 facts0 [] in
    trace
      (lazy
        (sprintf
           "guarded facts: %d variables split, %d hypotheses, %d questions, %s"
           nsplit (List.length hyps) !asked
           (match r with
           | `Proved -> "proved"
           | `Facts d -> sprintf "%d facts derived" (List.length d))));
    match r with
    | `Proved -> `Proved
    | `Facts [] -> `None
    | `Facts derived
      when theory_facts_only && List.for_all derived ~f:relation_read_fact ->
        trace
          (lazy
            "guarded facts: every derived fact is a relation read, no form");
        `None
    | `Facts derived ->
        let psi =
          Formula.or_of [ Formula.negate (Formula.and_of derived); phi ]
        in
        last_form := Some (psi, phi, derived);
        `Form psi

(** whether [form] can derive anything from [phi]: a hypothesis with a guard
    some fact of the negation matches.  Syntactic, asks nothing; meant to keep
    a caller from paying for [form] on a question it cannot act on. *)
let applicable phi =
  let conjuncts =
    Formula.conjuncts_list_of (Formula.nnf_of (Formula.negate phi))
  in
  let facts = List.filter conjuncts ~f:Formula.is_quantifier_free in
  List.exists (hypotheses conjuncts) ~f:(fun (senv, _, guards) ->
      not (List.is_empty (instances ~facts senv guards)))

(** The rule applied with no solver question (a disjunct is dropped only when
    the facts refute it syntactically: its negation is a fact, or a linear
    bound the facts' bounds imply), so it costs no process and no solver
    call. *)
let syntactic ?trace ?theory_facts_only phi =
  form ?trace ?theory_facts_only ~valid:(fun _ -> false) phi

(** [true] only when [psi] is valid: asked of Z3 in a forked copy killed after
    [ms] milliseconds ([ForkedQuery.run]).  In the copy the rewrite of bounded
    integers read through [int_to_bv] into bit-vectors is off: it is an
    equisatisfiable rewrite, so either reading answers the same question, and
    on the forms this rule builds (word and mask arithmetic over the fields of
    a split tuple) Z3 decided them in 0.1-0.3 s without it and left them
    undecided at 20 s with it.  Z3's own budget does not bound every question
    asked without that rewrite, which is why the copy is killed. *)
let form_valid_forked ?(trace = fun (_ : string lazy_t) -> ()) ~ms psi =
  (* With [COAR_DUMP_GUARDED_FORMS=dir] in the environment, each form asked
     here is written before it is asked: [dir/gN-PID_form_native.smt2] (its
     negation as the copy asks it, the range rewrite off),
     [..._question_off_native.smt2] and [..._question_on_native.smt2] (the
     split question without the facts, the rewrite off and on),
     [..._facts.txt] (the derived facts and the question), and one line
     [gN-PID outcome secs ms form_size question_size facts] appended to
     [dir/index.txt].  A diagnostic: nothing is written and the answer is
     unchanged without the variable. *)
  let dump =
    match Sys.getenv "COAR_DUMP_GUARDED_FORMS" with
    | None -> None
    | Some dir ->
        let name =
          sprintf "g%d-%d"
            (Atomic.fetch_and_add dump_count 1)
            (Common.ForkGuard.self_pid ())
        in
        let prefix = dir ^ "/" ^ name in
        let fenv = get_fenv () in
        let write suffix phi =
          Z3Smt.Z3interface.with_query_dump (prefix ^ suffix) (fun () ->
              Z3Smt.Z3interface.dump_native_question ~id:None fenv phi)
        in
        let saved = Atomic.get Z3Smt.Z3interface.int_to_bv_range in
        let q, facts =
          match !last_form with
          | Some (psi', q, facts) when phys_equal psi psi' -> (Some q, facts)
          | _ -> (None, [])
        in
        Fun.protect
          ~finally:(fun () -> Z3Smt.Z3interface.set_int_to_bv_range saved)
          (fun () ->
            Z3Smt.Z3interface.set_int_to_bv_range false;
            write "_form" psi;
            Option.iter q ~f:(write "_question_off");
            Z3Smt.Z3interface.set_int_to_bv_range true;
            Option.iter q ~f:(write "_question_on"));
        Out_channel.write_all (prefix ^ "_facts.txt")
          ~data:
            (String.concat ~sep:"\n"
               (List.map facts ~f:(fun f -> "fact: " ^ Formula.str_of f)
               @ [
                   "question: "
                   ^ Option.value_map q ~default:"?" ~f:Formula.str_of;
                   "";
                 ]));
        Some (dir, name, Common.Clock.now_float (), q, List.length facts)
  in
  let r =
    ForkedQuery.run ~ms (fun () ->
        Z3Smt.Z3interface.set_int_to_bv_range false;
        match
          Z3Smt.Z3interface.check_valid ~timeout:(Some ms) ~fresh_solver:true
            ~id:None
            (Z3Smt.Z3interface.fenv_reached_by (get_fenv ()) psi)
            psi
        with
        | `Valid -> true
        | _ -> false)
  in
  Option.iter dump ~f:(fun (dir, name, started, q, nfacts) ->
      let secs =
        Time_float.Span.to_sec
          (Time_float.diff (Common.Clock.now_float ()) started)
      in
      Out_channel.with_file (dir ^ "/index.txt") ~append:true ~f:(fun oc ->
          Out_channel.output_string oc
            (sprintf "%s %s %.3f %d %d %d %d\n" name
               (match r with
               | Some true -> "valid"
               | Some false -> "not-proved"
               | None -> "killed")
               secs ms (Formula.ast_size psi)
               (Option.value_map q ~default:0 ~f:Formula.ast_size)
               nfacts)));
  match r with
  | Some b ->
      trace
        (lazy
          (if b then "guarded facts: form valid"
           else "guarded facts: form not proved"));
      b
  | None ->
      trace (lazy "guarded facts: no answer from the forked copy");
      false
