open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* The evidence PCSat has when it answers [unsat], recorded instead of
   discarded.  This is the "quick" stage:
   the skeleton of a refutation over the *preprocessed* problem — which
   examples conflicted, which clauses they were derived from, which kind
   lemmas took part — without the substitutions that a checkable certificate
   would also need (Stage 1 of the document). *)

type source =
  | Clause of Clause.t  (** a clause of the preprocessed problem *)
  | Assumed of Clause.t
      (** a learned clause received over the messenger (MuVal exchange): not a
          consequence of the problem, the refutation is conditional on it *)
  | Untracked  (** derived by a component that records no sources *)

type example = {
  clause : ExClause.t;
  sources : source list;
  derivation : (string * TermSubst.t option * Clause.t option) option;
      (** the rule that produced the example, the substitution applied to the
          clause it was derived from, and that clause, when recorded *)
  parents : ExClause.t list;
      (** the examples it was directly derived from (unit propagation,
          resolution against examples) *)
}

type body =
  | Conflict of {
      atom : ExAtom.t;
      positives : example list;
      negatives : example list;
    }
      (** a ground atom is both a decided positive and a decided negative
          example (labeler) *)
  | Labeling of {
      positives : example list;
      negatives : example list;
      undecided : example list;
      lemmas : ExClause.t list;
    }
      (** the labeling problem over the example clauses and the learned kind
          lemmas (WF/NWF/Parity cycles, DWF self-loops, FN functionality) has no solution *)
  | Propagation of {
      conflicts : ExAtom.t list;
      positives : example list;
      negatives : example list;
      undecided : example list;
    }
      (** unit propagation over the examples derived a conflict (labeler, or
          candidate checker after instantiating the examples with a candidate)
      *)
  | FalseConstraint of Logic.sort_env_map * Logic.term
      (** a constraint is [false] after preprocessing *)
  | Countermodel of {
      formula : Formula.t;
      model : Formula.t;
      witnesses : (Ident.tvar * Sort.t * Term.t) list;
    }
      (** no unknown is left and Z3 refuted the remaining formula with the given
          model of its free variables; [witnesses] are closed terms for
          existential binders of the negation of a clause the model falsifies
          (universal binders of the clause), which let a checker decide that
          negation by existential introduction when it binds a sequence (see
          [CountermodelWitness]); possibly empty *)
  | External of string
      (** a component whose evidence is not yet recorded (strategy synthesis for
          FN totality, the old resolver) *)
  | FiniteInstance of finite_instance
      (** a constraint is [false] after preprocessing because a finite
          instance of the problem was refuted: see [finite_instance] *)

(* A refutation of the problem at one finite cardinality of its universally
   quantified sorts.  A universally quantified sort is uninterpreted, and a
   theory model may give it any non-empty carrier, a finite one included; the
   system is satisfiable only when every model admits a solution, so a model
   whose carrier for each such sort has [size] elements and admits none refutes
   the system.  Reading the problem in such a model is replacing each sort by
   a datatype with [size] nullary constructors, which is what [smap] does, and
   the instance so obtained is what [nested] refutes.  A checker re-derives the
   instance from [source] under [dtenv] and [fenv] rather than trusting a
   recorded copy, re-checks [nested] against it, and separately checks that
   the clauses of [source] follow from the original problem. *)
and finite_instance = {
  leaf : Logic.sort_env_map * Logic.term;
      (** the [false] constraint the refutation was turned into *)
  size : int;  (** the number of elements given to each quantified sort *)
  smap : sort_subst;
      (** each quantified sort variable to the enumeration datatype standing
          for its finite carrier *)
  source : PCSP.Problem.t;
      (** the problem the instantiation was applied to, which is the
          preprocessed problem at that stage and not the original *)
  dtenv : DTEnv.t;
  fenv : FunEnv.t;
      (** the process-global datatype and function environments the instance
          was substituted from, enumeration datatypes included *)
  nested : t;
      (** the refutation of the instance, whose [problem] is the instance as
          it was handed to the nested solve *)
}

and t = {
  senv : Logic.sort_env_map;
  body : body;
  problem : PCSP.Problem.t option;
      (** the preprocessed problem the witness refers to, for checking its
          clauses against the original ones *)
}

let make ?(problem = None) senv body = { senv; body; problem }

let str_of_source senv = function
  | Clause c -> sprintf "(clause %s)" (Clause.str_of senv c)
  | Assumed c -> sprintf "(assumed %s)" (Clause.str_of senv c)
  | Untracked -> "(untracked)"

let str_of_example senv { clause; sources; derivation; parents } =
  sprintf "  (example %s%s%s%s)" (ExClause.str_of clause)
    (match derivation with
    | None -> ""
    | Some (rule, sub, via) ->
        sprintf "\n    (rule %s)%s%s" rule
          (match sub with
          | None -> ""
          | Some sub -> sprintf "\n    (subst %s)" (TermSubst.str_of sub))
          (match via with
          | None -> ""
          | Some c -> sprintf "\n    (via %s)" (Clause.str_of senv c)))
    (String.concat_map_list sources ~sep:"" ~f:(fun s ->
         "\n    " ^ str_of_source senv s))
    (if List.is_empty parents then ""
     else sprintf "\n    (parents %d)" (List.length parents))

let str_of_examples senv name exs =
  if List.is_empty exs then ""
  else
    sprintf "\n (%s\n%s)" name
      (String.concat_map_list exs ~sep:"\n" ~f:(str_of_example senv))

let rec has_assumption { body; _ } =
  let assumed exs =
    List.exists exs ~f:(fun { sources; _ } ->
        List.exists sources ~f:(function Assumed _ -> true | _ -> false))
  in
  match body with
  | Conflict { positives; negatives; _ } ->
      assumed positives || assumed negatives
  | Labeling { positives; negatives; undecided; _ }
  | Propagation { positives; negatives; undecided; _ } ->
      assumed positives || assumed negatives || assumed undecided
  | FalseConstraint _ | Countermodel _ | External _ -> false
  | FiniteInstance { nested; _ } -> has_assumption nested

let rec str_of ({ senv; body; _ } as w) =
  let head, rest =
    match body with
    | Conflict { atom; positives; negatives } ->
        ( sprintf "(conflict %s)" (ExAtom.str_of atom),
          str_of_examples senv "positives" positives
          ^ str_of_examples senv "negatives" negatives )
    | Labeling { positives; negatives; undecided; lemmas } ->
        ( "(labeling-unsat)",
          str_of_examples senv "positives" positives
          ^ str_of_examples senv "negatives" negatives
          ^ str_of_examples senv "undecided" undecided
          ^
          if List.is_empty lemmas then ""
          else
            sprintf "\n (lemmas\n%s)"
              (String.concat_map_list lemmas ~sep:"\n" ~f:(fun l ->
                   "  " ^ ExClause.str_of l)) )
    | Propagation { conflicts; positives; negatives; undecided } ->
        ( sprintf "(propagation-conflict %s)"
            (String.concat_map_list conflicts ~sep:" " ~f:ExAtom.str_of),
          str_of_examples senv "positives" positives
          ^ str_of_examples senv "negatives" negatives
          ^ str_of_examples senv "undecided" undecided )
    | FalseConstraint (uni_senv, term) ->
        ( "(false-constraint)",
          "\n " ^ Logic.ExtTerm.str_of_formula senv uni_senv term )
    | Countermodel { formula; model; witnesses } ->
        ( "(countermodel)",
          sprintf "\n (formula %s)\n (model %s)%s" (Formula.str_of formula)
            (Formula.str_of model)
            (if List.is_empty witnesses then ""
             else
               sprintf "\n (witnesses %s)"
                 (String.concat_map_list witnesses ~sep:" " ~f:(fun (x, _, t) ->
                      sprintf "(%s %s)" (Ident.name_of_tvar x) (Term.str_of t))))
        )
    | External what -> (sprintf "(external \"%s\")" what, "")
    | FiniteInstance { leaf = uni_senv, term; size; nested; _ } ->
        ( sprintf "(finite-instance (size %d))" size,
          "\n " ^ Logic.ExtTerm.str_of_formula senv uni_senv term ^ "\n "
          ^ str_of nested )
  in
  sprintf "(unsat-witness %s%s%s)" head rest
    (if has_assumption w then "\n (conditional-on-assumed-clauses)" else "")

(* The witness as the typed payload of [PCSP.Problem.Unsat]: its examples
   become nodes (one per distinct example clause), their recorded parents
   become premises — a parent that is not itself a recorded example gets a
   leaf node without derivation — and the body becomes the conclusion with
   the top-level examples as roots.  The sources are folded into [assumed]; the clauses themselves
   stay in this record for the checker. *)
let to_refutation (w : t) : PCSP.Refutation.t =
  let key = ExClause.str_of in
  let ids : (string, int) Hashtbl.t = Hashtbl.create (module String) in
  let nodes : (int, PCSP.Refutation.node) Hashtbl.t =
    Hashtbl.create (module Int)
  in
  let id_of cl =
    Hashtbl.find_or_add ids (key cl) ~default:(fun () -> Hashtbl.length ids)
  in
  let leaf cl =
    let id = id_of cl in
    if not (Hashtbl.mem nodes id) then
      Hashtbl.set nodes ~key:id
        ~data:
          {
            PCSP.Refutation.id;
            example = cl;
            rule = None;
            subst = None;
            via = None;
            premises = [];
            assumed = false;
          };
    id
  in
  let add (e : example) =
    let id = id_of e.clause in
    let premises =
      List.dedup_and_sort ~compare:Int.compare (List.map e.parents ~f:leaf)
    in
    let rule, subst, via =
      match e.derivation with
      | None -> (None, None, None)
      | Some (r, s, v) -> (Some r, s, v)
    in
    let assumed =
      List.exists e.sources ~f:(function Assumed _ -> true | _ -> false)
    in
    Hashtbl.set nodes ~key:id
      ~data:
        {
          PCSP.Refutation.id;
          example = e.clause;
          rule;
          subst;
          via;
          premises;
          assumed;
        };
    id
  in
  let roots, conclusion =
    match w.body with
    | Conflict { atom; positives; negatives } ->
        (List.map (positives @ negatives) ~f:add, PCSP.Refutation.Conflict atom)
    | Labeling { positives; negatives; undecided; _ } ->
        ( List.map (positives @ negatives @ undecided) ~f:add,
          PCSP.Refutation.Labeling )
    | Propagation { conflicts; positives; negatives; undecided } ->
        ( List.map (positives @ negatives @ undecided) ~f:add,
          PCSP.Refutation.Propagation conflicts )
    | FalseConstraint (senv, t) ->
        ([], PCSP.Refutation.FalseConstraint (senv, t))
    | Countermodel { formula; model; _ } ->
        ([], PCSP.Refutation.Countermodel (formula, model))
    | External s -> ([], PCSP.Refutation.External s)
    | FiniteInstance { leaf = senv, t; _ } ->
        ([], PCSP.Refutation.FalseConstraint (senv, t))
  in
  {
    PCSP.Refutation.senv = w.senv;
    conclusion;
    nodes =
      List.sort (Hashtbl.data nodes) ~compare:(fun a b ->
          Int.compare a.PCSP.Refutation.id b.PCSP.Refutation.id);
    roots = List.dedup_and_sort roots ~compare:Int.compare;
  }
