(* Predicate constraint satisfaction problems (pfwCSP), the representation
   that nearly every input class and solver in this tool reduces to.

   A problem is a set of constraints over unknown predicates and functions,
   held either as quantified formulas ([Raw]) or as clauses ([Cnf]), together
   with parameters ([Params.t]): the unknowns and their sorts, each unknown's
   kind (ordinary, well-founded, functional, non-empty, ...), the datatype and
   function environments, and the solver bookkeeping (dependencies,
   eliminated predicates and how to recover their solutions).  Semantics: a
   problem is satisfiable when every model of the background theory admits an
   interpretation of the unknowns, of the kinds declared, under which every
   constraint holds; a solver answers [Sat] by exhibiting one solution valid
   in every model, and [Unsat] by a refutation.

   Beside the accessors and printers, this module holds the transformations
   that run on every problem: conversion to negation and clausal normal form,
   [normalize], substitution of (partial) solutions, removal of unused
   parameters, the elimination of trivially satisfiable or unsatisfiable kinded
   predicates, and [make], which builds a problem from SMT-LIB assertions and
   Skolemises the existentials an unknown lies under.  [check_valid] checks a
   candidate solution clause by clause with the validity test it is given.
   [refuse_non_ord_kinds] is how a backend that cannot honour a predicate kind
   declines the problem as an unsupported input rather than answering a
   weaker question. *)
open Core
open Graph
open Common.Ext
open Common.Combinator
open Ast
open Ast.Logic

type t =
  | Raw of (sort_env_map * term) Set.Poly.t * Params.t
  | Cnf of ClauseSet.t * Params.t

type refutation =
  | Formula of LogicOld.Formula.t
  | Proof of Refutation.t
  | External of string

type solution =
  | Sat of term_subst_map
  | Unsat of refutation option
  | Unknown
  | OutSpace of Ident.tvar list
  | Timeout

type oracle = CandSolOld.t option

let lts_str_of_solution = function
  | Sat _ -> "YES"
  | Unsat _ -> "NO"
  | Unknown | OutSpace _ | Timeout -> "MAYBE"

type bounds = (Ident.tvar, int * (sort_env_map * term)) Map.Poly.t

type Common.Messenger.info +=
  | CandidateSolution of
      (term_subst_map
      * term_subst_map
      * ClauseSet.t
      * ClauseSet.t
      * (sort_env_map * LogicOld.FunEnv.t * (Ident.tvar, term) Hashtbl.Poly.t)
        option)
  | LowerBounds of bounds
  | UpperBounds of bounds

module type ProblemType = sig
  val problem : t
end

let of_formulas ?(params = Params.empty) phis = Raw (phis, params)

let of_old_formulas ?(params = Params.empty) =
  Set.Poly.map ~f:ExtTerm.of_old >> of_formulas ~params

let of_clauses ?(params = Params.empty) cs = Cnf (cs, params)
let params_of = function Raw (_, params) | Cnf (_, params) -> params
let arg_original_names_of pcsp = (params_of pcsp).Params.arg_original_names
let senv_of pcsp = (params_of pcsp).Params.senv
let kind_map_of pcsp = (params_of pcsp).Params.kind_map
let kind_of pcsp = Map.Poly.find_exn (kind_map_of pcsp)

let kindpvs_of_aux pcsp is_kind =
  Map.key_set
  @@ Map.Poly.filter_keys ~f:(Map.Poly.mem (senv_of pcsp))
  @@ Map.Poly.filter ~f:is_kind @@ (params_of pcsp).Params.kind_map

(* The predicates whose kind a backend that solves ordinary Horn clauses cannot
   honour, with the kind, so that a refusal can name what it refused.

   Asking the question the other way round -- listing the kinds to refuse -- is
   what left DWF and non-emptiness accepted: the two CHC backends consulted only the
   well-founded and functional accessors, and a problem carrying either of the
   other kinds was converted into ordinary Horn relations with the kind's
   obligation silently dropped, so a non-empty predicate that must not be false
   everywhere, and a disjunctively well-founded one that must not contain a self
   loop, both came back sat.  Every kind but [Ord] is an obligation the clauses do
   not state, so [Ord] is the one to name and the rest follow from it -- including
   a kind added later, which is the point. *)
let non_ord_kinds_of pcsp =
  Map.Poly.to_alist
  @@ Map.Poly.filter_keys ~f:(Map.Poly.mem (senv_of pcsp))
  @@ Map.Poly.filter ~f:(Kind.is_ord >> not)
  @@ (params_of pcsp).Params.kind_map

let fnpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_fn
let uniqpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_uniq
let totpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_tot
let wfpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_wf
let dwfpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_dwf
let nwfpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_nwf
let paritypvs_of pcsp = kindpvs_of_aux pcsp Kind.is_parity
let admpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_adm
let integpvs_of pcsp = kindpvs_of_aux pcsp Kind.is_integ

let fnpvs_senv_of pcsp =
  let fnpvs = fnpvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.mem fnpvs)

(* Every predicate single-valued at a known position, with that position: an
   [FN] predicate at its last argument, a [Uniq] one at its declared one.  The
   mechanisms that use only single-valuedness (the labeling's conflict learner,
   the witness checker's functionality query) read this rather than
   [fnpvs_senv_of], so a [Uniq] predicate reaches them and a totality-using
   mechanism never sees it. *)
let single_valued_pvs_of pcsp =
  let kind_map = kind_map_of pcsp in
  Map.Poly.filter_mapi (senv_of pcsp) ~f:(fun ~key ~data:sort ->
      match Map.Poly.find kind_map key with
      | Some Kind.FN -> Some (sort, List.length (Sort.args_of sort) - 1)
      | Some (Kind.Uniq (j, _)) -> Some (sort, j)
      | _ -> None)

let totpvs_senv_of pcsp =
  let totpvs = totpvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.mem totpvs)

(* The universally quantified positions of every total predicate: what the
   totality-using mechanisms need besides the name, since [Tot []] and
   [Tot (all but last)] are different obligations. *)
let tot_positions_of pcsp =
  let kind_map = kind_map_of pcsp in
  Map.Poly.filter_mapi (senv_of pcsp) ~f:(fun ~key ~data:_ ->
      Option.bind (Map.Poly.find kind_map key) ~f:Kind.tot_positions_of)

let wfpvs_senv_of pcsp =
  let wfpvs = wfpvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.mem wfpvs)

let dwfpvs_senv_of pcsp =
  let dwfpvs = dwfpvs_of pcsp in
  Map.Poly.filter_keys (senv_of pcsp) ~f:(Set.mem dwfpvs)

let nwfpvs_senv_of pcsp =
  Map.Poly.filter_mapi (senv_of pcsp) ~f:(fun ~key ~data:_ ->
      match Map.Poly.find (kind_map_of pcsp) key with
      | Some (Kind.NWF (nwf, (idl, idr))) ->
          Some
            ( nwf.name,
              nwf.sorts_shared,
              idl,
              Hashtbl.Poly.find_exn nwf.sorts_map idl,
              idr,
              Hashtbl.Poly.find_exn nwf.sorts_map idr )
      | _ -> None)

let paritypvs_senv_of pcsp =
  Map.Poly.filter_mapi (senv_of pcsp) ~f:(fun ~key ~data:_ ->
      match Map.Poly.find (kind_map_of pcsp) key with
      | Some (Kind.Parity (nwf, (idl, idr))) ->
          Some
            ( nwf,
              idl,
              Hashtbl.Poly.find_exn nwf.sorts_map idl,
              idr,
              Hashtbl.Poly.find_exn nwf.sorts_map idr )
      | _ -> None)

let npfvs_of pcsp =
  Set.Poly.filter_map
    (Map.to_set @@ senv_of pcsp)
    ~f:(fun (x, s) ->
      if Fn.non BoolTerm.is_bool_sort @@ Sort.ret_of s then Some x else None)

let pvs_of pcsp =
  Set.Poly.filter_map
    (Map.to_set @@ senv_of pcsp)
    ~f:(fun (x, s) ->
      if BoolTerm.is_bool_sort @@ Sort.ret_of s then Some x else None)

let dtenv_of pcsp = (params_of pcsp).Params.dtenv
let fenv_of pcsp = (params_of pcsp).Params.fenv
let sol_space_of pcsp = (params_of pcsp).Params.sol_space
let messenger_of pcsp = (params_of pcsp).Params.messenger
let sol_for_eliminated_of pcsp = (params_of pcsp).Params.sol_for_eliminated
let elimination_reasons_of pcsp = (params_of pcsp).Params.elimination_reasons
let sol_for_resolved_of pcsp = (params_of pcsp).Params.sol_for_resolved
let erasure_trail_of pcsp = (params_of pcsp).Params.erasure_trail
let args_record_of pcsp = (params_of pcsp).Params.args_record
let stable_clauses_of pcsp = (params_of pcsp).Params.stable_clauses
let partial_sol_targets_of pcsp = (params_of pcsp).Params.partial_sol_targets
let dep_graph_of pcsp = (params_of pcsp).Params.dep_graph
let id_of pcsp = (params_of pcsp).id

(* the KIND alone, like every other [is_*_pred] below *)
let is_ord_kind pcsp = Params.is_kind (params_of pcsp) Kind.is_ord

(* and the sort, which is a separate question: an unknown of kind [Ord] whose
   return sort is not [bool] is not a predicate at all -- an SMT-LIB
   [declare-const] of a bit-vector or integer sort read as a constrained Horn
   problem is one, and it has no template. *)
let is_bool_valued pcsp x =
  match Map.Poly.find (senv_of pcsp) x with
  | None -> false
  | Some s -> BoolTerm.is_bool_sort @@ Sort.ret_of s

(* Both, and the name says both on purpose.  This used to be [is_ord_pred],
   which names only the kind while conjoining the sort test, and every sibling
   on the chain it heads ([is_fn_pred], [is_tot_pred], [is_wf_pred], ...) is the
   kind alone -- so the one that carried a second conjunct was the one that did
   not look like it.  What that cost: an unknown of kind [Ord] returning a
   bit-vector fell through every arm of the template dispatch and the failure
   reported its KIND as unsupported, which is the half that is fine, sending a
   reader to the kind table where everything is in order.

   Every caller wants the conjunction -- the eliminator, because its rules
   assign [true] or [false] to the predicate and that is only a value if it is
   bool-valued; the template dispatch, because a template is what the sort
   decides; the partial-solution targets, for the same reason -- so the two
   halves are exposed beside it rather than spelled at four call sites. *)
let is_bool_valued_ord_pred pcsp x = is_ord_kind pcsp x && is_bool_valued pcsp x

let is_fn_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_fn
let is_uniq_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_uniq
let is_tot_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_tot
let is_wf_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_wf
let is_dwf_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_dwf
let is_nwf_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_nwf
let is_parity_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_parity
let is_adm_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_adm

let is_adm_pred_with_cond pcsp =
  Params.is_kind (params_of pcsp) Kind.is_adm_with_cond

let is_integ_pred pcsp = Params.is_kind (params_of pcsp) Kind.is_integ

let is_int_fun pcsp x =
  Params.is_kind (params_of pcsp) Kind.is_int_fun x
  &&
  (*ToDo*)
  match Map.Poly.find (senv_of pcsp) x with
  | None -> false
  | Some s -> IntTerm.is_int_sort @@ Sort.ret_of s

let is_regex pcsp x =
  Params.is_kind (params_of pcsp) Kind.is_regex x
  &&
  (*ToDo*)
  match Map.Poly.find (senv_of pcsp) x with
  | None -> false
  | Some s -> RegexTerm.is_regex_sort s

(* The problem's clauses, with the stable ones unless [~full_clauses:false].
   Precondition: the problem is in its [Cnf] form. That is a state of the value,
   not a property of the input: it holds after [to_cnf] and [make], and not
   when a reader has just returned one. On a [Raw] problem this raises, and the
   message is kept as it is because diagnostics are keyed on it.
   [clauses_of_opt] is the total form, for a caller that cannot know which
   state it holds. *)
let clauses_of ?(full_clauses = true) = function
  | Raw _ -> failwith "The pfwCSP is not of CNF @ clauses_of"
  | Cnf (cnf, params) ->
      if full_clauses then Set.union cnf params.Params.stable_clauses else cnf

let clauses_of_opt ?(full_clauses = true) = function
  | Raw _ -> None
  | pcsp -> Some (clauses_of ~full_clauses pcsp)

let formulas_of ?(full_clauses = true) = function
  | Raw (phis, params) ->
      Set.union phis @@ ClauseSet.to_formulas
      @@ if full_clauses then params.Params.stable_clauses else Set.Poly.empty
  | Cnf (cnf, params) ->
      Set.union (ClauseSet.to_formulas cnf)
      @@ ClauseSet.to_formulas
      @@ if full_clauses then params.Params.stable_clauses else Set.Poly.empty

let formula_of ?(full_clauses = true) pcsp =
  let senvs, ts = Set.unzip @@ formulas_of ~full_clauses pcsp in
  ( Map.force_merge_list @@ Set.to_list @@ senvs,
    BoolTerm.and_of @@ Set.to_list ts )

let old_formulas_of ?(full_clauses = true) = function
  | Raw (phis, params) ->
      Set.union
        (Set.Poly.map
           ~f:(Tuple2.uncurry @@ ExtTerm.to_old_fml params.senv)
           phis)
      @@ Set.Poly.map ~f:(Clause.to_old_formula params.senv)
      @@ if full_clauses then params.Params.stable_clauses else Set.Poly.empty
  | Cnf (cnf, params) ->
      ClauseSetOld.to_formulas
      @@ ClauseSet.to_old_clause_set params.senv
      @@ Set.union cnf
      @@ if full_clauses then params.Params.stable_clauses else Set.Poly.empty

let old_formula_of ?(full_clauses = true) pcsp =
  LogicOld.Formula.and_of @@ Set.to_list @@ old_formulas_of ~full_clauses pcsp

let num_constrs pcsp = Set.length @@ formulas_of pcsp
let num_pvars pcsp = Set.length @@ pvs_of pcsp
let num_unknowns pcsp = Map.Poly.length @@ senv_of pcsp

let dtenv_of_def pcsp =
  let exi_senv = (params_of pcsp).senv in
  Set.fold ~init:Map.Poly.empty (formulas_of pcsp) ~f:(fun ret ->
      Tuple2.uncurry @@ ExtTerm.to_old_fml exi_senv
      >> LogicOld.DTEnv.of_formula
      >> LogicOld.DTEnv.force_merge ret)

let map_params ~f = function
  | Raw (phis, params) -> Raw (phis, f params)
  | Cnf (cls, params) -> Cnf (cls, f params)

let update_params pcsp params =
  match pcsp with
  | Raw (phis, _) -> Raw (phis, params)
  | Cnf (cls, _) -> Cnf (cls, params)

let update_params_dtenv pcsp =
  update_params pcsp
    {
      (params_of pcsp) with
      dtenv = Map.force_merge (dtenv_of pcsp) @@ dtenv_of_def pcsp;
    }

let set_params_sol_space pcsp sol_space =
  update_params pcsp { (params_of pcsp) with sol_space }

(* [pcsp] with its function environment ([Params.fenv]) restricted to the
   definitions its constraints (stable clauses included) reach -- applied
   directly, or through the body or the recorded property of another reached
   definition -- and the datatypes' size functions, which are kept whatever
   applies them. Reachability does not certify that omitted recursive
   equations impose no constraint: reusing this restricted environment as the
   complete background context needs a model-extension precondition, which
   this walk does not check. What it changes here is what reads the
   environment as vocabulary: the template hypothesis space applies
   every non-size function of [Params.fenv] to the parameters' terms, so an
   unused recursive definition becomes qualifiers whose truth at a parametric
   example is a question about the recursion.  The process-global environment
   ([LogicOld.get_fenv]) is left as it is.  Returns [pcsp] itself (physically)
   when nothing is dropped. *)
(* The functions a reconstruction pass added to the environment as
   vocabulary: applied by no clause, they are read by the hypothesis space
   only, so the pruning below keeps them as roots.  Written once, before
   solving, by the solver that runs the pass. *)
let reconstructed_functions : Ident.tvar Set.Poly.t Atomic.t =
  Atomic.make Set.Poly.empty

let prune_unreached_definitions pcsp =
  let params = params_of pcsp in
  let fenv = params.Params.fenv in
  if Map.Poly.is_empty fenv then pcsp
  else
    let called syms =
      Set.Poly.filter_map syms ~f:(function
        | LogicOld.FVar (v, _, _) when Map.Poly.mem fenv v -> Some v
        | _ -> None)
    in
    let rec close seen frontier =
      if Set.is_empty frontier then seen
      else
        let seen = Set.union seen frontier in
        let next =
          Set.Poly.union_list
          @@ List.map (Set.to_list frontier) ~f:(fun v ->
                 let _, _, def, _, property = Map.Poly.find_exn fenv v in
                 called
                   (Set.union
                      (LogicOld.Term.funsyms_of def)
                      (LogicOld.Formula.funsyms_of property)))
        in
        close seen (Set.diff next seen)
    in
    let roots =
      Set.union
        (Set.Poly.filter_map (Map.key_set fenv) ~f:(fun v ->
             if
               Ident.is_size_fun_var v
               || Set.mem (Atomic.get reconstructed_functions) v
             then Some v
             else None))
        (Set.Poly.union_list @@ List.map ~f:(fun phi ->
             called (LogicOld.Formula.funsyms_of phi))
        @@ Set.to_list @@ old_formulas_of pcsp)
    in
    let used = close Set.Poly.empty roots in
    if Set.length used = Map.Poly.length fenv then pcsp
    else
      update_params pcsp
        { params with fenv = Map.Poly.filter_keys fenv ~f:(Set.mem used) }

(* The synthesizer has no template for an unknown of this kind at this sort --
   an SMT-LIB [declare-const] of a bit-vector or integer sort read as a
   constrained Horn problem is one, the unknown being an ordinary predicate that
   does not return [bool].  It carries its own name because it is an UNSUPPORTED
   INPUT rather than an internal error: the caller reports [unknown], which is an
   ordinary answer, where a [failwith] reaches the user as a backtrace and a
   corpus sweep as a crash. *)
exception NoTemplate of string

(* Refuse a problem whose predicate kinds this backend cannot carry, as an
   UNSUPPORTED INPUT and not as an internal error.  Six backends reduce a
   predicate constraint problem to something that has no place for a kind --
   fixpoint logic, ordinary Horn relations -- so the obligation a kind states
   would be silently dropped and the answer would be about a different problem.

   It raises rather than returning, and it raises the exception the caller turns
   into an ordinary [unknown]: a [failwith] here reached the user as a backtrace
   with nothing on the verdict stream, and every harness in this tree reads a
   non-zero exit with no verdict as the tool CRASHING rather than declining --
   which is the one outcome a dispatch check exists to catch, earned by a
   backend behaving correctly.  The message is built here rather than at each
   site because six copies of it differing only in a name is how a refusal comes
   to be worded six ways. *)
let refuse_non_ord_kinds ~backend pcsp =
  let unsupported = non_ord_kinds_of pcsp in
  if not (List.is_empty unsupported) then
    raise
      (NoTemplate
         (sprintf
            "%s reduces a predicate constraint problem to fixpoint logic, \
             which carries no predicate kinds, but this problem has %d \
             predicate(s) of another kind: %s.  Use PCSat."
            backend
            (List.length unsupported)
            (String.concat_map_list ~sep:", " unsupported ~f:(fun (v, k) ->
                 sprintf "%s (%s)" (Ident.name_of_tvar v) (Kind.str_of k)))))

let is_raw = function Raw _ -> true | Cnf _ -> false
let is_cnf = function Raw _ -> false | Cnf _ -> true

(* [_exn] because this one refuses a problem that has already been clausified,
   and the refusal is an exception rather than a verdict.  It used to be called
   [map_if_raw], whose "if raw" promises the opposite -- a reader surprised by
   it once added a second function rather than correcting the first, and the
   pass that goes through it raised on a clausal problem while a catch-all
   above silently returned the problem unreduced.  A caller that would rather
   pass such a problem through untouched wants [map_if_raw]. *)
let map_raw_exn ~f = function
  | Raw (phis, params) -> Raw (f phis, params)
  | _cnf -> failwith "cnf not supported"

(* maps a raw problem and returns a clausified one unchanged, which is what
   "if raw" says *)
let map_if_raw ~f = function
  | Raw (phis, params) -> Raw (f phis, params)
  | cnf -> cnf

(* the same refusal as [map_raw_exn], which it is built on, with the two term
   representations converted on the way in and out *)
let map_raw_old_exn ~f pcsp =
  let exi_senv = (params_of pcsp).senv in
  let f =
    (fun phis ->
      Common.PhaseTime.with_phase "to-old" @@ fun () ->
      ExtTerm.with_shared_term_conversion @@ fun () ->
      Set.Poly.map phis ~f:(fun (uni_senv, phi) ->
          ( Map.of_set_exn @@ Map.to_set @@ to_old_sort_env_map uni_senv,
            ExtTerm.to_old_fml exi_senv uni_senv phi )))
    >> f
    >> fun phis ->
    Common.PhaseTime.with_phase "of-old" @@ fun () ->
    ExtTerm.with_shared_term_conversion @@ fun () ->
    Set.Poly.map phis ~f:ExtTerm.of_old
  in
  map_raw_exn ~f pcsp

(* Merging the clauses of a specification copies whatever premise they share, and
   each copy arrives with its own bound variable names, so a disjunct that is
   the *same* premise is not recognised as one: on a two-device contract whose
   three obligations each assume the same two-conjunct interference model, the
   merged clause carries thirty-two existential disjuncts of which six are
   distinct once the bound names are ignored, and the eight-fold copies are
   carried through every SMT query of every CEGIS round.  Deduplicating them is
   free of meaning -- a disjunction does not care how often a disjunct appears --
   and it has to happen before any pass that expands a quantifier, or the copies
   are expanded too.  The key renames each disjunct's binders by position, so
   alpha-equivalent disjuncts share it. *)
(* A clause's body may carry a premise the specification states with a
   quantifier -- [forall c. p(c) \/ p(c + 1)], say -- and the obligation it
   supports is at the clause's own terms.  In negation normal form that premise
   is an existential disjunct of the clause, so an instance of its body is a
   *consequence* of it and adding the instance as one more disjunct leaves the
   clause equivalent.  It is worth adding because everything downstream reads
   quantifier-free formulas better than quantified ones: the SMT queries no
   longer have to instantiate the premise themselves (the shape
   [forall c. a[c] \/ a[c + 1]] is an array property with an offset, outside the
   fragment a decision procedure covers), and the qualifier extractor, which
   keeps an atom only when the unknown's arguments cover its variables, sees the
   premise at those arguments.  Instantiated at the argument terms of the
   unknowns the clause applies, capped, and only for a body that mentions no
   unknown itself -- duplicating an unknown application would grow the problem
   rather than explain it. *)
let instantiate_quantified_premises ?(max_instances = 4) pcsp =
  (* the conversion to the first-order representation and back costs a walk over
     every clause, so do not pay it for a problem that states no premise with a
     quantifier -- which is every ordinary CHC *)
  let has_a_quantifier =
    let rec aux = function
      | Logic.Bin ((Logic.Forall | Logic.Exists), _, _, _, _) -> true
      | Logic.Bin (_, _, _, t, _) -> aux t
      | Logic.App (t1, t2, _) -> aux t1 || aux t2
      | Logic.Let (_, _, t1, t2, _) -> aux t1 || aux t2
      | _ -> false
    in
    match pcsp with
    | Raw (phis, _) -> Set.exists phis ~f:(snd >> aux)
    | Cnf _ -> false
  in
  if not has_a_quantifier then pcsp
  else
    let exi_senv = (params_of pcsp).senv in
    let is_unknown pvar = Map.Poly.mem exi_senv (Ident.pvar_to_tvar pvar) in
    map_raw_old_exn pcsp
      ~f:
        (Set.Poly.map ~f:(fun (uni_senv, phi) ->
             let cand =
               (* the terms the clause hands to its unknowns *)
               Set.Poly.filter_map
                 (fst @@ LogicOld.Formula.atoms_of phi)
                 ~f:(function
                   | LogicOld.Atom.App
                       (LogicOld.Predicate.Var (pvar, _), args, _)
                     when is_unknown pvar ->
                       Some args
                   | _ -> None)
               |> Set.concat_map ~f:Set.Poly.of_list
             in
             let rec aux phi =
               match phi with
               | LogicOld.Formula.BinaryOp (op, phi1, phi2, info) ->
                   LogicOld.Formula.mk_binop ~info op (aux phi1) (aux phi2)
               | LogicOld.Formula.UnaryOp (op, phi1, info) ->
                   LogicOld.Formula.mk_unop ~info op (aux phi1)
               | LogicOld.Formula.Bind (LogicOld.Formula.Exists, bounds, body, _)
                 when (not @@ Set.is_empty @@ Set.Poly.of_list bounds)
                      && List.length bounds <= 2
                      && Set.is_empty (LogicOld.Formula.pvs_of body)
                      && (Fn.non LogicOld.Formula.is_bind) body ->
                   let subs =
                     List.fold bounds ~init:[ Map.Poly.empty ]
                       ~f:(fun subs (v, sort) ->
                         List.concat_map subs ~f:(fun sub ->
                             Set.to_list cand
                             |> List.filter_map ~f:(fun t ->
                                 if
                                   Stdlib.(LogicOld.Term.sort_of t = sort)
                                   && (not @@ Set.mem (LogicOld.Term.tvs_of t) v)
                                 then Some (Map.Poly.set sub ~key:v ~data:t)
                                 else None)))
                     |> List.filter ~f:(Fn.non Map.Poly.is_empty)
                   in
                   let subs =
                     List.take
                       (List.dedup_and_sort ~compare:Stdlib.compare subs)
                       max_instances
                   in
                   if List.is_empty subs then phi
                   else
                     LogicOld.Formula.or_of
                       (phi
                       :: List.map subs ~f:(fun sub ->
                           LogicOld.Formula.subst sub body))
               | phi -> phi
             in
             (uni_senv, aux phi)))

let map ~f = function
  | Raw (phis, params) -> Raw (Set.Poly.map ~f phis, params)
  | Cnf (cls, params) -> Cnf (ClauseSet.map_formula ~f cls, params)

let map_old ~f pcsp =
  let exi_senv = (params_of pcsp).senv in
  let f =
    (fun (uni_senv, phi) ->
      ( Map.of_set_exn @@ Map.to_set @@ to_old_sort_env_map uni_senv,
        ExtTerm.to_old_fml exi_senv uni_senv phi ))
    >> f >> ExtTerm.of_old
  in
  (* one datatype-conversion scope for the round trip of every formula, so each
     datatype is converted once in each direction rather than once per
     occurrence; with [share_term_conversion_terms], one term-conversion scope
     too, so formulas that share subterms convert to formulas that share their
     images (same values, same fresh names) *)
  ExtTerm.with_shared_datatype_conversion @@ fun () ->
  if Atomic.get ExtTerm.share_term_conversion_terms then
    ExtTerm.with_shared_term_conversion @@ fun () -> map ~f pcsp
  else map ~f pcsp

(* [map_old_where ~touch ~f] is [map_old ~f] on the formulas [touch] holds of
   and the identity on the others, whose round trip through the other term
   representation is not made.  It equals [map_old ~f] exactly when, for every
   formula [touch] rejects, [map_old]'s round trip with [f] would have returned
   it unchanged: [touch] is the caller's claim that [f] cannot change that
   formula. *)
let map_old_where ~touch ~f pcsp =
  let exi_senv = (params_of pcsp).senv in
  let g =
    (fun (uni_senv, phi) ->
      ( Map.of_set_exn @@ Map.to_set @@ to_old_sort_env_map uni_senv,
        ExtTerm.to_old_fml exi_senv uni_senv phi ))
    >> f >> ExtTerm.of_old
  in
  ExtTerm.with_shared_datatype_conversion @@ fun () ->
  map pcsp ~f:(fun c -> if touch c then g c else c)

(* [alpha_canonical_key phi] is a string such that two formulas get the same
   key only if they are alpha-equivalent (assuming, as the dedup below does,
   that two formulas printed alike are equal), and alpha-variants get the same
   key when their bound names are the only difference among quantifier, [let]
   and [define-fun-rec] argument binders.  It prints [phi] with those binders
   renamed by a counter in traversal order.  The renaming is alpha-preserving
   only when no counter name already occurs in [phi]; a formula whose printed
   form mentions the counter's prefix anywhere (a free variable, an array
   lambda's binder, which is not renamed, or a string) gets its own printed
   form under a different tag instead, which equals another key only for a
   formula printed identically. *)
let alpha_canonical_key phi =
  let prefix = "#dk" in
  let raw = LogicOld.Formula.str_of phi in
  if String.is_substring raw ~substring:prefix then "raw " ^ raw
  else
    let cnt = ref 0 in
    "norm "
    ^ LogicOld.Formula.str_of
        (LogicOld.Formula.aconv_tvar_norm
           (fun () ->
             Int.incr cnt;
             Ident.Tvar (sprintf "%s%d" prefix !cnt))
           phi)

let dedup_alpha_equivalent_disjuncts ?(print = fun _ -> ()) pcsp =
  (* the walk costs a round trip through the other term representation, so do
     not pay it for a problem that states no premise with a quantifier, which is
     every ordinary CHC *)
  let has_a_quantifier =
    let rec aux = function
      | Logic.Bin ((Logic.Forall | Logic.Exists), _, _, _, _) -> true
      | Logic.Bin (_, _, _, t, _) -> aux t
      | Logic.App (t1, t2, _) -> aux t1 || aux t2
      | Logic.Let (_, _, t1, t2, _) -> aux t1 || aux t2
      | _ -> false
    in
    match pcsp with
    | Raw (phis, _) -> Set.exists phis ~f:(snd >> aux)
    | Cnf (cls, _) -> Set.exists cls ~f:(fun (_, _, _, phi) -> aux phi)
  in
  if not has_a_quantifier then pcsp
  else
    let canonical_key = alpha_canonical_key in
    map_old pcsp ~f:(fun (uni_senv, phi) ->
        let disjuncts = Set.to_list @@ LogicOld.Formula.disjuncts_of phi in
        if List.length disjuncts <= 1 then (uni_senv, phi)
        else
          let kept =
            List.rev @@ snd
            @@ List.fold disjuncts ~init:(Set.Poly.empty, [])
                 ~f:(fun (seen, acc) d ->
                   let key = canonical_key d in
                   if Set.mem seen key then (seen, acc)
                   else (Set.add seen key, d :: acc))
          in
          if List.length kept = List.length disjuncts then (uni_senv, phi)
          else (
            print
            @@ lazy
                 (sprintf
                    "dropped %d of %d disjuncts that differ only in binder \
                     names"
                    (List.length disjuncts - List.length kept)
                    (List.length disjuncts));
            (uni_senv, LogicOld.Formula.or_of kept)))

let concat_map ~f = function
  | Raw (phis, params) -> Raw (Set.concat_map ~f phis, params)
  | Cnf (cls, params) -> Cnf (ClauseSet.concat_map_formula ~f cls, params)

let concat_map_old ~f pcsp =
  let exi_senv = (params_of pcsp).senv in
  let f =
    (fun (uni_senv, phi) ->
      ( Map.of_set_exn @@ Map.to_set @@ to_old_sort_env_map uni_senv,
        ExtTerm.to_old_fml exi_senv uni_senv phi ))
    >> f
    >> Set.Poly.map ~f:ExtTerm.of_old
  in
  ExtTerm.with_shared_datatype_conversion @@ fun () -> concat_map ~f pcsp

type pcsp = { clauses : string list; unknowns : (string * string) list }
[@@deriving to_yojson]

let to_yojson pcsp =
  let exi_senv = (params_of pcsp).senv in
  {
    clauses =
      pcsp |> formulas_of
      |> Set.Poly.map ~f:(Tuple2.uncurry (ExtTerm.str_of_formula exi_senv))
      |> Set.to_list;
    unknowns =
      senv_of pcsp |> Map.Poly.to_alist
      |> List.map ~f:(fun (Ident.Tvar name, sort) ->
          (name, ExtTerm.str_of_sort sort));
  }
  |> pcsp_to_yojson

let str_of pcsp =
  sprintf
    "%s\n\n\
     sort env: %s\n\n\
     original arg names: %s\n\n\
     datatype env:\n\
     %s\n\n\
     fun env:\n\
     %s\n\n\
     sol_space: %s"
    (String.concat_map_set ~sep:"\n" (formulas_of pcsp)
       ~f:(fun (uni_senv, phi) ->
         String.bracket (string_of_int (Map.Poly.length uni_senv))
         ^ " "
         ^ ExtTerm.str_of_formula (params_of pcsp).senv uni_senv phi))
    (str_of_sort_env_list (fun (s, k) ->
         ExtTerm.str_of_sort s ^ " @ " ^ Kind.short_str_of k)
    @@ Map.Poly.to_alist
    @@ Map.Poly.mapi ~f:(fun ~key ~data ->
        (data, try kind_of pcsp key with exn_ when not (Common.Timer.is_async exn_) -> Kind.Ord (*ToDo*)))
    @@ senv_of pcsp)
    (Params.str_of_arg_original_names ~pvar_sep:"\n" ~tvar_sep:" "
       ~pvar_tvar_delim:": "
    @@ arg_original_names_of pcsp)
    (LogicOld.DTEnv.str_of @@ dtenv_of pcsp)
    (LogicOld.FunEnv.str_of @@ fenv_of pcsp)
    (SolSpace.str_of @@ sol_space_of pcsp)
(*let str_of_senv pcsp = "sort env: " ^ str_of_sort_env_map ExtTerm.str_of_sort @@ senv_of pcsp*)

let str_of_info pcsp =
  sprintf "number of unknowns: %d, number of constraints: %d"
    (num_unknowns pcsp) (num_constrs pcsp)

let str_of_solution ?(print_witness = false) = function
  | Sat subst ->
      "sat"
      ^
      if print_witness then
        " where\n" ^ Logic.str_of_term_subst ExtTerm.str_of subst
      else ""
  | Unsat r ->
      "unsat"
      ^
      if print_witness then
        match r with
        | None -> ""
        | Some (Formula phi) -> " where\n" ^ LogicOld.Formula.str_of phi
        | Some (Proof r) -> " where\n" ^ Refutation.str_of r
        | Some (External s) -> " where\n(external \"" ^ s ^ "\")"
      else ""
  | Unknown -> "unknown"
  | OutSpace pvs ->
      sprintf "out_space: %s"
      @@ String.concat_map_list ~sep:"," pvs ~f:Ident.name_of_tvar
  | Timeout -> "timeout"

let str_of_sol_with_witness = str_of_solution ~print_witness:true
let str_of_solution = str_of_solution ~print_witness:false

let str_of_sygus_solution = function
  | Sat sol -> SyGuS.Printer.str_of_solution @@ CandSolOld.of_subst sol
  | Unsat _ -> SyGuS.Printer.str_of_unsat ()
  | Unknown -> SyGuS.Printer.str_of_unknown ()
  | OutSpace pvs ->
      sprintf "out_space: %s"
      @@ String.concat_map_list ~sep:"," pvs ~f:Ident.name_of_tvar
  | Timeout -> "timeout" (*ToDo*)

(* expand existential quantification over boolean variables *)
let rec qelim xs body =
  let open Ast.LogicOld in
  match xs with
  | [] -> body
  | (x, sort) :: xs' ->
      assert (Term.is_bool_sort sort);
      let body = qelim xs' body in
      Formula.or_of
        [
          Formula.apply_pred (x, body) @@ T_bool.mk_true ();
          Formula.apply_pred (x, body) @@ T_bool.mk_false ();
        ]

let add_non_emptiness (pvar, sorts) =
  let open Ast.LogicOld in
  function
  | Raw (phis, p_params) ->
      let params = sort_env_list_of_sorts sorts in
      let bool_params, arith_params =
        List.partition_tf params ~f:(snd >> Term.is_bool_sort)
      in
      let pvs =
        List.map arith_params ~f:(fun (tvar, sort) ->
            let pvar =
              Ident.Pvar ("FN" ^ Ident.divide_flag ^ Ident.name_of_tvar tvar)
            in
            ( ExtTerm.of_old_sort_bind @@ Term.pred_to_sort_bind (pvar, [ sort ]),
              Formula.mk_atom @@ Atom.pvar_app_of_senv pvar [ (tvar, sort) ] ))
      in
      let phis =
        Set.add phis
          ( Map.Poly.of_alist_exn @@ of_old_sort_env_list params,
            BoolTerm.elim_imp @@ ExtTerm.of_old_formula @@ Evaluator.simplify
            @@ Formula.mk_imply (Formula.and_of @@ List.map pvs ~f:snd)
            @@ qelim bool_params @@ Formula.mk_atom
            @@ Atom.mk_pvar_app pvar sorts (Term.of_sort_env params) )
      in
      let p_params =
        let fnpv_senv = Map.Poly.of_alist_exn @@ List.map pvs ~f:fst in
        {
          p_params with
          senv = Map.force_merge p_params.senv fnpv_senv;
          kind_map =
            Kind.add_kinds (Map.key_set fnpv_senv) Kind.FN p_params.kind_map;
        }
      in
      Raw (phis, p_params)
  | Cnf (_, _) -> failwith "add_non_emptiness"

let add_formula (senv, phi) = function
  | Raw (phis, params) ->
      Raw (Set.add phis (senv, BoolTerm.elim_imp phi), params)
  | Cnf (_, _) -> failwith "add_formula"

let add_formulas senv_phis = function
  | Raw (phis, params) ->
      Raw
        ( Set.union phis
            (Set.Poly.map senv_phis ~f:(fun (senv, phi) ->
                 (senv, BoolTerm.elim_imp phi))),
          params )
  | Cnf (_, _) -> failwith "add_formula"

let add_clause clause = function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF @ add_clause"
  | Cnf (cnf, params) -> Cnf (Set.add cnf (Clause.canon clause), params)

let add_clauses clauses = function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF @ add_clauses"
  | Cnf (cnf, params) -> Cnf (Set.union cnf (ClauseSet.canon clauses), params)

(* under [ExtTerm.share_term_conversion], one scope of [with_shared_nnf_cnf]
   for the whole problem: a subformula many formulas share is put in normal
   form, and tested for unknowns, once (the same results) *)
let with_shared_normal_forms f =
  if Atomic.get ExtTerm.share_term_conversion then
    ExtTerm.with_shared_nnf_cnf f
  else f ()

let to_nnf = function
  | Raw (phis, params) ->
      with_shared_normal_forms @@ fun () ->
      Raw
        ( Set.Poly.map phis ~f:(fun (senv, phi) -> (senv, BoolTerm.nnf_of phi)),
          params )
  | cnf -> cnf

let to_cnf = function
  | Raw (phis, params) ->
      with_shared_normal_forms @@ fun () ->
      Cnf (ClauseSet.of_formulas params.senv phis, params)
  | cnf -> cnf

(* Encode every disjunctive head by a choice witness, so that the problem is
   Horn in its heads and the choice is a functional unknown the solver must
   synthesise rather than a disjunction it reasons about.  A clause
   [body -> G_0 \/ ... \/ G_{k-1} \/ phi] with k >= 2 unknown atoms in its head
   becomes, for a fresh [W] of kind [FN] over the clause's variables and an
   integer selector [z] (the result, last),

     body /\ W(x, z) -> G_i \/ phi \/ z <> i                 for i < k-1
     body /\ W(x, z) -> G_{k-1} \/ phi \/ z = 0 \/ ... \/ z = k-2

   Equisatisfiable (argued): a solution of the original chooses, per value of
   the clause variables, a true disjunct, and its index is a total
   single-valued [W]; conversely a total [W] gives a [z] at which one of the
   new clauses forces its [G_i] or [phi].  This is the existential-witness
   encoding of a disjunctive head (Bjorner, Gurfinkel, McMillan and
   Rybalchenko's survey, Proposition 5) with the witness already skolemised.
   It exists to measure what the encoding costs against keeping the
   disjunction; it is not an optimisation. *)
let encode_head_disjunctions pcsp =
  let pcsp = to_cnf pcsp in
  let params = params_of pcsp in
  let new_senv = ref Map.Poly.empty in
  let clauses =
    Set.concat_map (clauses_of pcsp) ~f:(fun ((uni_senv, ps, ns, phi) as cl) ->
        if Set.length ps < 2 then Set.Poly.singleton cl
        else
          let xs = Map.Poly.to_alist uni_senv in
          (* A prefixed fresh name is the prefix plus a global counter, so it
             can coincide with a name the input already uses: a selector drawn
             as [z1] in a clause over the program's own [z1] replaced that
             variable in [uni_senv], and the encoded clause became vacuous
             wherever the choice differed from it -- a weaker problem, whose
             [sat] was not a solution of the original.  Draw again until the
             name is new to the clause and to the problem's unknowns. *)
          let w =
            Ident.mk_fresh_tvar_avoiding ~prefix:"FN_choice"
              ~taken:(fun v ->
                Map.Poly.mem params.Params.senv v || Map.Poly.mem !new_senv v)
              ()
          in
          let z =
            Ident.mk_fresh_tvar_avoiding ~prefix:"z"
              ~taken:(Map.Poly.mem uni_senv) ()
          in
          new_senv :=
            Map.Poly.set !new_senv ~key:w
              ~data:
                (Logic.Sort.mk_fun
                   (List.map xs ~f:snd @ [ Logic.IntTerm.SInt; Logic.BoolTerm.SBool ]));
          let uni_senv' = Map.Poly.set uni_senv ~key:z ~data:Logic.IntTerm.SInt in
          let w_atom =
            Logic.Term.mk_var_app w
              (List.map xs ~f:(fst >> Logic.Term.mk_var) @ [ Logic.Term.mk_var z ])
          in
          let zt = Logic.Term.mk_var z in
          let eq i = Logic.BoolTerm.eq_of Logic.IntTerm.SInt zt (Logic.IntTerm.mk_int (Z.of_int i)) in
          let heads = Set.to_list ps in
          let k = List.length heads in
          Set.Poly.of_list
          @@ List.mapi heads ~f:(fun i g ->
              let side =
                if i < k - 1 then Logic.BoolTerm.neg_of (eq i)
                else Logic.BoolTerm.or_of (List.init (k - 1) ~f:eq)
              in
              ( uni_senv',
                Set.Poly.singleton g,
                Set.add ns w_atom,
                Logic.BoolTerm.or_of [ phi; side ] )))
  in
  let params =
    {
      params with
      Params.senv = Map.force_merge params.Params.senv !new_senv;
      kind_map =
        Kind.add_kinds (Map.Poly.key_set !new_senv) Kind.FN params.Params.kind_map;
    }
  in
  (* Returned as formulas, not as clauses: predicate elimination resolves
     unknowns away only on a problem that is not yet in clause form, so a
     clause-form result would also switch elimination off, and the encoded
     arm would differ from the kept one in more than the disjunction. *)
  of_formulas ~params (ClauseSet.to_formulas clauses)

let divide pcsp =
  pcsp |> to_nnf |> to_cnf |> function
  | Raw (_, _) -> failwith "The pfwCSP is not of CNF @ divide"
  | Cnf (cnf, params) ->
      let cnf1, cnf2 =
        Set.partition_tf cnf
          ~f:(Clause.is_query (wfpvs_of pcsp) (fnpvs_of pcsp))
      in
      Set.to_list
      @@ Set.Poly.map cnf1 ~f:(fun c -> Cnf (Set.add cnf2 c, params))

let merge_sols _pcsp sols =
  let merge _s s' =
    s'
    (* ToDo *)
  in
  let rec inner sol = function
    | [] -> Sat sol
    | Sat sol' :: sols -> inner (merge sol sol') sols
    | Unsat cex :: _sols -> Unsat cex
    | Unknown :: _sols -> Unknown
    | OutSpace pvs :: _sols -> OutSpace pvs
    | Timeout :: _sols -> Timeout
  in
  inner Map.Poly.empty sols

(* The solutions recorded for predicates eliminated during preprocessing may
   mention predicates eliminated later or solved by the solver (a predicate
   removed by resolution is defined by the bodies of its clauses); closing the
   map under substitution makes every entry pure.

   Contract: every entry of the result is its entry of [subst] with each key it
   mentions replaced by that key's closed entry (beta-reduced, binders renamed
   apart), so an entry whose dependencies do not reach a cycle mentions no key;
   an entry that reaches a cycle of definitions still mentions a key, which is
   what [prune_impure] then drops.  The result is the fixpoint of substituting
   the whole map into every entry, up to the names of bound variables.

   Each entry is closed once, depth first, and a closed entry is remembered and
   substituted as it is into every entry that mentions it.  Substituting the
   whole map into every entry until nothing changed took one round per link of
   the longest chain of definitions, and each round rebuilt every entry --
   renaming all its binders -- and compared the old map with the new one
   structurally: with two hundred predicates eliminated by resolution in one
   chain that was the whole of a 300 s budget after the elimination itself had
   finished.  A key met again while its own closure is under way is on a cycle
   and is left as it is, so the closure terminates without the chain bound the
   rounds needed.  Every entry goes through one substitution even when it
   mentions no key, as it did in the first round, so a redex already in a
   definition is reduced as before. *)
let close_subst subst =
  let keys = Map.key_set subst in
  let closed = Hashtbl.Poly.create () in
  let in_progress = Hash_set.Poly.create () in
  let rec close key term =
    match Hashtbl.find closed key with
    | Some t -> t
    | None ->
        Hash_set.add in_progress key;
        let env =
          Set.fold (ExtTerm.fvs_of term) ~init:Map.Poly.empty ~f:(fun env x ->
              if Set.mem keys x && not (Hash_set.mem in_progress x) then
                Map.Poly.set env ~key:x
                  ~data:(close x (Map.Poly.find_exn subst x))
              else env)
        in
        (* [subst] with the empty map first reduces any redex the
           definition already holds, as the first round of the earlier
           procedure did; the closed entries are then substituted in one
           traversal that renames a binder only where it could capture, since
           [subst] renamed every binder of a substituted body once per
           enclosing binder and application, which on definitions inlined
           two hundred deep was most of the time left *)
        let t =
          let t = ExtTerm.subst Map.Poly.empty term in
          if Map.Poly.is_empty env then t
          else ExtTerm.subst_rename_on_capture env t
        in
        Hash_set.remove in_progress key;
        Hashtbl.set closed ~key ~data:t;
        t
  in
  Map.Poly.mapi subst ~f:(fun ~key ~data -> close key data)

(* drop the recorded definitions that still mention a predicate after
   closure (its solution was never produced, e.g. it belongs to another
   solver in an exchange); consumers expect pure formulas *)
let prune_impure subst =
  Map.Poly.filter subst ~f:(fun term ->
      let params, body = ExtTerm.let_lam term in
      Set.is_subset (ExtTerm.fvs_of body)
        ~of_:(Set.Poly.of_list @@ List.map ~f:fst params))

let extend_sol sol sol' =
  match sol with
  | Sat sol ->
      Sat
        (prune_impure @@ close_subst
        @@ Map.Poly.merge sol sol' ~f:(fun ~key:_ -> function
          | `Left v | `Right v -> Some v
          | `Both (v, _) -> Some v))
  | Unsat _ | Unknown | OutSpace _ | Timeout -> sol

let svs_of = function
  | Raw (phis, _params) ->
      Set.concat_map phis
        ~f:(snd >> Term.svs_of ExtTerm.svs_of_sym ExtTerm.svs_of_sort)
  | Cnf (cnf, _params) -> ClauseSet.svs_of cnf

let instantiate_svars_to_int pcsp =
  let sub =
    Map.of_set_exn
    @@ Set.Poly.map (svs_of pcsp) ~f:(fun svar -> (svar, LogicOld.T_int.SInt))
  in
  map_old pcsp ~f:(fun (uni_senv, phi) ->
      (uni_senv, LogicOld.Formula.subst_sorts sub phi))

let elim_ite =
  map_old ~f:(fun (uni_senv, phi) ->
      (uni_senv, phi |> LogicOld.Formula.elim_ite |> Evaluator.simplify))

(* [phi] is read as a clause here: a disjunction of literals whose atoms may
   contain [ite], which is what the code below eliminates by distributing the
   branch conditions.  A problem formula need not be one -- the pGCL/SGCL and
   QFL reductions produce top-level conjunctions, and one of them is already in
   CNF -- and the result of this pass is conjoined by [concat_map_old], so a
   conjunction may be split and each part handled on its own.  Without the
   split, [Formula.to_atom] below raised [Failure "... is not atomic formula"]
   and the run died with a backtrace instead of an answer.  A part that is
   still not clausal after the split, and carries no quantifier, is put through
   [to_cnf] -- here only, where the alternative was that crash, so nothing that
   worked before takes a different route. *)
let clausal_parts phi =
  let is_literal psi =
    LogicOld.Formula.is_atom psi
    || LogicOld.Formula.is_neg psi
       && (LogicOld.Formula.is_atom @@ fst @@ LogicOld.Formula.let_neg psi)
  in
  let is_clause =
    LogicOld.Formula.disjuncts_list_of >> List.for_all ~f:is_literal
  in
  List.concat_map (LogicOld.Formula.conjuncts_list_of phi) ~f:(fun psi ->
      if is_clause psi then [ psi ]
      else if LogicOld.Formula.is_quantifier_free psi then
        Set.to_list @@ LogicOld.Formula.to_cnf ~process_pure:true psi
      else
        failwith
        @@ sprintf
             "[elim_ite_quant] a quantified formula that is not a clause: %s"
             (LogicOld.Formula.str_of psi))

(* one clause: the alternatives of each literal are cartesian-producted, which
   turns the clause into a conjunction of [ite]-free clauses *)
let elim_ite_quant_clause uni_senv phi =
  let phiss =
    List.map (LogicOld.Formula.disjuncts_list_of phi) ~f:(function
      | LogicOld.Formula.UnaryOp (Not, atm, _) ->
          atm |> LogicOld.Formula.to_atom
          |> LogicOld.Atom.elim_ite_quant false
               (Normalizer.normalize >> Evaluator.simplify)
          |> Set.Poly.map ~f:LogicOld.Formula.mk_neg
          |> Set.to_list
      | atm ->
          atm |> LogicOld.Formula.to_atom
          |> LogicOld.Atom.elim_ite_quant true
               (Normalizer.normalize >> Evaluator.simplify)
          |> Set.to_list)
  in
  Set.Poly.of_list
  @@ List.map (List.n_cartesian_product phiss) ~f:(fun phis ->
      let left, right = List.partition_tf phis ~f:LogicOld.Formula.is_neg in
      let right = LogicOld.Formula.or_of right in
      ( uni_senv,
        if List.is_empty left then right
        else
          let fml =
            let phis, right =
              if LogicOld.Formula.is_imply right then
                let left, right, _ = LogicOld.Formula.let_imply right in
                (LogicOld.Formula.conjuncts_list_of left, right)
              else ([], right)
            in
            let left =
              LogicOld.Formula.and_of @@ phis
              @ List.map left ~f:(LogicOld.Formula.let_neg >> fst)
            in
            LogicOld.Formula.mk_imply left right
          in
          if false then
            print_endline
            @@ sprintf "[elim_ite_quant] \n  before: %s\n  after: %s\n"
                 (LogicOld.Formula.str_of phi)
                 (LogicOld.Formula.str_of fml);
          fml ))

(* the parts are conjoined, so their results are unioned -- flattening their
   literals into one list would turn the conjunction into a disjunction *)
let elim_ite_quant =
  concat_map_old ~f:(fun (uni_senv, phi) ->
      Set.Poly.union_list
      @@ List.map (clausal_parts phi) ~f:(elim_ite_quant_clause uni_senv))

let normalize pcsp =
  let unknowns = Map.key_set @@ senv_of pcsp in
  (* with the normaliser's and the simplifier's memos switched on, one scope
     of each for the whole problem, so a subformula the formulas share is
     normalised and simplified once and stays shared; the results are the
     ones without them (see [Normalizer.with_shared_normalize]) *)
  Normalizer.with_shared_normalize @@ fun () ->
  Evaluator.with_shared_simplify @@ fun () ->
  LogicOld.with_shared_let_passes @@ fun () ->
  (* with COAR_SHARE_CENSUS set, every step's outputs over all the formulas
     are kept and counted afterwards (a diagnostic: the values are the same,
     only held longer) *)
  let census = Array.init 7 ~f:(fun _ -> ref []) in
  let keep i phi =
    if Common.DagCensus.enabled then census.(i) := phi :: !(census.(i));
    phi
  in
  let pcsp' =
  map_old pcsp ~f:(fun (uni_senv, phi) ->
      let phi' =
        phi |> keep 0
        (*|> LogicOld.Formula.elim_pvars unknowns*)
        |> Normalizer.normalize_let ~rename:true |> keep 1
        (* |> LogicOld.Formula.elim_let_equivalid *)
        |> LogicOld.Formula.elim_let_with_unknowns unknowns |> keep 2
        (* |> LogicOld.Formula.elim_let *)
        |> Normalizer.normalize |> keep 3
        |> Evaluator.simplify |> keep 4 |> Normalizer.normalize |> keep 5
        |> Evaluator.simplify |> keep 6
      in
      if false then
        print_endline
        @@ sprintf "[normalize] \n  before: %s\n  after: %s\n"
             (LogicOld.Formula.str_of phi)
             (LogicOld.Formula.str_of phi');
      (uni_senv, phi'))
  in
  if Common.DagCensus.enabled then
    List.iteri
      [
        "to-old"; "normalize-let"; "elim-let-with-unknowns"; "normalize";
        "simplify"; "normalize 2"; "simplify 2";
      ]
      ~f:(fun i lbl ->
        Common.DagCensus.report ("normalize: after " ^ lbl) !(census.(i)));
  pcsp'

let of_sygus (synth_funs, declared_vars, terms) =
  (* A [synth-fun] may carry a grammar restricting the terms its solution may be
     built from, and this conversion keeps only the sort: the grammar was parsed
     and then dropped, so the problem handed to the solver is the UNRESTRICTED
     one.  That is a weaker question, and its answer comes back as if it were the
     answer to the stated one -- a grammar admitting exactly the term [0] for a
     function that must satisfy [f 0 = 1] returned sat, where cvc5 reports the
     synthesis as failed.  Honouring the restriction is a feature of the
     synthesizer rather than of this conversion, so until it exists the problem
     is refused by name.  No file in this repository's SyGuS corpus carries a
     grammar -- 0 of 2,661 -- so nothing that used to be answered stops being
     answered. *)
  (match
     Map.Poly.to_alist
     @@ Map.Poly.filter_map synth_funs ~f:(fun (_, cfg) ->
            Option.map cfg ~f:(fun _ -> ()))
   with
  | [] -> ()
  | restricted ->
      failwith
      @@ sprintf
           "synthesis restricted by a grammar is not implemented, and %d \
            function(s) declare one: %s.  The grammar would be ignored and the \
            answer would be about the unrestricted problem."
           (List.length restricted)
           (String.concat_map_list ~sep:", " restricted
              ~f:(fst >> Ident.name_of_tvar)));
  let exi_senv = Map.Poly.map synth_funs ~f:fst in
  let kind_map =
    Map.Poly.filter_map exi_senv ~f:(fun sort ->
        if ExtTerm.is_int_sort @@ Sort.ret_of sort then Some Kind.IntFun
        else if ExtTerm.is_real_sort @@ Sort.ret_of sort then Some Kind.RealFun
        else if ExtTerm.is_regex_sort sort then Some Kind.RegEx
        else None)
  in
  List.map terms ~f:(fun t -> (declared_vars, t))
  |> Set.Poly.of_list
  |> of_formulas ~params:(Params.make ~kind_map exi_senv)
  |> normalize

(* No reduction of a labelled transition system to a pCSP exists; LTS
   problems reach the fixpoint backends through [MuCLP.Util.of_lts] instead, so
   no backend offered for an LTS calls this.  A call is refused as unsupported
   input rather than failing. *)
let of_lts _lts =
  Common.Refusal.refuse
    "an LTS cannot be reduced to a pCSP; use a fixpoint backend (MuVal, MuCyc \
     or MuStrat)"

(* The solution given to a predicate that no constraint mentions any more
   and that no elimination accounted for (Preprocessor.preprocess): [true] for
   an ordinary or total predicate, [false] (the empty relation, well-founded
   and a parity relation) for WF/DWF/NWF/Parity, [y = 0] for a functional
   predicate with an arithmetic output; other kinds get none.  Completes the
   printed model (the WF/FN companions of a predicate eliminated one-sided
   used to be missing from it) so that a checker can verify
   the kind. *)
let default_solution_of_unused params tvar sort =
  let args = Sort.args_of sort in
  let xs = List.map args ~f:(fun s -> (Ident.mk_fresh_tvar (), s)) in
  let lam body = Term.mk_lambda xs body in
  match Map.Poly.find params.Params.kind_map tvar with
  | Some Kind.Ord | Some (Kind.Tot _) | None -> Some (lam (BoolTerm.mk_bool true))
  | Some (Kind.WF | Kind.DWF | Kind.NWF _ | Kind.Parity _) ->
      Some (lam (BoolTerm.mk_bool false))
  (* [true] is not single-valued at arity >= 2; [false] is, and needs no
     totality *)
  | Some (Kind.Uniq _) -> Some (lam (BoolTerm.mk_bool false))
  | Some Kind.FN -> (
      match List.last xs with
      | Some (y, s) when Stdlib.(s = ExtTerm.SInt) ->
          Some
            (lam (BoolTerm.eq_of s (ExtTerm.mk_var y) (ExtTerm.mk_int Z.zero)))
      | Some (y, s) when Stdlib.(s = ExtTerm.SReal) ->
          Some
            (lam (BoolTerm.eq_of s (ExtTerm.mk_var y) (ExtTerm.mk_real Q.zero)))
      | _ -> None)
  | Some _ -> None

let share_unused_params_fvs = Atomic.make false

let remove_unused_params pcsp =
  let pcsp' =
    let bpvs = ClauseSet.pvs_of @@ stable_clauses_of pcsp in
    (* a dropped predicate gets no solution here: whether it is unconstrained
       or was resolved away (its constraints living on in the resolvents,
       without a recorded definition when a head is disjunctive) is known only
       to the preprocessor, which records the defaults after all eliminations
       (Preprocessor.preprocess) — the checker caught a wrong [true] recorded
       here for a resolved predicate *)
    let with_defaults params mem =
      {
        params with
        Params.senv = Map.Poly.filter_keys ~f:mem params.Params.senv;
      }
    in
    match pcsp with
    | Raw (phis, params) ->
        (* with [share_unused_params_fvs], the free variables are read once
           per physical node: the same membership test *)
        let fvs_of =
          if Atomic.get share_unused_params_fvs then Term.fvs_of_shared ()
          else Term.fvs_of
        in
        let mem =
          Set.mem @@ Set.union bpvs
          @@ Set.concat_map phis ~f:(snd >> fvs_of)
        in
        Raw (phis, with_defaults params mem)
    | Cnf (cnf, params) ->
        let mem = Set.mem @@ Set.union bpvs @@ ClauseSet.fvs_of cnf in
        Cnf (cnf, with_defaults params mem)
  in
  let partial_sol_targets =
    let pvs = pvs_of pcsp' in
    Map.Poly.filter_keys (partial_sol_targets_of pcsp') ~f:(fun k ->
        Set.exists pvs ~f:(fun pv ->
            is_bool_valued_ord_pred pcsp pv && Ident.is_related_tvar pv k))
  in
  update_params pcsp' { (params_of pcsp') with partial_sol_targets }

let normalize_uni_senv = function
  | Raw (phis, params) ->
      Raw
        ( Set.Poly.map phis ~f:Clause.normalize_uni_senv_formula,
          {
            params with
            stable_clauses =
              Set.Poly.map ~f:Clause.normalize_uni_senv @@ params.stable_clauses;
          } )
  | Cnf (cls, params) ->
      Cnf
        ( Set.Poly.map cls ~f:Clause.normalize_uni_senv,
          {
            params with
            stable_clauses =
              Set.Poly.map ~f:Clause.normalize_uni_senv @@ params.stable_clauses;
          } )

let ast_size_of pcsp =
  Set.fold ~init:0
    ~f:(fun acc cl -> 1 + acc + Clause.ast_size_of cl)
    (stable_clauses_of pcsp)
  +
  match pcsp with
  | Raw (phis, _) ->
      Set.fold phis ~init:0 ~f:(fun acc (_, t) -> 1 + acc + ExtTerm.ast_size t)
  | Cnf (cls, _) ->
      Set.fold cls ~init:0 ~f:(fun acc cl -> 1 + acc + Clause.ast_size_of cl)

let nwf_tag_of pcsp tvar =
  match Map.Poly.find (kind_map_of pcsp) tvar with
  | Some (Kind.NWF (nwf, tag)) -> Some (nwf, tag)
  | Some (Kind.Parity (nwf, tag)) -> Some (nwf, tag)
  | _ -> None

let recover_elimed_params_of_sol elimed_params_logs =
  Map.Poly.mapi ~f:(fun ~key ~data:term ->
      let pvar = Ident.tvar_to_pvar key in
      if not @@ Map.Poly.mem elimed_params_logs pvar then term
      else
        let arr, args = Map.Poly.find_exn elimed_params_logs pvar in
        let senv, term = Term.let_lam term in
        let senv = ref senv in
        let senv' =
          List.mapi args ~f:(fun i arg ->
              if Array.get arr i then
                match !senv with
                | hd :: tl ->
                    senv := tl;
                    hd
                | [] -> assert false
              else (Ident.mk_fresh_tvar (), arg))
        in
        Term.mk_lambda senv' term)

let sol_of_candidate pcsp (cand : CandSol.t) =
  (* the definitions recorded for predicates removed by resolution
     ([sol_for_resolved]) are deliberately not part of a candidate: they feed
     validation and the MuVal exchange, and adding them changed CEGIS runs;
     they only complete the final answer, see [extend_sol] *)
  let defs = sol_for_eliminated_of pcsp in
  let sol =
    recover_elimed_params_of_sol (args_record_of pcsp)
    @@ Map.force_merge defs (CandSol.to_subst cand)
  in
  (* Contract: an entry of the result mentions no key of the result.  A
     recorded definition may be over an unknown that is still being solved --
     a pass that drops an unknown's constant arguments, or shares its
     determined ones, defines it by a fresh unknown of smaller arity -- and
     the consumers of a candidate (the MuVal exchange, the partial-solution
     redundancy check) read every entry as a closed formula, so such a
     definition left as it is raised "... is not bound" out of the exchange.
     Only those definitions are closed, against the candidate after its
     arguments were restored; every other entry, the candidate's own above
     all, is returned unchanged, so a run whose definitions are pure sees the
     same terms as before. *)
  let keys = Map.key_set sol in
  let open_def ~key ~data =
    Map.Poly.mem defs key && Set.exists (ExtTerm.fvs_of data) ~f:(Set.mem keys)
  in
  if not (Map.Poly.existsi sol ~f:open_def) then sol
  else
    let closed = close_subst sol in
    Map.Poly.mapi sol ~f:(fun ~key ~data ->
        if open_def ~key ~data then Map.Poly.find_exn closed key else data)

(* assume the codomain of subst is pure *)
let subst ?(bpvs = Set.Poly.empty) ?(elim = true) subst pcsp =
  let phis = formulas_of pcsp in
  let params = params_of pcsp in
  let subst = Map.Poly.filter_keys subst ~f:(Fn.non @@ Set.mem bpvs) in
  let params' =
    if elim then
      let f = Map.Poly.mem subst >> not in
      {
        params with
        Params.senv = Map.Poly.filter_keys ~f params.Params.senv;
        Params.kind_map = Map.Poly.filter_keys ~f params.Params.kind_map;
      }
    else { params with Params.sol_for_eliminated = subst }
  in
  (*let c = ref 0 in*)
  let phis =
    Set.Poly.map phis ~f:(fun (univ_senv, phi) ->
        (*print_endline @@ string_of_int !c;
          c := !c + 1;*)
        (*let fvs = ExtTerm.fvs_of phi in
          let sub = Map.Poly.filter_keys subst ~f:(Set.mem fvs) in
          if Map.Poly.is_empty sub then (univ_senv, phi)
          else*)
        (univ_senv, ExtTerm.subst subst phi))
  in
  of_formulas phis ~params:params'
  |>
  if true then Fn.id
  else
    map_old
      ~f:
        (Tuple2.map_snd
           ~f:
             (Z3Smt.Z3interface.qelim
                ~id:(id_of pcsp) (*(senv_of pcsp)*)
                ~fenv:(LogicOld.get_fenv ())))

(* Replace each [Uniq (j, _)] predicate [P] by an ordinary predicate [G] over
   the other arguments and a functional one [F] over the other arguments and
   position [j] (its result, last):

     P := fun x. G(x without j) /\ F(x without j, x_j)

   Equisatisfiable (argued): a single-valued [P] gives [G] its domain and [F] a
   total extension of it, since every sort is non-empty so a value can be chosen
   outside the domain; conversely [G /\ F] is single-valued at [j] because [F]
   is.  The point is to reuse what [FN] already has -- a template whose
   candidates are functions, and the labeling's conflict from two witnesses --
   rather than to build a partial-function template.  [F]'s totality restricts
   nothing, being satisfiable by extension, so the totality-using [FN]
   mechanisms may act on it.  [P]'s definition is recorded among the
   eliminated ones, and the final answer composes it with [G]'s and [F]'s
   solutions. *)
let decompose_uniq pcsp =
  let kind_map = kind_map_of pcsp in
  let uniqs =
    Map.Poly.filter_mapi (senv_of pcsp) ~f:(fun ~key ~data:sort ->
        match Map.Poly.find kind_map key with
        | Some (Kind.Uniq (j, _)) -> Some (sort, j)
        | _ -> None)
  in
  if Map.Poly.is_empty uniqs then pcsp
  else
    let defs, new_senv, new_kinds =
      Map.Poly.fold uniqs ~init:(Map.Poly.empty, Map.Poly.empty, Map.Poly.empty)
        ~f:(fun ~key:p ~data:(sort, j) (defs, senv, kinds) ->
          let sorts = Sort.args_of sort in
          let xs = List.map sorts ~f:(fun s -> (Ident.mk_fresh_tvar (), s)) in
          let rest = List.take xs j @ List.drop xs (j + 1) in
          let xj = List.nth_exn xs j in
          let g = Ident.mk_fresh_tvar ~prefix:(Some (Ident.name_of_tvar p ^ "_dom")) () in
          let f =
            Ident.mk_fresh_tvar ~prefix:(Some ("FN_" ^ Ident.name_of_tvar p ^ "_fun")) ()
          in
          let app v args = ExtTerm.mk_var_app v (List.map args ~f:(fst >> ExtTerm.mk_var)) in
          let def =
            Term.mk_lambda xs
              (BoolTerm.and_of [ app g rest; app f (rest @ [ xj ]) ])
          in
          ( Map.Poly.set defs ~key:p ~data:def,
            Map.Poly.set
              (Map.Poly.set senv ~key:g
                 ~data:(Sort.mk_fun (List.map rest ~f:snd @ [ BoolTerm.SBool ])))
              ~key:f
              ~data:(Sort.mk_fun (List.map (rest @ [ xj ]) ~f:snd @ [ BoolTerm.SBool ])),
            Map.Poly.set (Map.Poly.set kinds ~key:g ~data:Kind.Ord) ~key:f ~data:Kind.FN ))
    in
    let pcsp' = subst ~elim:true defs pcsp in
    let params = params_of pcsp' in
    update_params pcsp'
      {
        params with
        Params.senv = Map.force_merge params.Params.senv new_senv;
        kind_map = Map.force_merge params.Params.kind_map new_kinds;
        sol_for_eliminated = Map.force_merge params.Params.sol_for_eliminated defs;
      }

(* The [Prop] position of an admissible or integrable unknown, relativised to
   the non-negative reals.

   Both kinds carry one answer value, their last argument, whose domain in the
   source semantics is the extended non-negative reals [0, oo]; the solver gives
   that position the sort [Real], or a tuple of [Real]s (a value and a score
   under conditioning).  A clause is one demand per instance of its variables,
   so read over [Real] it also demands the instances in which such an argument
   is negative -- instances the source semantics does not have.  A clause
   forcing [P(-1)] and a goal forbidding it is then refuted, although under the
   source semantics neither clause has an instance and [P = {0}] solves it.

   The relativisation conjoins [0 <= t] to the premise of the clause for every
   real component [t] of the last argument of every application of such an
   unknown in it, body or head, which removes exactly the negative instances
   and adds none:
   - the solution space is untouched; on a body application the premise is
     redundant for every template candidate, which is already false at a
     negative value (both templates assert [0 <= v], and the conditioned
     admissible one bounds the score below by a non-negative expression), and
     on a head application it is what removes the demand;
   - the clauses only get weaker, so no solution of the original is lost;
   - a refutation of the relativised problem needs no assumption that the
     clause's constraint keeps answer values non-negative, since every instance
     it uses has non-negative answer values on both sides by construction.

   Precondition: a variable met at a [Prop] position is not also used as an
   ordinary real, or that use is restricted too.  Only the kinded positions are
   known here; an answer value carried by an ordinary unknown is not guarded.

   Coverage: on a clause-form problem, every application.  On a formula-form
   problem, the applications outside every binder of the formula's matrix whose
   answer argument mentions only the formula's universal variables; one under a
   binder is left as it is, since its instance is not the formula's.

   Applied once, at the solver's entry.  A problem without such an unknown is
   returned as it is. *)
let prop_sorts_of pcsp =
  let kind_map = kind_map_of pcsp in
  Map.Poly.filter_mapi (senv_of pcsp) ~f:(fun ~key ~data:sort ->
      match Map.Poly.find kind_map key with
      | Some (Kind.Adm _ | Kind.Integ) -> (
          match List.last (Sort.args_of sort) with
          | Some s -> Some s
          | None -> None)
      | _ -> None)

(* The real components of an answer value [t] of sort [sort]: [t] itself, or
   its projections when the sort is a tuple of reals; nothing for any other
   sort, which neither template accepts. *)
let prop_components sort t =
  match sort with
  | ExtTerm.SReal -> [ t ]
  | ExtTerm.STuple sorts when List.for_all sorts ~f:ExtTerm.is_real_sort ->
      List.mapi sorts ~f:(fun i _ -> ExtTerm.tuple_sel_of sorts t i)
  | _ -> []

(* The real components of the answer argument of [atm] when it applies an
   unknown of [prop_sorts], and nothing otherwise. *)
let prop_components_of_app prop_sorts atm =
  match Term.let_apps atm with
  | Var (x, _), (_ :: _ as args) -> (
      match Map.Poly.find prop_sorts x with
      | Some sort -> prop_components sort (List.last_exn args)
      | None -> [])
  | _ -> []

(* The applications of an unknown of [prop_sorts] in [t] that lie outside
   every binder. *)
let rec kinded_apps_outside_binders prop_sorts acc t =
  match t with
  | App _ -> (
      let h, args = Term.let_apps t in
      match h with
      | Var (x, _) when Map.Poly.mem prop_sorts x -> t :: acc
      | _ ->
          List.fold args
            ~init:(kinded_apps_outside_binders prop_sorts acc h)
            ~f:(kinded_apps_outside_binders prop_sorts))
  | TyApp (t', _, _) -> kinded_apps_outside_binders prop_sorts acc t'
  | Var _ | Con _ | Bin _ | Let _ | TyLam _ -> acc

(* [t < 0] for each distinct component, the disjuncts that make the clause's
   premise require every component to be non-negative. *)
let negative_prop_disjuncts ?(keep = fun _ -> true) prop_sorts apps =
  List.concat_map apps ~f:(prop_components_of_app prop_sorts)
  |> List.filter ~f:keep
  |> List.dedup_and_sort ~compare:Stdlib.compare
  |> List.map ~f:(fun t -> ExtTerm.mk_apps (ExtTerm.mk_rlt ()) [ t; ExtTerm.rzero () ])

let relativise_prop_clause prop_sorts ((uni_senv, ps, ns, phi) as cl : Clause.t) =
  let apps = Set.to_list ps @ Set.to_list ns in
  match negative_prop_disjuncts prop_sorts apps with
  | [] -> cl
  | negs -> Clause.canon (uni_senv, ps, ns, BoolTerm.or_of (phi :: negs))

let relativise_prop_positions pcsp =
  let prop_sorts = prop_sorts_of pcsp in
  if Map.Poly.is_empty prop_sorts then pcsp
  else
    let clauses = ClauseSet.canon <<< Set.Poly.map ~f:(relativise_prop_clause prop_sorts) in
    let params = params_of pcsp in
    let params =
      { params with Params.stable_clauses = clauses params.Params.stable_clauses }
    in
    match pcsp with
    | Cnf (cls, _) -> Cnf (clauses cls, params)
    | Raw (phis, _) ->
        Raw
          ( Set.Poly.map phis ~f:(fun (uni_senv, phi) ->
                let apps = kinded_apps_outside_binders prop_sorts [] phi in
                let keep t =
                  Set.is_subset (Term.fvs_of t) ~of_:(Map.key_set uni_senv)
                in
                match negative_prop_disjuncts ~keep prop_sorts apps with
                | [] -> (uni_senv, phi)
                | negs -> (uni_senv, BoolTerm.or_of (negs @ [ phi ]))),
            params )

(* Sort separation at the kinded positions: the variables that occur, in one
   constraint, both in the answer argument of an admissible or integrable
   application and in a non-answer argument of one (an integrable unknown's
   sample, or an ordinary argument).  The relativisation above restricts a
   variable met at an answer position to the non-negative reals, which is
   the source semantics only when that variable is an answer value
   everywhere it occurs; a variable returned here is also used as an
   ordinary real, whose use the premise restricts too.  Positions of ordinary
   unknowns are not inspected, since nothing records which of them carry
   answer values. *)
let prop_position_violations pcsp =
  let prop_sorts = prop_sorts_of pcsp in
  if Map.Poly.is_empty prop_sorts then Set.Poly.empty
  else
    Set.concat_map (formulas_of pcsp) ~f:(fun (_, phi) ->
        let apps = kinded_apps_outside_binders prop_sorts [] phi in
        let answer, other =
          List.fold apps ~init:(Set.Poly.empty, Set.Poly.empty)
            ~f:(fun (answer, other) atm ->
              match List.rev (snd (Term.let_apps atm)) with
              | last :: rest ->
                  ( Set.union answer (Term.fvs_of last),
                    Set.union other (Set.Poly.union_list (List.map rest ~f:Term.fvs_of)) )
              | [] -> (answer, other))
        in
        Set.inter answer other)

(* The substitution [cochc_to_chc] applies: every [Ord] predicate [P] of the
   problem is replaced by its complement [\x. not P(x)], which turns the
   co-CHC form of a problem into a CHC over the complements.  Exposed so that a caller building the CHC formula by formula
   can apply the same substitution to each part of a formula before joining
   them. *)
let cochc_subst_of pcsp =
  Map.Poly.filter_mapi (senv_of pcsp) ~f:(fun ~key ~data ->
        if Kind.is_ord @@ kind_of pcsp key then (
          let sargs, sret = Sort.args_ret_of data in
          let params = sort_env_list_of_sorts sargs in
          let args = List.map params ~f:(fst >> ExtTerm.mk_var) in
          assert (BoolTerm.is_bool_sort sret);
          Some
            (ExtTerm.mk_lambda params @@ BoolTerm.neg_of
            @@ ExtTerm.mk_var_app key args))
        else None)

let cochc_to_chc pcsp =
  let sub = cochc_subst_of pcsp in
  subst ~elim:false (*ToDo*) sub pcsp

let mmap ~f pcsp =
  map pcsp ~f:(fun (uni_senv, phi) ->
      ( uni_senv,
        ExtTerm.nnf_of phi
        |> ExtTerm.cnf_of (senv_of pcsp) uni_senv
        |> Set.Poly.map ~f:(fun (ps, ns, phi) ->
            (uni_senv, Set.Poly.map ps ~f, Set.Poly.map ns ~f, phi))
        |> ClauseSet.to_formula ))

let elim_unsat_wf_predicates ~print pcsp =
  (* kind_map legitimately holds kinds for predicates not (yet) in senv, e.g.
     every NWF/Parity tag pair; ask senv which are actually present *)
  if Fn.non Set.is_empty (wfpvs_of pcsp) then
    let replace_wf_term term =
      let pv, args = ExtTerm.let_var_app term in
      if is_wf_pred pcsp pv then (
        let length = List.length args / 2 in
        assert (List.length args mod 2 = 0);
        let args_l, args_r = List.split_n args length in
        if Stdlib.(args_l = args_r) then (
          print @@ lazy (sprintf "eliminating %s" @@ ExtTerm.str_of term);
          ExtTerm.mk_bool false)
        else term)
      else term
    in
    mmap pcsp ~f:replace_wf_term
  else pcsp

let elim_unsat_nwf_predicates ~print pcsp =
  if Fn.non Set.is_empty (nwfpvs_of pcsp) then
    let replace_nwf_term term =
      let pv, args = ExtTerm.let_var_app term in
      if is_nwf_pred pcsp pv then
        match nwf_tag_of pcsp pv with
        | None -> assert false
        | Some (nwf, (idl, idr)) ->
            if Ident.tvar_equal idl idr then (
              let args = List.drop args (List.length nwf.sorts_shared) in
              let len_args = List.length args in
              assert (len_args mod 2 = 0);
              let length = len_args / 2 in
              let args_l, args_r = List.split_n args length in
              if Stdlib.(args_l = args_r) then (
                print @@ lazy (sprintf "eliminating %s" @@ ExtTerm.str_of term);
                ExtTerm.mk_bool false)
              else term)
            else term
      else term
    in
    mmap pcsp ~f:replace_nwf_term
  else pcsp

let elim_unsat_parity_predicates ~print pcsp =
  if Fn.non Set.is_empty (paritypvs_of pcsp) then
    let replace_parity_term term =
      let pv, args = ExtTerm.let_var_app term in
      if is_parity_pred pcsp pv then
        match nwf_tag_of pcsp pv with
        | None -> assert false
        | Some (nwf, (idl, idr)) ->
            if
              Ident.tvar_equal idl idr
              && (not @@ Set.mem nwf.acc_set (Map.Poly.find_exn nwf.sigma idl))
            then (
              let args = List.drop args (List.length nwf.sorts_shared) in
              let len_args = List.length args in
              assert (len_args mod 2 = 0);
              let length = len_args / 2 in
              let args_l, args_r = List.split_n args length in
              if Stdlib.(args_l = args_r) then (
                print @@ lazy (sprintf "eliminating %s" @@ ExtTerm.str_of term);
                ExtTerm.mk_bool false)
              else term)
            else term
      else term
    in
    mmap pcsp ~f:replace_parity_term
  else pcsp

let elim_triv_nwf_predicate pcsp =
  let kind_map = kind_map_of pcsp in
  if Fn.non Set.is_empty (nwfpvs_of pcsp) then
    let clauses = clauses_of @@ to_cnf @@ to_nnf pcsp in
    let non_trivial =
      Set.concat_map clauses ~f:(fun (_, ps, ns (*ToDo*), _) ->
          Set.Poly.filter_map (Set.union ps ns) ~f:(fun atm ->
              match Map.Poly.find kind_map @@ ExtTerm.pvar_of_atom atm with
              | Some (Kind.NWF (nwf, (idl, idr))) -> Some (nwf.name, idl, idr)
              | _ -> None))
      |> Set.group_by ~equiv:(fun (pv1, _, _) (pv2, _, _) ->
          Ident.tvar_equal pv1 pv2)
      |> List.map ~f:(fun l ->
          let pv = fst3 @@ Set.choose_exn l in
          let idls, idrs =
            Set.unzip @@ Set.Poly.map l ~f:(fun (_, idl, idr) -> (idl, idr))
          in
          (pv, Set.inter idls idrs))
      |> Map.Poly.of_alist_exn
    in
    let trivially_satisfied atm =
      (* ToDo: NWF predicate variables that do not appear in any cycle can be set trivially to either true or false *)
      match Map.Poly.find kind_map @@ ExtTerm.pvar_of_atom atm with
      | Some (Kind.NWF (nwf, (idl, idr))) ->
          let non_trivial_set = Map.Poly.find_exn non_trivial nwf.name in
          not (Set.mem non_trivial_set idl && Set.mem non_trivial_set idr)
      | _ -> false
    in
    let clauses' =
      Set.Poly.filter_map clauses ~f:(fun (uni_senv, ps, ns, phi) ->
          if Set.exists ps ~f:trivially_satisfied then None
          else
            let ns = (*ToDo*) Set.filter ns ~f:(Fn.non trivially_satisfied) in
            Some (uni_senv, ps, ns, phi))
    in
    (* the members set to [true] are recorded as such: the printed model must
       include them and the witness checker treats the assumption as a
       definition it can name *)
    let params =
      let params = params_of pcsp in
      let assumed =
        Set.concat_map clauses ~f:(fun (_, ps, ns, _) ->
            Set.Poly.filter_map (Set.union ps ns) ~f:(fun atm ->
                if trivially_satisfied atm then
                  let pv = ExtTerm.pvar_of_atom atm in
                  match Map.Poly.find params.Params.senv pv with
                  | Some sort ->
                      Some
                        ( pv,
                          Term.mk_lambda
                            (List.map (Sort.args_of sort) ~f:(fun s ->
                                 (Ident.mk_fresh_tvar (), s)))
                            (BoolTerm.mk_bool true) )
                  | None -> None
                else None))
      in
      {
        params with
        Params.sol_for_eliminated =
          Set.fold assumed ~init:params.Params.sol_for_eliminated
            ~f:(fun m (k, v) -> Map.Poly.set m ~key:k ~data:v);
        (* [true] here preserves satisfiability rather than being implied: the
           member lies on no cycle.  A checker needs to be told which *)
        Params.elimination_reasons =
          Set.fold assumed ~init:params.Params.elimination_reasons
            ~f:(fun m (k, _) ->
              (* before every step the eliminator records *)
              Map.Poly.set m ~key:k ~data:(Params.TrivKind, 0));
      }
    in
    match pcsp with
    | Raw (_, _) ->
        Raw
          ( Set.Poly.map clauses' ~f:(fun cl ->
                (Quadruple.fst cl, Clause.to_formula cl)),
            params )
    | Cnf (_, _) -> Cnf (clauses', params)
  else pcsp

let elim_triv_parity_predicate pcsp =
  let kind_map = kind_map_of pcsp in
  if Fn.non Set.is_empty (paritypvs_of pcsp) then
    let clauses = clauses_of @@ to_cnf @@ to_nnf pcsp in
    let non_trivial =
      Set.concat_map clauses ~f:(fun (_, ps, ns (*ToDo*), _) ->
          Set.Poly.filter_map (Set.union ps ns) ~f:(fun atm ->
              match Map.Poly.find kind_map @@ ExtTerm.pvar_of_atom atm with
              | Some (Kind.Parity (nwf, (idl, idr))) -> Some (nwf.name, idl, idr)
              | _ -> None))
      |> Set.group_by ~equiv:(fun (pv1, _, _) (pv2, _, _) ->
          Ident.tvar_equal pv1 pv2)
      |> List.map ~f:(fun l ->
          let pv = fst3 @@ Set.choose_exn l in
          let idls, idrs =
            Set.unzip @@ Set.Poly.map l ~f:(fun (_, idl, idr) -> (idl, idr))
          in
          (pv, Set.inter idls idrs))
      |> Map.Poly.of_alist_exn
    in
    let trivially_satisfied atm =
      (* ToDo: parity predicate variables that do not appear in any cycle can be set trivially to either true or false *)
      match Map.Poly.find kind_map @@ ExtTerm.pvar_of_atom atm with
      | Some (Kind.Parity (nwf, (idl, idr))) ->
          let non_trivial_set = Map.Poly.find_exn non_trivial nwf.name in
          not (Set.mem non_trivial_set idl && Set.mem non_trivial_set idr)
      | _ -> false
    in
    let clauses' =
      Set.Poly.filter_map clauses ~f:(fun (uni_senv, ps, ns, phi) ->
          if Set.exists ps ~f:trivially_satisfied then None
          else
            let ns = (*ToDo*) Set.filter ns ~f:(Fn.non trivially_satisfied) in
            Some (uni_senv, ps, ns, phi))
    in
    (* the members set to [true] are recorded as such: the printed model must
       include them and the witness checker treats the assumption as a
       definition it can name *)
    let params =
      let params = params_of pcsp in
      let assumed =
        Set.concat_map clauses ~f:(fun (_, ps, ns, _) ->
            Set.Poly.filter_map (Set.union ps ns) ~f:(fun atm ->
                if trivially_satisfied atm then
                  let pv = ExtTerm.pvar_of_atom atm in
                  match Map.Poly.find params.Params.senv pv with
                  | Some sort ->
                      Some
                        ( pv,
                          Term.mk_lambda
                            (List.map (Sort.args_of sort) ~f:(fun s ->
                                 (Ident.mk_fresh_tvar (), s)))
                            (BoolTerm.mk_bool true) )
                  | None -> None
                else None))
      in
      {
        params with
        Params.sol_for_eliminated =
          Set.fold assumed ~init:params.Params.sol_for_eliminated
            ~f:(fun m (k, v) -> Map.Poly.set m ~key:k ~data:v);
        (* [true] here preserves satisfiability rather than being implied: the
           member lies on no cycle.  A checker needs to be told which *)
        Params.elimination_reasons =
          Set.fold assumed ~init:params.Params.elimination_reasons
            ~f:(fun m (k, _) ->
              (* before every step the eliminator records *)
              Map.Poly.set m ~key:k ~data:(Params.TrivKind, 0));
      }
    in
    match pcsp with
    | Raw (_, _) ->
        Raw
          ( Set.Poly.map clauses' ~f:(fun cl ->
                (Quadruple.fst cl, Clause.to_formula cl)),
            params )
    | Cnf (_, _) -> Cnf (clauses', params)
  else pcsp

(* With [triv_fn_linear], [elim_triv_fn_predicate] reads the free variables
   of each functional body atom of a clause once, where it read, for each of
   the clause's k such atoms, those of the k - 1 others: O(k) free-variable
   walks per clause instead of O(k^2).  The question it answers is the same
   -- is the result [y] of atom i free in the pure part, in the other atoms,
   in atom i's inputs or in another functional body atom, outside the
   unknowns' names? -- because a variable is in a union exactly when it is
   in one of the parts, and the parts are the same sets; and the pure part's
   and other atoms' variables are read only when some result is a variable,
   the only case the question is asked.  So every value the pass builds is
   the one it builds with the switch off.  Why: after resolution copies the
   clause, a clause of a Thrust input holds 21 to 33 functional body atoms
   over large argument terms, and the k^2 walks were most of a 150 s pass. *)
let triv_fn_linear = Atomic.make false

let triv_fn_trace = Option.is_some (Stdlib.Sys.getenv_opt "COAR_TRIV_FN_TRACE")

let elim_triv_fn_predicate pcsp =
  if Fn.non Set.is_empty (fnpvs_of pcsp) then
    let linear = Atomic.get triv_fn_linear in
    let unknown_names = Map.Poly.key_set @@ senv_of pcsp in
    let ph = Common.PhaseTime.with_phase in
    (* the functional body atoms kept: [fnns] are the clause's, [phi], [ps]
       and [ns] the rest of it.  The two forms below return the same subset
       of [fnns] (see [triv_fn_linear]). *)
    let kept_quadratic phi ps ns fnns =
      let fvs_ps_ns_phi =
        Set.diff
          (Set.union (ExtTerm.fvs_of phi)
             (Set.concat_map (Set.union ps ns) ~f:ExtTerm.fvs_of))
          unknown_names
      in
      Set.filter fnns ~f:(fun fnn ->
          let ins, out = List.rest_last (snd fnn) in
          if ExtTerm.is_var out then
            let fvs_fnns =
              Set.diff
                (Set.Poly.union_list
                @@ Set.concat_map (Set.remove fnns fnn)
                     ~f:(Tuple2.uncurry ExtTerm.mk_var_app >> ExtTerm.fvs_of)
                   :: List.map ins ~f:ExtTerm.fvs_of)
                unknown_names
            in
            if
              Set.mem
                (Set.union fvs_ps_ns_phi fvs_fnns)
                (fst (ExtTerm.let_var out))
            then true
            else (* fnn is trivial *) false
          else true)
    in
    let kept_linear phi ps ns fnns =
      (* each atom's own variables, read once; [Set.remove fnns fnn] above
         ranges over the atoms other than [fnn], which are the entries at
         other positions here, the set holding each atom once *)
      let atoms =
        List.map (Set.to_list fnns) ~f:(fun fnn ->
            (fnn, ExtTerm.fvs_of (Tuple2.uncurry ExtTerm.mk_var_app fnn)))
      in
      let rest =
        lazy
          (Set.union (ExtTerm.fvs_of phi)
             (Set.concat_map (Set.union ps ns) ~f:ExtTerm.fvs_of))
      in
      let kept =
        List.filteri atoms ~f:(fun i (fnn, _) ->
            let ins, out = List.rest_last (snd fnn) in
            if ExtTerm.is_var out then
              let y = fst (ExtTerm.let_var out) in
              (not (Set.mem unknown_names y))
              && (Set.mem (Lazy.force rest) y
                 || List.exists ins ~f:(fun t -> Set.mem (ExtTerm.fvs_of t) y)
                 || List.existsi atoms ~f:(fun j (_, fv) ->
                     j <> i && Set.mem fv y))
            else true)
      in
      Set.Poly.of_list (List.map kept ~f:fst)
    in
    (* under [ExtTerm.share_term_conversion] the normal forms of all the
       formulas share one scope, so a subformula many clauses share is put
       in negation normal form, and tested for unknowns, once *)
    with_shared_normal_forms @@ fun () ->
    let trace_i = ref 0 in
    ph "map" @@ fun () ->
    map pcsp ~f:(fun (uni_senv, phi) ->
        let t0 = Common.PhaseTime.now () in
        let cls0 =
          ph "nnf" (fun () -> ExtTerm.nnf_of phi)
          |> fun t ->
          ph "cnf" (fun () -> ExtTerm.cnf_of (senv_of pcsp) uni_senv t)
        in
        let phi' =
          cls0
          |> fun cls -> ph "clauses" @@ fun () ->
          Set.Poly.map cls ~f:(fun (ps, ns, phi) ->
              let fnns, ns =
                Set.partition_map ns ~f:(fun term ->
                    let pv, args = ExtTerm.let_var_app term in
                    if is_fn_pred pcsp pv then First (pv, args) else Second term)
              in
              let ns', phiss =
                (if linear then kept_linear else kept_quadratic) phi ps ns fnns
                |> Set.to_list
                |> List.classify (fun (pv1, args1) (pv2, args2) ->
                    Ident.tvar_equal pv1 pv2
                    && Stdlib.(
                         Common.Ext.List.drop_last_exn args1
                         = Common.Ext.List.drop_last_exn args2))
                |> List.map ~f:(fun pvs ->
                    let hd, tl = List.hd_tl pvs in
                    let out = List.last_exn @@ snd hd in
                    let sort = ExtTerm.sort_of uni_senv out in
                    ( Tuple2.uncurry ExtTerm.mk_var_app hd,
                      List.map tl
                        ~f:(snd >> List.last_exn >> ExtTerm.neq_of sort out) ))
                |> List.unzip
              in
              ( uni_senv,
                ps,
                Set.union ns (Set.Poly.of_list ns'),
                ExtTerm.or_of (phi :: List.concat phiss) ))
          |> fun cls -> ph "to-formula" (fun () -> ClauseSet.to_formula cls)
        in
        (* with COAR_TRIV_FN_TRACE set, one line per formula that takes more
           than a tenth of a second: its clauses and their functional body
           atoms (a diagnostic only) *)
        (if triv_fn_trace then (
           let dt = Common.PhaseTime.now () -. t0 in
           incr trace_i;
           if Float.(dt > 0.1) then
             let fnns =
               Set.fold cls0 ~init:0 ~f:(fun n (_, ns, _) ->
                   n
                   + Set.count ns ~f:(fun t ->
                       is_fn_pred pcsp (fst (ExtTerm.let_var_app t))))
             in
             Printf.eprintf "[triv-fn] formula %d: %.2f s, %d clauses, %d fn atoms\n%!"
               !trace_i dt (Set.length cls0) fnns));
        (uni_senv, phi'))
  else pcsp

(* Dropping a functional witness whose result only feeds other witnesses.

   A functional (total, single-valued) unknown [P] is dropped -- every atom of
   it removed -- when every occurrence of [P] in the problem is a body atom
   [P(t1..tn, y)] of a clause in which the result [y] is a variable that
   occurs nowhere else -- not in the pure part, not in a head atom, not in an
   atom of an ordinary unknown, not among [P]'s own inputs -- except as a
   whole input argument of other functional body atoms [Q(..., y, ..., w)]
   (never their result), and every such user [Q] is fed UNIFORMLY: at every
   occurrence of [Q] in the problem, a body atom of [P] in the same clause
   puts its result at the same input positions [K] of [Q], and each input
   [t_i] of [P] is [Q]'s argument at one fixed position [pi(i)] outside [K].

   This is the shape skolemising nested body universals leaves once the
   unknown the outer witness was for has been eliminated: the outer witness's
   value is passed to the inner witness and to nothing else, and resolution
   copies the clause with both atoms together.  The trivial case (no user at
   all) is [elim_triv_fn_predicate]'s.

   Equisatisfiable, model by model.
   - Reduced solution to original: each reduced clause is the original one
     with body literals removed, so it implies the original under the same
     interpretation; [P] is absent from the reduced problem and may be any
     total function of its sort (the sorts are non-empty).
   - Original solution to reduced: let [f] be [P]'s function in a solution.
     Reinterpret each user [Q] as [Q'(a, w) := Q(a with the positions K
     replaced by f(a at the positions pi), w)], defined positionally, a
     function of [Q]'s own arguments, total and single-valued because [Q] is.
     At every occurrence of [Q] the clause also held [P(t, y)], i.e.
     [y = f(t)], so the original clause says the rest holds where [Q'] and
     [Q] agree; the reduced clause, for every [y], applies [Q'], which is [Q]
     at [y = f(t)].  So the reduced clause holds under [Q'].
   So [sat] and [unsat] both transfer. *)
let elim_fn_feeding_fn_predicate_once pcsp =
  let fns = fnpvs_of pcsp in
  let count = Hashtbl.Poly.create () in
  let rec occ = function
    | Logic.Var (pv, _) ->
        if Set.mem fns pv then
          Hashtbl.Poly.update count pv ~f:(function None -> 1 | Some n -> n + 1)
    | Logic.App _ as t ->
        let h, ts = ExtTerm.let_apps t in
        occ h;
        List.iter ts ~f:occ
    | Logic.Bin (_, _, _, t, _) | Logic.TyApp (t, _, _) | Logic.TyLam (_, t, _)
      ->
        occ t
    | Logic.Let (_, _, t1, t2, _) ->
        occ t1;
        occ t2
    | Logic.Con _ -> ()
  in
  let count_of pv = Option.value ~default:0 (Hashtbl.Poly.find count pv) in
  let fvs = ExtTerm.fvs_of in
  let is_var_named y t =
    ExtTerm.is_var t && Ident.tvar_equal (fst (ExtTerm.let_var t)) y
  in
  let fn_atom t =
    match t with
    | Logic.Var _ | Logic.App _ -> (
        match ExtTerm.let_apps t with
        | Logic.Var (pv, _), args when Set.mem fns pv -> (
            match List.rest_last args with
            | ins, out -> Some (pv, ins, out)
            | exception _ -> None)
        | _ -> None)
    | _ -> None
  in
  let clauses =
    Set.to_list (formulas_of pcsp)
    |> List.concat_map ~f:(fun (uni_senv, phi) ->
        occ phi;
        Set.to_list
          (ExtTerm.nnf_of phi |> ExtTerm.cnf_of (senv_of pcsp) uni_senv))
  in
  (* per clause, the feeding edges: (P, its atom, y, [(Q's atom, K, pi)]) for
     every functional body atom whose result is a variable used only as whole
     inputs of other functional body atoms; [None] users when it is used
     anywhere else *)
  let edges_of (ps, ns, phi) =
    let fnns =
      List.filter_map (Set.to_list ns) ~f:(fun t ->
          Option.map (fn_atom t) ~f:(fun a -> (t, a)))
    in
    let others = Set.filter ns ~f:(fun t -> Option.is_none (fn_atom t)) in
    let outside =
      Set.Poly.union_list
        [ fvs phi; Set.concat_map ps ~f:fvs; Set.concat_map others ~f:fvs ]
    in
    List.map fnns ~f:(fun (atm, (pv, ins, out)) ->
        let users =
          if not (ExtTerm.is_var out) then None
          else
            let y = fst (ExtTerm.let_var out) in
            if
              Set.mem outside y
              || List.exists ins ~f:(fun t -> Set.mem (fvs t) y)
            then None
            else
              List.fold fnns ~init:(Some []) ~f:(fun acc (a, (qv, qins, qout)) ->
                  match acc with
                  | None -> None
                  | Some l ->
                      if Stdlib.(a == atm) || not (Set.mem (fvs a) y) then acc
                      else if
                        Ident.tvar_equal qv pv
                        || Set.mem (fvs qout) y
                        || List.exists qins ~f:(fun t ->
                            Set.mem (fvs t) y && not (is_var_named y t))
                      then None
                      else
                        let qa = Array.of_list qins in
                        let k =
                          List.filter (List.range 0 (Array.length qa))
                            ~f:(fun j -> is_var_named y qa.(j))
                        in
                        let pi =
                          List.map ins ~f:(fun t ->
                              List.find (List.range 0 (Array.length qa))
                                ~f:(fun j ->
                                  (not (List.mem k j ~equal:Int.equal))
                                  && Stdlib.(qa.(j) = t)))
                        in
                        if List.exists pi ~f:Option.is_none then None
                        else
                          Some ((a, qv, k, List.filter_opt pi) :: l))
        in
        (pv, atm, users))
  in
  let all_edges = List.map clauses ~f:(fun cl -> (cl, edges_of cl)) in
  (* [P] is locally droppable when all its occurrences are such atoms *)
  let local = Hashtbl.Poly.create () in
  List.iter all_edges ~f:(fun (_, es) ->
      List.iter es ~f:(fun (pv, _, users) ->
          Hashtbl.Poly.update local pv ~f:(fun prev ->
              let ok, n = Option.value prev ~default:(true, 0) in
              (ok && Option.is_some users, n + 1))));
  let candidates =
    Hashtbl.Poly.fold local ~init:Set.Poly.empty ~f:(fun ~key ~data acc ->
        match data with
        | true, n when n = count_of key -> Set.add acc key
        | _ -> acc)
  in
  (* uniformity: every occurrence of a user Q is fed by P with the same K and
     pi; the number of fed occurrences must be all of Q's occurrences *)
  let feeds = Hashtbl.Poly.create () in
  List.iteri all_edges ~f:(fun idx (_, es) ->
      List.iter es ~f:(fun (pv, _, users) ->
          if Set.mem candidates pv then
            List.iter (Option.value users ~default:[])
              ~f:(fun (qatm, qv, k, pi) ->
                Hashtbl.Poly.add_multi feeds ~key:(pv, qv)
                  ~data:((idx, qatm), (k, pi)))));
  let uniform pv =
    Hashtbl.Poly.for_alli feeds ~f:(fun ~key:(pv', qv) ~data ->
        (not (Ident.tvar_equal pv pv'))
        ||
        let sigs = List.map data ~f:snd in
        let occs =
          List.dedup_and_sort (List.map data ~f:fst) ~compare:Stdlib.compare
        in
        (* every occurrence of Q fed, each by exactly one atom of P *)
        List.length data = count_of qv
        && List.length occs = List.length data
        &&
        let s0 = List.hd_exn sigs in
        List.for_all sigs ~f:(fun s -> Stdlib.(s = s0)))
  in
  (* one unknown per pass, so that each pass is the single step argued above *)
  let droppable =
    Option.value_map ~default:Set.Poly.empty ~f:Set.Poly.singleton
    @@ Set.find candidates ~f:uniform
  in
  if Set.is_empty droppable then (pcsp, false)
  else
    let pcsp' =
      map pcsp ~f:(fun (uni_senv, phi) ->
          let cls =
            ExtTerm.nnf_of phi |> ExtTerm.cnf_of (senv_of pcsp) uni_senv
          in
          let hit = ref false in
          let cls' =
            Set.Poly.map cls ~f:(fun (ps, ns, phi) ->
                ( uni_senv,
                  ps,
                  Set.filter ns ~f:(fun t ->
                      match fn_atom t with
                      | Some (pv, _, _) when Set.mem droppable pv ->
                          hit := true;
                          false
                      | _ -> true),
                  phi ))
          in
          if !hit then (uni_senv, ClauseSet.to_formula cls') else (uni_senv, phi))
    in
    (pcsp', true)

let elim_fn_feeding_fn_predicate pcsp =
  (* one atom per clause per pass: a dropped witness's users may become
     droppable themselves, and the occurrence counts are recomputed; the
     number of functional body atoms bounds the passes *)
  let rec go pcsp n =
    if n <= 0 || Set.is_empty (fnpvs_of pcsp) then pcsp
    else
      match elim_fn_feeding_fn_predicate_once pcsp with
      | pcsp', true -> go pcsp' (n - 1)
      | _, false -> pcsp
  in
  go pcsp 64

(* Restoring a witness's quantifier once the body it guards mentions no
   unknown.

   The reader skolemises a body universal [forall y. psi(y)] over an unknown
   into a functional (total, single-valued) witness [w]; if preprocessing then
   eliminates that unknown, every clause of [w] reads
   [not w(t, y) \/ phi_k(y) \/ R], with [y] only in the pure parts [phi_k],
   and the witness is a function the loop must still learn although the
   question it stands for is now a quantified formula with no unknown in it.

   The step.  A functional unknown [w] whose every application in the problem
   is the SAME body atom [w(t, y)] (one spelling: same arguments, same result
   variable [y]) in clauses that agree on everything but their pure parts
   (the same head atoms and the same other body atoms, together [R]) is
   removed, and those clauses are replaced by ONE clause [R \/ exists y.
   forall E. /\_k phi_k], where [D] is the set of variables that are whole
   arguments of [t], [E] the variables of the [phi_k] other than [y] outside
   [D], and the step is taken only when [y] occurs nowhere but the [phi_k],
   no variable of [E] occurs in [t] or in [R], and the clauses' sorts agree.

   Equivalence, model by model.  The clauses share their variable names and
   are each universally closed, so they are one clause [not w(t, y) \/ R \/
   /\_k phi_k].  Write [psi = /\_k phi_k]; it depends on [y], on variables
   of [D] and on [E].
   - Original to restored: with [w]'s function [f], fix the variables
     outside [E].  If [R] is false there, the original clause at [y = f(t)]
     gives [psi] for every [E], so [exists y. forall E. psi] holds.
   - Restored to original: [D]'s values are a function of [t]'s, since each
     is an argument.  For a value of [t] choose [f(t)] as a [y] with [forall
     E. psi] where there is one, and anything otherwise; where there is none
     the restored clause gives [R] for every value of the variables outside
     [D] and [E] -- [R] mentions no variable of [E] -- so the original clause
     holds at every [y].  [w] occurs nowhere else, so this [f] is
     unconstrained otherwise.
   So [sat] and [unsat] both transfer. *)
let restore_witness_universal_once pcsp =
  let fns = fnpvs_of pcsp in
  let exi_senv = senv_of pcsp in
  let fn_atom t =
    match t with
    | Logic.Var _ | Logic.App _ -> (
        match ExtTerm.let_apps t with
        | Logic.Var (pv, _), args when Set.mem fns pv -> (
            match List.rest_last args with
            | ins, out -> Some (pv, ins, out)
            | exception _ -> None)
        | _ -> None)
    | _ -> None
  in
  (* every clause of the problem, tagged with the formula it came from *)
  let formulas = Set.to_list (formulas_of ~full_clauses:false pcsp) in
  let clauses =
    List.concat_mapi formulas ~f:(fun fi (uni_senv, phi) ->
        List.map
          (Set.to_list
             (ExtTerm.nnf_of phi |> ExtTerm.cnf_of exi_senv uni_senv))
          ~f:(fun cl -> (fi, uni_senv, cl)))
  in
  (* occurrences of each functional unknown: (clause index, atom, ins, out);
     an occurrence anywhere but a body atom (a head, a pure part, inside a
     term) disqualifies it *)
  let occs = Hashtbl.Poly.create () in
  let bad = Hash_set.Poly.create () in
  List.iteri clauses ~f:(fun ci (_, _, (ps, ns, phi)) ->
      Set.iter (ExtTerm.fvs_of phi) ~f:(fun v ->
          if Set.mem fns v then Hash_set.add bad v);
      Set.iter ps ~f:(fun t ->
          Set.iter (ExtTerm.fvs_of t) ~f:(fun v ->
              if Set.mem fns v then Hash_set.add bad v));
      Set.iter ns ~f:(fun t ->
          match fn_atom t with
          | Some (pv, ins, out) ->
              List.iter ins ~f:(fun a ->
                  Set.iter (ExtTerm.fvs_of a) ~f:(fun v ->
                      if Set.mem fns v then Hash_set.add bad v));
              Hashtbl.Poly.add_multi occs ~key:pv ~data:(ci, t, ins, out)
          | None ->
              Set.iter (ExtTerm.fvs_of t) ~f:(fun v ->
                  if Set.mem fns v then Hash_set.add bad v)));
  (* an unknown mentioned by a stable clause is left alone: those clauses are
     not rewritten here *)
  Set.iter (ClauseSet.to_formulas (stable_clauses_of pcsp)) ~f:(fun (_, phi) ->
      Set.iter (ExtTerm.fvs_of phi) ~f:(fun v ->
          if Set.mem fns v then Hash_set.add bad v));
  let arr = Array.of_list clauses in
  (* the clauses are renamed apart, so a member is read through a renaming of
     its variables onto the first member's, found by matching its witness
     atom and then its other atoms against the first member's *)
  let rec mtch m a b =
    match (a, b) with
    | Logic.Var (x, _), Logic.Var (y, _) -> (
        match Map.Poly.find m x with
        | Some y' -> if Ident.tvar_equal y y' then Some m else None
        | None -> Some (Map.Poly.set m ~key:x ~data:y))
    | Logic.App (f1, a1, _), Logic.App (f2, a2, _) ->
        Option.bind (mtch m f1 f2) ~f:(fun m -> mtch m a1 a2)
    | Logic.Con _, Logic.Con _ ->
        if String.equal (ExtTerm.str_of a) (ExtTerm.str_of b) then Some m
        else None
    | _ -> None
  in
  (* a bijection between two atom lists extending [m], greedily *)
  let rec match_atoms m xs ys =
    match xs with
    | [] -> if List.is_empty ys then Some m else None
    | x :: xs' ->
        List.find_mapi ys ~f:(fun i yv ->
            Option.bind (mtch m x yv) ~f:(fun m' ->
                match_atoms m'
                  xs'
                  (List.filteri ys ~f:(fun j _ -> j <> i))))
  in
  let candidate pv =
    if Hash_set.mem bad pv then None
    else
      match Hashtbl.Poly.find occs pv with
      | None | Some [] -> None
      | Some ((ci0, atm0, ins, out) :: _ as os) -> (
          let cis = List.map os ~f:(fun (ci, _, _, _) -> ci) in
          if
            List.length (List.dedup_and_sort ~compare:Int.compare cis)
            <> List.length os
            || not (ExtTerm.is_var out)
          then None
          else
            let y = fst (ExtTerm.let_var out) in
            let rest ci atm =
              let _, _, (ps, ns, _) = arr.(ci) in
              (Set.to_list ps, Set.to_list (Set.remove ns atm))
            in
            let ps0, ns0 = rest ci0 atm0 in
            (* each member's renaming onto the first member *)
            let renamings =
              List.map os ~f:(fun (ci, atm, _, _) ->
                  let ps, ns = rest ci atm in
                  Option.bind (mtch Map.Poly.empty atm atm0) ~f:(fun m ->
                      Option.bind (match_atoms m ps ps0) ~f:(fun m ->
                          match_atoms m ns ns0))
                  |> Option.map ~f:(fun m -> (ci, m)))
              |> Option.all
            in
            match renamings with
            | None -> None
            | Some renamings -> (
                let members =
                  List.map renamings ~f:(fun (ci, m) ->
                      let _, uni, (_, _, phi) = arr.(ci) in
                      let uni' =
                        Map.Poly.fold uni ~init:Map.Poly.empty
                          ~f:(fun ~key ~data acc ->
                            Map.Poly.set acc
                              ~key:(Option.value ~default:key (Map.Poly.find m key))
                              ~data)
                      in
                      (uni', ExtTerm.rename m phi))
                in
                let r_fvs =
                  Set.Poly.union_list
                    (List.map (ps0 @ ns0) ~f:ExtTerm.fvs_of)
                in
                let t_fvs =
                  Set.Poly.union_list (List.map ins ~f:ExtTerm.fvs_of)
                in
                let d =
                  Set.Poly.of_list
                  @@ List.filter_map ins ~f:(fun a ->
                      if ExtTerm.is_var a then Some (fst (ExtTerm.let_var a))
                      else None)
                in
                let phis = List.map members ~f:snd in
                let phi_fvs =
                  Set.Poly.union_list (List.map phis ~f:ExtTerm.fvs_of)
                in
                let e =
                  Set.diff (Set.remove phi_fvs y)
                    (Set.union d (Map.key_set exi_senv))
                in
                let senv =
                  List.fold members ~init:(Some Map.Poly.empty)
                    ~f:(fun acc (uni, _) ->
                      Option.bind acc ~f:(fun m ->
                          Map.Poly.fold uni ~init:(Some m)
                            ~f:(fun ~key ~data acc ->
                              Option.bind acc ~f:(fun m ->
                                  match Map.Poly.find m key with
                                  | Some s when not (Stdlib.( = ) s data) -> None
                                  | _ -> Some (Map.Poly.set m ~key ~data)))))
                in
                match senv with
                | None -> None
                | Some senv ->
                    if
                      (not (Set.mem r_fvs y))
                      && (not (Set.mem t_fvs y))
                      && Set.is_empty (Set.inter e t_fvs)
                      && Set.is_empty (Set.inter e r_fvs)
                      && Map.Poly.mem senv y
                    then
                      let bound vs =
                        List.map (Set.to_list vs) ~f:(fun v ->
                            (v, Map.Poly.find_exn senv v))
                      in
                      let restored =
                        Logic.BoolTerm.exists (bound (Set.Poly.singleton y))
                        @@ Logic.BoolTerm.forall (bound e)
                        @@ Logic.BoolTerm.and_of phis
                      in
                      Some
                        ( cis,
                          senv,
                          (Set.Poly.of_list ps0, Set.Poly.of_list ns0, restored) )
                    else None))
  in
  match Set.find_map fns ~f:(fun pv -> Option.map (candidate pv) ~f:(fun c -> (pv, c))) with
  | None -> (pcsp, false)
  | Some (_pv, (cis, senv, (ps0, ns0, restored))) ->
      (* rebuild every formula from its clauses, with the members of the group
         replaced by the restored clause, kept with the first member's
         formula *)
      let first = List.hd_exn cis in
      let replaced = Set.Poly.of_list cis in
      let by_formula =
        List.filter_mapi clauses ~f:(fun ci (fi, uni, (ps, ns, phi)) ->
            if ci = first then Some (fi, (senv, ps0, ns0, restored))
            else if Set.mem replaced ci then None
            else Some (fi, (uni, ps, ns, phi)))
      in
      let phis =
        List.mapi formulas ~f:(fun fi (uni_senv, _) ->
            let cls =
              List.filter_map by_formula ~f:(fun (fi', c) ->
                  if fi = fi' then Some c else None)
            in
            let uni =
              List.fold cls ~init:uni_senv ~f:(fun acc (u, _, _, _) ->
                  Map.Poly.merge_skewed acc u ~combine:(fun ~key:_ a _ -> a))
            in
            (uni, ClauseSet.to_formula (Set.Poly.of_list cls)))
      in
      let params = params_of pcsp in
      let pcsp' =
        match pcsp with
        | Raw _ -> Raw (Set.Poly.of_list phis, params)
        | Cnf _ ->
            Cnf
              ( Set.Poly.of_list
                @@ List.map by_formula ~f:(fun (_, c) -> Clause.canon c),
                params )
      in
      (pcsp', true)

let restore_witness_universals pcsp =
  let rec go pcsp n =
    if n <= 0 then pcsp
    else
      match restore_witness_universal_once pcsp with
      | pcsp', true -> go pcsp' (n - 1)
      | _, false -> pcsp
  in
  go pcsp 64

(** assume pcsp is cnf *)
let merge_clauses pcsp =
  let mk_flag =
    Set.to_list
    >> List.map ~f:ExtTerm.pvar_of_atom
    >> List.sort ~compare:Stdlib.compare
  in
  let sorted_atms =
    Set.to_list
    >> List.sort ~compare:(fun atm1 atm2 ->
        let p1 = ExtTerm.pvar_of_atom atm1 in
        let p2 = ExtTerm.pvar_of_atom atm2 in
        Stdlib.compare p1 p2)
  in
  let unify_atm atm1 atm2 =
    let p1, args1 = ExtTerm.let_var_app atm1 in
    let p2, args2 = ExtTerm.let_var_app atm2 in
    if Stdlib.(p1 = p2) then
      let tvars1 = List.map args1 ~f:(ExtTerm.let_var >> fst) in
      let tvars2 = List.map args2 ~f:(ExtTerm.let_var >> fst) in
      Map.Poly.of_alist_exn @@ List.zip_exn tvars1 tvars2
    else Map.Poly.empty
  in
  let senv = senv_of pcsp in
  clauses_of pcsp
  |> Set.Poly.map ~f:(Clause.refresh_tvar >> Clause.refresh_pvar_args senv)
  |> Set.to_list
  |> List.map ~f:(fun (uni_senv, ps, ns, phi) ->
      ((mk_flag ps, mk_flag ns), (uni_senv, sorted_atms ps, sorted_atms ns, phi)))
  |> List.classify (fun (flag1, _) (flag2, _) -> Stdlib.(flag1 = flag2))
  |> List.concat_map ~f:(fun cls ->
      let flag_head, flag_body = fst @@ List.hd_exn cls in
      let cls = List.map ~f:snd cls in
      if
        List.length cls <= 1
        || List.length flag_head <> Set.length (Set.Poly.of_list flag_head)
        || List.length flag_body <> Set.length (Set.Poly.of_list flag_body)
      then cls
      else
        let uni_senvs, ps, ns, phiss =
          List.fold cls ~init:([], [], [], [])
            ~f:(fun (uni_senvs, ps, ns, phis) (uni_senv0, ps0, ns0, phi0) ->
              if List.is_empty uni_senvs then ([ uni_senv0 ], ps0, ns0, [ phi0 ])
              else
                let subst =
                  Map.force_merge_list
                  @@ List.map2_exn (ps0 @ ns0) (ps @ ns) ~f:unify_atm
                in
                ( uni_senv0 :: uni_senvs,
                  ps,
                  ns,
                  ExtTerm.rename subst phi0 :: phis ))
        in
        [ (Map.force_merge_list uni_senvs, ps, ns, ExtTerm.and_of phiss) ])
  |> List.map ~f:(fun (uni_senv, ps, ns, phi) ->
      (uni_senv, Set.Poly.of_list ps, Set.Poly.of_list ns, phi))
  |> Set.Poly.of_list
  |> of_clauses ~params:(params_of pcsp)

let is_qualified_partial_solution ~print pvars_the_target_pvar_depends_on
    target_pvars violated_non_query_clauses =
  not
  @@ Set.exists violated_non_query_clauses
       ~f:
         (Clause.must_be_satisfied ~print target_pvars
            pvars_the_target_pvar_depends_on)

let check_valid is_valid pcsp sol =
  Set.for_all (formulas_of pcsp) ~f:(fun (uni_senv, phi) ->
      let phi' = Term.subst sol phi in
      let res = is_valid uni_senv phi' in
      (*if not res then
        print_endline @@ sprintf "before: %s\nafter: %s"
          (LogicOld.Formula.str_of @@
           ExtTerm.to_old_fml (senv_of pcsp) uni_senv phi)
          (LogicOld.Formula.str_of @@
           ExtTerm.to_old_fml (senv_of pcsp) uni_senv phi');*)
      res)

(* On unless a caller switches it off for the process (PCSat's
   [onepoint_constructor_binders] = false): before [make] skolemises an existential
   (in negation normal form) that has an unknown under it, remove each of its
   bound variables that a conjunct of its body determines through constructor
   applications, by [elim_constructor_points]. *)
let onepoint_constructor_binders = ref true

(* [solve_constructor_point x lhs rhs]: when [rhs] contains [x] only along one
   path of constructor applications of inductive datatypes, ending at [x]
   itself, and [lhs] does not contain [x]: [Some (s, guards)] such that
   [lhs = rhs] is equivalent, in every model of the background theory, to
   [x = s /\ guards], where [s] reads [x]'s position off [lhs] by selectors and
   [guards] are the testers of the constructors on the path (left out for a
   datatype with one constructor) and the equations of the other fields.
   Neither [s] nor a guard contains [x].  The equivalence is the injectivity
   and disjointness of constructors: [lhs = C(t1 .. tn)] holds exactly when
   [lhs] is built by [C] and its fields are [t1 .. tn]; a selector applied
   off its constructor is never read, because the tester guards it.  A
   codatatype is not decomposed (its equality is bisimilarity, not field-wise
   on finite terms). *)
let rec solve_constructor_point x lhs rhs =
  let open LogicOld in
  match rhs with
  | Term.Var (y, _, _) when Ident.tvar_equal x y -> Some (lhs, [])
  | Term.FunApp (T_dt.DTCons (name, _, dt), ts, _) when Datatype.is_dt dt -> (
      let occurs t = Set.mem (Term.tvs_of t) x in
      match List.filter_mapi ts ~f:(fun i t -> if occurs t then Some i else None) with
      | [ i ] ->
          let field j = T_dt.mk_sel_by_cons dt name j lhs in
          let tester =
            match Datatype.conses_of dt with
            | [ _ ] -> []
            | _ -> [ Formula.mk_atom (T_dt.mk_is_cons dt name lhs) ]
          in
          let others =
            List.filter_mapi ts ~f:(fun j t ->
                if j = i then None else Some (Formula.eq (field j) t))
          in
          Option.map (solve_constructor_point x (field i) (List.nth_exn ts i))
            ~f:(fun (s, guards) -> (s, tester @ others @ guards))
      | _ -> None)
  | _ -> None

(* The one-point rule through constructors, applied to every existential of a
   formula in negation normal form that has an unknown under it.

   Contract: the result is equivalent to the input in every model of the
   background theory, has the same free variables and the same unknowns, and
   is in negation normal form.  For a block [exists xs. c1 /\ .. /\ cm], a
   conjunct [ci] that is an equation [u = t] (either way round) with [u] free
   of [x] and [t] containing [x] along one constructor path is rewritten by
   [solve_constructor_point] into [x = s /\ guards]; then [exists x. x = s /\
   phi] is [phi[s/x]] since [s] does not contain [x].  Variables of the block
   other than [x] may occur in [u], [s] and the guards: they stay bound.

   Why it exists: an existential in effect over an unknown is skolemised into a
   functional predicate, and one functional predicate in a problem keeps every
   pass that requires ordinary unknowns from running at all (the Houdini
   pre-pass among them).  A front end writes a match on an enum as
   [forall q. v = C(q) => phi(q)] in a clause body, an existential in effect
   whose witness the theory already fixes as the field of [v]; no witness has
   to be synthesised for it. *)
let elim_constructor_points phi =
  let open LogicOld in
  let point_of xs conjunct =
    match conjunct with
    | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _) ->
        List.find_map xs ~f:(fun (x, _) ->
            let occurs t = Set.mem (Term.tvs_of t) x in
            let try_ lhs rhs =
              if occurs lhs then None
              else
                Option.map (solve_constructor_point x lhs rhs)
                  ~f:(fun (s, guards) -> (x, s, guards))
            in
            match try_ t1 t2 with Some r -> Some r | None -> try_ t2 t1)
    | _ -> None
  in
  let rec reduce xs conjuncts =
    let rec pick seen = function
      | [] -> None
      | c :: rest -> (
          match point_of xs c with
          | Some (x, s, guards) -> Some (x, s, guards, List.rev_append seen rest)
          | None -> pick (c :: seen) rest)
    in
    match pick [] conjuncts with
    | None -> (xs, conjuncts)
    | Some (x, s, guards, rest) ->
        let sub = Map.Poly.singleton x s in
        reduce
          (List.filter xs ~f:(fst >> Fn.non (Ident.tvar_equal x)))
          (guards @ List.map rest ~f:(Formula.subst sub))
  in
  let rec aux = function
    | Formula.UnaryOp (op, p, info) -> Formula.mk_unop ~info op (aux p)
    | Formula.BinaryOp (op, p1, p2, info) ->
        Formula.mk_binop ~info op (aux p1) (aux p2)
    | Formula.Bind (Formula.Exists, xs, body, info)
      when not (Set.is_empty (Formula.pvs_of body)) -> (
        let xs', conjuncts = reduce xs (Formula.conjuncts_list_of body) in
        let body' =
          if List.length xs' = List.length xs then body
          else Formula.and_of conjuncts
        in
        let body' = aux body' in
        match xs' with
        | [] -> body'
        | _ -> Formula.mk_bind ~info Formula.Exists xs' body')
    | Formula.Bind (b, xs, body, info) -> Formula.mk_bind ~info b xs (aux body)
    | Formula.LetFormula (v, s, d, body, info) ->
        Formula.mk_let_formula ~info v s d (aux body)
    | phi -> phi
  in
  aux phi

let make ?(skolem_pred = false) ?(prefix = None) phis (envs : SMT.Problem.envs)
    =
  let _uni_senv = of_old_sort_env_map envs.uni_senv in
  let exi_senv = of_old_sort_env_map envs.exi_senv in
  let fenv =
    let size_fenv =
      Map.Poly.of_alist_exn
      @@ List.map ~f:LogicOld.Datatype.size_fun_of
      @@ List.filter (Map.Poly.data envs.dtenv)
           ~f:
             (Fn.non
                LogicOld.Datatype.is_poly
                (*ToDo: generate size functions for polymorphic datatypes*))
    in
    Map.force_merge size_fenv
    @@ Map.Poly.filter envs.fenv ~f:Quintuple.fth (*ToDo*)
  in
  Map.Poly.iteri envs.dtenv ~f:(fun ~key ~data ->
      if LogicOld.Datatype.is_undef data then
        LogicOld.add_dummy_term (*ToDo: unnecessary?*)
          (Ident.Tvar ("dummy_" ^ key))
          (LogicOld.T_dt.SUS (key, LogicOld.Datatype.params_of data)));
  LogicOld.update_dtenv envs.dtenv;
  LogicOld.update_fenv fenv;
  (* Which universals a head existential's witness may see.  The clause's
     universals are in scope at the existential and a witness may in general
     depend on all of them -- without that, an input whose witness must depend
     on one is refuted although it is satisfiable.  But an unknown declared with
     a *dependency set* may see only the universal functions in it, and the
     witness is an element of that unknown's extension, which depends on nothing
     else; so a witness chosen as a function of the dependency set always
     exists, and letting it see more solves the problem with the dependency
     enlarged.  That is a different and weaker problem: its [unsat] still
     transfers back, its [sat] does not.

     Only the universals a dependency set can name are filtered -- the
     Bool-valued universal functions, which is the same set the parser draws a
     default dependency from -- so an ordinary declared variable and a non-Bool
     universal stay available to every witness.  An unknown with no recorded
     dependency set sees everything, which is what it means to have none, so a
     system that declares none is untouched. *)
  let dep_filter =
    let candidates =
      Set.Poly.of_list @@ List.map ~f:fst
      @@ List.filter (Map.Poly.to_alist envs.uni_senv)
           ~f:(fst >> Map.Poly.mem envs.kind_map)
    in
    if Map.Poly.is_empty envs.dep_map || Set.is_empty candidates then
      fun _ args -> args
    else fun pvs args ->
      if Set.is_empty pvs then args
      else
        let allowed =
          Set.Poly.union_list @@ Set.to_list
          @@ Set.Poly.map pvs ~f:(fun pv ->
              match
                Map.Poly.find envs.dep_map (Ident.pvar_to_tvar pv)
              with
              | Some deps -> Set.Poly.of_list @@ List.map deps ~f:fst
              | None -> candidates)
        in
        List.filter args ~f:(fun (x, _) ->
            (not (Set.mem candidates x)) || Set.mem allowed x)
  in
  let fsenvs, phis =
    List.unzip
    @@ List.rev_map phis ~f:(fun phi ->
        let phi =
          LogicOld.Formula.aconv_tvar ~prefix @@ LogicOld.Formula.nnf_of phi
        in
        let phi =
          if !onepoint_constructor_binders then elim_constructor_points phi
          else phi
        in
        let _, fsenv, phi =
          (* the clause's universals -- the free term variables of the assertion,
             among them the array-sorted variable a universally quantified
             function is encoded as and any universal constant -- are in scope at
             every existential in it, so a witness may depend on them and they go
             into the Skolem function's arguments.  Without them the witness is
             forced uniform in the universals: an input whose witness must depend
             on one (pick an element of the universal predicate's extension) is
             then refuted although it is satisfiable. *)
          let uni_senv =
            Map.of_set_exn
            @@ Set.filter ~f:(fst >> Map.Poly.mem exi_senv >> not)
            @@ LogicOld.Formula.term_sort_env_of phi
          in
          (* [only_impure] is the line between the two things an existential
             here can be, and it is not a placeholder.  The formula is in
             negation normal form, so an existential at this point is any
             quantifier that is existential IN EFFECT -- a written [exists] in
             a positive position, and equally a written [forall] in a clause
             BODY, since [(forall y. phi) => H] is [(exists y. not phi) or H].
             When an unknown occurs under it the solver must supply a witness,
             so it is skolemised and the witness becomes a functional predicate
             (an equisatisfiable translation into predicate constraints with
             kinds).  When no unknown occurs under it -- only universal symbols
             and theory atoms -- it is an ordinary quantified CONSTRAINT: the
             constraint language admits it and it is passed to the SMT solver
             as it stands, so skolemising it would invent a witness predicate
             for something no one has to witness.  The two cases are identical
             in the syntax and differ only in what [pvs_of] finds. *)
          LogicOld.Formula.skolemize ~dep_filter ~uni_senv
            ~use_fn_pred:skolem_pred ~only_impure:true phi
        in
        let fsenv = of_old_sort_env_map fsenv in
        let uni_senv =
          let senv =
            Set.filter ~f:(fst >> Map.Poly.mem fsenv >> not)
            @@ Set.filter ~f:(fst >> Map.Poly.mem exi_senv >> not)
            @@ LogicOld.Formula.sort_env_of phi
          in
          try Map.of_set_exn senv
          with e ->
            print_endline
              (LogicOld.str_of_sort_env_list LogicOld.Term.str_of_sort
              @@ Set.to_list senv);
            raise e
        in
        (fsenv, (uni_senv, phi)))
  in
  if false then
    List.iter phis ~f:(fun (_, phi) ->
        print_endline ("phi: " ^ LogicOld.Formula.str_of phi));
  let kind_map =
    Kind.add_kinds
      (Set.Poly.union_list @@ List.map fsenvs ~f:Map.key_set)
      (if skolem_pred then Kind.FN else Kind.IntFun (*ToDo*))
      envs.kind_map
  in
  let params =
    Params.make ~kind_map ~fenv ~dtenv:envs.dtenv
      ~candidate_atoms:envs.candidates
    @@ Map.force_merge_list (exi_senv :: fsenvs)
  in
  (* The datatypes the formulas mention, collected from the formulas as they
     are here rather than from their conversion: [update_params_dtenv] converts
     every formula back to this representation only to collect them, and on a
     generated input of thousands of clauses that conversion and the walk over
     its fresh copies of every datatype took longer than the rest of this
     function.  The conversion keeps every term's sort and every datatype
     symbol, so both collect the same datatypes. *)
  let dtenv =
    Map.force_merge envs.dtenv
    @@ List.fold phis ~init:Map.Poly.empty ~f:(fun ret (_, phi) ->
        LogicOld.DTEnv.force_merge ret (LogicOld.DTEnv.of_formula phi))
  in
  (* one datatype-conversion scope for all the formulas: each datatype is then
     converted once instead of once per occurrence, and the converted formulas
     share the images *)
  let pcsp =
    ExtTerm.with_shared_datatype_conversion @@ fun () ->
    Set.Poly.of_list phis |> of_old_formulas ~params
  in
  update_params pcsp { (params_of pcsp) with dtenv }
(*|> normalize*)

module V = struct
  type t = Ident.tvar option

  let compare v1 v2 =
    match (v1, v2) with
    | None, None -> 0
    | None, Some _ -> 1
    | Some _, None -> -1
    | Some v1, Some v2 -> Ident.tvar_compare v1 v2

  let equal v1 v2 =
    match (v1, v2) with
    | None, None -> true
    | None, Some _ -> false
    | Some _, None -> false
    | Some v1, Some v2 -> Ident.tvar_equal v1 v2

  let hash = Hashtbl.hash
end

module G = Persistent.Digraph.ConcreteBidirectional (V)

module Dot = Graph.Graphviz.Dot (struct
  include G

  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let name_of_false = "__false__"

  let vertex_name = function
    | None -> name_of_false
    | Some v ->
        let name = Ident.name_of_tvar v in
        assert (Stdlib.(name <> name_of_false));
        name

  let vertex_attributes _ = []
  let get_subgraph _ = None
  let default_edge_attributes _ = []
  let edge_attributes _ = []
end)

let dep_graph_of_chc =
  clauses_of
  >> Set.fold ~init:G.empty ~f:(fun g (_, ps, ns, _) ->
      match Set.to_list ps with
      | [] ->
          Set.fold ~init:g ns ~f:(fun g t ->
              let src = Option.return @@ Term.pvar_of_atom t in
              G.add_edge g src None)
      | [ t ] ->
          let des = Option.return @@ Term.pvar_of_atom t in
          Set.fold ~init:g ns ~f:(fun g t ->
              let src = Option.return @@ Term.pvar_of_atom t in
              G.add_edge g src des)
      | _ ->
          (*ToDo*)
          Set.fold ~init:g ps ~f:(fun g t ->
              let des = Option.return @@ Term.pvar_of_atom t in
              Set.fold ~init:g ns ~f:(fun g t ->
                  let src = Option.return @@ Term.pvar_of_atom t in
                  G.add_edge g src des)))

let output_graph = Dot.output_graph

let str_of_graph g =
  let buffer = Format.stdbuf in
  Buffer.clear buffer;
  Dot.fprint_graph Format.str_formatter g;
  Buffer.contents buffer
