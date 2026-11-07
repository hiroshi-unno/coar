open Core
open Common.Ext

(* Refuting a problem that still has unknowns by a clause that mentions none
   of them: the coordinator's [unknown_free_clauses.sweep] (at the start of a
   solve, before the loop) and the preprocessor's
   [unknown_free_clauses.sweep_before_finite_instances] (after predicate
   elimination, before the finite instantiation of quantified sorts, whose
   nested solve can spend a whole run before the outer solve starts).

   Why it is sound.  A problem is satisfiable when every model [M] of the
   background theory admits some interpretation [I] of the unknowns making
   every clause hold.  A clause [C] that mentions no unknown has the same truth
   value under every [I], so if [C] is false in some model [M] -- false for some
   value of its free variables, which a validity question answered [Invalid]
   exhibits -- then no [I] helps in that [M], and the problem is
   unsatisfiable.  That is exactly the argument the zero-unknown verdict rests
   on, applied clause by clause: there, too, an invalid clause refutes.  The
   model Z3 returns is a model of the theory: what the theory leaves open (a
   selector on the wrong constructor, a division by zero, an uninterpreted
   function, the carrier of an uninterpreted sort) it interprets, and every such
   interpretation is one of the models the definition quantifies over, so no
   guard for interpretation-dependent terms is needed HERE -- that guard is for
   steps that read "invalid" as "false in every model", which this does not.
   The clauses are the ones the solve was handed (or the preprocessed ones),
   so a refutation of them is one of the problem exactly when the zero-unknown
   verdict's would be.

   "Mentions no unknown" is decided on every part of the clause, its pure part
   included ([Clause.fvs_of]), against the problem's unknowns ([senv]): a clause
   with an unknown applied only inside its pure part is NOT unknown-free.

   What it cannot do.  Only [Invalid] is read: a clause shown valid, undecided
   or not asked changes nothing, and the loop then runs as without the sweep.
   It asks each such clause once, at a short budget, so it costs at most the
   sweep budget. *)

open Ast

(** [c] mentions no variable of [senv], in its atoms or its pure part *)
let unknown_free (senv : Logic.sort_env_map) (c : Clause.t) =
  Set.for_all (Clause.fvs_of c) ~f:(fun x -> not (Map.Poly.mem senv x))

(** the unknown-free clauses of [clauses] as first-order formulas, each
    read as valid when it holds for every value of its free variables *)
let formulas senv (clauses : ClauseSet.t) =
  let free = Set.filter clauses ~f:(unknown_free senv) in
  if Set.is_empty free then []
  else
    Set.to_list @@ ClauseSetOld.to_formulas
    @@ ClauseSet.to_old_clause_set Map.Poly.empty free

(** [formulas] of a problem in clausal form; of one that is not, the
    constraints that mention no unknown, each closed by its own universal
    variables (no normal form is computed: on the inputs this is for, putting
    the constraints in clausal form is what multiplies them) *)
let formulas_of_problem senv pcsp =
  match PCSP.Problem.clauses_of_opt pcsp with
  | Some clauses -> formulas senv clauses
  | None ->
      Set.to_list (PCSP.Problem.formulas_of pcsp)
      |> List.filter_map ~f:(fun (uni_senv, term) ->
          if
            Set.for_all (Logic.Term.fvs_of term) ~f:(fun x ->
                not (Map.Poly.mem senv x))
          then Some (Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv term)
          else None)

(** the first [(i, piece, model)] for which [ask] answers [`Invalid model]
    about a piece of the [i]-th formula, asking nothing once [expired ()];
    [pieces] splits a formula into pieces each of which it implies (a
    refutation of a piece is one of the formula) *)
let sweep ~pieces ~expired ~ask formulas =
  List.find_mapi formulas ~f:(fun i c ->
      if expired () then None
      else
        List.find_map (pieces c) ~f:(fun p ->
            if expired () then None
            else
              match ask p with
              | `Invalid model -> Some (i, p, model)
              | _ -> None))

(** How one sweep question is asked in this process: [here phi], unless
    [refuse phi], in which case nothing is asked, [on_refused ()] is called and
    the answer is [`Unknown].

    Why a question may be refused.  The caller's [refuse] is the solver
    boundary's shape test for questions the solver may not return from (a
    quantifier binding a sequence: Z3's sequence theory then reads neither its
    timeout nor its resource limit, and an in-process call has stayed open for
    over a minute while the process grew to its memory cap).  A caller that
    asks in a killed copy is bounded by the kill and need not gate.

    Sound for [sweep]: it reads only [`Invalid], and [`Unknown] refutes
    nothing, so a refused question changes the sweep's result only from a
    refutation to none -- the problem then goes on as it was.  Exact on every
    question [refuse] does not hold of: [here] is asked as it would be
    without the gate. *)
let ask_gated ~refuse ~on_refused ~here phi =
  if refuse phi then (
    on_refused ();
    `Unknown "a shape the solver may not return on")
  else here phi
