open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* Witnesses for the existential quantifiers of a refuted clause's negation,
   recorded beside the countermodel of the zero-unknown verdict so that the
   refutation can be checked against the clause as it stands.

   The setting.  A formula with no unknown is refuted by a model [M] of its
   free variables under which some clause [C] of it is false.  When [C] binds
   a sequence, the question "is [not C] true under [M]" is closed but
   quantified, and the solver may decide it neither way; the verdict itself
   may have been reached through an exact rewrite of [C] that removed those
   binders.  Under [M], [not C] in negation normal form is a closed formula
   whose existential quantifiers come from the universal quantifiers of [C].
   Replacing such an existential by a closed term (existential introduction)
   only strengthens it, so if the instantiated formula is true, so is
   [not C].  A checker that is given the terms therefore needs no rewrite to
   be trusted: it substitutes them and asks a question whose remaining
   quantifiers are universal, i.e. existential in its negation, which the
   solver decides after Skolemisation.

   This module only FINDS the terms, and how it finds them is not part of any
   soundness argument: a wrong term makes the check fail to pass, never pass
   wrongly.  It hoists every existential of each conjunct of [not C] under
   [M] out to a free variable of the same name (again a strengthening: one
   value for every choice of the enclosing universals), applies the exact
   one-point / constructor / sequence-length rewrites of
   [Evaluator.elim_onepoint_and_split_binders] to what is left, and reads the
   hoisted variables' values off a model of the result.  On a Rust-derived
   call-site obligation whose clause binds a history sequence universally
   under a pinned tuple, this gives the history ([0, 1, 2]) at once, where the
   unrewritten question was undecided at 10 s. *)

(** The free variables of [model] -- a conjunction of equations [x = t] with [t]
    closed -- as a substitution, keeping each variable's sort. *)
let assignment_of model =
  List.fold (Formula.conjuncts_list_of model) ~init:Map.Poly.empty
    ~f:(fun acc -> function
    | Formula.Atom
        (Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, s, _); t ], _), _)
      when Set.is_empty (Term.tvs_of t) && not (Map.Poly.mem acc x) ->
        Map.Poly.set acc ~key:x ~data:(s, t)
    | _ -> acc)

(** [c] under [asg] when every free variable of [c] is assigned at the sort [c]
    uses it at; [None] otherwise. The sort test matters: the clauses of one
    problem name their variables [x0], [x1], ... each on its own, so one name
    can stand for variables of different sorts in different clauses. *)
let ground_clause asg c =
  let env = Formula.term_sort_env_of c in
  if
    Set.for_all env ~f:(fun (x, s) ->
        match Map.Poly.find asg x with
        | Some (s', _) -> Stdlib.(s = s')
        | None -> false)
  then
    Some
      (Formula.subst
         (Map.Poly.of_alist_exn
         @@ List.map (Set.to_list env) ~f:(fun (x, _) ->
             (x, snd @@ Map.Poly.find_exn asg x)))
         c)
  else None

(* every existential of [phi] (in negation normal form) opened to a free
   variable of its own name, with the names and sorts opened *)
let rec hoist opened = function
  | Formula.Bind (Formula.Exists, senv, body, _) ->
      opened := senv @ !opened;
      hoist opened body
  | Formula.Bind (b, senv, body, _) ->
      Formula.mk_bind b senv (hoist opened body)
  | Formula.BinaryOp (op, p, q, _) ->
      Formula.mk_binop op (hoist opened p) (hoist opened q)
  | phi -> phi

(** Witness terms [(x, sort, t)] for existential binders [x] of the negation of
    a clause of [formula] that [model] falsifies, found as described above, or
    [[]]. Each solver question carries [timeout]. *)
let find ~timeout formula model =
  let asg = assignment_of model in
  if Map.Poly.is_empty asg then []
  else
    let fenv = get_fenv () in
    List.find_map (Formula.conjuncts_list_of formula) ~f:(fun c ->
        match ground_clause asg c with
        | None -> None
        | Some c -> (
            match Formula.nnf_of (Formula.negate c) with
            | exception exn when not (Common.Timer.is_async exn) -> None
            | neg ->
                let ws =
                  List.map (Formula.conjuncts_list_of neg) ~f:(fun d ->
                      let opened = ref [] in
                      let h = hoist opened d in
                      if List.is_empty !opened then Some []
                      else
                        let h = Evaluator.elim_onepoint_and_split_binders h in
                        match
                          Z3Smt.Z3interface.check_sat ~timeout
                            ~fresh_solver:true ~id:None
                            (Z3Smt.Z3interface.fenv_reached_by fenv h)
                            [ Formula.nnf_of h ]
                        with
                        | `Sat m ->
                            Some
                              (List.filter_map !opened ~f:(fun (x, s) ->
                                   List.find_map m ~f:(fun ((y, _), t) ->
                                       match t with
                                       | Some t
                                         when Ident.tvar_equal x y
                                              && Set.is_empty (Term.tvs_of t) ->
                                           Some (x, s, t)
                                       | _ -> None)))
                        | _ -> None
                        | exception exn when not (Common.Timer.is_async exn) ->
                            None)
                in
                (* a clause is used only when every conjunct that binds
                   something got its terms *)
                if List.for_all ws ~f:Option.is_some then
                  match List.concat (List.filter_map ws ~f:Fn.id) with
                  | [] -> None
                  | ws -> Some ws
                else None))
    |> Option.value ~default:[]
