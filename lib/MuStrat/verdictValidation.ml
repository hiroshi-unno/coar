(* Translation validation of a strategy check's verdict.

   A verdict of the strategy check is a fact about the check object this
   solver builds (a set of constraint formulas over predicate unknowns): a win
   is the check's satisfiability, a refutation its unsatisfiability.  Between
   that object and the CHC backend's answer lie rewrites this solver does not
   prove correct -- the constraint problem's normalisation and simplification,
   negation and clausal normal forms, let elimination, the backend's encoding
   and the decoding of its answer.  Instead of trusting them, each verdict is
   checked here against the check object itself, from the certificate the
   backend returns:

   - a win, from the backend's solution: every formula of the check, with the
     solution substituted, must be valid ([solution_validates]);
   - a refutation, from the backend's derivation: every derived atom must be
     forced by one formula of the check from the atoms derived beneath it, and
     the atoms at the top must contradict one formula ([refutation_validates]);
   - a rewrite of the input applied before the reduction, as a pair
     (before, after) that must be equivalent with every predicate read as an
     uninterpreted relation ([equivalent]).

   Each question goes to Z3 on the formula's direct encoding (no simplifier,
   no normaliser, no clausal form) after the one rewrite
   [Logic.select_constant_cases], which is exact by the definition of [case].
   So what a validated verdict still trusts is the conversion between the two
   term representations, substitution, the Z3 encoding, and Z3's answer to a
   (usually quantifier-free) question; the CHC backend and the rewrites listed
   above are no longer on the verdict's path.  Every function answers [Ok ()]
   only when each question was answered as required, and [Error reason]
   otherwise (a counter-model, Z3's unknown or timeout, or a shape this module
   does not read); [Error] claims nothing about the verdict. *)

open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* [`Sat], [`Unsat] or [`Other reason] for the conjunction of [phis], their
   predicate variables read as uninterpreted relations and their free term
   variables as constants, asked of a fresh Z3 context within [timeout_ms].  A
   shape on which Z3 may not return is not asked. *)
let ask ~timeout_ms phis =
  if List.exists phis ~f:Z3Smt.Z3interface.may_not_return then
    `Other "a question Z3 may not return on"
  else
    match
      Z3Smt.Z3interface.check_sat_with_preds ~timeout:(Some timeout_ms) ~id:None
        (get_fenv ()) phis
    with
    | `Sat -> `Sat
    | `Unsat -> `Unsat
    | `Unknown -> `Other "Z3 answered unknown or ran out of its budget"

let valid ~timeout_ms phi =
  match ask ~timeout_ms [ Formula.mk_neg phi ] with
  | `Unsat -> Ok ()
  | `Sat -> Error "a counter-model exists"
  | `Other r -> Error r

(* [Ok ()] when [before] and [after] are equivalent: no assignment of their
   free term variables and interpretation of their predicate variables makes
   one true and the other false.  Universal closure of an equivalence implies
   the equivalence of the closures, so a rewrite of a closed formula, or of a
   body read under the same parameters, is validated by this question. *)
let equivalent ~timeout_ms before after =
  (* asked as two implications: each negated implication is a conjunction,
     whose quantifiers Z3 can skolemise or instantiate on one polarity each,
     where the negated equivalence puts every quantifier under both *)
  match valid ~timeout_ms (Formula.mk_imply before after) with
  | Error r -> Error ("before => after: " ^ r)
  | Ok () -> (
      match valid ~timeout_ms (Formula.mk_imply after before) with
      | Error r -> Error ("after => before: " ^ r)
      | Ok () -> Ok ())

(* [equivalent_pairs ~timeout_ms pairs]: the first pair not shown equivalent,
   with its index, or [Ok ()]. *)
let equivalent_pairs ~timeout_ms pairs =
  List.foldi pairs ~init:(Ok ()) ~f:(fun i acc (before, after) ->
      match acc with
      | Error _ -> acc
      | Ok () -> (
          if phys_equal before after then Ok ()
          else
            match equivalent ~timeout_ms before after with
            | Ok () -> Ok ()
            | Error r ->
                Error
                  (sprintf "rewrite %d (%s  ~>  %s): %s" i
                     (Formula.str_of before) (Formula.str_of after) r)))

(* The unknowns of [chc]: its existential environment, read as predicate
   variables (an unknown that is not a predicate never occurs as a predicate
   application). *)
let unknowns_of chc =
  Set.Poly.map ~f:Ident.tvar_to_pvar @@ Map.key_set (PCSP.Problem.senv_of chc)

(* [Ok ()] when every unknown of [chc] has the ordinary kind: then any
   interpretation of the unknowns is admissible, which the two certificates
   below rely on (a solution is admissible whatever it is; a derivation reasons
   about arbitrary sets of atoms). *)
let all_ordinary chc =
  let kinds = PCSP.Problem.kind_map_of chc in
  match
    Map.Poly.fold (PCSP.Problem.senv_of chc) ~init:None
      ~f:(fun ~key ~data:_ acc ->
        match acc with
        | Some _ -> acc
        | None -> (
            match Map.Poly.find kinds key with
            | Some k when not (Kind.is_ord k) -> Some key
            | _ -> None))
  with
  | None -> Ok ()
  | Some x ->
      Error
        (sprintf "unknown %s is not of the ordinary kind" (Ident.name_of_tvar x))

(* Validating a win.

   Precondition: [sol] maps unknowns of [chc] to closed lambda terms.
   [Ok ()] means: for every formula [phi] of [chc] (stable clauses included),
   [phi] with [sol] substituted and beta-reduced is valid, an unknown [sol]
   leaves out being read as an arbitrary relation (so validity holds for every
   interpretation of it, the one picked by [sol] among them).  With every
   unknown ordinary, [sol] extended by any interpretation is then a solution of
   [chc], so [chc] is satisfiable: the win is a property of the check object,
   whatever rewrites the backend applied before finding [sol]. *)
let solution_validates ~timeout_ms chc sol =
  let open Result.Monad_infix in
  all_ordinary chc >>= fun () ->
  if Map.Poly.is_empty sol then Error "no solution to validate"
  else
    let exi_senv = PCSP.Problem.senv_of chc in
    Set.fold_until
      (PCSP.Problem.formulas_of chc)
      ~init:()
      ~finish:(fun () -> Ok ())
      ~f:(fun () (uni_senv, phi) ->
        match
          let phi' = Logic.select_constant_cases @@ Logic.Term.subst sol phi in
          Logic.ExtTerm.to_old_fml exi_senv uni_senv phi'
        with
        | exception exn when not (Common.Timer.is_async exn) ->
            Stop (Error ("cannot convert a formula: " ^ Exn.to_string exn))
        | fml -> (
            match valid ~timeout_ms fml with
            | Ok () -> Continue ()
            | Error r ->
                Stop
                  (Error
                     (sprintf "%s under the solution: %s" (Formula.str_of fml) r))
            ))

(* Refuting a win's certificate: the cheap half of [solution_validates], kept
   on whether or not verdicts are validated.

   A CHC backend's win comes with a solution, its certificate; the backend's
   verdict is believed without it, so a backend that answers the check
   satisfiable with a solution that is not one has answered wrongly, and
   nothing else on the way to a verdict notices.  Spacer (Z3 5.1.0) has been
   seen doing exactly that on a strategy check: the query declared
   unreachable, and the answer -- read straight from Z3, before any decoding
   of this tree -- violating one rule at a concrete point, so the run
   answered the negation of the input's truth.

   Contract.  [solution_refuted ~timeout_ms chc sol] is [Some reason] only
   when some formula [phi] of [chc], with [sol] substituted and beta-reduced,
   mentions no unknown of [chc] and Z3 finds a model of its negation (a
   counter-model: an assignment of [phi]'s free term variables making it
   false).  Then [sol] is not a solution of [chc], whatever kinds its unknowns
   have.  [None] claims nothing: every formula held, or was not refuted
   because Z3 answered unknown within [timeout_ms], because the formula still
   mentions an unknown [sol] leaves out (another interpretation of it may
   satisfy the formula), because a conversion failed, or because [sol] is
   empty (a verdict-only answer, which carries no certificate).  So a caller
   that discards a win only on [Some] loses no win whose certificate is
   correct, and keeps every win it kept before when the certificate cannot be
   checked.  Each formula is asked at most once, within [timeout_ms]; the
   search stops at the first counter-model. *)
let solution_refuted ~timeout_ms chc sol =
  if Map.Poly.is_empty sol then None
  else
    let exi_senv = PCSP.Problem.senv_of chc in
    let unknowns = unknowns_of chc in
    Set.find_map (PCSP.Problem.formulas_of chc) ~f:(fun (uni_senv, phi) ->
        match
          let phi' = Logic.select_constant_cases @@ Logic.Term.subst sol phi in
          Logic.ExtTerm.to_old_fml exi_senv uni_senv phi'
        with
        | exception exn when not (Common.Timer.is_async exn) -> None
        | fml -> (
            if Set.exists (Formula.pvs_of fml) ~f:(Set.mem unknowns) then None
            else
              match ask ~timeout_ms [ Formula.mk_neg fml ] with
              | `Sat ->
                  Some
                    (sprintf "%s under the solution: a counter-model exists"
                       (Formula.str_of fml))
              | `Unsat | `Other _ -> None))

(* Validating a refutation.

   A derivation node is a derived atom [pvar(args)], [args] ground, with the
   nodes it was derived from. *)
type node = { pvar : Ident.pvar; args : Term.t list; children : node list }

exception Reject of string

(* A table keyed by a derivation node compared physically, hashed on its
   predicate and its first argument nodes (consistent with physical
   equality, and distinct nodes with one atom are told apart by identity). *)
module NodeTbl = Stdlib.Hashtbl.Make (struct
  type t = node

  let equal = phys_equal
  let hash n = Stdlib.Hashtbl.hash_param 20 100 (n.pvar, n.args)
end)

(* [walk_distinct ~visit roots]: [visit n] for each node of the derivation
   [roots] in post-order (a node's children left to right before the node,
   the roots left to right), skipping a node physically met before, and
   stopping at the first [Error] (an exception raised by [visit] passes
   through).  A derivation shares a node used by several parents, and its
   unfolding as a tree can be exponentially larger than its distinct nodes.
   Post: the calls made are those of the per-path post-order walk with every
   repeated occurrence of a node (and its subtree) dropped, and the result is
   the per-path walk's whenever [visit] answers [Ok ()] with no further effect
   on a node it has already answered [Ok ()] for: a repeated occurrence's
   subtree was then walked to the end with [Ok ()], so walking it again
   changes nothing. *)
let walk_distinct ~visit roots =
  let open Result.Monad_infix in
  let seen = NodeTbl.create 256 in
  let rec node n =
    if NodeTbl.mem seen n then Ok ()
    else
      List.fold n.children ~init:(Ok ()) ~f:(fun acc c ->
          acc >>= fun () -> node c)
      >>= fun () ->
      visit n >>| fun () -> NodeTbl.replace seen n ()
  in
  List.fold roots ~init:(Ok ()) ~f:(fun acc n -> acc >>= fun () -> node n)

(* [mixed_point ~unknowns ~pos ~neg phi]: [phi] with every occurrence of an
   unknown [Q(t)] replaced by [pos Q t] where it occurs positively and by
   [neg Q t] where it occurs negatively.  Raises [Reject] when an unknown
   occurs where its polarity is not determined -- under [<=>] or [xor], inside
   a term, a let definition, a recursive definition or a random binder -- or
   with arguments that mention an unknown. *)
let mixed_point ~unknowns ~pos ~neg phi =
  let mentions f = Set.exists (Formula.pvs_of f) ~f:(Set.mem unknowns) in
  let rec go positive phi =
    match phi with
    | Formula.Atom (Atom.App (Predicate.Var (q, _), args, _), _)
      when Set.mem unknowns q ->
        if
          List.exists args ~f:(fun t ->
              Set.exists (Term.pvs_of t) ~f:(Set.mem unknowns))
        then raise (Reject "an unknown inside the arguments of an unknown")
        else if positive then pos q args
        else neg q args
    | Formula.Atom _ ->
        if mentions phi then raise (Reject "an unknown inside an atom's terms")
        else phi
    | Formula.UnaryOp (Formula.Not, f, _) ->
        Formula.mk_neg (go (not positive) f)
    | Formula.BinaryOp (Formula.And, a, b, _) ->
        Formula.mk_and (go positive a) (go positive b)
    | Formula.BinaryOp (Formula.Or, a, b, _) ->
        Formula.mk_or (go positive a) (go positive b)
    | Formula.BinaryOp (Formula.Imply, a, b, _) ->
        Formula.mk_imply (go (not positive) a) (go positive b)
    | Formula.Bind (((Formula.Forall | Formula.Exists) as b), senv, f, _) ->
        Formula.mk_bind b senv (go positive f)
    | Formula.BinaryOp ((Formula.Iff | Formula.Xor), _, _, _)
    | Formula.Bind (Formula.Random _, _, _, _)
    | Formula.LetRec _ | Formula.LetFormula _ ->
        if mentions phi then
          raise (Reject "an unknown at a position of no single polarity")
        else phi
  in
  go true phi

(* [phi] with its free term variables bound existentially. *)
let existential_closure phi =
  let free = Formula.tvs_of phi in
  Formula.term_sort_env_of phi
  |> Set.to_list
  |> List.filter ~f:(fst >> Set.mem free)
  |> List.dedup_and_sort ~compare:(fun (x, _) (y, _) -> Ident.tvar_compare x y)
  |> fun senv -> Formula.exists senv phi

let args_equal ts vs =
  if List.length ts <> List.length vs then raise (Reject "an arity mismatch")
  else Formula.and_of (List.map2_exn ts vs ~f:Formula.eq)

(* [forced_by ~unknowns ~head ~below phi]: the formula whose satisfiability
   shows that every set of atoms [K] containing [below] and not containing
   [head] falsifies [phi] for some values of its variables ([head = None]: any
   [K] containing [below]).  A positive occurrence [Q(t)] becomes "[Q(t)] is
   not [head]" (true for [Q] other than [head]'s predicate), a negative one
   becomes "[Q(t)] is one of [below]".  [phi] is monotone in its positive
   occurrences and antitone in its negative ones, so under such a [K] it
   implies the result; a model of the result's negation falsifies [phi]
   under [K]. *)
let forced_by ~unknowns ~head ~below phi =
  let pos q ts =
    match head with
    | Some (p, vs) when Stdlib.( = ) p q -> Formula.mk_neg (args_equal ts vs)
    | _ -> Formula.mk_true ()
  in
  let neg q ts =
    Formula.or_of
    @@ List.filter_map below ~f:(fun (p, vs) ->
        if Stdlib.( = ) p q then Some (args_equal ts vs) else None)
  in
  mixed_point ~unknowns ~pos ~neg phi

(* Precondition: [roots] are the topmost derived atoms of a derivation the
   backend returned for [chc].
   [Ok ()] means, for [chc]'s formulas read with their free variables
   universally closed: each node's atom is in every model of [chc] that holds
   the atoms of its children (some formula of [chc] is falsified by every set
   of atoms holding the children and not the node's atom), and some formula
   of [chc] is falsified by every set holding the roots.  By induction from
   the leaves every model holds every node, so [chc] has no model: the
   refutation is a property of the check object.  An unknown that is not
   ordinary, a non-ground argument, or a formula whose unknowns' polarity is
   not determined is an [Error]. *)
let refutation_validates ~timeout_ms chc roots =
  let open Result.Monad_infix in
  all_ordinary chc >>= fun () ->
  let unknowns = unknowns_of chc in
  let exi_senv = PCSP.Problem.senv_of chc in
  match
    Set.Poly.map (PCSP.Problem.formulas_of chc) ~f:(fun (uni_senv, phi) ->
        Logic.ExtTerm.to_old_fml exi_senv uni_senv
          (Logic.select_constant_cases phi))
    |> Set.to_list
  with
  | exception exn when not (Common.Timer.is_async exn) ->
      Error ("cannot convert a formula: " ^ Exn.to_string exn)
  | fmls -> (
      let polarities =
        List.map fmls ~f:(fun phi ->
            let ps = ref Set.Poly.empty and ns = ref Set.Poly.empty in
            (try
               ignore
                 (mixed_point ~unknowns
                    ~pos:(fun q _ ->
                      ps := Set.add !ps q;
                      Formula.mk_true ())
                    ~neg:(fun q _ ->
                      ns := Set.add !ns q;
                      Formula.mk_true ())
                    phi)
             with Reject _ -> ());
            (phi, !ps, !ns))
      in
      let decided = Hashtbl.Poly.create () in
      let witnesses = ref [] in
      (* one step: [head] forced from [below] by some formula; the formulas
         that can match it structurally (the head's predicate occurs
         positively, every negative unknown is among [below]'s) are asked
         first, then the others *)
      let step head below =
        let key =
          ( Option.map head ~f:(fun (p, vs) -> (p, List.map vs ~f:Term.str_of)),
            List.sort ~compare:Stdlib.compare
              (List.map below ~f:(fun (p, vs) ->
                   (p, List.map vs ~f:Term.str_of))) )
        in
        if Hashtbl.mem decided key then Ok ()
        else
          let below_ps = Set.Poly.of_list (List.map below ~f:fst) in
          let fits (_, ps, ns) =
            Set.is_subset ns ~of_:below_ps
            && match head with Some (p, _) -> Set.mem ps p | None -> true
          in
          (* Only a formula that can match is asked: one with a negative
             unknown outside [below] has that occurrence read as false, and
             one without a positive occurrence of the head's predicate can
             force the head only by contradicting [below] outright, which the
             root step asks.  Leaving the others out loses no soundness (each
             question is still a proof); it saves questions that seldom
             succeed, each a fresh solver context, at every node of a long
             derivation. *)
          let candidates = List.filter polarities ~f:fits in
          let reasons = ref [] in
          let found =
            List.find_map candidates ~f:(fun (phi, _, _) ->
                match forced_by ~unknowns ~head ~below phi with
                | exception Reject r ->
                    reasons := r :: !reasons;
                    None
                | phi_m -> (
                    let q = Formula.mk_neg phi_m in
                    match ask ~timeout_ms [ q ] with
                    | `Sat -> Some q
                    | `Unsat -> None
                    | `Other r ->
                        reasons := r :: !reasons;
                        None))
          in
          match found with
          | Some q ->
              Hashtbl.set decided ~key ~data:();
              witnesses := existential_closure q :: !witnesses;
              Ok ()
          | None ->
              Error
                (sprintf "no formula forces %s%s"
                   (match head with
                   | Some (p, vs) ->
                       sprintf "%s(%s)" (Ident.name_of_pvar p)
                         (String.concat_map_list ~sep:"," vs ~f:Term.str_of)
                   | None -> "a contradiction")
                   (match !reasons with
                   | [] -> ""
                   | r :: _ -> " (one formula: " ^ r ^ ")"))
      in
      let atom_of n =
        if not (Set.mem unknowns n.pvar) then
          raise
            (Reject
               (sprintf "a derived atom of %s, not an unknown of the check"
                  (Ident.name_of_pvar n.pvar)))
        else if
          List.exists n.args ~f:(fun t -> not (Set.is_empty (Term.fvs_of t)))
        then raise (Reject "a derived atom with a non-ground argument")
        else (n.pvar, n.args)
      in
      (* Each distinct node is visited once ([walk_distinct]): visiting a
         node again would read the same atoms (no raise, since the first
         visit did not) and ask a step [decided] already holds, which answers
         [Ok ()] and records nothing, so the result is the per-path walk's. *)
      try
        walk_distinct roots ~visit:(fun n ->
            step (Some (atom_of n)) (List.map n.children ~f:atom_of))
        >>= fun () ->
        step None (List.map roots ~f:atom_of) >>= fun () ->
        (* The steps were each shown in some model of the background theory;
           the induction needs them in one, which differs from "each in its
           own" only where a formula has an interpretation-dependent term
           (a division by zero, a selector off its constructor, an
           uninterpreted function).  Their conjunction, each step closed
           existentially so their variables stay apart, is asked once. *)
        match ask ~timeout_ms [ Formula.and_of !witnesses ] with
        | `Sat -> Ok ()
        | `Unsat -> Error "the steps hold in no common model"
        | `Other r -> Error ("the joint question: " ^ r)
      with Reject r -> Error r)
