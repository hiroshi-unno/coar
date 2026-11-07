(* The certificate behind a MuVal verdict, written after the verdict line for
   a consumer that builds a correctness witness from it (an SV-COMP YAML
   witness: loop invariants, and loop transition invariants for termination).

   What is written is about the muCLP problem MuVal received, in its own
   predicate and parameter names, never about the problem MuVal's optimizer
   made of it:

   - an invariant per predicate of the received problem: a formula over that
     predicate's parameters.  It is read off the constraint solver's solution
     of the optimized problem and carried back through the optimizer: a
     parameter the optimizer removed because every application passes it one
     constant comes back as [parameter = constant]; a parameter removed as
     irrelevant is simply not mentioned; a predicate the optimizer removed
     (inlined, left unreached), or one the constraint solver resolved away
     without a definition in its solution, gets its own body with the other
     predicates' invariants substituted, which is exact for an equation that holds as an
     identity at the fixpoint.  The assignment is then checked as a whole
     (unless the configuration declines): every invariant implies its
     predicate's body under the assignment, and the query holds under it,
     each a validity question to Z3.  Passing makes the assignment a
     post-fixpoint of the received problem read with every predicate as a
     greatest fixpoint, which contains the query's states and is closed under
     the bodies: every state reachable at a predicate satisfies its
     invariant.  A failed or undecided check withholds every invariant: one
     member of an assignment that is not closed proves nothing about
     reachable states.
   - a ranking per least-fixpoint predicate, from the certificate PCSat's
     well-founded template records (pieces, each a discriminator and a
     lexicographic tuple, over the predicate's parameters), and the decrease
     relation it induces between an earlier and a later visit.  The relation
     is transitive (a lexicographic decrease with negative components read as
     undefined composes, and so does the piecewise one), so it holds between
     ANY two visits exactly when every return of the predicate to itself
     passes through its well-foundedness guard; the reduction guarantees that
     for the returns that avoid every predicate listed before it, so a
     ranking is written as a transition invariant only when no predicate on a
     cycle with it comes earlier in the reduced problem's order.
   - a [skipped] line with a reason for anything that could not be written:
     nothing is dropped silently.

   Only the side that decided the verdict is written: the primal's solution
   for a valid query; for an invalid one, nothing but the reason.

   The line format (one S-expression per line, SMT-LIB terms inside):
     (certificate-format 1)
     (side primal|primal-ad|dual|ground)
     (invariant P ((x Int) ..) FORMULA (kind nu|mu|fix) (erased (x 5) ..) (status STATUS))
     (ranking P ((x Int) ..) (pieces (piece DISC (R1 R2 ..)) ..)
        (transition ((x__prev Int) ..) RELATION) (status STATUS))
     (skipped P REASON "detail")
   where STATUS is [inductive] (the whole assignment passed the check),
   [unchecked] (the configuration declined the check, or an invariant has a
   free variable that is not a parameter, so the check was not made), or for a ranking
   [direct-returns-checked] / [unchecked].  A name is written as an SMT-LIB
   symbol, quoted with bars when it is not a simple one. *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

type side = Witness.side = Primal | Primal_ad | Dual | Ground

(* What the side that answered leaves for the certificate.  [solved] is the
   problem the reduction received (after the optimizer and the
   skolemisation); [solution] maps each unknown of the reduced constraint
   problem to its lambda; [kind_certs] the ranking certificates PCSat recorded
   for its well-founded unknowns; [extended] the argument positions the
   reduction prepended to a predicate (absent: none). *)
type evidence = {
  side : side;
  solved : MuCLP.Problem.t option;
  solution : PCSP.Problem.solution option;
  kind_certs : (Ident.tvar, PCSatCommon.KindCert.t) Map.Poly.t;
  extended : (Ident.pvar, MuCLP.Reducer.prefix_entry list) Hashtbl.Poly.t;
  wf_reduction : bool;
}

(* -- From the solution to formulas ---------------------------------------- *)

(* [lambda_of sol key]: the parameters and the body of [key]'s solution, as an
   old formula over fresh parameter names ([None] when [sol] has no entry). *)
let lambda_of (sol : Logic.term_subst_map) key =
  match Map.Poly.find sol key with
  | None -> None
  | Some data ->
      let args, term = Logic.ExtTerm.let_lam data in
      let senv = Map.Poly.of_alist_exn args in
      let phi = Logic.ExtTerm.to_old_formula Map.Poly.empty senv term [] in
      Some
        ( List.map args ~f:(fun (x, s) -> (x, Logic.ExtTerm.to_old_sort s)),
          phi )

(* [instantiate params phi actuals]: [phi] with each parameter replaced by the
   corresponding actual term (simultaneous and capture-avoiding).  Requires
   the two lists to have one length. *)
let instantiate params phi actuals =
  Formula.subst
    (Map.Poly.of_alist_exn
    @@ List.map2_exn params actuals ~f:(fun (x, _) t -> (x, t)))
    phi

let var_terms = List.map ~f:(fun (x, s) -> Term.mk_var x s)

(* -- Reconstruction over the received problem ----------------------------- *)

type outcome = Formula of Formula.t | Skip of string * string

(* [invariants ~erased received evidence]: per predicate of [received], its
   invariant over its own parameters, or why there is none.  [erased] lists
   the argument positions the optimizer removed as constant.  The order of
   [received.preds] is kept. *)
let invariants ?read ?max_nodes ~erased (received : MuCLP.Problem.t)
    (ev : evidence) =
  let sol =
    match ev.solution with Some (PCSP.Problem.Sat sol) -> sol | _ -> Map.Poly.empty
  in
  (* the solution of a solved predicate: its parameters and its formula over
     them, by default read off the constraint solver's solution *)
  let read =
    match read with
    | Some read -> read
    | None ->
        fun (q : MuCLP.Pred.t) ->
          lambda_of sol (Ident.pvar_to_tvar (Ident.uninterp_pvar q.name))
  in
  let solved_preds =
    match ev.solved with Some m -> m.MuCLP.Problem.preds | None -> []
  in
  let erased_of name =
    List.filter_map erased ~f:(fun (p, x, c) ->
        if Ident.pvar_equal p name then Some (x, c) else None)
  in
  (* the invariant read off the solution of the solved problem's [name], over
     [params] (the received predicate's parameters) *)
  let from_solution (pred : MuCLP.Pred.t) =
    match
      List.find solved_preds ~f:(fun (q : MuCLP.Pred.t) ->
          Ident.pvar_equal q.name pred.name)
    with
    | None -> None
    | Some q -> (
        let prefix =
          Option.value ~default:[]
            (Hashtbl.Poly.find ev.extended q.name)
        in
        match read q with
        | None ->
            (* the constraint solver resolved the predicate away without
               recording a definition: reconstructed from its body like a
               predicate the optimizer removed *)
            None
        | Some (lparams, body) ->
            let n_prefix = List.length prefix in
            if List.length lparams <> n_prefix + List.length q.args then
              Some
                (Skip
                   ( "arity-mismatch",
                     sprintf "the solution takes %d arguments, the predicate %d (+%d prepended)"
                       (List.length lparams) (List.length q.args) n_prefix ))
            else
              let prefix_params, own_params = List.split_n lparams n_prefix in
              (* each solved parameter must be one of the received ones, by name *)
              let missing =
                List.filter q.args ~f:(fun (x, _) ->
                    not (List.exists pred.args ~f:(fun (y, _) -> Ident.tvar_equal x y)))
              in
              if not (List.is_empty missing) then
                Some
                  (Skip
                     ( "renamed",
                       sprintf "the solved predicate has parameters the received one lacks: %s"
                         (String.concat_map_list ~sep:" " missing ~f:(fun (Ident.Tvar x, _) -> x)) ))
              else
                let phi = instantiate own_params body (var_terms q.args) in
                (* a prefix the reduction prepended is projected away: the
                   invariant at the predicate's own arguments is that some
                   prefix makes the solution hold *)
                let phi =
                  if List.is_empty prefix_params then phi
                  else
                    let fresh =
                      mk_fresh_sort_env_list (List.map prefix_params ~f:snd)
                    in
                    Formula.exists fresh
                      (instantiate prefix_params phi (var_terms fresh))
                in
                let consts =
                  List.filter_map (erased_of pred.name) ~f:(fun (x, c) ->
                      match List.Assoc.find pred.args ~equal:Ident.tvar_equal x with
                      | Some s -> Some (Formula.eq (Term.mk_var x s) c)
                      | None -> None)
                in
                Some (Formula (Formula.and_of (phi :: consts))))
  in
  let table : (Ident.pvar, outcome) Hashtbl.Poly.t = Hashtbl.Poly.create () in
  let rec get visiting (pred : MuCLP.Pred.t) =
    match Hashtbl.Poly.find table pred.name with
    | Some o -> o
    | None ->
        let o =
          match from_solution pred with
          | Some o -> o
          | None ->
              if Set.mem visiting pred.name then
                Skip
                  ( "not-reconstructible",
                    "removed by the optimizer and recursive through itself" )
              else unfold (Set.add visiting pred.name) pred
        in
        if not (Set.mem visiting pred.name) || (match o with Formula _ -> true | _ -> false)
        then Hashtbl.Poly.set table ~key:pred.name ~data:o;
        o
  (* a predicate the optimizer removed: its body with the other predicates'
     invariants substituted *)
  and unfold visiting (pred : MuCLP.Pred.t) =
    let callees = Set.to_list (Formula.pvs_of pred.body) in
    let rec go acc = function
      | [] -> (
          (* each unfolding copies its callees' invariants, so along a chain
             of removed predicates the size multiplies: a ground answer's
             invariants (disjunctions of states) once filled 10 GB this way
             on a product of two threads *)
          let nodes () =
            List.fold acc ~init:(Formula.ast_size pred.body)
              ~f:(fun n (_, (_, phi)) -> n + Formula.ast_size phi)
          in
          match max_nodes with
          | Some limit when nodes () > limit ->
              Skip
                ( "too-large",
                  sprintf
                    "removed by the optimizer; its body with its callees' \
                     invariants would exceed %d formula nodes"
                    limit )
          | _ -> (
              try
                Formula
                  (Formula.subst_preds (Map.Poly.of_alist_exn acc) pred.body)
              with exn_ when not (Common.Timer.is_async exn_) ->
                Skip ("not-reconstructible", Exn.to_string exn_)))
      | q :: rest -> (
          match
            List.find received.preds ~f:(fun (r : MuCLP.Pred.t) ->
                Ident.pvar_equal r.name q)
          with
          | None -> go acc rest
          | Some r -> (
              match get visiting r with
              | Formula phi -> go ((q, (r.args, phi)) :: acc) rest
              | Skip (_, why) ->
                  Skip
                    ( "not-reconstructible",
                      sprintf "removed by the optimizer; its body calls %s: %s"
                        (Ident.name_of_pvar q) why )))
    in
    go [] callees
  in
  List.map received.preds ~f:(fun pred -> (pred, get Set.Poly.empty pred))

(* the budget of one validity question of [check]; the obligations of the
   problems LLVMFront builds for small loops are decided in milliseconds *)
let check_timeout_ms = 10_000

(* [open_invariant invs]: the first predicate whose invariant has a free term
   variable that is not one of its parameters, with those variables. *)
let open_invariant invs =
  List.find_map invs ~f:(fun ((p : MuCLP.Pred.t), phi) ->
      let extra =
        Set.diff (Formula.tvs_of phi) (Set.Poly.of_list (List.map p.args ~f:fst))
      in
      if Set.is_empty extra then None else Some (p, Set.to_list extra))

(* [check ~id received invs]: whether the assignment [invs] (every predicate
   of [received] mapped to a formula) is a post-fixpoint of [received] read
   with greatest fixpoints and makes the query valid.  [Error (`Failed why)]
   names the first obligation Z3 refuted, [Error (`Undecided why)] the first
   it left undecided (not asked, out of budget); [Error (`Open why)]
   says the check was not made.

   Requires nothing of [invs]; guarantees that [Ok ()] is returned only when
   every invariant's free term variables are among its predicate's
   parameters.  An invariant is printed over its parameters alone, and the
   obligations are validity questions, which read a free variable as
   universally quantified over the whole obligation: a name outside the
   parameters would be shared between the invariants of one obligation and
   with the variables of the body it is substituted into, so obligations
   that are all valid say nothing about the formula as printed.  For example
   [P(x) =nu x <= 1] with the query [P(0) \/ P(1)] and the invariant
   [(x = 0 /\ y >= 0) \/ (x = 1 /\ y < 0)] makes every obligation valid,
   while the invariant read with [y] standing for any value is [false].  No
   producer in this module emits such an invariant (the constraint solver's
   lambdas are closed and a removed predicate's body mentions only its
   parameters), so the guard costs no certificate. *)
let check ~id (received : MuCLP.Problem.t) invs =
  match open_invariant invs with
  | Some (p, xs) ->
      Error
        (`Open
          (sprintf "the invariant of %s has a free variable that is not a parameter: %s"
             (Ident.name_of_pvar p.name)
             (String.concat_map_list ~sep:" " xs ~f:Ident.name_of_tvar)))
  | None ->
  let psub =
    Map.Poly.of_alist_exn
    @@ List.map invs ~f:(fun ((p : MuCLP.Pred.t), phi) -> (p.name, (p.args, phi)))
  in
  let fenv = LogicOld.get_fenv () in
  (* a query whose shape may keep Z3 from returning (quantifiers it cannot
     instantiate finitely, regular expressions) is not asked: it counts as
     undecided, which withholds the invariants and costs no answer, since the
     verdict is already printed.  The others get [check_timeout_ms] each: the
     check runs after the verdict, inside the competition's time limit. *)
  let valid phi =
    if Z3Smt.Z3interface.may_not_return phi then
      `Undecided "not asked: its shape may keep Z3 from returning"
    else
      try
        match
          Z3Smt.Z3interface.decide_valid ~timeout:(Some check_timeout_ms) ~id
            fenv phi
        with
        | `Valid -> `Valid
        | `Invalid -> `Refuted
        | `Undecided reason -> `Undecided ("Z3 did not decide it: " ^ reason)
      with exn_ when not (Common.Timer.is_async exn_) ->
        `Undecided ("the check raised " ^ Exn.to_string exn_)
  in
  (* the reason names the obligation and whether it is false (Z3 found a
     counter-model) or only not shown *)
  let fail what = function
    | `Refuted -> Error (`Failed (what ^ " (refuted)"))
    | `Undecided why ->
        Error (`Undecided (sprintf "%s (undecided: %s)" what why))
  in
  let rec go = function
    | [] -> (
        match valid (Formula.subst_preds psub received.query) with
        | `Valid -> Ok ()
        | (`Refuted | `Undecided _) as r ->
            fail "the query does not hold under the invariants" r)
    | ((p : MuCLP.Pred.t), phi) :: rest -> (
        match valid (Formula.mk_imply phi (Formula.subst_preds psub p.body)) with
        | `Valid -> go rest
        | (`Refuted | `Undecided _) as r ->
            fail
              (sprintf "the invariant of %s does not imply its body"
                 (Ident.name_of_pvar p.name))
              r)
  in
  go invs

(* -- Rankings ------------------------------------------------------------- *)

(* [ranking_scope solved name]: whether the reduction ranked every return of
   [name] to itself: no predicate of [name]'s call-graph component comes
   before it in [solved] (the reduction handles predicates from the last to
   the first, and ranks the returns through those already handled). *)
let ranking_scope (solved : MuCLP.Problem.t) name =
  let preds = solved.preds in
  match
    List.findi preds ~f:(fun _ (p : MuCLP.Pred.t) -> Ident.pvar_equal p.name name)
  with
  | None -> Error "not in the solved problem"
  | Some (i, _) -> (
      match
        List.find (MuCLP.Reducer.call_graph_sccs preds) ~f:(fun comp ->
            List.mem comp i ~equal:( = ))
      with
      | None -> Ok ()
      | Some comp -> (
          match List.filter comp ~f:(fun j -> j < i) with
          | [] -> Ok ()
          | earlier ->
              Error
                (sprintf "returns through %s are not ranked"
                   (String.concat_map_list ~sep:", " earlier ~f:(fun j ->
                        Ident.name_of_pvar (List.nth_exn preds j).name)))))

let prev_name (Ident.Tvar x) = Ident.Tvar (x ^ "__prev")

(* [ranking_lines ~id received ev]: one line per least-fixpoint predicate of
   [received] *)
let ranking_lines (received : MuCLP.Problem.t) (ev : evidence) =
  let mus =
    List.filter received.preds ~f:(fun (p : MuCLP.Pred.t) ->
        Stdlib.( = ) p.kind Predicate.Mu)
  in
  List.map mus ~f:(fun (pred : MuCLP.Pred.t) ->
      let name = Ident.name_of_pvar pred.name in
      let skip reason detail = `Skip (name, reason, detail) in
      if not ev.wf_reduction then
        skip "not-a-ranking"
          "the parity-progress-measure reduction was used; its families are not written"
      else
        match ev.solved with
        | None -> skip "no-solution" "no solved problem"
        | Some solved -> (
            match
              List.find solved.preds ~f:(fun (q : MuCLP.Pred.t) ->
                  Ident.pvar_equal q.name pred.name)
            with
            | None ->
                skip "not-reconstructible"
                  "removed by the optimizer: no ranking of its own was synthesised"
            | Some q -> (
                let key = Ident.pvar_to_tvar (Ident.wfpred_pvar q.name) in
                match Map.Poly.find ev.kind_certs key with
                | None ->
                    skip "no-ranking-certificate"
                      "the constraint solver recorded no ranking for this predicate"
                | Some [ (r : PCSatCommon.KindCert.ranking) ]
                  when List.length r.levels = 1 && not r.accepting -> (
                    if
                      List.length r.params_x <> List.length q.args
                      || not (List.is_empty r.params_shared)
                    then skip "arity-mismatch" "the ranking's parameters differ from the predicate's"
                    else
                      match ranking_scope solved q.name with
                      | Error why -> skip "not-a-transition-invariant" why
                      | Ok () ->
                          let to_x =
                            Map.Poly.of_alist_exn
                            @@ List.map2_exn r.params_x q.args ~f:(fun (x, _) (y, s) ->
                                (x, Term.mk_var y s))
                          in
                          let prev = List.map q.args ~f:(fun (x, s) -> (prev_name x, s)) in
                          let to_rel =
                            Map.Poly.of_alist_exn
                            @@ List.map2_exn r.params_x prev ~f:(fun (x, _) (y, s) ->
                                (x, Term.mk_var y s))
                            @ List.map2_exn r.params_y q.args ~f:(fun (x, _) (y, s) ->
                                (x, Term.mk_var y s))
                          in
                          let px, _ = List.hd_exn r.levels in
                          let pieces =
                            List.map px ~f:(fun (disc, ranks) ->
                                ( Formula.subst to_x disc,
                                  List.map ranks ~f:(Term.subst to_x) ))
                          in
                          let rel =
                            Formula.subst to_rel (PCSatCommon.KindCert.dec_of [ r ])
                          in
                          `Ranking (pred, q.args, pieces, prev, rel))
                | Some _ ->
                    skip "not-a-ranking"
                      "the certificate is a union or a parity ranking, not one lexicographic ranking")))

(* [check_ranking ~id received invs w prev rel]: whether [rel] (over [prev],
   the earlier visit's parameters, and [w]'s own, the later visit's) holds
   on every return of [w] to itself through [fix] predicates only, from a
   state in [w]'s invariant: [I_w(x) => body_w], each application [w(y)] read
   as [rel(x, y) /\ I_w(y)], each [fix] predicate unfolded (they form no
   cycle among themselves), every other predicate read as its invariant.
   [`Not_direct] when no return avoids every other cut point, so the
   obligation would hold vacuously and says nothing.  Requires [invs] to be
   closed for [received] (Theorem 1 of the design), which is what makes the
   invariants of the other predicates usable as their readings. *)
let check_ranking ~id (received : MuCLP.Problem.t) invs (w : MuCLP.Pred.t) params prev rel =
  let is_fix (p : MuCLP.Pred.t) = Stdlib.( = ) p.kind Predicate.MuOrNu in
  let fixes = List.filter received.preds ~f:is_fix in
  let fix_sub =
    Map.Poly.of_alist_exn
    @@ List.map fixes ~f:(fun (p : MuCLP.Pred.t) -> (p.name, (p.args, p.body)))
  in
  (* the body with every fix predicate unfolded: at most one round per
     predicate, since they form no cycle among themselves *)
  let rec unfold n phi =
    let has_fix =
      Set.exists (Formula.pvs_of phi) ~f:(fun q -> Map.Poly.mem fix_sub q)
    in
    if (not has_fix) || n = 0 then phi
    else unfold (n - 1) (Formula.subst_preds fix_sub phi)
  in
  let body = unfold (List.length fixes) w.body in
  if Set.exists (Formula.pvs_of body) ~f:(fun q -> Map.Poly.mem fix_sub q) then
    `Not_direct "the fix predicates form a cycle"
  else if not (Set.mem (Formula.pvs_of body) w.name) then
    `Not_direct "every return passes another cut point"
  else
    let ys = mk_fresh_sort_env_list (List.map w.args ~f:snd) in
    let y_of x =
      List.find_map_exn (List.zip_exn w.args ys) ~f:(fun ((x', _), (y, s)) ->
          if Ident.tvar_equal x x' then Some (Term.mk_var y s) else None)
    in
    (* [rel] over ([prev], [params]) read at (the current parameters, [ys]);
       [params] are the solved predicate's, each one of [w]'s by name *)
    let rel_at =
      Formula.subst
        (Map.Poly.of_alist_exn
        @@ List.map2_exn prev params ~f:(fun (p, _) (x, s) -> (p, Term.mk_var x s))
        @ List.map params ~f:(fun (x, _) -> (x, y_of x)))
        rel
    in
    let inv_w = List.Assoc.find_exn invs ~equal:(fun (a : MuCLP.Pred.t) b -> Ident.pvar_equal a.name b.name) w in
    let inv_w_at = instantiate w.args inv_w (var_terms ys) in
    let psub =
      Map.Poly.of_alist_exn
      @@ List.map invs ~f:(fun ((p : MuCLP.Pred.t), phi) ->
          if Ident.pvar_equal p.name w.name then
            (p.name, (ys, Formula.and_of [ rel_at; inv_w_at ]))
          else (p.name, (p.args, phi)))
    in
    let phi = Formula.mk_imply inv_w (Formula.subst_preds psub body) in
    let fenv = LogicOld.get_fenv () in
    if
      (not (Z3Smt.Z3interface.may_not_return phi))
      &&
      try Z3Smt.Z3interface.is_valid ~timeout:(Some check_timeout_ms) ~id fenv phi
      with exn_ when not (Common.Timer.is_async exn_) -> false
    then `Checked
    else `Failed "the ranking does not decrease on a direct return, or Z3 did not decide it"


(* -- The value ------------------------------------------------------------ *)

let skip subject reason detail =
  Witness.Skipped { subject; reason; detail }

(* the bound on a removed predicate's reconstruction from a ground answer's
   invariants (see [invariants ?max_nodes]) *)
let ground_max_nodes = 20_000

(* [holds ~id ?read ~check_inductive ~erased received ev]: the value for a
   valid answer, the invariants read with [read] (see [invariants]) and
   checked as a whole when [check_inductive], and a ranking line per
   least-fixpoint predicate.

   On a ground answer nothing is asked of Z3 and every invariant is written
   [unchecked]: each solved predicate's invariant lists the states the
   decision reached at it, a post-fixpoint by the decision's own argument
   ([MuCLP.GroundSolve.true_atoms]), so each holds of the reachable states on
   its own and a predicate left out (a reconstruction past
   [ground_max_nodes]) does not void the others; and a disjunction of up to
   the atom budget's states per obligation would cost Z3 time after the
   verdict, inside the competition's limit.  No ranking is written for a
   ground answer, which synthesises none. *)
let holds ~id ?read ~check_inductive ~erased (received : MuCLP.Problem.t)
    (ev : evidence) : Witness.t =
      let is_ground = match ev.side with Ground -> true | _ -> false in
      let invs =
        invariants ?read
          ?max_nodes:(if is_ground then Some ground_max_nodes else None)
          ~erased received ev
      in
      let all_found =
        List.filter_map invs ~f:(fun (p, o) ->
            match o with Formula phi -> Some (p, phi) | Skip _ -> None)
      in
      let complete = List.length all_found = List.length invs in
      let status =
        if is_ground || not check_inductive then Ok Witness.Unchecked_invariant
        else if not complete then
          Error
            "some predicate has no invariant, so the assignment cannot be \
             checked"
        else
          match check ~id received all_found with
          | Ok () -> Ok Witness.Inductive
          | Error (`Open _) -> Ok Witness.Unchecked_invariant
          | Error (`Failed why) | Error (`Undecided why) -> Error why
      in
      let erased_of (p : MuCLP.Pred.t) =
        List.filter_map erased ~f:(fun (q, x, c) ->
            if Ident.pvar_equal q p.name then Some (x, c) else None)
      in
      let inv_entries =
        List.map invs ~f:(fun ((p : MuCLP.Pred.t), o) ->
            match (o, status) with
            | Skip (reason, detail), _ -> skip (Some p.name) reason detail
            | Formula _, Error why -> skip (Some p.name) "check-failed" why
            | Formula phi, Ok st ->
                (* a formula the line printer refuses is still a value: the
                   caller rewrites it itself *)
                Witness.Invariant
                  {
                    name = p.name;
                    params = p.args;
                    kind = p.kind;
                    formula = phi;
                    erased = erased_of p;
                    status = st;
                  })
      in
      let rank_entries =
        List.map
          (match ev.side with
          | Ground ->
              List.filter_map received.preds ~f:(fun (p : MuCLP.Pred.t) ->
                  if Stdlib.( = ) p.kind Predicate.Mu then
                    Some
                      (`Skip
                        ( Ident.name_of_pvar p.name,
                          "ground-answer",
                          "the ground decision synthesises no ranking" ))
                  else None)
          | Primal | Primal_ad | Dual -> ranking_lines received ev)
          ~f:(function
          | `Skip (name, reason, detail) ->
              skip (Some (Ident.Pvar name)) reason detail
          | `Ranking ((p : MuCLP.Pred.t), params, pieces, prev, rel) -> (
              let rstatus =
                match status with
                | Ok Witness.Inductive when check_inductive -> (
                    match
                      try check_ranking ~id received all_found p params prev rel
                      with exn_ when not (Common.Timer.is_async exn_) ->
                        `Failed (Exn.to_string exn_)
                    with
                    | `Checked -> Ok Witness.Direct_returns_checked
                    | `Not_direct why -> Ok (Witness.Ranking_unchecked (Some why))
                    | `Failed why -> Error why)
                | _ -> Ok (Witness.Ranking_unchecked None)
              in
              match rstatus with
              | Error why -> skip (Some p.name) "check-failed" why
              | Ok rstatus ->
                  Witness.Ranking
                    {
                      rname = p.name;
                      rparams = params;
                      pieces;
                      prev;
                      transition = rel;
                      rstatus;
                    }))
      in
      let invariants =
        Map.Poly.of_alist_exn
        @@ List.filter_map inv_entries ~f:(function
          | Witness.Invariant i -> Some (i.name, i.formula)
          | _ -> None)
      in
      {
        side = ev.side;
        invariants;
        entries = inv_entries @ rank_entries;
        violation = None;
      }

(* [witness ~id ~check_inductive ~erased received ev]: the value of
   [Witness] for the answer [ev] records, over [received].  Asks Z3 only
   when [check_inductive], and calls [Violation] (ground evaluation, plus Z3
   per depth of the path search) only on a primal refutation, on a ground
   answer with [ground_paths], and on every invalid verdict of a termination
   problem (a lasso, or the cycle head of a single-cut-point problem). *)
let witness ~id ?print ?(ground_paths = false) ?ground_budget ~invalid
    ~check_inductive ~erased
    (received : MuCLP.Problem.t) (ev : evidence) : Witness.t =
  match (ev.side, ev.solution) with
  | _ when invalid && Violation.is_nontermination_shape received -> (
      (* any side: the lasso search needs only the received problem; the
         primal's refutation, when recorded, only guides it *)
      let r =
        match (ev.side, ev.solution) with
        | (Primal | Primal_ad), Some (PCSP.Problem.Unsat r) -> r
        | _ -> None
      in
      let solution =
        match ev.side with Dual -> ev.solution | _ -> None
      in
      match
        Common.PhaseTime.with_phase "muval-violation" @@ fun () ->
        try
          Nontermination.witness ~id ?print ~received ~solved:ev.solved
            ~refutation:r ~solution ()
        with exn_ when not (Common.Timer.is_async exn_) ->
          Error ("no-path-found", "the extraction raised " ^ Exn.to_string exn_)
      with
      | Ok (Lasso v, _) -> { (Witness.empty ev.side) with violation = Some v }
      | Ok (Recurrent { w; set; stem; entry }, _) ->
          {
            (Witness.empty ev.side) with
            entries =
              [
                Witness.Recurrent
                  {
                    head = w.name;
                    hparams = w.args;
                    set;
                    stem;
                    entry =
                      List.map2_exn w.args entry ~f:(fun (x, s) v ->
                          Witness.
                            { var = x; sort = s; value = Violation.term_of_value v });
                  };
              ];
          }
      | Ok (Head w, _) ->
          {
            (Witness.empty ev.side) with
            entries = [ Witness.Cycle_head { head = w.name; hparams = w.args } ];
          }
      | Error (reason, detail) -> Witness.skipped_whole ev.side reason detail)
  | (Primal | Primal_ad), Some (PCSP.Problem.Sat _) ->
      holds ~id ~check_inductive ~erased received ev
  | Ground, _ when not invalid -> (
      (* the reached atoms that are true, as each predicate's invariant: the
         disjunction of [args = values] over its true atoms ([false] for a
         predicate with none), a post-fixpoint of the solved problem read
         with greatest fixpoints ([GroundSolve.true_atoms]); carried back to
         the received problem as a constraint solver's solution is *)
      match (ev.solved, ground_budget) with
      | Some solved, Some atom_budget -> (
          match
            Common.PhaseTime.with_phase "muval-ground-invariants" @@ fun () ->
            MuCLP.GroundSolve.true_atoms ~atom_budget solved
          with
          | Error why ->
              Witness.skipped_whole ev.side "ground-answer"
                ("the query was decided on its finite reachable part, whose \
                  states could not be listed: " ^ why)
          | Ok atoms ->
              let by_pred = Hashtbl.Poly.create () in
              List.iter atoms ~f:(fun (p, vs) ->
                  Hashtbl.Poly.add_multi by_pred ~key:p ~data:vs);
              let read (q : MuCLP.Pred.t) =
                let tuples = List.rev (Hashtbl.Poly.find_multi by_pred q.name) in
                Some
                  ( q.args,
                    Formula.or_of
                    @@ List.map tuples ~f:(fun vs ->
                        Formula.and_of
                        @@ List.map2_exn q.args vs ~f:(fun (x, s) v ->
                            Formula.eq (Term.mk_var x s)
                              (Violation.term_of_value v))) )
              in
              holds ~id ~read ~check_inductive ~erased received ev)
      | _ ->
          Witness.skipped_whole ev.side "ground-answer"
            "the query was decided on its finite reachable part, without a \
             solution")
  | (Primal | Primal_ad), Some (PCSP.Problem.Unsat r) -> (
      match
        Common.PhaseTime.with_phase "muval-violation" @@ fun () ->
        try Violation.of_refutation ~id ?print ~received ~solved:ev.solved r
        with exn_ when not (Common.Timer.is_async exn_) ->
          (* the verdict is already decided: an extraction that fails costs
             the path, never the answer *)
          Error ("no-path-found", "the extraction raised " ^ Exn.to_string exn_)
      with
      | Ok v -> { (Witness.empty ev.side) with violation = Some v }
      | Error (reason, detail) -> Witness.skipped_whole ev.side reason detail)
  | Dual, _ ->
      Witness.skipped_whole ev.side "dual-answer"
        "the verdict came from the dual (the negated query); its solution is \
         not written"
  | Ground, _ when ground_paths && invalid -> (
      match
        Common.PhaseTime.with_phase "muval-violation" @@ fun () ->
        try Violation.of_ground ~id ?print ~received ()
        with exn_ when not (Common.Timer.is_async exn_) ->
          Error ("no-path-found", "the extraction raised " ^ Exn.to_string exn_)
      with
      | Ok v -> { (Witness.empty ev.side) with violation = Some v }
      | Error (reason, detail) -> Witness.skipped_whole ev.side reason detail)
  | Ground, _ ->
      Witness.skipped_whole ev.side "ground-answer"
        "the query was decided on its finite reachable part, without a \
         solution"
  | _, _ ->
      Witness.skipped_whole ev.side "no-solution"
        "the deciding side left no solution"
