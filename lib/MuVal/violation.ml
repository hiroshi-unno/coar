(* A violation path of a muCLP problem, from the constraint solver's
   refutation of its primal, replayed on the problem MuVal received before it
   is handed out.

   Setting.  The received problem [P] is a safety problem: every predicate a
   greatest fixpoint or [fix] (read as one), every body and the query built
   from atoms, predicate applications, conjunction, disjunction, implication
   with a predicate-free premise, negation of predicate-free formulas, and
   universal quantifiers only.  Its query is invalid iff there is a finite
   REFUTATION TREE: nodes are configurations [(Q, v)] (a predicate and ground
   argument values), the root(s) are applications the query reaches, and at
   each node there are values of the body's universal binders under which the
   body evaluates to false when exactly the node's children are read as false
   and every other application as true (applications occur positively, so
   reading the others as true is the weakest assumption).  A childless node is
   false by its atoms alone: for a program, an error (or, in a return
   summary, the return it summarises).

   What this module guarantees (the gate).  [of_refutation] returns a path
   only after [replay] has checked every node of it on [P] by ground
   evaluation -- no solver, no trust in where the candidate came from -- so a
   returned path is a refutation tree of [P] and its query is invalid.  The
   candidate itself is found by a search on [P] guided by the configurations
   the refutation mentions; the search may use Z3, the replay does not.

   The search (from the refutation).  The constraint solver's refutation is a
   derivation over the problem after MuVal's optimizer and reduction and the
   solver's own preprocessing: some predicates are inlined or eliminated and
   some argument positions erased, so its atoms are not a path of [P].  They
   are used as HINTS: each ground atom it mentions gives, for the received
   predicate of that name, the values of the positions that survived.  From
   the query, each node asks Z3 (quantifier-free: the node's values are
   fixed, the binders free) for binder values making the body false with the
   applications it reads as false restricted to configurations consistent
   with some hint of their predicate (unrestricted for a predicate with no
   hint), first with no application read as false (an error reached
   directly), then with some; a child that cannot be refuted within the
   budget is blocked and the node asked again.  Every query has its state
   fixed, so it is quantifier-free and its shape is decided before the call.

   Execution order.  Read in preorder, with each node's universal binders and
   children in the order the body nests them, the tree is an execution of the
   program that ends in the error (given the frontend's encoding: each
   universal binder of a body is one nondeterministic value or one returned
   value, met in execution order; a call [S_g(a) /\ forall r. (T_g(a, r) \/ k)]
   puts the callee's return-summary subtree before the continuation [k]).

   Termination problems (least fixpoints present).  A NO is an infinite
   execution, so the evidence is a LASSO: a candidate tree as above in which
   one node reads, as false, the application of its own or an ancestor's
   predicate at exactly that ancestor's values (the back edge).
   [of_nontermination] searches for one on the received problem (the query
   unfolded, back edges allowed between equal configurations of a chain with
   a least fixpoint and no greatest one, one quantifier-free Z3 question per
   depth, guided by the states the primal's refutation names) and returns it
   only after [replay_lasso] has checked it by ground evaluation; failing
   that, a problem with exactly one least fixpoint gets that predicate as its
   cycle head, which needs no path (see [cycle_head]). *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* -- Ground falsification -------------------------------------------------- *)

(* the last thing on the path through a falsified formula: a leaf of this body
   (the [n]th [false] literal, or [None] for another false atom), or a child
   (by its index in the node's children) *)
type final = Leaf of int option | Final_child of int
type event = EBind of Ident.tvar * Sort.t * Value.t | EChild of int

let rec count_false = function
  | Formula.Atom (Atom.False _, _) -> 1
  | Formula.Atom _ -> 0
  | Formula.UnaryOp (_, phi, _) -> count_false phi
  | Formula.BinaryOp (_, a, b, _) -> count_false a + count_false b
  | Formula.Bind (_, _, phi, _) -> count_false phi
  | Formula.LetRec (_, phi, _) -> count_false phi
  | Formula.LetFormula (_, _, _, phi, _) -> count_false phi

let veq a b = String.equal (Value.str_of a) (Value.str_of b)
let has_pvar phi = not (Set.is_empty (Formula.pvs_of phi))

(* [ground_eval env phi]: [Some b] when the predicate-free [phi] evaluates to
   [b] under [env]; [None] when it cannot be evaluated (a free variable
   without a value, a quantifier, an operator the evaluator refuses) *)
let ground_eval env phi =
  if has_pvar phi then None
  else
    try Some (Evaluator.eval ~env phi)
    with exn_ when not (Common.Timer.is_async exn_) -> None

(* [falsify ~binders ~child env base phi]: [Some (events, final)] when [phi]
   is false under [env] (the node's parameters, and binders as they are met),
   reading a universal binder [x] at the value [binders x], and an
   application [Q(t)] as false exactly when [child Q (t's values)] is
   [Some i] (the node's [i]th child) and true otherwise; [None] when it cannot
   be shown false this way.  Sound: [Some _] implies [phi] is false in every
   interpretation in which the children are false, since [phi] is positive in
   its applications and a universal is false when one instance is.  [base] is
   the number of [false] literals before [phi] in its body, for numbering
   leaves.  [falsify_gen ~choose] is the same with the binder's value chosen
   by [choose env x sort], [env] holding the values in scope (the binders of
   one quantifier are chosen in order, each seeing the earlier ones). *)
let rec falsify_gen ~choose ~child env base phi =
  let fals = falsify_gen ~choose ~child in
  match phi with
  | Formula.Atom (Atom.True _, _) -> None
  | Formula.Atom (Atom.False _, _) -> Some ([], Leaf (Some base))
  | Formula.Atom (Atom.App (Predicate.Var (pvar, _), args, _), _) -> (
      match
        try Some (List.map args ~f:(Evaluator.eval_term ~env))
        with exn_ when not (Common.Timer.is_async exn_) -> None
      with
      | None -> None
      | Some vs -> (
          match child pvar vs with
          | Some i -> Some ([ EChild i ], Final_child i)
          | None -> None))
  | Formula.Atom (_, _) | Formula.UnaryOp (Not, _, _) -> (
      match ground_eval env phi with
      | Some false -> Some ([], Leaf None)
      | _ -> None)
  | Formula.BinaryOp (And, a, b, _) -> (
      match fals env base a with
      | Some r -> Some r
      | None -> fals env (base + count_false a) b)
  | Formula.BinaryOp (Or, a, b, _) -> (
      match fals env base a with
      | None -> None
      | Some (ea, _) -> (
          match fals env (base + count_false a) b with
          | None -> None
          | Some (eb, fb) -> Some (ea @ eb, fb)))
  | Formula.BinaryOp (Imply, a, b, _) -> (
      match ground_eval env a with
      | Some true -> fals env (base + count_false a) b
      | _ -> None)
  | Formula.BinaryOp ((Iff | Xor), _, _, _) -> (
      match ground_eval env phi with
      | Some false -> Some ([], Leaf None)
      | _ -> None)
  | Formula.Bind (Forall, xs, body, _) -> (
      let bound =
        List.fold xs ~init:(Some (env, [])) ~f:(fun acc (x, s) ->
            match acc with
            | None -> None
            | Some (env, evs) -> (
                match choose env x s with
                | None -> None
                | Some v ->
                    Some (Map.Poly.set env ~key:x ~data:v, EBind (x, s, v) :: evs)))
      in
      match bound with
      | None -> None
      | Some (env, evs) -> (
          match fals env base body with
          | None -> None
          | Some (e, f) -> Some (List.rev evs @ e, f)))
  | Formula.LetFormula (x, _, def, body, _) -> (
      match
        try Some (Evaluator.eval_term ~env def)
        with exn_ when not (Common.Timer.is_async exn_) -> None
      with
      | None -> None
      | Some v -> fals (Map.Poly.set env ~key:x ~data:v) base body)
  | Formula.Bind ((Exists | Random _), _, _, _) | Formula.LetRec _ -> None

let falsify ~binders ~child env base phi =
  falsify_gen ~choose:(fun _ x _ -> binders x) ~child env base phi

(* -- Candidates and replay ------------------------------------------------- *)

(* a candidate node: a configuration, the values of its body's universal
   binders (by name), and its children *)
type cand = {
  cpred : Ident.pvar;
  cvals : Value.t list;
  binders : (Ident.tvar, Value.t) Map.Poly.t;
  children : cand list;
}

type cand_root = {
  qbinders : (Ident.tvar, Value.t) Map.Poly.t;
  roots : cand list;
}

let find_pred (p : MuCLP.Problem.t) name =
  List.find p.preds ~f:(fun (q : MuCLP.Pred.t) -> Ident.pvar_equal q.name name)

let child_of (children : cand list) pvar vs =
  List.find_mapi children ~f:(fun i c ->
      if
        Ident.pvar_equal c.cpred pvar
        && List.length c.cvals = List.length vs
        && List.for_all2_exn c.cvals vs ~f:veq
      then Some i
      else None)

let term_of_value v = Term.of_value (get_dtenv ()) v

(* [replay_gen ~lasso received cand]: [Ok v] when [cand] is a refutation tree
   of [received] (every node checked by [falsify], the query falsified by the
   roots; a child no falsification reaches is pruned), with the witness path
   [v] read off the checks; [Error why] names the first failing node.  Pure:
   no solver.

   With [~lasso:true] the tree is a LASSO candidate: a node may also read as
   false an application whose configuration equals its own or an ancestor's
   (when no child of it matches), which is the BACK EDGE.  Accepted only when
   exactly one back edge is read, and on the ancestor chain from its target
   [k] down to the node [c] that reads it no predicate is a greatest
   fixpoint and at least one is a least fixpoint.  Then the tree, with the
   subtree at [k] repeated forever below [c], is an infinite refutation whose
   only infinitely visited predicates are those of the chain: least
   fixpoints and [fix] predicates, which MuVal requires to have one solution
   whichever way they are read, so the refuter wins the infinite play (the
   game reading of nested fixpoints) and the query is invalid.  For the
   direct LLVM translation of a termination problem the chain is moreover a
   path of the program (a return summary's body applies only return
   summaries and every cycle of return summaries passes a greatest-fixpoint
   cut point, so a chain with a least fixpoint and no greatest one has no
   return summary on it), and the lasso is an infinite execution: the stem,
   then the chain's code forever with the same nondeterministic values.

   With [~target:(w, holds)] (a STEM into a recurrent set) a node may also
   read as false an application of [w] at values [vs] with [holds vs] (when
   no child of it matches): the application is false because [vs] lies in a
   set from which [w] has an infinite execution, which the caller has
   established.  Accepted only when exactly one such application is read;
   [on_target index vs] is told the step that reads it and its values, and
   that step is the [error] step of the result. *)
let replay_gen ?target ?(on_target = fun _ _ -> ()) ~lasso ~source
    (received : MuCLP.Problem.t) (c : cand_root) :
    (Witness.violation, string) result =
  let steps = ref [] in
  let next = ref 0 in
  let hits = ref [] in
  (* the back edge read so far: (the step reading it, the step it returns
     to, the chain between them) *)
  let back = ref None in
  (* the children a falsification reached, each once, in the order it reached
     them (the execution order); a child it did not reach is pruned, which
     leaves a refutation tree, since the falsification did not read it *)
  let reached evs =
    List.fold evs ~init:[] ~f:(fun acc -> function
      | EChild j when not (List.mem acc j ~equal:( = )) -> acc @ [ j ]
      | _ -> acc)
  in
  let binding (x, s, v) =
    Witness.{ var = x; sort = s; value = term_of_value v }
  in
  let kind_of pvar =
    Option.map (find_pred received pvar) ~f:(fun (q : MuCLP.Pred.t) -> q.kind)
  in
  (* [visit chain parent node]: checks [node] and its subtree, numbering in
     preorder; [chain] is the ancestors' (index, predicate, values), nearest
     first; returns its index and the step its error final ends in *)
  let rec visit chain parent (node : cand) =
    match find_pred received node.cpred with
    | None ->
        Error
          (sprintf "%s is not a received predicate"
             (Ident.name_of_pvar node.cpred))
    | Some pred -> (
        if List.length pred.args <> List.length node.cvals then
          Error (sprintf "%s: arity" (Ident.name_of_pvar pred.name))
        else
          let env =
            Map.Poly.of_alist_exn
            @@ List.map2_exn pred.args node.cvals ~f:(fun (x, _) v -> (x, v))
          in
          (* the index this node gets if it is accepted (a failure anywhere
             fails the whole replay, so numbering before the check is the
             same as numbering after it) *)
          let index = !next in
          let chain = (index, node.cpred, node.cvals) :: chain in
          let nkids = List.length node.children in
          let target_code = nkids + List.length chain in
          (* the target applications the falsification tried at this node
             (a branch it abandoned may have tried one too) *)
          let tried = ref [] in
          let child pvar vs =
            match child_of node.children pvar vs with
            | Some i -> Some i
            | None
              when match target with
                   | Some (w, holds) -> Ident.pvar_equal w pvar && holds vs
                   | None -> false ->
                if
                  not
                    (List.exists !tried ~f:(fun vs' ->
                         List.for_all2_exn vs vs' ~f:veq))
                then tried := vs :: !tried;
                Some target_code
            | None when lasso ->
                List.find_mapi chain ~f:(fun pos (_, p, vals) ->
                    if
                      Ident.pvar_equal p pvar
                      && List.length vals = List.length vs
                      && List.for_all2_exn vals vs ~f:veq
                    then Some (nkids + pos)
                    else None)
            | None -> None
          in
          match
            falsify ~binders:(Map.Poly.find node.binders) ~child env 0
              pred.body
          with
          | None ->
              Error
                (sprintf "the body of %s is not false at the candidate's values"
                   (Ident.name_of_pvar pred.name))
          | Some (evs, final) -> (
              incr next;
              let slot = ref None in
              steps := (index, slot) :: !steps;
              let reached_kids, backs =
                List.partition_tf (reached evs) ~f:(fun i -> i < nkids)
              in
              let hit_ok =
                if not (List.mem backs target_code ~equal:( = )) then Ok ()
                else
                  match !tried with
                  | [ vs ] ->
                      hits := (index, vs) :: !hits;
                      Ok ()
                  | _ ->
                      Error
                        "the falsification tried several target applications \
                         at one step"
              in
              let backs = List.filter backs ~f:(fun i -> i <> target_code) in
              let back_ok =
                match backs with
                | [] -> Ok ()
                | [ b ] when Option.is_none !back -> (
                    let pos = b - nkids in
                    let segment = List.take chain (pos + 1) in
                    let kinds = List.map segment ~f:(fun (_, p, _) -> kind_of p) in
                    if
                      List.exists kinds ~f:(function
                        | Some Predicate.Nu | None -> true
                        | _ -> false)
                    then
                      Error
                        "the back edge closes a cycle through a greatest \
                         fixpoint (a return summary)"
                    else if
                      not
                        (List.exists kinds ~f:(function
                          | Some Predicate.Mu -> true
                          | _ -> false))
                    then Error "the back edge closes a cycle with no cut point"
                    else (
                      back :=
                        Some (index, (fun (k, _, _) -> k) (List.nth_exn chain pos));
                      Ok ()))
                | _ -> Error "more than one back edge"
              in
              match Result.bind hit_ok ~f:(fun () -> back_ok) with
              | Error e -> Error e
              | Ok () ->
                  let rec kids acc = function
                    | [] -> Ok (List.rev acc)
                    | i :: rest -> (
                        match
                          visit chain (Some index) (List.nth_exn node.children i)
                        with
                        | Error e -> Error e
                        | Ok r -> kids ((i, r) :: acc) rest)
                  in
                  Result.bind (kids [] reached_kids) ~f:(fun ks ->
                      let seen = Hash_set.Poly.create () in
                      let events =
                        List.filter_map evs ~f:(function
                          | EBind (x, s, v) ->
                              Some (Witness.Bind (binding (x, s, v)))
                          | EChild i ->
                              if i >= nkids || Hash_set.mem seen i then None
                              else (
                                Hash_set.add seen i;
                                Some
                                  (Witness.Child
                                     (fst
                                        (List.Assoc.find_exn ks ~equal:( = ) i)))))
                      in
                      slot :=
                        Some
                          Witness.
                            {
                              index;
                              pred = pred.name;
                              args =
                                List.map2_exn pred.args node.cvals
                                  ~f:(fun (x, s) v -> binding (x, s, v));
                              events;
                              parent;
                            };
                      let err =
                        match final with
                        | Leaf leaf -> Witness.{ estep = index; leaf }
                        | Final_child i when i >= nkids ->
                            Witness.{ estep = index; leaf = None }
                        | Final_child i ->
                            snd (List.Assoc.find_exn ks ~equal:( = ) i)
                      in
                      Ok (index, err))))
  in
  match
    falsify ~binders:(Map.Poly.find c.qbinders) ~child:(child_of c.roots)
      Map.Poly.empty 0 received.query
  with
  | None -> Error "the query is not false at the candidate's roots"
  | Some (evs, final) -> (
      let rec go acc = function
        | [] -> Ok (List.rev acc)
        | i :: rest -> (
            match visit [] None (List.nth_exn c.roots i) with
            | Error e -> Error e
            | Ok x -> go ((i, x) :: acc) rest)
      in
      match go [] (reached evs) with
      | Error e -> Error e
      | Ok rs -> (
          let target_ok =
            match (target, !hits) with
            | None, _ -> Ok None
            | Some _, [ (k, vs) ] ->
                on_target k vs;
                Ok (Some k)
            | Some _, [] -> Error "the stem reaches no state of the target set"
            | Some _, _ -> Error "the stem reads the target set more than once"
          in
          match (final, lasso, !back, target_ok) with
          | _, _, _, Error e -> Error e
          | Leaf _, _, _, _ -> Error "the query is false by its own atoms: no path"
          | Final_child _, true, None, _ -> Error "no back edge: not a lasso"
          | Final_child i, _, _, Ok hit ->
              let steps =
                List.sort !steps ~compare:(fun (a, _) (b, _) -> compare a b)
                |> List.map ~f:(fun (_, s) -> Option.value_exn !s)
              in
              Ok
                Witness.
                  {
                    source;
                    initial =
                      List.filter_map evs ~f:(function
                        | EBind (x, s, v) -> Some (binding (x, s, v))
                        | EChild _ -> None);
                    roots = List.map rs ~f:(fun (_, (k, _)) -> k);
                    steps;
                    error =
                      (match (!back, hit) with
                      | Some (c, _), _ -> { estep = c; leaf = None }
                      | None, Some k -> { estep = k; leaf = None }
                      | None, None -> snd (List.Assoc.find_exn rs ~equal:( = ) i));
                    cycle_from = Option.map !back ~f:snd;
                  }))

let replay ~source received c = replay_gen ~lasso:false ~source received c
let replay_lasso ~source received c = replay_gen ~lasso:true ~source received c

(* -- Hints from the refutation -------------------------------------------- *)

(* [hints received solved r]: per received predicate, the partial
   configurations (position -> value) the refutation's ground atoms give it.
   An atom of the solver's problem names an unknown [U|P|] (or [P]); its
   arguments are read positionally against the solved predicate's
   parameters, each of which is a received parameter by name; an atom whose
   arity does not match is not used. *)
let hints (received : MuCLP.Problem.t) (solved : MuCLP.Problem.t option)
    (r : PCSP.Refutation.t) =
  let solved_preds = match solved with Some s -> s.preds | None -> [] in
  let pred_of_unknown name =
    List.find solved_preds ~f:(fun (q : MuCLP.Pred.t) ->
        String.equal name (Ident.name_of_pvar q.name)
        || String.equal name (Ident.name_of_pvar (Ident.uninterp_pvar q.name)))
  in
  let atoms =
    List.concat_map r.nodes ~f:(fun n ->
        Set.to_list n.example.positive @ Set.to_list n.example.negative)
    @
    match r.conclusion with
    | Conflict a -> [ a ]
    | Propagation l -> l
    | _ -> []
  in
  let tbl = Hashtbl.Poly.create () in
  List.iter atoms ~f:(function
    | ExAtom.PApp ((pvar, _), args) -> (
        match pred_of_unknown (Ident.name_of_pvar pvar) with
        | None -> ()
        | Some q -> (
            match find_pred received q.name with
            | None -> ()
            | Some p ->
                if List.length args = List.length q.args then
                  let partial =
                    List.filter_map (List.zip_exn q.args args)
                      ~f:(fun ((x, _), t) ->
                        match
                          List.findi p.args ~f:(fun _ (y, _) ->
                              Ident.tvar_equal x y)
                        with
                        | Some (i, _) when Set.is_empty (Term.tvs_of t) -> (
                            try Some (i, Evaluator.eval_term t)
                            with exn_ when not (Common.Timer.is_async exn_) ->
                              None)
                        | _ -> None)
                  in
                  Hashtbl.Poly.add_multi tbl ~key:p.name ~data:partial))
    | _ -> ());
  tbl

(* -- The search ------------------------------------------------------------ *)

(* the budget of one Z3 question: one formula of the unfolded query, quantifier
   free (every binder of every unfolded instance is a free variable) *)
let query_timeout_ms = 10_000

(* the largest unfolding asked: the number of predicate instances in it *)
let max_instances = 20_000

exception Too_large

(* An instance of a predicate in the unfolding: its arguments (terms over the
   unfolding's free variables), its body's binders (received name, the fresh
   variable standing for it, sort), its formula in the unfolding, and the
   instances of the applications its body makes, in order. *)
type inst = {
  ipred : Ident.pvar;
  iargs : Term.t list;
  ibinders : (Ident.tvar * Ident.tvar * Sort.t) list;
  mutable iformula : Formula.t;
  mutable kids : inst list;
}

(* [unfold received ~hints depth] builds the query unfolded [depth]
   applications deep: each application [Q(t)] above the depth is replaced by
   [Q]'s body at [t] (binders renamed apart), and one at the depth by [true]
   (it is never read as refuted).  The result [phi] is false in a model only
   if the model's values give a refutation tree of depth at most [depth] (an
   instance whose formula is false is a node; the instances under it whose
   formulas are false are its children).  With [hints], an application of a
   predicate that has hints is read as refuted only at a configuration
   consistent with one of them. *)
let unfold (received : MuCLP.Problem.t) ~hints depth =
  let count = ref 0 in
  let hint_ok pvar args =
    match hints with
    | None -> Formula.mk_true ()
    | Some hints -> (
        match Hashtbl.Poly.find hints pvar with
        | None | Some [] -> Formula.mk_true ()
        | Some hs ->
            Formula.or_of
            @@ List.map hs ~f:(fun partial ->
                Formula.and_of
                @@ List.map partial ~f:(fun (i, v) ->
                    Formula.eq (List.nth_exn args i) (term_of_value v))))
  in
  let rec instance pvar args depth =
    incr count;
    if !count > max_instances then raise Too_large;
    let pred = Option.value_exn (find_pred received pvar) in
    let sub =
      Map.Poly.of_alist_exn
      @@ List.map2_exn pred.args args ~f:(fun (x, _) t -> (x, t))
    in
    let i =
      {
        ipred = pvar;
        iargs = args;
        ibinders = [];
        iformula = Formula.mk_true ();
        kids = [];
      }
    in
    let binders, kids, phi = formula sub depth pred.body in
    let i = { i with ibinders = binders } in
    i.iformula <- phi;
    i.kids <- kids;
    i
  (* [formula sub depth phi]: [phi] under [sub], its binders renamed apart
     and its applications unfolded; with the binders and the instances met *)
  and formula sub depth phi =
    let binders = ref [] in
    let kids = ref [] in
    let rec go sub = function
      | Formula.Atom (Atom.App (Predicate.Var (q, _), args, _), _) ->
          let args = List.map args ~f:(Term.subst sub) in
          if depth <= 0 || Option.is_none (find_pred received q) then
            Formula.mk_true ()
          else
            let k = instance q args (depth - 1) in
            kids := k :: !kids;
            Formula.mk_or k.iformula (Formula.mk_neg (hint_ok q args))
      | Formula.Atom (_, _) as a -> Formula.subst sub a
      | Formula.UnaryOp (op, a, info) -> Formula.mk_unop ~info op (go sub a)
      | Formula.BinaryOp (op, a, b, info) ->
          Formula.mk_binop ~info op (go sub a) (go sub b)
      | Formula.Bind (Forall, xs, body, _) ->
          let sub =
            List.fold xs ~init:sub ~f:(fun sub (x, s) ->
                let x' = Ident.mk_fresh_tvar () in
                binders := (x, x', s) :: !binders;
                Map.Poly.set sub ~key:x ~data:(Term.mk_var x' s))
          in
          go sub body
      | Formula.LetFormula (x, s, def, body, _) ->
          let x' = Ident.mk_fresh_tvar () in
          let def = Term.subst sub def in
          let body =
            go (Map.Poly.set sub ~key:x ~data:(Term.mk_var x' s)) body
          in
          Formula.mk_and (Formula.eq (Term.mk_var x' s) def) body
      | phi -> raise (Invalid_argument ("the shape of " ^ Formula.str_of phi))
    in
    let phi = go sub phi in
    (List.rev !binders, List.rev !kids, phi)
  in
  let binders, kids, phi = formula Map.Poly.empty depth received.query in
  (binders, kids, phi)

(* [read model (qbinders, roots, _)]: the candidate tree a model of the
   negated unfolding gives *)
let read model (qbinders, roots, _) =
  let value_of (x, s) =
    match LogicOld.model_find model (x, s) with
    | Some (Some t) -> (
        try Some (Evaluator.eval_term t)
        with exn_ when not (Common.Timer.is_async exn_) -> None)
    | _ -> (
        (* a variable the model leaves free may take any value *)
        match s with
        | T_int.SInt -> Some (Value.Int Z.zero)
        | T_bool.SBool -> Some (Value.Bool false)
        | T_bv.SBV (Some n) -> Some (Value.BV (Some n, Z.zero))
        | _ -> None)
  in
  let env = Hashtbl.Poly.create () in
  let rec collect_vars i =
    List.iter i.ibinders ~f:(fun (_, x', s) ->
        Option.iter
          (value_of (x', s))
          ~f:(fun v -> Hashtbl.Poly.set env ~key:x' ~data:v));
    List.iter i.kids ~f:collect_vars
  in
  List.iter qbinders ~f:(fun (_, x', s) ->
      Option.iter
        (value_of (x', s))
        ~f:(fun v -> Hashtbl.Poly.set env ~key:x' ~data:v));
  List.iter roots ~f:collect_vars;
  let env = Map.Poly.of_alist_exn (Hashtbl.Poly.to_alist env) in
  let refuted i =
    match ground_eval env i.iformula with Some false -> true | _ -> false
  in
  let bmap bs =
    Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
    @@ List.filter_map bs ~f:(fun (x, x', _) ->
        Option.map (Map.Poly.find env x') ~f:(fun v -> (x, v)))
  in
  let rec node i =
    let cvals = List.map i.iargs ~f:(Evaluator.eval_term ~env) in
    let children =
      List.fold (List.filter i.kids ~f:refuted) ~init:[] ~f:(fun acc k ->
          let c = node k in
          if
            List.exists acc ~f:(fun c' ->
                Ident.pvar_equal c.cpred c'.cpred
                && List.for_all2_exn c.cvals c'.cvals ~f:veq)
          then acc
          else acc @ [ c ])
    in
    { cpred = i.ipred; cvals; binders = bmap i.ibinders; children }
  in
  let roots =
    List.fold (List.filter roots ~f:refuted) ~init:[] ~f:(fun acc k ->
        let c = node k in
        if
          List.exists acc ~f:(fun c' ->
              Ident.pvar_equal c.cpred c'.cpred
              && List.for_all2_exn c.cvals c'.cvals ~f:veq)
        then acc
        else acc @ [ c ])
  in
  { qbinders = bmap qbinders; roots }

(* [search ~id ~print received hints]: a candidate refutation tree from the
   query unfolded 1, 2, 4, ... applications deep, each depth asked first with
   the hints and then without, until an answer, an unfolding larger than
   [max_instances], or a depth beyond [max_depth]; [None] otherwise. *)
let search ~id ~print ~max_depth (received : MuCLP.Problem.t) hints =
  let fenv = LogicOld.get_fenv () in
  let ask phi =
    if Z3Smt.Z3interface.may_not_return phi then None
    else
      match
        try
          Z3Smt.Z3interface.check_sat ~id ~timeout:(Some query_timeout_ms) fenv
            [ phi ]
        with exn_ when not (Common.Timer.is_async exn_) ->
          `Unknown (Exn.to_string exn_)
      with
      | `Sat model -> Some model
      | `Unsat -> None
      | `Timeout | `Unknown _ ->
          print @@ lazy "violation search: a question was not decided";
          None
  in
  let has_hints =
    Hashtbl.Poly.exists hints ~f:(fun l -> not (List.is_empty l))
  in
  let rec go depth =
    if depth > max_depth then None
    else
      let try_with h =
        match unfold received ~hints:h depth with
        | exception Too_large -> `Too_large
        | (_, _, phi) as u -> (
            match ask (Formula.mk_neg phi) with
            | Some model -> `Found (read model u)
            | None -> `No)
      in
      let r =
        match if has_hints then try_with (Some hints) else `No with
        | `Found c -> `Found c
        | _ -> try_with None
      in
      print
      @@ lazy
           (sprintf "violation search: depth %d: %s" depth
              (match r with
              | `Found _ -> "found"
              | `No -> "none"
              | `Too_large -> "too large"));
      match r with
      | `Found c -> Some c
      | `Too_large -> None
      | `No -> go (if depth < 8 then depth + 1 else depth * 2)
  in
  go 1

(* -- Lassos (termination problems) ----------------------------------------- *)

(* [cycle_hints received solved r]: [hints] plus, from each ground atom of a
   well-foundedness unknown [WF_P_] (a pair of states of [P] that the primal's
   refutation forces around a cycle), both of its halves as partial
   configurations of the received [P], read by name like [hints] reads
   [U_P_] *)
let cycle_hints (received : MuCLP.Problem.t) (solved : MuCLP.Problem.t option)
    (r : PCSP.Refutation.t) =
  let tbl = hints received solved r in
  let solved_preds = match solved with Some s -> s.preds | None -> [] in
  let atoms =
    List.concat_map r.nodes ~f:(fun n ->
        Set.to_list n.example.positive @ Set.to_list n.example.negative)
  in
  List.iter atoms ~f:(function
    | ExAtom.PApp ((pvar, _), args) -> (
        match
          List.find solved_preds ~f:(fun (q : MuCLP.Pred.t) ->
              String.equal (Ident.name_of_pvar pvar)
                (Ident.name_of_pvar (Ident.wfpred_pvar q.name)))
        with
        | None -> ()
        | Some q -> (
            match find_pred received q.name with
            | None -> ()
            | Some p ->
                let n = List.length q.args in
                if List.length args = 2 * n then
                  List.iter
                    [ List.take args n; List.drop args n ]
                    ~f:(fun half ->
                      let partial =
                        List.filter_map (List.zip_exn q.args half)
                          ~f:(fun ((x, _), t) ->
                            match
                              List.findi p.args ~f:(fun _ (y, _) ->
                                  Ident.tvar_equal x y)
                            with
                            | Some (i, _) when Set.is_empty (Term.tvs_of t) -> (
                                try Some (i, Evaluator.eval_term t)
                                with exn_
                                when not (Common.Timer.is_async exn_)
                                ->
                                  None)
                            | _ -> None)
                      in
                      if not (List.is_empty partial) then
                        Hashtbl.Poly.add_multi tbl ~key:p.name ~data:partial)))
    | _ -> ());
  tbl

(* the largest number of back-edge selectors in one lasso question *)
let max_selectors = 20_000

(* An application instance of the lasso unfolding: as [inst], plus [lback],
   the selectors (Boolean variables) of the back edges it may be read as,
   each to an ancestor instance with the same predicate; [unfolded] is false
   for an application at the depth, whose body is not unfolded. *)
type linst = {
  lpred : Ident.pvar;
  largs : Term.t list;
  mutable lbinders : (Ident.tvar * Ident.tvar * Sort.t) list;
  mutable lformula : Formula.t;
  mutable lkids : linst list;
  mutable lback : (Ident.tvar * linst) list;
  unfolded : bool;
}

(* [unfold_lasso received ~hints depth]: [unfold]'s formula with back edges.
   An application [Q(t)] whose ancestor chain (nearest first, itself
   excluded) has an instance [a] of [Q] such that no instance from [a] down
   to the application's parent is a greatest fixpoint and one is a least
   fixpoint gets a selector [b] with [b => args(a) = t] (and, with [hints]
   for [Q], [a]'s arguments consistent with one of them); the application is
   read as [(body \/ not hint) /\ not (b1 \/ ...)], so a selected one is read
   as false, and at the depth an application is [not (b1 \/ ...)].  Returns
   the query's binders, its instances, the formula and the side conditions
   (the selectors' equalities and "some selector is chosen").  A model of
   [not phi /\ side] is a lasso candidate: each selected instance closes a
   cycle to its ancestor. *)
let unfold_lasso (received : MuCLP.Problem.t) ~hints depth =
  let count = ref 0 in
  let nsel = ref 0 in
  let side = ref [] in
  let selectors = ref [] in
  let kind_of q =
    Option.map (find_pred received q) ~f:(fun (p : MuCLP.Pred.t) -> p.kind)
  in
  let hint_ok pvar args =
    match hints with
    | None -> Formula.mk_true ()
    | Some hints -> (
        match Hashtbl.Poly.find hints pvar with
        | None | Some [] -> Formula.mk_true ()
        | Some hs ->
            Formula.or_of
            @@ List.map hs ~f:(fun partial ->
                Formula.and_of
                @@ List.map partial ~f:(fun (i, v) ->
                    Formula.eq (List.nth_exn args i) (term_of_value v))))
  in
  (* the back-edge selectors of an application [q(args)] below [chain] *)
  let backs chain q args =
    let rec go acc seen_mu = function
      | [] -> acc
      | (a : linst) :: rest -> (
          match kind_of a.lpred with
          | Some Predicate.Nu | None -> acc
          | Some k ->
              let seen_mu = seen_mu || Stdlib.( = ) k Predicate.Mu in
              let acc =
                if seen_mu && Ident.pvar_equal a.lpred q then (
                  incr nsel;
                  if !nsel > max_selectors then raise Too_large;
                  let b = Ident.mk_fresh_tvar () in
                  side :=
                    Formula.mk_imply
                      (Formula.of_bool_var b)
                      (Formula.and_of
                         (hint_ok q a.largs
                         :: List.map2_exn a.largs args ~f:Formula.eq))
                    :: !side;
                  selectors := b :: !selectors;
                  (b, a) :: acc)
                else acc
              in
              go acc seen_mu rest)
    in
    go [] false chain
  in
  let not_back l =
    Formula.mk_neg
      (Formula.or_of (List.map l ~f:(fun (b, _) -> Formula.of_bool_var b)))
  in
  let rec instance chain pvar args depth =
    incr count;
    if !count > max_instances then raise Too_large;
    let pred = Option.value_exn (find_pred received pvar) in
    let sub =
      Map.Poly.of_alist_exn
      @@ List.map2_exn pred.args args ~f:(fun (x, _) t -> (x, t))
    in
    let i =
      {
        lpred = pvar;
        largs = args;
        lbinders = [];
        lformula = Formula.mk_true ();
        lkids = [];
        lback = backs chain pvar args;
        unfolded = true;
      }
    in
    let binders, kids, phi = formula (i :: chain) sub depth pred.body in
    i.lbinders <- binders;
    i.lformula <- phi;
    i.lkids <- kids;
    i
  and formula chain sub depth phi =
    let binders = ref [] in
    let kids = ref [] in
    let rec go sub = function
      | Formula.Atom (Atom.App (Predicate.Var (q, _), args, _), _) ->
          let args = List.map args ~f:(Term.subst sub) in
          if Option.is_none (find_pred received q) then Formula.mk_true ()
          else if depth <= 0 then (
            let k =
              {
                lpred = q;
                largs = args;
                lbinders = [];
                lformula = Formula.mk_true ();
                lkids = [];
                lback = backs chain q args;
                unfolded = false;
              }
            in
            kids := k :: !kids;
            not_back k.lback)
          else
            let k = instance chain q args (depth - 1) in
            kids := k :: !kids;
            Formula.mk_and
              (Formula.mk_or k.lformula (Formula.mk_neg (hint_ok q args)))
              (not_back k.lback)
      | Formula.Atom (_, _) as a -> Formula.subst sub a
      | Formula.UnaryOp (op, a, info) -> Formula.mk_unop ~info op (go sub a)
      | Formula.BinaryOp (op, a, b, info) ->
          Formula.mk_binop ~info op (go sub a) (go sub b)
      | Formula.Bind (Forall, xs, body, _) ->
          let sub =
            List.fold xs ~init:sub ~f:(fun sub (x, s) ->
                let x' = Ident.mk_fresh_tvar () in
                binders := (x, x', s) :: !binders;
                Map.Poly.set sub ~key:x ~data:(Term.mk_var x' s))
          in
          go sub body
      | Formula.LetFormula (x, s, def, body, _) ->
          let x' = Ident.mk_fresh_tvar () in
          let def = Term.subst sub def in
          let body =
            go (Map.Poly.set sub ~key:x ~data:(Term.mk_var x' s)) body
          in
          Formula.mk_and (Formula.eq (Term.mk_var x' s) def) body
      | phi -> raise (Invalid_argument ("the shape of " ^ Formula.str_of phi))
    in
    let phi = go sub phi in
    (List.rev !binders, List.rev !kids, phi)
  in
  let binders, kids, phi = formula [] Map.Poly.empty depth received.query in
  let side =
    Formula.and_of
      (Formula.or_of (List.map !selectors ~f:Formula.of_bool_var) :: !side)
  in
  (binders, kids, phi, side)

(* [read_lasso model (qbinders, roots, _, _)]: the lasso candidate a model
   gives: [read]'s tree, in which a selected application is left out of its
   parent's children (the replay reads it as the back edge) and an
   application at the depth is never a child *)
let read_lasso model (qbinders, roots, _, _) =
  let value_of (x, s) =
    match LogicOld.model_find model (x, s) with
    | Some (Some t) -> (
        try Some (Evaluator.eval_term t)
        with exn_ when not (Common.Timer.is_async exn_) -> None)
    | _ -> (
        match s with
        | T_int.SInt -> Some (Value.Int Z.zero)
        | T_bool.SBool -> Some (Value.Bool false)
        | T_bv.SBV (Some n) -> Some (Value.BV (Some n, Z.zero))
        | _ -> None)
  in
  let env = Hashtbl.Poly.create () in
  let add (_, x', s) =
    Option.iter (value_of (x', s)) ~f:(fun v ->
        Hashtbl.Poly.set env ~key:x' ~data:v)
  in
  let rec collect i =
    List.iter i.lbinders ~f:add;
    List.iter i.lback ~f:(fun (b, _) -> add ((), b, T_bool.SBool));
    List.iter i.lkids ~f:collect
  in
  List.iter qbinders ~f:add;
  List.iter roots ~f:collect;
  let env = Map.Poly.of_alist_exn (Hashtbl.Poly.to_alist env) in
  let selected i =
    List.exists i.lback ~f:(fun (b, _) ->
        match Map.Poly.find env b with Some (Value.Bool true) -> true | _ -> false)
  in
  let refuted i =
    i.unfolded && (not (selected i))
    && match ground_eval env i.lformula with Some false -> true | _ -> false
  in
  let bmap bs =
    Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
    @@ List.filter_map bs ~f:(fun (x, x', _) ->
        Option.map (Map.Poly.find env x') ~f:(fun v -> (x, v)))
  in
  let dedup l =
    List.fold l ~init:[] ~f:(fun acc c ->
        if
          List.exists acc ~f:(fun c' ->
              Ident.pvar_equal c.cpred c'.cpred
              && List.for_all2_exn c.cvals c'.cvals ~f:veq)
        then acc
        else acc @ [ c ])
  in
  let rec node i =
    let cvals = List.map i.largs ~f:(Evaluator.eval_term ~env) in
    {
      cpred = i.lpred;
      cvals;
      binders = bmap i.lbinders;
      children = dedup (List.map (List.filter i.lkids ~f:refuted) ~f:node);
    }
  in
  {
    qbinders = bmap qbinders;
    roots = dedup (List.map (List.filter roots ~f:refuted) ~f:node);
  }

(* the deepest lasso unfolding asked: stem and one round together *)
let lasso_max_depth = 256

(* [search_lasso ~id ~print received hints]: lasso candidates from the query
   unfolded 1, 2, ..., 8, 16, ... applications deep, each depth asked first
   with the hints restricting the back edges' targets and then without; at
   each depth whose candidate does not replay the next depth is asked.
   Returns the first replayed lasso, or the last reason. *)
let search_lasso ~id ~print ~source (received : MuCLP.Problem.t) hints =
  let fenv = LogicOld.get_fenv () in
  let ask phi =
    if Z3Smt.Z3interface.may_not_return phi then None
    else
      match
        try
          Z3Smt.Z3interface.check_sat ~id ~timeout:(Some query_timeout_ms) fenv
            [ phi ]
        with exn_ when not (Common.Timer.is_async exn_) ->
          `Unknown (Exn.to_string exn_)
      with
      | `Sat model -> Some model
      | `Unsat -> None
      | `Timeout | `Unknown _ ->
          print @@ lazy "lasso search: a question was not decided";
          None
  in
  let has_hints =
    Hashtbl.Poly.exists hints ~f:(fun l -> not (List.is_empty l))
  in
  let last = ref "no lasso was found within the search budget" in
  let rec go depth =
    if depth > lasso_max_depth then Error ("no-lasso-found", !last)
    else
      let try_with h =
        match unfold_lasso received ~hints:h depth with
        | exception Too_large -> `Too_large
        | (_, _, phi, side) as u -> (
            match ask (Formula.mk_and (Formula.mk_neg phi) side) with
            | None -> `No
            | Some model -> (
                match replay_lasso ~source received (read_lasso model u) with
                | Ok v -> `Found v
                | Error why ->
                    last := sprintf "depth %d: not replayed: %s" depth why;
                    `No))
      in
      let r =
        match if has_hints then try_with (Some hints) else `No with
        | `Found v -> `Found v
        | _ -> try_with None
      in
      print
      @@ lazy
           (sprintf "lasso search: depth %d: %s" depth
              (match r with
              | `Found _ -> "found"
              | `No -> "none"
              | `Too_large -> "too large"));
      match r with
      | `Found v -> Ok v
      | `Too_large -> Error ("no-lasso-found", !last ^ " (the unfolding grew too large)")
      | `No -> go (if depth < 8 then depth + 1 else depth * 2)
  in
  go 1

(* -- The entry ------------------------------------------------------------- *)

(* the deepest unfolding asked (applications from the query to the error,
   callee summaries included) *)
let search_max_depth = 1024

let rec no_exists = function
  | Formula.Atom _ -> true
  | Formula.UnaryOp (_, phi, _) -> no_exists phi
  | Formula.BinaryOp (_, a, b, _) -> no_exists a && no_exists b
  | Formula.Bind (Forall, _, phi, _) -> no_exists phi
  | Formula.Bind ((Exists | Random _), _, _, _) | Formula.LetRec _ -> false
  | Formula.LetFormula (_, _, _, phi, _) -> no_exists phi

let is_safety_shape (p : MuCLP.Problem.t) =
  no_exists p.query
  && List.for_all p.preds ~f:(fun (q : MuCLP.Pred.t) -> no_exists q.body)
  && List.for_all p.preds ~f:(fun (q : MuCLP.Pred.t) ->
      Stdlib.( <> ) q.kind Predicate.Mu)

(* [of_refutation ~id ~received ~solved r]: a replayed violation path of
   [received] from the primal's refutation [r] of [solved] (the problem the
   reduction received), or [Error (reason, detail)] saying why there is
   none.  Never raises except an asynchronous exception (a timeout). *)
(* [find ~id ~print ~source received hints]: a searched, replayed path *)
let find ~id ~print ~source received hints =
  match
    try search ~id ~print ~max_depth:search_max_depth received hints
    with exn_ when not (Common.Timer.is_async exn_) -> None
  with
  | None ->
      Error
        ( "no-path-found",
          "no refutation tree of the received problem was found within the \
           search budget" )
  | Some cand -> (
      match replay ~source received cand with
      | Ok v -> Ok v
      | Error why -> Error ("path-not-replayed", why))

let not_safety =
  Error
    ( "no-path-found",
      "not a safety problem (a least fixpoint or an existential): \
       non-termination paths are not built" )

(* [of_ground ~id ~received]: a replayed path of [received] whose query was
   decided invalid without a refutation (the ground decision), found by the
   unguided search *)
let of_ground ~id ?(print = fun _ -> ()) ~(received : MuCLP.Problem.t) () =
  if not (is_safety_shape received) then not_safety
  else
    find ~id ~print ~source:"ground-unrolling" received (Hashtbl.Poly.create ())

let of_refutation ~id ?(print = fun _ -> ()) ~(received : MuCLP.Problem.t)
    ~solved (r : PCSP.Problem.refutation option) :
    (Witness.violation, string * string) result =
  if not (is_safety_shape received) then not_safety
  else
    match r with
    | None ->
        Error
          ( "no-refutation-recorded",
            "the constraint solver did not record its refutation (its \
             witness.unsat setting)" )
    | Some (Proof rf) ->
        let hints = hints received solved rf in
        print
        @@ lazy
             (sprintf "violation: the refutation\n%s"
                (PCSP.Refutation.str_of rf));
        print
        @@ lazy
             (sprintf "violation: hints %s"
                (String.concat_map_list ~sep:"; " (Hashtbl.Poly.to_alist hints)
                   ~f:(fun (p, hs) ->
                     sprintf "%s: %d" (Ident.name_of_pvar p) (List.length hs))));
        find ~id ~print ~source:"refutation" received hints
    | Some _ ->
        Error
          ( "no-refutation-recorded",
            "the refutation is not a derivation (a formula, a counterexample \
             or an external one)" )


(* -- Non-termination: the entry ------------------------------------------- *)

(* a termination problem in the sense of the lasso search: universal binders
   only, and at least one least fixpoint *)
let is_nontermination_shape (p : MuCLP.Problem.t) =
  no_exists p.query
  && List.for_all p.preds ~f:(fun (q : MuCLP.Pred.t) -> no_exists q.body)
  && List.exists p.preds ~f:(fun (q : MuCLP.Pred.t) ->
      Stdlib.( = ) q.kind Predicate.Mu)

(* [cycle_head received]: [Ok w] when [received] has exactly one least
   fixpoint [w].  For the direct LLVM translation of a termination problem
   the least fixpoints are exactly the program side's cut points, and the
   cut points cut every cycle of the program (recursion included; assumed of
   the frontend), so every infinite execution passes [w] infinitely often:
   a non-termination witness whose only cycle waypoint is at [w]'s loop
   location with constraint [1] is valid as soon as the query is invalid.
   Syntactic: no solver, no path. *)
let cycle_head (received : MuCLP.Problem.t) =
  match
    List.filter received.preds ~f:(fun (q : MuCLP.Pred.t) ->
        Stdlib.( = ) q.kind Predicate.Mu)
  with
  | [ w ] -> Ok w
  | [] -> Error ("no-cut-point", "the problem has no least fixpoint")
  | ws ->
      Error
        ( "several-cut-points",
          sprintf
            "%d least fixpoints (%s): a cycle head alone needs exactly one"
            (List.length ws)
            (String.concat_map_list ~sep:", " ws ~f:(fun (q : MuCLP.Pred.t) ->
                 Ident.name_of_pvar q.name)) )

(* [of_nontermination ~id ~received ~solved r]: the non-termination evidence
   of an invalid verdict on [received], cheapest sufficient first: a
   replayed lasso ([`Lasso], searched with the hints [r] gives, then
   without), else the cycle head ([`Head (w, why_no_lasso)]), else
   [Error (reason, detail)].  Never raises except an asynchronous
   exception. *)
let of_nontermination ~id ?(print = fun _ -> ()) ~(received : MuCLP.Problem.t)
    ~solved (r : PCSP.Problem.refutation option) =
  if not (is_nontermination_shape received) then
    Error
      ( "no-path-found",
        "not a termination problem (an existential, or no least fixpoint)" )
  else
    let hints =
      match r with
      | Some (Proof rf) ->
          print
          @@ lazy
               (sprintf "lasso: the refutation\n%s" (PCSP.Refutation.str_of rf));
          cycle_hints received solved rf
      | _ -> Hashtbl.Poly.create ()
    in
    print
    @@ lazy
         (sprintf "lasso: hints %s"
            (String.concat_map_list ~sep:"; " (Hashtbl.Poly.to_alist hints)
               ~f:(fun (p, hs) ->
                 sprintf "%s: %d" (Ident.name_of_pvar p) (List.length hs))));
    let source =
      match r with Some (Proof _) -> "refutation" | _ -> "lasso-search"
    in
    let lasso =
      try search_lasso ~id ~print ~source received hints
      with exn_ when not (Common.Timer.is_async exn_) ->
        Error ("no-lasso-found", "the search raised " ^ Exn.to_string exn_)
    in
    match lasso with
    | Ok v -> Ok (`Lasso v)
    | Error (reason, detail) -> (
        print @@ lazy (sprintf "lasso: %s: %s" reason detail);
        match cycle_head received with
        | Ok w -> Ok (`Head (w, (reason, detail)))
        | Error (r2, d2) ->
            Error (reason, sprintf "%s; no cycle head: %s (%s)" detail r2 d2))
