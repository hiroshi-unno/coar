(* Non-termination evidence for an invalid verdict of a termination problem
   (least fixpoints present, universal binders only), about the problem MuVal
   RECEIVED.  Four sources, each handed out only after a check on the received
   problem that does not trust where the candidate came from:

   - a LASSO from the unfolding search ([Violation.search_lasso]);
   - a LASSO from a WALK: a deterministic simulation of the received problem
     from its query, each universal binder (a nondeterministic value) chosen
     by the term the dual's solution gives it (the Skolem function of its
     existential in the dual) or by a constant, until a configuration repeats;
     replayed with [Violation.replay_lasso];
   - a RECURRENT SET [D] of a least fixpoint [w] (a program-side cut point)
     with a stem into it.  [D] and the terms [f] choosing the binders of one
     round of [w]'s body are guessed (from the dual's solution, read by name or
     by sort, and from the variables in scope and small constants) and
     strengthened by one-round preimages; they are kept only when the
     quantifier-free formula [D(s) => pre_f(D)(s)] is valid, where
     [pre_f(D)(s)] says that [w]'s body at [s], with every [fix] application
     unfolded, every binder at its term, every application of [w] at [t] read
     as [not D(t)] and every other application as true, is false.  Then from a
     state in [D] the body is false by an application of [w] at a state in [D]
     (a round of the loop reaching [w] again in [D], with the values the terms
     give), so by induction there is an infinite run passing [w] in [D] at
     every visit: [w] is refuted at every state of [D].  The stem is a
     refutation tree of the query whose one leaf reads [w] at a state in [D],
     found by Z3 and replayed by ground evaluation
     ([Violation.replay_gen ~target]);
   - the CYCLE HEAD of a problem with one least fixpoint
     ([Violation.cycle_head]), which needs no path.

   For the direct LLVM translation a recurrent set's round is a program path
   when no return summary is read false, which the reading above ensures (it
   reads every other application as true). *)
open Core
open Common.Ext
open Ast
open Ast.LogicOld
module V = Violation

(* -- The dual's solution, by name ----------------------------------------- *)

(* the sets the dual's solution gives its predicates ([U_P_]: parameters and
   formula) and the terms it gives the Skolem functions of its existentials
   ([FN_P_x_]: the dependencies and the term the last parameter equals) *)
type dual = {
  sets : (string * (sort_env_list * Formula.t)) list;
  terms : (string * (sort_env_list * Term.t)) list;
}

let empty_dual = { sets = []; terms = [] }

let strip ~prefix name =
  let lp = String.length prefix in
  if
    String.is_prefix name ~prefix
    && String.is_suffix name ~suffix:"_"
    && String.length name > lp + 1
  then Some (String.sub name ~pos:lp ~len:(String.length name - lp - 1))
  else None

(* a [case sel [b0 | ... | bn-1]] term (the constraint solver's piecewise
   template: the [sel]th branch, counted from 0) rewritten to its branch when
   [sel] is a numeral and to nested if-then-else otherwise, so that Z3 and the
   evaluator read it *)
let decase =
  Term.map_term true ~f:(function
    | Term.FunApp (T_int.Case n, sel :: branches, _)
      when List.length branches = n && n > 0 -> (
        match sel with
        | Term.FunApp (T_int.Int k, [], _)
          when Z.(leq zero k && lt k (of_int n)) ->
            List.nth_exn branches (Z.to_int k)
        | _ ->
            let last = List.last_exn branches in
            List.foldi (List.rev (List.drop_last_exn branches)) ~init:last
              ~f:(fun i acc b ->
                let k = n - 2 - i in
                T_bool.ifte (Formula.eq sel (T_int.mk_int (Z.of_int k))) b acc))
    | t -> t)

let dual_of_solution (sol : Logic.term_subst_map) =
  Map.Poly.fold sol ~init:empty_dual ~f:(fun ~key ~data acc ->
      try
        let args, term = Logic.ExtTerm.let_lam data in
        let phi =
          Logic.ExtTerm.to_old_formula Map.Poly.empty
            (Map.Poly.of_alist_exn args) term []
          |> Formula.map_term ~f:decase
        in
        let params =
          List.map args ~f:(fun (x, s) -> (x, Logic.ExtTerm.to_old_sort s))
        in
        let name = Ident.name_of_tvar key in
        match strip ~prefix:"FN_" name with
        | Some n -> (
            match List.last params with
            | None -> acc
            | Some (r, _) -> (
                let is_r = function
                  | Term.Var (x, _, _) -> Ident.tvar_equal x r
                  | _ -> false
                in
                let free t = not (Set.mem (Term.tvs_of t) r) in
                match phi with
                | Formula.Atom
                    (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _) ->
                    let t =
                      if is_r a && free b then Some b
                      else if is_r b && free a then Some a
                      else None
                    in
                    Option.value_map t ~default:acc ~f:(fun t ->
                        {
                          acc with
                          terms = (n, (List.drop_last_exn params, t)) :: acc.terms;
                        })
                | _ -> acc))
        | None -> (
            match strip ~prefix:"U_" name with
            | Some n -> { acc with sets = (n, (params, phi)) :: acc.sets }
            | None -> acc)
      with exn_ when not (Common.Timer.is_async exn_) -> acc)

(* -- One round of a cut point ---------------------------------------------- *)

let is_fix (q : MuCLP.Pred.t) = Stdlib.( = ) q.kind Predicate.MuOrNu

(* [contexts received w]: the binders of [w]'s round ([w]'s body, each [fix]
   application unfolded), each once, in the order met: (the predicate whose
   body binds it, the binder, its sort, the variables in scope there in
   order: the predicate's parameters, then the earlier binders) *)
let contexts (received : MuCLP.Problem.t) (w : MuCLP.Pred.t) =
  let out = ref [] in
  let rec go fuel (p : MuCLP.Pred.t) scope phi =
    match phi with
    | Formula.Atom (Atom.App (Predicate.Var (q, _), _, _), _) -> (
        match V.find_pred received q with
        | Some q' when is_fix q' && fuel > 0 -> go (fuel - 1) q' q'.args q'.body
        | _ -> ())
    | Formula.Atom _ -> ()
    | Formula.UnaryOp (_, a, _) -> go fuel p scope a
    | Formula.BinaryOp (_, a, b, _) ->
        go fuel p scope a;
        go fuel p scope b
    | Formula.Bind (_, xs, body, _) ->
        let scope =
          List.fold xs ~init:scope ~f:(fun scope (x, s) ->
              if
                not
                  (List.exists !out ~f:(fun (p', x', _, _) ->
                       Ident.pvar_equal p' p.name && Ident.tvar_equal x x'))
              then out := (p.name, x, s, scope) :: !out;
              scope @ [ (x, s) ])
        in
        go fuel p scope body
    | Formula.LetFormula (x, s, _, body, _) -> go fuel p (scope @ [ (x, s) ]) body
    | Formula.LetRec _ -> ()
  in
  go (List.length received.preds) w w.args w.body;
  List.rev !out

exception Not_readable

(* [pre received w ~choice (dparams, d)]: over [w]'s parameters, the formula
   saying that [w]'s body there, with every [fix] application unfolded, each
   binder [x] of a predicate [p] at the term [choice p x] (over [p]'s scope),
   each application of [w] at [t] read as [not d(t)] and every other
   application as true, is FALSE.  Raises [Not_readable] on a shape this
   reading does not cover (an application under a negation or in a premise,
   an existential). *)
let pre (received : MuCLP.Problem.t) (w : MuCLP.Pred.t) ~choice
    ((dparams : sort_env_list), d) =
  let d_at args =
    Formula.subst
      (Map.Poly.of_alist_exn (List.zip_exn (List.map dparams ~f:fst) args))
      d
  in
  let has_pvar phi = not (Set.is_empty (Formula.pvs_of phi)) in
  let rec go fuel (p : MuCLP.Pred.t) sub phi =
    match phi with
    | Formula.Atom (Atom.App (Predicate.Var (q, _), args, _), _) -> (
        let args = List.map args ~f:(Term.subst sub) in
        if Ident.pvar_equal q w.name then Formula.mk_neg (d_at args)
        else
          match V.find_pred received q with
          | Some q' when is_fix q' && fuel > 0 ->
              go (fuel - 1) q'
                (Map.Poly.of_alist_exn
                   (List.zip_exn (List.map q'.args ~f:fst) args))
                q'.body
          | _ -> Formula.mk_true ())
    | Formula.Atom _ -> Formula.subst sub phi
    | Formula.UnaryOp (_, a, _) when has_pvar a -> raise Not_readable
    | Formula.UnaryOp _ -> Formula.subst sub phi
    | Formula.BinaryOp (Imply, a, _, _) when has_pvar a -> raise Not_readable
    | Formula.BinaryOp ((Iff | Xor), a, b, _) when has_pvar a || has_pvar b ->
        raise Not_readable
    | Formula.BinaryOp (op, a, b, info) ->
        Formula.mk_binop ~info op (go fuel p sub a) (go fuel p sub b)
    | Formula.Bind (Forall, xs, body, _) ->
        let sub =
          List.fold xs ~init:sub ~f:(fun sub (x, _) ->
              match choice p.name x with
              | Some t -> Map.Poly.set sub ~key:x ~data:(Term.subst sub t)
              | None -> raise Not_readable)
        in
        go fuel p sub body
    | Formula.LetFormula (x, _, def, body, _) ->
        go fuel p (Map.Poly.set sub ~key:x ~data:(Term.subst sub def)) body
    | Formula.Bind _ | Formula.LetRec _ -> raise Not_readable
  in
  Formula.mk_neg (go (List.length received.preds) w Map.Poly.empty w.body)

(* -- Candidates ------------------------------------------------------------ *)

let dedup_terms l =
  List.fold l ~init:[] ~f:(fun acc t ->
      if List.exists acc ~f:(fun t' -> String.equal (Term.str_of t) (Term.str_of t'))
      then acc
      else acc @ [ t ])

(* every assignment of [params] to variables of [scope] of the same sort, at
   most [cap] of them *)
let mappings (params : sort_env_list) (scope : sort_env_list) cap =
  let rec go = function
    | [] -> [ [] ]
    | (x, s) :: rest ->
        let tails = go rest in
        List.concat_map
          (List.filter scope ~f:(fun (_, s') -> Stdlib.( = ) s s'))
          ~f:(fun (y, s') ->
            List.map tails ~f:(fun tl -> (x, Term.mk_var y s') :: tl))
  in
  List.take (go params) cap

let max_mappings = 8

(* the candidate terms for one binder: the dual's term for it by name (the
   Skolem function [FN_P_x_] of the binder [x] of [P], its first parameters
   [P]'s and the rest the binders just before [x]), every dual term with its
   parameters mapped onto the scope by sort, the variables in scope of the
   binder's sort, and 0 and 1 (or [true] and [false]) *)
let candidates dual (received : MuCLP.Problem.t) (p, x, s, scope) =
  let byname =
    match
      List.Assoc.find dual.terms ~equal:String.equal
        (Ident.name_of_pvar p ^ "_" ^ Ident.name_of_tvar x)
    with
    | None -> []
    | Some (params, t) -> (
        match V.find_pred received p with
        | None -> []
        | Some pr ->
            let n = List.length pr.args in
            let d = List.length params - n in
            let before = List.drop scope n in
            if d < 0 || d > List.length before then []
            else
              let targets = pr.args @ List.drop before (List.length before - d) in
              if
                List.for_all2_exn params targets ~f:(fun (_, s1) (_, s2) ->
                    Stdlib.( = ) s1 s2)
              then
                [
                  Term.subst
                    (Map.Poly.of_alist_exn
                       (List.map2_exn params targets ~f:(fun (a, _) (b, s) ->
                            (a, Term.mk_var b s))))
                    t;
                ]
              else [])
  in
  let mapped =
    List.concat_map dual.terms ~f:(fun (_, (params, t)) ->
        if List.length params > 3 then []
        else
          List.map (mappings params scope max_mappings) ~f:(fun m ->
              Term.subst (Map.Poly.of_alist_exn m) t))
  in
  let vars =
    List.filter_map scope ~f:(fun (y, s') ->
        if Stdlib.( = ) s s' then Some (Term.mk_var y s') else None)
  in
  let consts =
    match s with
    | T_int.SInt -> [ T_int.zero (); T_int.one () ]
    | T_bool.SBool -> [ T_bool.mk_true (); T_bool.mk_false () ]
    | _ -> []
  in
  let scope_names = Set.Poly.of_list (List.map scope ~f:fst) in
  dedup_terms (byname @ mapped @ vars @ consts)
  |> List.filter ~f:(fun t -> Set.is_subset (Term.tvs_of t) ~of_:scope_names)

(* the starting sets for [w]: the dual's set of [w] by name (same arity,
   positional), every dual set with its parameters mapped onto [w]'s by sort,
   and [true] *)
let start_sets dual (w : MuCLP.Pred.t) =
  let byname =
    match List.Assoc.find dual.sets ~equal:String.equal (Ident.name_of_pvar w.name) with
    | Some (params, phi) when List.length params = List.length w.args ->
        [
          Formula.subst
            (Map.Poly.of_alist_exn
               (List.map2_exn params w.args ~f:(fun (a, _) (b, s) ->
                    (a, Term.mk_var b s))))
            phi;
        ]
    | _ -> []
  in
  let mapped =
    List.concat_map dual.sets ~f:(fun (_, (params, phi)) ->
        if List.is_empty params || List.length params > 3 then []
        else
          List.map (mappings params w.args max_mappings) ~f:(fun m ->
              Formula.subst (Map.Poly.of_alist_exn m) phi))
  in
  let all = byname @ mapped @ [ Formula.mk_true () ] in
  List.fold all ~init:[] ~f:(fun acc phi ->
      if List.exists acc ~f:(fun phi' -> String.equal (Formula.str_of phi) (Formula.str_of phi'))
      then acc
      else acc @ [ phi ])
  |> fun l -> List.take l 8

(* -- Recurrent sets (Theorem 9's check) ------------------------------------ *)

let check_timeout_ms = 2_000
let max_combos = 48
let max_queries = 150
let max_strengthening = 2

let valid ~id phi =
  let fenv = LogicOld.get_fenv () in
  (not (Z3Smt.Z3interface.may_not_return phi))
  &&
  try Z3Smt.Z3interface.is_valid ~id ~timeout:(Some check_timeout_ms) fenv phi
  with exn_ when not (Common.Timer.is_async exn_) -> false

(* [recurrent ~id ~print received dual w]: a set [D] over [w]'s parameters
   and the binder terms of [w]'s round such that [D => pre(D)] is valid, or
   [Error why] *)
let recurrent ~id ~print (received : MuCLP.Problem.t) dual (w : MuCLP.Pred.t) =
  let ctxs = contexts received w in
  let combos =
    List.fold ctxs ~init:[ [] ] ~f:(fun combos ((p, x, _, _) as c) ->
        let cands = candidates dual received c in
        print
        @@ lazy
             (sprintf "recurrent set of %s: binder %s of %s: %s"
                (Ident.name_of_pvar w.name) (Ident.name_of_tvar x)
                (Ident.name_of_pvar p)
                (String.concat_map_list ~sep:" | " cands ~f:Term.str_of));
        List.take
          (List.concat_map combos ~f:(fun combo ->
               List.map cands ~f:(fun t -> combo @ [ ((p, x), t) ])))
          max_combos)
  in
  let starts = start_sets dual w in
  let queries = ref 0 in
  let try_one combo d0 =
    let choice p x =
      List.find_map combo ~f:(fun ((p', x'), t) ->
          if Ident.pvar_equal p p' && Ident.tvar_equal x x' then Some t else None)
    in
    let rec go k d =
      if k > max_strengthening || !queries >= max_queries then None
      else
        match pre received w ~choice (w.args, d) with
        | exception Not_readable -> None
        | exception exn_ when not (Common.Timer.is_async exn_) -> None
        | p ->
            incr queries;
            if valid ~id (Formula.mk_imply d p) then (
              (* an empty set passes the check vacuously: keep [d] only
                 when Z3 shows it is not empty *)
              incr queries;
              if valid ~id (Formula.mk_neg d) then None
              else if
                (not (Z3Smt.Z3interface.may_not_return d))
                &&
                match
                  try
                    Z3Smt.Z3interface.check_sat ~id
                      ~timeout:(Some check_timeout_ms) (LogicOld.get_fenv ())
                      [ d ]
                  with exn_ when not (Common.Timer.is_async exn_) ->
                    `Unknown (Exn.to_string exn_)
                with
                | `Sat _ -> true
                | _ -> false
              then Some d
              else None)
            else go (k + 1) (Formula.and_of [ d; p ])
    in
    go 0 d0
  in
  let found =
    List.find_map combos ~f:(fun combo ->
        List.find_map starts ~f:(fun d0 ->
            Option.map (try_one combo d0) ~f:(fun d -> (d, combo))))
  in
  print
  @@ lazy
       (sprintf "recurrent set of %s: %d binders, %d choices, %d starts, %d questions: %s"
          (Ident.name_of_pvar w.name) (List.length ctxs) (List.length combos)
          (List.length starts) !queries
          (match found with Some (d, _) -> Formula.str_of d | None -> "none"));
  match found with
  | Some r -> Ok r
  | None ->
      Error
        (sprintf "%s: no recurrent set among %d binder choices and %d starting sets"
           (Ident.name_of_pvar w.name) (List.length combos) (List.length starts))

(* -- The stem into a recurrent set ----------------------------------------- *)

(* [unfold_target received w d depth]: [Violation.unfold] with every
   application of [w] at [t] read as [not d(t)] (refuted exactly when [t] is
   in [d]) instead of unfolded *)
let unfold_target (received : MuCLP.Problem.t) (w : MuCLP.Pred.t) d depth =
  let count = ref 0 in
  let d_at args =
    Formula.subst
      (Map.Poly.of_alist_exn (List.zip_exn (List.map w.args ~f:fst) args))
      d
  in
  let rec instance pvar args depth =
    incr count;
    if !count > V.max_instances then raise V.Too_large;
    let pred = Option.value_exn (V.find_pred received pvar) in
    let sub =
      Map.Poly.of_alist_exn
      @@ List.map2_exn pred.args args ~f:(fun (x, _) t -> (x, t))
    in
    let binders, kids, phi = formula sub depth pred.body in
    V.{ ipred = pvar; iargs = args; ibinders = binders; iformula = phi; kids }
  and formula sub depth phi =
    let binders = ref [] in
    let kids = ref [] in
    let rec go sub = function
      | Formula.Atom (Atom.App (Predicate.Var (q, _), args, _), _) ->
          let args = List.map args ~f:(Term.subst sub) in
          if Ident.pvar_equal q w.name then Formula.mk_neg (d_at args)
          else if depth <= 0 || Option.is_none (V.find_pred received q) then
            Formula.mk_true ()
          else
            let k = instance q args (depth - 1) in
            kids := k :: !kids;
            k.iformula
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
          let body = go (Map.Poly.set sub ~key:x ~data:(Term.mk_var x' s)) body in
          Formula.mk_and (Formula.eq (Term.mk_var x' s) def) body
      | phi -> raise (Invalid_argument ("the shape of " ^ Formula.str_of phi))
    in
    let phi = go sub phi in
    (List.rev !binders, List.rev !kids, phi)
  in
  formula Map.Poly.empty depth received.query

let stem_max_depth = 64

(* [stem ~id ~print received w d]: a replayed path from the query to an
   application of [w] at a state in [d], with that state *)
let stem ~id ~print (received : MuCLP.Problem.t) (w : MuCLP.Pred.t) d =
  let fenv = LogicOld.get_fenv () in
  let holds vs =
    let env =
      Map.Poly.of_alist_exn (List.map2_exn w.args vs ~f:(fun (x, _) v -> (x, v)))
    in
    match V.ground_eval env d with Some true -> true | _ -> false
  in
  let last = ref "no stem was found within the search budget" in
  let rec go depth =
    if depth > stem_max_depth then Error !last
    else
      let r =
        match unfold_target received w d depth with
        | exception V.Too_large -> `Too_large
        | (_, _, phi) as u -> (
            let phi = Formula.mk_neg phi in
            if Z3Smt.Z3interface.may_not_return phi then (
              last := "the stem question may not return (its shape)";
              `No)
            else
              match
                try
                  Z3Smt.Z3interface.check_sat ~id
                    ~timeout:(Some V.query_timeout_ms) fenv [ phi ]
                with exn_ when not (Common.Timer.is_async exn_) ->
                  `Unknown (Exn.to_string exn_)
              with
              | `Sat model -> (
                  let entry = ref None in
                  match
                    V.replay_gen ~target:(w.name, holds)
                      ~on_target:(fun _ vs -> entry := Some vs)
                      ~lasso:false ~source:"recurrent-stem" received
                      (V.read model u)
                  with
                  | Ok v -> `Found (v, Option.value_exn !entry)
                  | Error why ->
                      last := sprintf "depth %d: not replayed: %s" depth why;
                      `No)
              | `Unsat -> `No
              | `Timeout | `Unknown _ ->
                  last := sprintf "depth %d: Z3 did not decide" depth;
                  `No)
      in
      print
      @@ lazy
           (sprintf "stem search: depth %d: %s" depth
              (match r with
              | `Found _ -> "found"
              | `No -> "none"
              | `Too_large -> "too large"));
      match r with
      | `Found x -> Ok x
      | `Too_large -> Error (!last ^ " (the unfolding grew too large)")
      | `No -> go (if depth < 8 then depth + 1 else depth * 2)
  in
  go 1

(* -- The walk -------------------------------------------------------------- *)

let max_walk_steps = 2_000

(* [walk received dual ~seed]: from the query, at each configuration the
   body's binders chosen by the dual's term for them by name (evaluated at
   the values in scope) or else [seed] (an integer; [seed <> 0] for a
   Boolean), the body falsified reading every application false, and the
   one application it reads followed.  [Ok (cand, visits)] when a
   configuration repeats: a lasso candidate (the configurations from the
   first visit of the repeated one on, each the only child of the one
   before, the last reading the first by its back edge); [Error (why,
   visits)] when the body is not false (the choices let the run end), reads
   several applications (a call), or the budget runs out.  [visits] counts
   the visits per predicate. *)
let walk (received : MuCLP.Problem.t) dual ~seed =
  let visits = Hashtbl.Poly.create () in
  let choose (p : Ident.pvar) env x s =
    let named =
      List.Assoc.find dual.terms ~equal:String.equal
        (Ident.name_of_pvar p ^ "_" ^ Ident.name_of_tvar x)
    in
    let from_term =
      match (named, V.find_pred received p) with
      | Some (params, t), Some pr -> (
          (* the first parameters are [p]'s, the rest the binders bound just
             before [x], which [env] holds *)
          let n = List.length pr.args in
          if List.length params < n then None
          else
            let own, deps = List.split_n params n in
            let dep_vals =
              (* the binders in scope that are not parameters, in the order
                 [env] cannot give: only the case without dependencies is
                 read *)
              if List.is_empty deps then Some [] else None
            in
            match dep_vals with
            | None -> None
            | Some _ -> (
                try
                  let sub =
                    Map.Poly.of_alist_exn
                      (List.map2_exn own pr.args ~f:(fun (a, _) (b, s) ->
                           (a, Term.mk_var b s)))
                  in
                  Some (Evaluator.eval_term ~env (Term.subst sub t))
                with exn_ when not (Common.Timer.is_async exn_) -> None))
      | _ -> None
    in
    match from_term with
    | Some v -> Some v
    | None -> (
        match s with
        | T_int.SInt -> Some (Value.Int (Z.of_int seed))
        | T_bool.SBool -> Some (Value.Bool (seed <> 0))
        | _ -> None)
  in
  (* one step: the binders met and the one application read false *)
  let step (p : Ident.pvar option) env body =
    let apps = ref [] in
    let child q vs =
      apps := !apps @ [ (q, vs) ];
      Some (List.length !apps - 1)
    in
    let choose env x s =
      match p with
      | Some p -> choose p env x s
      | None -> (
          match s with
          | T_int.SInt -> Some (Value.Int (Z.of_int seed))
          | T_bool.SBool -> Some (Value.Bool (seed <> 0))
          | _ -> None)
    in
    match V.falsify_gen ~choose ~child env 0 body with
    | None -> Error "the body is not false at the chosen values"
    | Some (evs, _) -> (
        let reached =
          List.dedup_and_sort ~compare
            (List.filter_map evs ~f:(function V.EChild i -> Some i | _ -> None))
        in
        let binders =
          Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
            (List.filter_map evs ~f:(function
              | V.EBind (x, _, v) -> Some (x, v)
              | _ -> None))
        in
        match reached with
        | [ i ] -> Ok (binders, List.nth_exn !apps i)
        | [] -> Error "the body is false by its atoms"
        | _ -> Error "the body reads several applications (a call)")
  in
  let key q vs =
    Ident.name_of_pvar q ^ "(" ^ String.concat_map_list ~sep:"," vs ~f:Value.str_of ^ ")"
  in
  match step None Map.Poly.empty received.query with
  | Error why -> Error ("query: " ^ why, visits)
  | Ok (qbinders, first) ->
      let seen = Hashtbl.Poly.create () in
      (* [path]: the configurations visited, newest first, with their
         binders *)
      let rec go n path (q, vs) =
        Hashtbl.Poly.incr visits q;
        match Hashtbl.Poly.find seen (key q vs) with
        | Some j ->
            let path = List.rev path in
            let loop = List.drop path j in
            let rec nest = function
              | [] -> []
              | (q, vs, b) :: rest ->
                  [ V.{ cpred = q; cvals = vs; binders = b; children = nest rest } ]
            in
            let stem = List.take path j in
            let rec nest_stem = function
              | [] -> nest loop
              | (q, vs, b) :: rest ->
                  [ V.{ cpred = q; cvals = vs; binders = b; children = nest_stem rest } ]
            in
            Ok (V.{ qbinders; roots = nest_stem stem }, visits)
        | None -> (
            if n >= max_walk_steps then Error ("the step budget ran out", visits)
            else
              match V.find_pred received q with
              | None -> Error ("not a received predicate", visits)
              | Some pr -> (
                  Hashtbl.Poly.set seen ~key:(key q vs) ~data:n;
                  let env =
                    Map.Poly.of_alist_exn
                      (List.map2_exn pr.args vs ~f:(fun (x, _) v -> (x, v)))
                  in
                  match step (Some q) env pr.body with
                  | Error why ->
                      Error (sprintf "at %s: %s" (key q vs) why, visits)
                  | Ok (b, next) -> go (n + 1) ((q, vs, b) :: path) next))
      in
      go 0 [] first

let walk_seeds = [ 1; 0; 2; -1 ]

(* -- The entry ------------------------------------------------------------- *)

type evidence =
  | Lasso of Witness.violation
  | Recurrent of {
      w : MuCLP.Pred.t;
      set : Formula.t;
      stem : Witness.violation;
      entry : Value.t list;
    }
  | Head of MuCLP.Pred.t

(* [witness ~id ~received ~solved ~refutation ~solution]: the cheapest
   checked evidence (a lasso by search, a lasso by the walk, a recurrent set
   with its stem, the cycle head), with the reasons the earlier sources gave
   nothing; [Error (reason, detail)] when there is none.  Never raises except
   an asynchronous exception. *)
let witness ~id ?(print = fun _ -> ()) ~(received : MuCLP.Problem.t) ~solved
    ~(refutation : PCSP.Problem.refutation option) ~solution () =
  if not (V.is_nontermination_shape received) then
    Error
      ( "no-path-found",
        "not a termination problem (an existential, or no least fixpoint)" )
  else
    let protect f =
      try f ()
      with exn_ when not (Common.Timer.is_async exn_) ->
        Error ("raised " ^ Exn.to_string exn_)
    in
    let reasons = ref [] in
    let note src why =
      print @@ lazy (sprintf "%s: %s" src why);
      reasons := sprintf "%s: %s" src why :: !reasons
    in
    let hints =
      match refutation with
      | Some (PCSP.Problem.Proof rf) ->
          print
          @@ lazy
               (sprintf "lasso: the refutation\n%s" (PCSP.Refutation.str_of rf));
          V.cycle_hints received solved rf
      | _ -> Hashtbl.Poly.create ()
    in
    print
    @@ lazy
         (sprintf "lasso: hints %s"
            (String.concat_map_list ~sep:"; " (Hashtbl.Poly.to_alist hints)
               ~f:(fun (p, hs) ->
                 sprintf "%s: %d" (Ident.name_of_pvar p) (List.length hs))));
    let dual =
      match solution with
      | Some (PCSP.Problem.Sat sol) -> dual_of_solution sol
      | _ -> empty_dual
    in
    let source =
      match refutation with Some (Proof _) -> "refutation" | _ -> "lasso-search"
    in
    (* N1 *)
    match
      protect (fun () ->
          match V.search_lasso ~id ~print ~source received hints with
          | Ok v -> Ok v
          | Error (_, d) -> Error d)
    with
    | Ok v -> Ok (Lasso v, List.rev !reasons)
    | Error why -> (
        note "lasso search" why;
        (* N2 *)
        let visits = Hashtbl.Poly.create () in
        let walked =
          List.find_map walk_seeds ~f:(fun seed ->
              match protect (fun () ->
                  match walk received dual ~seed with
                  | Ok (cand, vs) ->
                      Hashtbl.Poly.merge_into ~src:vs ~dst:visits
                        ~f:(fun ~key:_ a b ->
                          Hashtbl.Merge_into_action.Set_to
                            (a + Option.value b ~default:0));
                      V.replay_lasso ~source:"walk" received cand
                  | Error (why, vs) ->
                      Hashtbl.Poly.merge_into ~src:vs ~dst:visits
                        ~f:(fun ~key:_ a b ->
                          Hashtbl.Merge_into_action.Set_to
                            (a + Option.value b ~default:0));
                      Error why)
              with
              | Ok v -> Some v
              | Error why ->
                  note (sprintf "walk (seed %d)" seed) why;
                  None)
        in
        match walked with
        | Some v -> Ok (Lasso v, List.rev !reasons)
        | None -> (
            (* N3, the cut points the walks visited most first *)
            let ws =
              List.filter received.preds ~f:(fun (q : MuCLP.Pred.t) ->
                  Stdlib.( = ) q.kind Predicate.Mu)
              |> List.stable_sort ~compare:(fun (a : MuCLP.Pred.t) b ->
                  compare
                    (Option.value ~default:0 (Hashtbl.Poly.find visits b.name))
                    (Option.value ~default:0 (Hashtbl.Poly.find visits a.name)))
            in
            let rec n3 = function
              | [] -> None
              | (w : MuCLP.Pred.t) :: rest -> (
                  match
                    protect (fun () ->
                        Result.bind (recurrent ~id ~print received dual w)
                          ~f:(fun (d, _) ->
                            Result.map (stem ~id ~print received w d)
                              ~f:(fun (v, entry) -> (d, v, entry))))
                  with
                  | Ok (set, stem, entry) -> Some (Recurrent { w; set; stem; entry })
                  | Error why ->
                      note (sprintf "recurrent set at %s" (Ident.name_of_pvar w.name)) why;
                      n3 rest)
            in
            match n3 ws with
            | Some e -> Ok (e, List.rev !reasons)
            | None -> (
                (* N0 *)
                match V.cycle_head received with
                | Ok w -> Ok (Head w, List.rev !reasons)
                | Error (r, d) ->
                    note "cycle head" (r ^ ": " ^ d);
                    Error
                      ( "no-lasso-found",
                        String.concat ~sep:"; " (List.rev !reasons) ))))
