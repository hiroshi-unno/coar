(* Function reconstruction, totality and lemmas for recursive functions.

   SOURCE.  Champion, Chiba, Kobayashi and Sato, "ICE-Based Refinement Type
   Discovery for Higher-Order Functional Programs", Journal of Automated
   Reasoning 64(7), 2020, section 5.2 ("function reconstruction") and the
   remark on invariant discovery after it.  The source omits the totality
   check and says its implementation is unsound for that reason; it is made
   here and every step below that it guards refuses when it is not proved.

   RECONSTRUCTION ([reconstruct]).  An ordinary Bool-valued unknown [rho] of
   arity k + 1 is ELIGIBLE when every clause mentioning it either has it as
   its only head atom and mentions no other unknown (a DEFINING clause), or
   has it in the body only and no other unknown in the head (a NEGATIVE
   clause).  A nullary unknown whose every body occurrence is alone in its
   clause (a goal marker, [body => ff] and [ff => false]) is not counted as
   another unknown.  The unknown must not occur in a clause's pure part.

   Each defining clause [C /\ rho(s_1, w_1) /\ .. => rho(u_1 .. u_k, t)] is
   NORMALISED over fresh formals [x_1 .. x_k]: the equations [x_i = u_i] and
   the equations of each cube of [C]'s disjunctive normal form are solved for
   the clause's variables -- a variable equal to a term over what is already
   known is replaced by it, an equation [T = c(e_1 .. e_n)] with [T] known
   becomes the tester [is-c(T)] and the equations [sel_i(T) = e_i], an integer
   equation with one unknown variable of coefficient one is solved for it.
   The [w_j] must be distinct variables (the results [y_j] of the recursive
   calls) and count as known.  A variable left unsolved, a guard that
   mentions a [y_j], or calls whose arguments depend on each other cyclically
   refuse the predicate.  The normalised clause is equivalent to the original
   one in every model: each step is the one-point rule or the identity
   [x = c(z) <=> is-c(x) /\ z = sel(x)], valid in the term algebra.

   The guards [g_1 .. g_n] must be proved MUTUALLY EXCLUSIVE (validity), or,
   for two branches with no recursive call, their results proved equal where
   both guards hold, and the function
     f(x) = ite(g_1, e_1, ite(g_2, e_2, .. e_n)),
     e_i = t_i with each y_j replaced by f(args_j) in call order,
   must be proved TOTAL ([total]).  Guards proved EXHAUSTIVE make [f] the
   function the clauses define; otherwise the clauses define a partial
   function, which is completed by a default value (an integer, real or
   Boolean result only; any other is refused) and is vocabulary only.  Then
   [f] is added to the function environment and its applications to the
   qualifier vocabulary; [rho] stays an unknown.

   WHY TOTALITY.  A [define-fun-rec] is read by the solver as the equation
   [forall x. f(x) = body]; for a non-terminating "definition" that equation
   may have many solutions or none, and an inconsistent one makes every query
   that declares it valid -- a candidate mentioning it would then be accepted
   whatever it says.  For a total function the equation has exactly one
   solution in each model, and it is the least solution of the defining
   clauses (well-founded induction on the arguments: exactly one guard holds
   and the premises' calls are smaller).

   REPLACEMENT ([replace]: optional).  With the totality proof and
   exhaustive guards, every
   occurrence [rho(a, b)] outside the defining clauses is replaced by
   [b = f(a)] and the defining clauses dropped; [rho] leaves the signature
   with the definition [lambda x y. y = f(x)].  Equisatisfiable: [rho] occurs
   elsewhere only as a premise, so those clauses are antitone in it and the
   least solution -- the graph of [f] -- is the best choice, and the graph
   satisfies every defining clause by the definition.

   TOTALITY ([total]).  The recursive calls of a body are collected with the
   condition under which each one's value can matter (the conditions of the
   enclosing [ite]s, and the left operand of an enclosing [and], [or] or
   [=>], read short-circuit); a call under any other binder refuses.  A
   lexicographic measure of one or two components is searched, a component
   being the size of a datatype argument (decreasing only to a proper
   subterm: a selector chain under its testers, after the eta rule
   [c(sel_1(T) .. sel_n(T)) = T]) or [max(e, 0)] for an integer argument, its
   negation, the difference of two integer arguments, or a sequence's length.
   For every call, the call's condition must make the measure decrease, as a
   validity question.  Each function the body applies other than [f] itself
   must already have been proved total: a validity question that declares a
   non-terminating definition proves nothing.

   LEMMAS ([lemmas]).  For a total function, candidates from the signature --
   an integer result [>= 0] and compared with each integer argument and each
   sequence argument's length; a sequence result's length compared with each
   sequence argument's; for a Boolean result, implications with each tester
   of each datatype argument -- are filtered to a jointly inductive set: each
   call's value is replaced by a fresh variable [r] assumed to satisfy the
   current set under the call's condition, and each candidate is kept when it
   then holds of the body, until nothing more is dropped.  Sound by
   well-founded induction on the measure [total] found.  The kept set is
   recorded as the function's property, [forall x. inv(x, f(x))] together
   with the instances at the body's recursive calls, which every query that
   reaches the function conjoins at each application it contains.

   Every validity question here has a resource limit and a kill budget; an
   undecided question counts as not proved, which refuses (or drops) and so
   never adds anything unproved. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

(* ---------------------------------------------------------------------- *)
(* Solver questions                                                        *)

let rlimit = 4_000_000
let kill_ms = 5000

(* The number of validity questions asked; read by a property check. *)
let questions = Atomic.make 0

let z3_valid ~(fenv : FunEnv.t) phi =
  match
    Z3Smt.Z3interface.with_rlimit ~label:"recon" (Some rlimit) @@ fun () ->
    Z3Smt.Z3interface.check_valid ~timeout:(Some kill_ms) ~fresh_solver:true
      ~id:None
      (Z3Smt.Z3interface.fenv_reached_by fenv phi)
      phi
  with
  | `Valid -> true
  | _ -> false
  | exception exn when not (Common.Timer.is_async exn) -> false

(* The oracle every question goes through.  A property check replaces it by
   one that lies, to show that a check fails when the oracle is wrong. *)
let oracle : (fenv:FunEnv.t -> Formula.t -> bool) ref = ref z3_valid

let valid ~fenv phi =
  Atomic.incr questions;
  !oracle ~fenv phi

(* ---------------------------------------------------------------------- *)
(* Small term utilities                                                    *)

exception Refuse of string

let refuse fmt = Printf.ksprintf (fun s -> raise (Refuse s)) fmt
let tvs_mem t x = Set.mem (Term.tvs_of t) x

let is_var_named x = function
  | Term.Var (y, _, _) -> Ident.tvar_equal x y
  | _ -> false

let formula_of_bool_term t =
  if T_bool.is_formula t then T_bool.let_formula t else Formula.of_bool_term t

let sdt_of_sort = function
  | T_dt.SDT dt when not (Datatype.is_codt dt) -> Some dt
  | _ -> None

(* [c(sel_1(T), .., sel_n(T))] with the selectors of [c] in order, rewritten
   to [T], bottom-up.  Equal to its input wherever the testers of the
   selectors it removes hold. *)
let rec eta t =
  match t with
  | Term.FunApp ((T_dt.DTCons (cname, _, dt) as sym), args, info) -> (
      let args = List.map args ~f:eta in
      let rebuilt () = Term.mk_fsym_app ~info sym args in
      match Datatype.look_up_cons dt cname with
      | None -> rebuilt ()
      | Some cons -> (
          let sels = Datatype.sels_of_cons cons in
          if List.is_empty sels || List.length sels <> List.length args then
            rebuilt ()
          else
            let inner =
              List.map2_exn sels args ~f:(fun sel a ->
                  match a with
                  | Term.FunApp (T_dt.DTSel (sname, _, _), [ t' ], _)
                    when String.equal sname (Datatype.name_of_sel sel) ->
                      Some t'
                  | _ -> None)
            in
            match inner with
            | Some t0 :: rest
              when List.for_all rest ~f:(function
                     | Some t' -> Stdlib.( = ) t' t0
                     | None -> false) ->
                t0
            | _ -> rebuilt ()))
  | Term.FunApp (sym, args, info) ->
      Term.mk_fsym_app ~info sym (List.map args ~f:eta)
  | _ -> t

(* When [t] is a chain of selectors over the variable [x], of depth at least
   one, the testers that make each selector applied to its own constructor;
   [None] otherwise. *)
let selector_chain_testers x t =
  let rec go acc = function
    | Term.FunApp (T_dt.DTSel (sname, dt, _), [ inner ], _) -> (
        match Datatype.look_up_cons_of_sel dt sname with
        | None -> None
        | Some cons ->
            let tester =
              Formula.mk_atom
              @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) inner
            in
            go (tester :: acc) inner)
    | t when is_var_named x t -> if List.is_empty acc then None else Some acc
    | _ -> None
  in
  go [] t

(* ---------------------------------------------------------------------- *)
(* Recursive calls of a body, with the condition under which each matters  *)

type call = {
  r : Ident.tvar;  (** stands for the call's value in [abstracted] *)
  path : Formula.t;
  args : Term.t list;  (** inner calls replaced by their [r]s *)
  orig_args : Term.t list;  (** as written in the body *)
}

(* The calls of [f] in [body] and [body] with each call replaced by its [r].
   Raises [Refuse] when a call sits where its condition cannot be read (under
   a binder, a [let], or inside a formula's quantifier). *)
let calls_of_body ~f ~(sret : Sort.t) body =
  let calls = ref [] in
  let mentions_f_term t =
    Set.exists (Term.fvar_apps_of t) ~f:(function
      | Term.FunApp (FVar (g, _, _), _, _) -> Ident.tvar_equal g f
      | _ -> false)
  in
  let mentions_f_fml phi =
    Set.exists (Formula.fvar_apps_of phi) ~f:(function
      | Term.FunApp (FVar (g, _, _), _, _) -> Ident.tvar_equal g f
      | _ -> false)
  in
  let rec walk path t =
    match t with
    | Term.Var _ -> t
    | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], info) ->
        let c' = walk path c in
        let cphi = formula_of_bool_term c' in
        Term.mk_fsym_app ~info T_bool.IfThenElse
          [
            c';
            walk (Formula.and_of [ path; cphi ]) a;
            walk (Formula.and_of [ path; Formula.mk_neg cphi ]) b;
          ]
    | Term.FunApp (FVar (g, _, _), args, _) when Ident.tvar_equal g f ->
        let args' = List.map args ~f:(walk path) in
        let r = Ident.mk_fresh_tvar () in
        calls := { r; path; args = args'; orig_args = args } :: !calls;
        Term.mk_var r sret
    | Term.FunApp (T_bool.Formula phi, [], info) ->
        T_bool.of_formula ~info (walk_fml path phi)
    | Term.FunApp (sym, args, info) ->
        Term.mk_fsym_app ~info sym (List.map args ~f:(walk path))
    | _ ->
        if mentions_f_term t then refuse "a recursive call under a binder"
        else t
  and walk_fml path phi =
    match phi with
    | Formula.Atom (Atom.App (pred, args, ai), info) ->
        Formula.mk_atom ~info
          (Atom.mk_app ~info:ai pred (List.map args ~f:(walk path)))
    | Formula.Atom _ -> phi
    | Formula.UnaryOp (Formula.Not, p, info) ->
        Formula.mk_neg ~info (walk_fml path p)
    | Formula.BinaryOp (Formula.And, a, b, info) ->
        let a' = walk_fml path a in
        Formula.mk_and ~info a' (walk_fml (Formula.and_of [ path; a' ]) b)
    | Formula.BinaryOp (Formula.Or, a, b, info) ->
        let a' = walk_fml path a in
        Formula.mk_or ~info a'
          (walk_fml (Formula.and_of [ path; Formula.mk_neg a' ]) b)
    | Formula.BinaryOp (Formula.Imply, a, b, info) ->
        let a' = walk_fml path a in
        Formula.mk_imply ~info a' (walk_fml (Formula.and_of [ path; a' ]) b)
    | Formula.BinaryOp (op, a, b, info) ->
        Formula.mk_binop ~info op (walk_fml path a) (walk_fml path b)
    | _ ->
        if mentions_f_fml phi then refuse "a recursive call under a binder"
        else phi
  in
  let abstracted = walk (Formula.mk_true ()) body in
  (List.rev !calls, abstracted)

(* the functions of [fenv] that [t] applies *)
let applied_functions (fenv : FunEnv.t) t =
  Set.Poly.filter_map (Term.fvar_apps_of t) ~f:(function
    | Term.FunApp (FVar (g, _, _), _, _) when Map.Poly.mem fenv g -> Some g
    | _ -> None)

(* ---------------------------------------------------------------------- *)
(* Totality                                                                *)

type component =
  | Struct of int  (** the size of the datatype argument at this position *)
  | Nat of Term.t  (** [max(e, 0)] for an integer term over the formals *)

let str_of_component = function
  | Struct i -> sprintf "size(#%d)" i
  | Nat e -> sprintf "nat(%s)" (Term.str_of e)

let components (formals : sort_env_list) =
  let vars = List.mapi formals ~f:(fun i (x, s) -> (i, Term.mk_var x s, s)) in
  let structs =
    List.filter_map vars ~f:(fun (i, _, s) ->
        Option.map (sdt_of_sort s) ~f:(fun _ -> Struct i))
  in
  let ints =
    List.filter_map vars ~f:(fun (_, v, s) ->
        if Term.is_int_sort s then Some v else None)
  in
  let lens =
    List.filter_map vars ~f:(fun (_, v, s) ->
        if T_seq.is_sseq s then
          Some (Nat (T_seq.mk_len (T_seq.elem_sort_of s) v))
        else None)
  in
  let diffs =
    List.concat_map ints ~f:(fun a ->
        List.filter_map ints ~f:(fun b ->
            if Stdlib.( = ) a b then None else Some (Nat (T_int.mk_sub b a))))
  in
  structs @ lens
  @ List.concat_map ints ~f:(fun v -> [ Nat v; Nat (T_int.mk_neg v) ])
  @ diffs

let nat t =
  T_bool.ifte
    (Formula.mk_atom (T_int.mk_geq t (T_int.zero ())))
    t (T_int.zero ())

(* [strict] and [non-strict] decrease of one component from the formals to
   [args], as formulas *)
let decrease (formals : sort_env_list) args comp =
  match comp with
  | Struct i ->
      let x, s = List.nth_exn formals i in
      let a = List.nth_exn args i in
      let a' = eta a in
      let strict =
        match selector_chain_testers x a' with
        | Some testers -> Formula.and_of (testers @ [ Formula.eq a a' ])
        | None -> Formula.mk_false ()
      in
      (strict, Formula.or_of [ Formula.eq a (Term.mk_var x s); strict ])
  | Nat e ->
      let sub =
        Map.Poly.of_alist_exn
        @@ List.map2_exn formals args ~f:(fun (x, _) a -> (x, a))
      in
      let before = nat e and after = nat (Term.subst sub e) in
      ( Formula.mk_atom (T_int.mk_lt after before),
        Formula.mk_atom (T_int.mk_leq after before) )

let lex_decrease formals args = function
  | [ c ] -> fst (decrease formals args c)
  | [ c1; c2 ] ->
      let s1, n1 = decrease formals args c1 in
      let s2, _ = decrease formals args c2 in
      Formula.or_of [ s1; Formula.and_of [ n1; s2 ] ]
  | _ -> assert false

let max_orders = 48

(* A lexicographic measure under which every call decreases, if one is
   found; [Some []] when there is no call. *)
let find_measure ~fenv (formals : sort_env_list)
    (calls : (Formula.t * Term.t list) list) =
  if List.is_empty calls then Some []
  else
    let comps = components formals in
    let singles = List.map comps ~f:(fun c -> [ c ]) in
    let pairs =
      List.concat_map comps ~f:(fun a ->
          List.filter_map comps ~f:(fun b ->
              if Stdlib.( = ) a b then None else Some [ a; b ]))
    in
    List.find
      (List.take (singles @ pairs) max_orders)
      ~f:(fun order ->
        List.for_all calls ~f:(fun (path, args) ->
            valid ~fenv
              (Formula.mk_imply path (lex_decrease formals args order))))

(* ---------------------------------------------------------------------- *)
(* Eligibility and normalisation                                           *)

type branch = {
  guard : Formula.t;  (** over the formals only *)
  calls : (Ident.tvar * Term.t list) list;
      (** [y_j] and its arguments, each mentioning only earlier [y]s *)
  result : Term.t;  (** over the formals and the [y]s *)
}

let pvar_of_atom = function
  | Atom.App (Predicate.Var (p, _), _, _) -> Some p
  | _ -> None

let args_of_atom = function Atom.App (_, args, _) -> args | _ -> []
let atom_pvars ps ns = Set.Poly.filter_map (Set.union ps ns) ~f:pvar_of_atom

(* nullary unknowns whose every body occurrence is alone in its clause *)
let goal_markers (clauses : ClauseOld.t list) senv =
  let nullary =
    Map.Poly.filter_keys senv ~f:(fun _ -> true)
    |> Map.Poly.filter ~f:(fun s -> List.is_empty (Logic.Sort.args_of s))
    |> Map.key_set
    |> Set.Poly.map ~f:Ident.tvar_to_pvar
  in
  Set.filter nullary ~f:(fun g ->
      List.for_all clauses ~f:(fun (_, ps, ns, _) ->
          if
            Set.exists ns ~f:(fun a ->
                Option.equal Ident.pvar_equal (pvar_of_atom a) (Some g))
          then Set.is_empty ps && Set.length ns = 1
          else true))

type role = Defining | Negative | Unrelated

(* the role of one clause for [rho]; raises [Refuse] when it makes [rho]
   ineligible *)
let role_of ~markers rho ((_, ps, ns, phi) : ClauseOld.t) =
  let is_rho a = Option.equal Ident.pvar_equal (pvar_of_atom a) (Some rho) in
  let in_head = Set.exists ps ~f:is_rho and in_body = Set.exists ns ~f:is_rho in
  if Set.mem (Formula.pvs_of phi) rho then refuse "occurs in a pure part"
  else if not (in_head || in_body) then Unrelated
  else
    let others =
      Set.filter (atom_pvars ps ns) ~f:(fun p ->
          (not (Ident.pvar_equal p rho)) && not (Set.mem markers p))
    in
    if in_head then
      if Set.length ps = 1 && Set.is_empty others then Defining
      else refuse "a clause with it in the head mentions another unknown"
    else
      let pos_others =
        Set.filter (Set.Poly.filter_map ps ~f:pvar_of_atom) ~f:(fun p ->
            not (Set.mem markers p))
      in
      if Set.is_empty pos_others then Negative
      else refuse "a clause with it in the body has another unknown in the head"

(* the disjunctive normal form of a negation-normal formula, as cubes of
   literals, at most [cap] of them *)
let dnf ~cap phi =
  let rec go phi =
    match phi with
    | Formula.BinaryOp (Formula.Or, a, b, _) -> go a @ go b
    | Formula.BinaryOp (Formula.And, a, b, _) ->
        let ca = go a and cb = go b in
        if List.length ca * List.length cb > cap then refuse "too many cubes"
        else List.concat_map ca ~f:(fun x -> List.map cb ~f:(fun y -> x @ y))
    | phi when Formula.is_true phi -> [ [] ]
    | phi when Formula.is_false phi -> []
    | phi -> [ [ phi ] ]
  in
  let cubes = go phi in
  if List.length cubes > cap then refuse "too many cubes" else cubes

(* a Boolean literal read as an equation where it is one *)
let equation_of_literal lit =
  let bool_const t = T_bool.is_true t || T_bool.is_false t in
  let flip t =
    if T_bool.is_true t then T_bool.mk_false () else T_bool.mk_true ()
  in
  match lit with
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _) ->
      Some (a, b)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _),
        _ )
    when bool_const b ->
      Some (a, flip b)
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ a; b ], _), _),
        _ )
    when bool_const a ->
      Some (flip a, b)
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ a; b ], _), _)
    when bool_const b ->
      Some (a, flip b)
  | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ a; b ], _), _)
    when bool_const a ->
      Some (flip a, b)
  | _ -> None

(* The branches of one defining clause over [formals] (one per cube of its
   guard), or [Refuse]. *)
let normalise ~formals ((uni_senv, ps, ns, phi) : ClauseOld.t) =
  let head = Set.choose_exn ps in
  let hargs = args_of_atom head in
  let us, t = (List.drop_last_exn hargs, List.last_exn hargs) in
  let old_sort x =
    match Map.Poly.find uni_senv x with
    | Some s -> Logic.ExtTerm.to_old_sort s
    | None -> refuse "a variable without a sort"
  in
  ignore old_sort;
  let formal_set = Set.Poly.of_list (List.map formals ~f:fst) in
  let body_calls =
    List.map (Set.to_list ns) ~f:(fun a ->
        let args = args_of_atom a in
        match List.last_exn args with
        | Term.Var (y, _, _) -> (y, List.drop_last_exn args)
        | _ -> refuse "a recursive call's result is not a variable")
  in
  let ys = List.map body_calls ~f:fst in
  if List.contains_dup ys ~compare:Ident.tvar_compare then
    refuse "two calls share a result variable";
  if
    List.exists ys ~f:(fun y ->
        List.exists us ~f:(fun u -> tvs_mem u y) || Set.mem formal_set y)
  then refuse "a call's result occurs in the head's arguments";
  let ys_set = Set.Poly.of_list ys in
  let known0 = Set.union formal_set ys_set in
  let cubes = dnf ~cap:16 (Formula.nnf_of (Formula.negate phi)) in
  List.filter_map cubes ~f:(fun cube ->
      let defs = ref Map.Poly.empty in
      let testers = ref [] in
      let contradiction = ref false in
      let apply t = Term.subst !defs t in
      let resolved t =
        Set.for_all (Term.tvs_of t) ~f:(fun v ->
            Set.mem known0 v || Map.Poly.mem !defs v)
      in
      let unknown_var = function
        | Term.Var (z, _, _)
          when (not (Set.mem known0 z)) && not (Map.Poly.mem !defs z) ->
            Some z
        | _ -> None
      in
      let define z e =
        let e = apply e in
        defs := Map.Poly.map !defs ~f:(Term.subst (Map.Poly.singleton z e));
        defs := Map.Poly.set !defs ~key:z ~data:e
      in
      let eqs, rest =
        List.partition_map cube ~f:(fun lit ->
            match equation_of_literal lit with
            | Some (a, b) -> First (a, b)
            | None -> Second lit)
      in
      let pending =
        ref
          (List.map2_exn formals us ~f:(fun (x, s) u -> (Term.mk_var x s, u))
          @ eqs)
      in
      let step (a, b) =
        let a = apply a and b = apply b in
        let cons_app = function
          | Term.FunApp (T_dt.DTCons (c, _, dt), args, _) -> Some (c, dt, args)
          | _ -> None
        in
        let solve_one () =
          (* an integer or real equation with one unknown variable *)
          let unknowns =
            Set.filter
              (Set.union (Term.tvs_of a) (Term.tvs_of b))
              ~f:(fun v -> not (Set.mem known0 v || Map.Poly.mem !defs v))
          in
          match Set.to_list unknowns with
          | [ z ] -> (
              let occurs t = tvs_mem t z in
              match
                Evaluator.isolate_target ~is_target:(is_var_named z) ~occurs a b
              with
              | Some e when resolved e -> `Define (z, e)
              | _ -> `Keep)
          | _ -> `Keep
        in
        match (unknown_var a, unknown_var b) with
        | Some z, _ when resolved b && not (tvs_mem b z) -> `Define (z, b)
        | _, Some z when resolved a && not (tvs_mem a z) -> `Define (z, a)
        | _ -> (
            match (cons_app a, cons_app b) with
            | Some (c1, _, args1), Some (c2, _, args2) ->
                if String.equal c1 c2 then `Split ([], List.zip_exn args1 args2)
                else `Contradiction
            | Some (c, dt, args), None when resolved b ->
                `Split
                  ( [ T_dt.mk_is_cons dt c b ],
                    List.mapi args ~f:(fun i e ->
                        (T_dt.mk_sel_by_cons dt c i b, e)) )
            | None, Some (c, dt, args) when resolved a ->
                `Split
                  ( [ T_dt.mk_is_cons dt c a ],
                    List.mapi args ~f:(fun i e ->
                        (T_dt.mk_sel_by_cons dt c i a, e)) )
            | _ -> solve_one ())
      in
      let rec loop () =
        let progress = ref false in
        let next = ref [] in
        List.iter !pending ~f:(fun eq ->
            if not !contradiction then
              match step eq with
              | `Define (z, e) ->
                  progress := true;
                  define z e
              | `Split (ts, eqs) ->
                  progress := true;
                  testers := !testers @ ts;
                  next := !next @ eqs
              | `Contradiction -> contradiction := true
              | `Keep -> next := !next @ [ eq ]);
        pending := !next;
        if !progress && not !contradiction then loop ()
      in
      loop ();
      if !contradiction then None
      else
        let close t =
          let t = apply t in
          if resolved t then t else refuse "a variable could not be eliminated"
        in
        let close_fml phi =
          let phi = Formula.subst !defs phi in
          if Set.for_all (Formula.tvs_of phi) ~f:(Set.mem known0) then phi
          else refuse "a variable could not be eliminated"
        in
        let guard =
          Formula.and_of
            (List.map !testers ~f:(fun a -> close_fml (Formula.mk_atom a))
            @ List.map !pending ~f:(fun (a, b) ->
                Formula.eq (close a) (close b))
            @ List.map rest ~f:close_fml)
        in
        if Set.exists (Formula.tvs_of guard) ~f:(Set.mem ys_set) then
          refuse "a guard mentions a recursive call's result";
        let calls =
          List.map body_calls ~f:(fun (y, args) -> (y, List.map args ~f:close))
        in
        (* order the calls so that each mentions only earlier results *)
        let rec order placed acc = function
          | [] -> List.rev acc
          | remaining ->
              let ready, waiting =
                List.partition_tf remaining ~f:(fun (_, args) ->
                    List.for_all args ~f:(fun a ->
                        Set.for_all (Term.tvs_of a) ~f:(fun v ->
                            (not (Set.mem ys_set v)) || Set.mem placed v)))
              in
              if List.is_empty ready then
                refuse "calls depend on each other cyclically"
              else
                order
                  (Set.union placed (Set.Poly.of_list (List.map ready ~f:fst)))
                  (List.rev_append ready acc)
                  waiting
        in
        Some { guard; calls = order Set.Poly.empty [] calls; result = close t })

(* ---------------------------------------------------------------------- *)
(* The registry and the result of the pass                                 *)

type reconstructed = {
  pvar : Ident.pvar;
  fname : Ident.tvar;
  formals : sort_env_list;
  sret : Sort.t;
  body : Term.t;
  branches : branch list;
  exhaustive : bool;
      (** the defining clauses' guards cover every argument; otherwise the last
          branch is a default value and the function is vocabulary only *)
}

type outcome = {
  problem : PCSP.Problem.t;
  reconstructed : reconstructed list;
  refused : (Ident.pvar * string) list;
  replaced : Ident.pvar list;
  lemmas : (Ident.tvar * Formula.t list) list;
}

let build_body ~fname ~formals ~sret branches =
  let sargs = List.map formals ~f:snd in
  let branch_term b =
    let sub =
      List.fold b.calls ~init:Map.Poly.empty ~f:(fun sub (y, args) ->
          let call =
            Term.mk_fvar_app fname sargs sret
              (List.map args ~f:(Term.subst sub))
          in
          Map.Poly.set sub ~key:y ~data:call)
    in
    Term.subst sub b.result
  in
  match List.rev branches with
  | [] -> refuse "no branch"
  | last :: rest ->
      List.fold rest ~init:(branch_term last) ~f:(fun acc b ->
          T_bool.ifte b.guard (branch_term b) acc)

(* the problem's clauses in their old form *)
let clauses_of pcsp =
  let senv = PCSP.Problem.senv_of pcsp in
  let cls =
    match PCSP.Problem.clauses_of_opt pcsp with
    | Some cls -> cls
    | None -> ClauseSet.of_formulas senv (PCSP.Problem.formulas_of pcsp)
  in
  Set.to_list @@ ClauseSet.to_old_clause_set senv cls

(* Every function [f]'s body applies other than [f] itself, transitively. *)
let reached_others (fenv : FunEnv.t) f body =
  let rec close seen = function
    | [] -> seen
    | g :: rest when Set.mem seen g -> close seen rest
    | g :: rest -> (
        let seen = Set.add seen g in
        match Map.Poly.find fenv g with
        | Some (_, _, b, _, _) ->
            close seen (Set.to_list (applied_functions fenv b) @ rest)
        | None -> close seen rest)
  in
  Set.remove
    (close Set.Poly.empty (Set.to_list (applied_functions fenv body)))
    f

(* Whether [f] (in [fenv]) is total, given the set [total] of functions
   already proved total; [Error] with the reason otherwise. *)
let check_total ~(fenv : FunEnv.t) ~total f =
  match Map.Poly.find fenv f with
  | None -> Error "not a defined function"
  | Some (formals, sret, body, _, _) -> (
      let others = reached_others fenv f body in
      if Set.mem others f then Error "mutual recursion"
      else if not (Set.is_subset others ~of_:total) then
        Error "applies a function not proved total"
      else
        match calls_of_body ~f ~sret body with
        | exception Refuse why -> Error why
        | calls, _ -> (
            match
              find_measure ~fenv formals
                (List.map calls ~f:(fun c -> (c.path, c.args)))
            with
            | Some _ -> Ok ()
            | None -> Error "no decreasing measure proved"))

(* The input's recursive functions proved total, each after every other
   function its body applies. *)
let total_functions (fenv : FunEnv.t) =
  let rec fix total pending =
    let total', pending' =
      List.fold pending ~init:(total, []) ~f:(fun (total, acc) f ->
          let _, _, body, _, _ = Map.Poly.find_exn fenv f in
          let others = reached_others fenv f body in
          if Set.mem others f then (total, acc)
          else if Set.is_subset others ~of_:total then
            match check_total ~fenv ~total f with
            | Ok () -> (Set.add total f, acc)
            | Error _ -> (total, acc)
          else (total, f :: acc))
    in
    if Set.length total' > Set.length total then fix total' pending' else total'
  in
  fix Set.Poly.empty
    (Map.Poly.keys (Map.Poly.filter fenv ~f:(fun (_, _, _, r, _) -> r)))

(* ---------------------------------------------------------------------- *)
(* Lemmas                                                                  *)

(* candidate invariants over the formals and [v], the function's value *)
let lemma_candidates (formals : sort_env_list) (sret : Sort.t) v =
  let vars = List.map formals ~f:(fun (x, s) -> (Term.mk_var x s, s)) in
  if Term.is_int_sort sret then
    Formula.mk_atom (T_int.mk_geq v (T_int.zero ()))
    :: List.concat_map vars ~f:(fun (x, s) ->
        if Term.is_int_sort s then
          [
            Formula.mk_atom (T_int.mk_leq v x);
            Formula.mk_atom (T_int.mk_geq v x);
          ]
        else if T_seq.is_sseq s then
          let l = T_seq.mk_len (T_seq.elem_sort_of s) x in
          [
            Formula.mk_atom (T_int.mk_leq v l);
            Formula.mk_atom (T_int.mk_geq v l);
          ]
        else [])
  else if T_seq.is_sseq sret then
    let lv = T_seq.mk_len (T_seq.elem_sort_of sret) v in
    List.concat_map vars ~f:(fun (x, s) ->
        if T_seq.is_sseq s then
          let l = T_seq.mk_len (T_seq.elem_sort_of s) x in
          [
            Formula.mk_atom (T_int.mk_leq lv l);
            Formula.mk_atom (T_int.mk_geq lv l);
          ]
        else [])
  else if Term.is_bool_sort sret then
    let b = Formula.of_bool_term v in
    List.concat_map vars ~f:(fun (x, s) ->
        match sdt_of_sort s with
        | None -> []
        | Some dt ->
            List.concat_map (Datatype.conses_of dt) ~f:(fun cons ->
                let is_c =
                  Formula.mk_atom
                  @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) x
                in
                [
                  Formula.mk_imply is_c b;
                  Formula.mk_imply is_c (Formula.mk_neg b);
                ]))
  else []

(* The largest jointly inductive subset of the candidates of a total [f]. *)
let prove_lemmas ~(fenv : FunEnv.t) f =
  let formals, sret, body, _, _ = Map.Poly.find_exn fenv f in
  match calls_of_body ~f ~sret body with
  | exception Refuse _ -> []
  | calls, abstracted ->
      let v = Ident.mk_fresh_tvar () in
      let vterm = Term.mk_var v sret in
      let cands = lemma_candidates formals sret vterm in
      let inst inv args value =
        Formula.subst
          (Map.Poly.of_alist_exn
             ((v, value)
             :: List.map2_exn formals args ~f:(fun (x, _) a -> (x, a))))
          inv
      in
      let self_args = List.map formals ~f:(fun (x, s) -> Term.mk_var x s) in
      (* the body without [f]: the questions must not declare it *)
      let fenv' = Map.Poly.remove fenv f in
      let rec fix cur =
        let hyp =
          Formula.and_of
          @@ List.map calls ~f:(fun c ->
              Formula.mk_imply c.path
                (Formula.and_of
                   (List.map cur ~f:(fun inv ->
                        inst inv c.args (Term.mk_var c.r sret)))))
        in
        let kept =
          List.filter cur ~f:(fun inv ->
              valid ~fenv:fenv'
                (Formula.mk_imply hyp (inst inv self_args abstracted)))
        in
        if List.length kept = List.length cur then cur else fix kept
      in
      let kept = if List.is_empty cands then [] else fix cands in
      if List.is_empty kept then []
      else
        let sargs = List.map formals ~f:snd in
        let at args =
          List.map kept ~f:(fun inv ->
              inst inv args (Term.mk_fvar_app f sargs sret args))
        in
        at self_args @ List.concat_map calls ~f:(fun c -> at c.orig_args)

(* [prop] (the existing property of [f], [forall formals. phi] or [true])
   with [extra] conjoined, as one universal over [formals] *)
let extend_property formals prop extra =
  let old =
    if Formula.is_bind prop then
      let _, env, phi, _ = Formula.let_bind prop in
      if List.length env = List.length formals then
        Formula.subst
          (Map.Poly.of_alist_exn
             (List.map2_exn env formals ~f:(fun (y, _) (x, s) ->
                  (y, Term.mk_var x s))))
          phi
      else Formula.mk_true ()
    else Formula.mk_true ()
  in
  Formula.mk_forall formals (Formula.and_of (old :: extra))

(* ---------------------------------------------------------------------- *)
(* The pass                                                                *)

(* Names the template and the Houdini pre-pass read their vocabulary from,
   and the vocabulary limit; set once, by the solver, before solving. *)
let qual_limit = Atomic.make 0

(* [COAR_RECON_TRACE] set: the pass says on stderr what it reconstructed,
   refused (and why) and proved, whatever the solver's tracing *)
let trace = Option.is_some (Sys.getenv "COAR_RECON_TRACE")

(* this pass's own counters for [reconstruct ~names_apart:true]: the
   replay scopes and the function names drawn under it *)
let scope_count = Atomic.make 0
let fname_count = Atomic.make 0

let try_reconstruct ~fenv ~total pcsp (clauses : ClauseOld.t list) ~markers rho
    =
  let tv = Ident.pvar_to_tvar rho in
  let sort = Map.Poly.find_exn (PCSP.Problem.senv_of pcsp) tv in
  let sorts = List.map (Logic.Sort.args_of sort) ~f:Logic.ExtTerm.to_old_sort in
  if List.length sorts < 2 then refuse "arity below two";
  let roles = List.map clauses ~f:(fun c -> (role_of ~markers rho c, c)) in
  let defining =
    List.filter_map roles ~f:(function Defining, c -> Some c | _ -> None)
  in
  if List.is_empty defining then refuse "no defining clause";
  let formals =
    List.map (List.drop_last_exn sorts) ~f:(fun s ->
        (Ident.mk_fresh_tvar (), s))
  in
  let sret = List.last_exn sorts in
  let branches = List.concat_map defining ~f:(normalise ~formals) in
  if List.is_empty branches then refuse "no satisfiable defining clause";
  let guards = List.map branches ~f:(fun b -> b.guard) in
  let rec pairs = function
    | [] -> []
    | g :: gs -> List.map gs ~f:(fun h -> (g, h)) @ pairs gs
  in
  (* two branches may overlap only where neither recurses and their results
     are proved equal there: the clauses then still describe one value at
     each argument, and the [ite] below takes the first branch, whose result
     is the other's on the overlap *)
  if
    not
      (List.for_all (pairs branches) ~f:(fun (b1, b2) ->
           valid ~fenv (Formula.mk_neg (Formula.and_of [ b1.guard; b2.guard ]))
           || List.is_empty b1.calls && List.is_empty b2.calls
              && valid ~fenv
                   (Formula.mk_imply
                      (Formula.and_of [ b1.guard; b2.guard ])
                      (Formula.eq b1.result b2.result))))
  then refuse "guards not proved mutually exclusive";
  (* where the guards miss a case, the clauses describe a PARTIAL function:
     the definition is completed by a default value of an integer, real or
     Boolean result (the function is then vocabulary only and is never put in
     the place of the unknown, whose least solution is false there) *)
  let exhaustive = valid ~fenv (Formula.or_of guards) in
  let branches =
    if exhaustive then branches
    else
      let default =
        if Term.is_int_sort sret then T_int.zero ()
        else if Term.is_real_sort sret then T_real.rzero ()
        else if Term.is_bool_sort sret then T_bool.mk_false ()
        else refuse "guards not proved exhaustive"
      in
      branches
      @ [
          {
            guard = Formula.mk_neg (Formula.or_of guards);
            calls = [];
            result = default;
          };
        ]
  in
  (* functions applied by the guards or results must be total already *)
  let applied =
    Set.Poly.union_list
    @@ List.concat_map branches ~f:(fun b ->
        Set.Poly.filter_map (Formula.fvar_apps_of b.guard) ~f:(function
          | Term.FunApp (FVar (g, _, _), _, _) when Map.Poly.mem fenv g ->
              Some g
          | _ -> None)
        :: applied_functions fenv b.result
        :: List.map b.calls ~f:(fun (_, args) ->
            Set.Poly.union_list (List.map args ~f:(applied_functions fenv))))
  in
  if not (Set.is_empty applied || Set.is_subset applied ~of_:(total ())) then
    refuse "a definition applies a function not proved total";
  (* totality: calls' arguments decrease under their own branch's guard; a
     result variable of an earlier call is any value *)
  let calls =
    List.concat_map branches ~f:(fun b ->
        List.map b.calls ~f:(fun (_, args) -> (b.guard, args)))
  in
  (match find_measure ~fenv formals calls with
  | None -> refuse "no decreasing measure proved (not shown total)"
  | Some _ -> ());
  let taken v =
    Map.Poly.mem fenv v || Map.Poly.mem (PCSP.Problem.senv_of pcsp) v
  in
  let fname =
    let prefix = "recon_" ^ Ident.name_of_pvar rho ^ "_" in
    if Ident.replaying_fresh_names () then
      (* names apart: numbered by this pass's own counter, so the draw moves
         no process-global counter; [taken] keeps it fresh against the
         environments, and the prefix ends in [_] followed by digits and [a],
         which no global draw ([prefix] followed by digits) spells *)
      let rec draw () =
        let v =
          Ident.Tvar
            (sprintf "%s%da" prefix (Atomic.fetch_and_add fname_count 1))
        in
        if taken v then draw () else v
      in
      draw ()
    else Ident.mk_fresh_tvar_avoiding ~prefix ~taken ()
  in
  let body = build_body ~fname ~formals ~sret branches in
  { pvar = rho; fname; formals; sret; body; branches; exhaustive }

(* the clause [cl] with every [rho(a, b)] of [r] in its body read as
   [b = f(a)], as a formula *)
let replace_in_clause (rs : reconstructed list)
    ((uni_senv, ps, ns, phi) : ClauseOld.t) =
  let find p = List.find rs ~f:(fun r -> Ident.pvar_equal r.pvar p) in
  let ns', extra =
    Set.fold ns ~init:([], []) ~f:(fun (keep, extra) a ->
        match Option.bind (pvar_of_atom a) ~f:find with
        | Some r ->
            let args = args_of_atom a in
            let app =
              Term.mk_fvar_app r.fname
                (List.map r.formals ~f:snd)
                r.sret (List.drop_last_exn args)
            in
            (keep, Formula.mk_neg (Formula.eq (List.last_exn args) app) :: extra)
        | None -> (a :: keep, extra))
  in
  let senv, phi' =
    ClauseOld.to_formula
      (uni_senv, ps, Set.Poly.of_list ns', Formula.or_of (phi :: extra))
  in
  (Map.Poly.map senv ~f:Logic.ExtTerm.to_old_sort, phi')

(* [reconstruct ~replace ~lemmas pcsp]: the pass stated at the top.

   [~names_apart:true] runs it with its fresh names drawn apart from the
   process: every unprefixed term-variable draw is [Ident]'s replay under a
   scope of this pass's own ([#recfun<k>r], [k] from [scope_count]), and the
   function names are numbered by [fname_count].  Contract: the result is the
   one [~names_apart:false] gives up to the names this pass draws (each such
   name is bound in a definition, a property or an eliminated solution, or is
   a function name kept fresh by [taken]), and the process-global term
   variable counter is where it was before the call -- so the rest of the
   run draws the names it would have drawn had the pass not run.  Why: a
   moved counter reorders the conjuncts Z3 is given for the whole remaining
   run, which can turn a run answered in a second into one whose validation
   question never returns.  Other counters (predicate variables, dummies)
   are not detached; the trace reports how far the global fresh stamp
   moved (0 on the inputs tried). *)
let rec reconstruct ?(print = fun (_ : string lazy_t) -> ())
    ?(names_apart = false) ~functions ~replace ~lemmas pcsp =
  if names_apart && not (Ident.replaying_fresh_names ()) then (
    let before = Ident.fresh_stamp () in
    let scope = sprintf "#recfun%dr" (Atomic.fetch_and_add scope_count 1) in
    let out =
      Ident.with_replayed_fresh_names ~scope (fun () ->
          reconstruct ~print ~names_apart:false ~functions ~replace ~lemmas pcsp)
    in
    if trace then
      eprintf "[recon] names apart: global fresh stamp moved by %d\n%!"
        (Ident.fresh_stamp () - before);
    out)
  else reconstruct_aux ~print ~functions ~replace ~lemmas pcsp

and reconstruct_aux ~print ~functions ~replace ~lemmas pcsp =
  let print l =
    print l;
    if trace then eprintf "%s\n%!" (Lazy.force l)
  in
  let params = PCSP.Problem.params_of pcsp in
  let fenv0 =
    Map.force_merge params.PCSP.Params.fenv (get_fenv ()) ~catch_dup:ignore
      ~equal:(fun _ _ -> true)
  in
  (* asked only when needed: by a guard that applies an input function, and
     by the lemmas *)
  let input_total = lazy (total_functions fenv0) in
  let clauses = clauses_of pcsp in
  let senv = PCSP.Problem.senv_of pcsp in
  let markers = goal_markers clauses senv in
  let candidates =
    if not functions then []
    else
      Map.Poly.keys senv
      |> List.filter ~f:(fun v ->
          PCSP.Problem.is_bool_valued_ord_pred pcsp v
          && not (Set.mem markers (Ident.tvar_to_pvar v)))
      |> List.map ~f:Ident.tvar_to_pvar
  in
  let fenv = ref fenv0 and recon_total = ref Set.Poly.empty in
  let total () = Set.union (Lazy.force input_total) !recon_total in
  let recon = ref [] and refused = ref [] in
  List.iter candidates ~f:(fun rho ->
      match try_reconstruct ~fenv:!fenv ~total pcsp clauses ~markers rho with
      | r ->
          print
            (lazy
              (sprintf "[recon] %s reconstructed as %s = %s"
                 (Ident.name_of_pvar rho)
                 (Ident.name_of_tvar r.fname)
                 (Term.str_of r.body)));
          fenv :=
            Map.Poly.set !fenv ~key:r.fname
              ~data:(r.formals, r.sret, r.body, true, Formula.mk_true ());
          recon_total := Set.add !recon_total r.fname;
          recon := r :: !recon
      | exception Refuse why ->
          print
            (lazy
              (sprintf "[recon] %s refused: %s" (Ident.name_of_pvar rho) why));
          refused := (rho, why) :: !refused);
  let total = if lemmas then total () else !recon_total in
  let recon = List.rev !recon in
  (* lemmas for every total function: the reconstructed ones and the input's *)
  let lemma_list =
    if not lemmas then []
    else
      List.filter_map (Set.to_list total) ~f:(fun f ->
          match prove_lemmas ~fenv:!fenv f with
          | [] -> None
          | invs ->
              print
                (lazy
                  (sprintf "[recon] lemmas for %s: %s" (Ident.name_of_tvar f)
                     (String.concat_map_list ~sep:"; " invs ~f:Formula.str_of)));
              Some (f, invs))
  in
  let fenv_final =
    List.fold lemma_list ~init:!fenv ~f:(fun fenv (f, invs) ->
        Map.Poly.update fenv f ~f:(function
          | Some (formals, sret, body, r, prop) ->
              (formals, sret, body, r, extend_property formals prop invs)
          | None -> assert false))
  in
  (* the problem's own environment: its entries, updated, and the new ones *)
  let changed =
    Map.Poly.filter_mapi fenv_final ~f:(fun ~key ~data ->
        if
          Map.Poly.mem params.PCSP.Params.fenv key
          || List.exists recon ~f:(fun r -> Ident.tvar_equal r.fname key)
        then Some data
        else None)
  in
  let global_changed =
    Map.Poly.filter_keys fenv_final ~f:(fun key ->
        List.exists recon ~f:(fun r -> Ident.tvar_equal r.fname key)
        || List.exists lemma_list ~f:(fun (f, _) -> Ident.tvar_equal f key))
  in
  update_fenv_replacing global_changed;
  Atomic.set PCSP.Problem.reconstructed_functions
    (Set.union
       (Atomic.get PCSP.Problem.reconstructed_functions)
       (Set.Poly.of_list (List.map recon ~f:(fun r -> r.fname))));
  let params = { params with PCSP.Params.fenv = changed } in
  let problem, replaced =
    (* only a function the defining clauses define everywhere is put in the
       unknown's place *)
    let recon = List.filter recon ~f:(fun r -> r.exhaustive) in
    if (not replace) || List.is_empty recon then
      (PCSP.Problem.update_params pcsp params, [])
    else
      let is_def_of_recon ((_, ps, _, _) : ClauseOld.t) =
        Set.exists ps ~f:(fun a ->
            match pvar_of_atom a with
            | Some p ->
                List.exists recon ~f:(fun r -> Ident.pvar_equal r.pvar p)
            | None -> false)
      in
      let phis =
        Set.Poly.of_list
        @@ List.filter_map clauses ~f:(fun c ->
            if is_def_of_recon c then None else Some (replace_in_clause recon c))
      in
      let removed = List.map recon ~f:(fun r -> Ident.pvar_to_tvar r.pvar) in
      let remove m = List.fold removed ~init:m ~f:Map.Poly.remove in
      let sols =
        Map.Poly.of_alist_exn
        @@ List.map recon ~f:(fun r ->
            let y = Ident.mk_fresh_tvar () in
            let xs = r.formals @ [ (y, r.sret) ] in
            ( Ident.pvar_to_tvar r.pvar,
              Logic.Term.mk_lambda
                (List.map xs ~f:(fun (x, s) -> (x, Logic.ExtTerm.of_old_sort s)))
              @@ Logic.ExtTerm.of_old_formula
              @@ Formula.eq (Term.mk_var y r.sret)
                   (Term.mk_fvar_app r.fname
                      (List.map r.formals ~f:snd)
                      r.sret
                      (List.map r.formals ~f:(fun (x, s) -> Term.mk_var x s)))
            ))
      in
      let params =
        {
          params with
          PCSP.Params.senv = remove params.PCSP.Params.senv;
          kind_map = remove params.PCSP.Params.kind_map;
          sol_for_eliminated =
            Map.force_merge params.PCSP.Params.sol_for_eliminated sols;
        }
      in
      ( PCSP.Problem.of_old_formulas ~params phis,
        List.map recon ~f:(fun r -> r.pvar) )
  in
  {
    problem;
    reconstructed = recon;
    refused = List.rev !refused;
    replaced;
    lemmas = lemma_list;
  }
