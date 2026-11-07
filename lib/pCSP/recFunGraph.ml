(* Replace applications of a counted recursive function by an unknown for its
   graph, so that the induction a property of the function needs becomes an
   invariant the solver synthesises.

   SHAPE.  A recursive definition [f(x_1, .., x_n)] of the function
   environment is COUNTED at position [p] when its body is

     ite (x_p <= c) base step

   with [c] an integer numeral (also written [x_p < c + 1], [c >= x_p],
   [c + 1 > x_p]), [base] free of [f], and [step] mentioning [f] only as the
   call [f(x_1, .., x_p - 1, .., x_n)] -- every other argument the formal
   itself.  Such an [f] is total and the definition has exactly one solution:
   [f(a, j)] is [base] for [j <= c] and [step] at [j] over [f(a, j - 1)]
   above, by induction on [j - c].

   ENCODING.  In each conjunct [C] of a constraint's negation normal form, the
   applications [f(a_1, t) .. f(a_m, t)] of one counted [f] at one counter term
   [t] that are not under a binder and whose arguments mention neither a
   recursive function nor a variable bound inside [C] are replaced by fresh
   variables [r_1 .. r_m], and a fresh ordinary unknown [G(v, j, r_1 .. r_m)]
   is introduced, [v] the variables of the [a_i] and of [t]:

     goal:  C[r_i / f(a_i, t)] \/ not G(v, t, r_1, .., r_m)
     base:  P(v) /\ J(j) => G(v, j, base[a_1, j], .., base[a_m, j])
     step:  G(v, j, r) /\ c <= j /\ j + 1 <= t
              => G(v, j + 1, step[a_1, j + 1, r_1], .., step[a_m, j + 1, r_m])

   where [P(v)] is the conjunction of the negations of [C]'s disjuncts that
   mention no replaced application and only variables of [v] (where one of
   them holds, [C] holds whatever the [r_i] are), and [J(j)] is [j = c] when
   [t] is a numeral at least [c] and [j <= c] otherwise.

   EQUISATISFIABLE (argued per model of the background theory, since every
   term involved is one the model fixes alike in the original and here).
   The least [G] satisfying base and step is the graph of the [m] calls on
   [{v : P(v)}] and on the counter values from the base to [t]: base puts in
   the values at [c] (or below), and step, guarded by [c <= j], only moves to
   a [j + 1] above [c], where the definition is [step].  So (1) a solution of
   the encoding contains that graph and its goal clause, read at the true
   values, is [C] wherever [P] holds, while [C] holds trivially where [P]
   fails; and (2) when the original holds, the least [G] satisfies the goal.
   The guard [j + 1 <= t] keeps [G] to the counter values the goal reads: a
   counter beyond them would make the unknown describe values the property
   never mentions (a 64-bit shift amount wraps at [2^64], so a bit count past
   it is not the count the goal is about), and no invariant need hold there.

   Nothing else changes: a constraint without such an application is kept as
   it is, and a function stays in the problem's environment exactly when the
   encoded problem still applies it, directly or through another definition's
   body. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type counted = {
  name : Ident.tvar;
  params : sort_env_list;
  sret : Sort.t;
  pos : int;  (** the counter's position in [params] *)
  bound : Z.t;  (** [c]: the body is [base] exactly where the counter is <= c *)
  base : Term.t;
  step : Term.t;
  rec_call : Term.t;  (** the one recursive call in [step], over the formals *)
}

let is_var_named x = function
  | Term.Var (y, _, _) -> Ident.tvar_equal x y
  | _ -> false

(* the value of an integer numeral, also one spelled as a negation [- n] *)
let rec num = function
  | t when T_int.is_int t -> Some (T_int.let_int t)
  | Term.FunApp (T_int.Neg, [ t ], _) -> Option.map (num t) ~f:Z.neg
  | _ -> None

(* [Some c] when [phi] is [x <= c] up to the four spellings named above *)
let counter_bound x phi =
  match phi with
  | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) -> (
      match psym with
      | T_int.Leq when is_var_named x t1 -> num t2
      | T_int.Lt when is_var_named x t1 -> Option.map (num t2) ~f:Z.pred
      | T_int.Geq when is_var_named x t2 -> num t1
      | T_int.Gt when is_var_named x t2 -> Option.map (num t1) ~f:Z.pred
      | _ -> None)
  | _ -> None

let calls_of name t =
  Set.filter (Term.fvar_apps_of t) ~f:(function
    | Term.FunApp (FVar (g, _, _), _, _) -> Ident.tvar_equal g name
    | _ -> false)

(* [Some d] when [t] is [x + d] for an integer numeral [d], spelled [x - n],
   [x + n] or [n + x] *)
let offset_from x t =
  match t with
  | Term.FunApp (T_int.Sub, [ a; n ], _) when is_var_named x a ->
      Option.map (num n) ~f:Z.neg
  | Term.FunApp (T_int.Add, [ a; n ], _) when is_var_named x a -> num n
  | Term.FunApp (T_int.Add, [ n; a ], _) when is_var_named x a -> num n
  | _ -> None

(* [Some c'] when [phi] is [x >= c'] for an integer numeral [c'], spelled
   [x >= c'], [x > c' - 1], [c' <= x] or [c' - 1 < x] *)
let counter_lower_bound x phi =
  match phi with
  | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) -> (
      match psym with
      | T_int.Geq when is_var_named x t1 -> num t2
      | T_int.Gt when is_var_named x t1 -> Option.map (num t2) ~f:Z.succ
      | T_int.Leq when is_var_named x t2 -> num t1
      | T_int.Lt when is_var_named x t2 -> Option.map (num t1) ~f:Z.succ
      | _ -> None)
  | _ -> None

(* GUARDED SHAPE.  [ite (x_p >= c') (ite (x_p <= c) base step) base'] with
   [c' <= c + 1] and [base'] the same term as [base] is the function
   [ite (x_p <= c) base step]: below [c'] the counter is at most [c], where
   the inner [ite] would give [base] too.  A front end that states a
   termination measure (a [:decreases] clause) emits this guard around the
   counted body.  [Some (x_p, inner)] for that inner [ite], at any integer
   parameter [x_p] for which the shape holds; [None] otherwise.  The equality of
   [base] and [base'] is syntactic, so it never accepts two different
   functions. *)
let guarded_body params body =
  match body with
  | Term.FunApp (T_bool.IfThenElse, [ cond; inner; base' ], _)
    when T_bool.is_formula cond -> (
      match inner with
      | Term.FunApp (T_bool.IfThenElse, [ cond2; base; _ ], _)
        when T_bool.is_formula cond2
             && (try Stdlib.(base = base') with Invalid_argument _ -> false) ->
          let phi = T_bool.let_formula cond and phi2 = T_bool.let_formula cond2 in
          List.find_map params ~f:(fun (x, s) ->
              if not (Term.is_int_sort s) then None
              else
                match (counter_lower_bound x phi, counter_bound x phi2) with
                | Some c', Some c when Z.leq c' (Z.succ c) -> Some inner
                | _ -> None)
      | _ -> None)
  | _ -> None

(* [Some] exactly for a definition of the COUNTED shape stated above whose body
   is closed: every variable it mentions is a parameter or a function of
   [fenv].  The encoding substitutes the body at new arguments into clauses
   whose variables are the arguments' variables, so a variable free in the
   body would enter a clause unbound -- a universal the definition shares with
   the clauses, which only the clause's own copy of it may stand for. *)
let counted_of ?(guarded_counter = false) ~(fenv : FunEnv.t) name (params, sret, body, is_rec, _) =
  let closed () =
    Set.for_all (Term.tvs_of body) ~f:(fun x ->
        List.exists params ~f:(fun (y, _) -> Ident.tvar_equal x y)
        || Map.Poly.mem fenv x)
  in
  if not (is_rec && closed ()) then None
  else
    let body =
      if guarded_counter then
        Option.value (guarded_body params body) ~default:body
      else body
    in
    match body with
    | Term.FunApp (T_bool.IfThenElse, [ cond; base; step ], _)
      when T_bool.is_formula cond ->
        let phi = T_bool.let_formula cond in
        List.find_mapi params ~f:(fun pos (x, s) ->
            if not (Term.is_int_sort s) then None
            else
              match counter_bound x phi with
              | None -> None
              | Some bound -> (
                  if not (Set.is_empty (calls_of name base)) then None
                  else
                    match Set.to_list (calls_of name step) with
                    | [ (Term.FunApp (_, args, _) as rec_call) ]
                      when List.length args = List.length params
                           && List.for_alli args ~f:(fun i a ->
                               let y, _ = List.nth_exn params i in
                               if i = pos then
                                 match offset_from y a with
                                 | Some d -> Z.equal d Z.minus_one
                                 | None -> false
                               else is_var_named y a) ->
                        Some
                          {
                            name;
                            params;
                            sret;
                            pos;
                            bound;
                            base;
                            step;
                            rec_call;
                          }
                    | _ -> None))
    | _ -> None

(* [guarded_counter]: a body of the GUARDED SHAPE ([guarded_body]) counts as
   its inner counted body; [false] (the default) recognises the COUNTED shape
   alone.  The same value is passed by every entry point below, so one run
   recognises one set of definitions throughout. *)
let counted_defs ?guarded_counter (fenv : FunEnv.t) =
  Map.Poly.filter_mapi fenv ~f:(fun ~key ~data ->
      counted_of ?guarded_counter ~fenv key data)

let has_rec_call (fenv : FunEnv.t) t =
  Set.exists (Term.fvar_apps_of t) ~f:(function
    | Term.FunApp (FVar (g, _, _), _, _) -> (
        match Map.Poly.find fenv g with
        | Some (_, _, _, r, _) -> r
        | None -> false)
    | _ -> false)

(* the applications of counted functions in [phi] outside every binder whose
   arguments mention no recursive function and only variables of [scope] *)
let candidate_apps ~fenv ~defs ~scope phi =
  let found = ref [] in
  ignore
  @@ Formula.map_term_no_binders phi ~f:(fun t ->
      (match t with
      | Term.FunApp (FVar (g, _, _), args, _) when Map.Poly.mem defs g ->
          if
            (not (List.exists args ~f:(has_rec_call fenv)))
            && List.for_all args ~f:(fun a ->
                Set.is_subset (Term.tvs_of a) ~of_:scope)
          then found := t :: !found
      | _ -> ());
      t);
  List.rev !found

let str_key = Term.str_of

(* BINDER INSTANCES.  [binder_instances ~fenv ~defs ~scope c] for a conjunct
   [c] (a disjunction, in negation normal form): the instances [psi[a / xs]]
   of each top-level disjunct [exists xs. psi] of [c] at the arguments of a
   counted application of [c] outside every binder ([candidate_apps]) that
   matches an application [f(.., x, ..)] in [psi] (outside [psi]'s own
   binders): at each position where the pattern's argument is a variable of
   [xs] the outside argument is taken for it, every other argument is the
   same term in both, and every variable of [xs] gets exactly one value.
   Distinct instances, in order of discovery; empty when there is none.

   Why.  A lemma a clause uses -- a callee's postcondition such as
   [forall s. (forall j. 64 j < n -> s[j] = 0) -> ones(s, n) = 0] -- sits in
   the clause's body as a universal, so in the clause as an existential
   disjunct, and the counted function applied under it is out of the
   encoding's reach (an application under a binder is never replaced).  The
   same clause applies the function at its own sequence, [ones(x0, n)], and
   that application alone is replaced by the graph unknown's result [r].
   The lemma and [r] then share nothing: the goal clause holds only if the
   graph unknown itself states the lemma, an invariant over every cell of the
   sequence that no quantifier-free candidate expresses, while the clause
   needed nothing but the lemma at [x0].  Its instance, a disjunct outside
   every binder, puts [ones(x0, n)] in the same replaced group, so [r] is
   bound by the lemma in the goal itself.

   Exact: [exists xs. psi] holds wherever [psi[a / xs]] does, so [c] and
   [c \/ psi[a / xs]] are equivalent in every model.  [Formula.subst] is
   capture-avoiding, so [psi]'s own binders do not capture [a]'s
   variables. *)
let binder_instances ~fenv ~defs ~scope c =
  let outside = candidate_apps ~fenv ~defs ~scope c in
  if List.is_empty outside then []
  else
    let seen = Hash_set.Poly.create () in
    List.concat_map (Formula.disjuncts_list_of c) ~f:(function
      | Formula.Bind (Formula.Exists, bounds, psi, _) ->
          let bound x = List.exists bounds ~f:(fun (y, _) -> Ident.tvar_equal x y) in
          let patterns = ref [] in
          ignore
          @@ Formula.map_term_no_binders psi ~f:(fun t ->
              (match t with
              | Term.FunApp (FVar (g, _, _), _, _) when Map.Poly.mem defs g ->
                  patterns := t :: !patterns
              | _ -> ());
              t);
          List.filter_map (List.rev !patterns) ~f:(fun pat ->
              List.find_map outside ~f:(fun app ->
                  match (pat, app) with
                  | ( Term.FunApp (FVar (g, _, _), pargs, _),
                      Term.FunApp (FVar (h, _, _), aargs, _) )
                    when Ident.tvar_equal g h
                         && List.length pargs = List.length aargs -> (
                      let ok, map =
                        List.fold2_exn pargs aargs ~init:(true, Map.Poly.empty)
                          ~f:(fun (ok, map) p a ->
                            if not ok then (false, map)
                            else
                              match p with
                              | Term.Var (x, _, _) when bound x -> (
                                  match Map.Poly.find map x with
                                  | None -> (true, Map.Poly.set map ~key:x ~data:a)
                                  | Some a' ->
                                      (String.equal (str_key a) (str_key a'), map))
                              | _ ->
                                  ( Set.for_all (Term.tvs_of p) ~f:(Fn.non bound)
                                    && String.equal (str_key p) (str_key a),
                                    map ))
                      in
                      if
                        ok
                        && List.for_all bounds ~f:(fun (x, _) -> Map.Poly.mem map x)
                      then
                        let inst = Formula.subst map psi in
                        let key = Formula.str_of inst in
                        if Hash_set.mem seen key then None
                        else (
                          Hash_set.add seen key;
                          Some inst)
                      else None)
                  | _ -> None))
      | _ -> [])

(* [with_binder_instances ~fenv ~defs ~scope phi]: [phi] (in negation normal
   form) with each conjunct extended by its [binder_instances]; [phi] itself,
   as the same value, when no conjunct has one.  Equivalent to [phi] in every
   model, by the argument at [binder_instances]. *)
let binder_instances_added = Atomic.make 0

let with_binder_instances ~fenv ~defs ~scope phi =
  let changed = ref false in
  let cs =
    List.map (Formula.conjuncts_list_of phi) ~f:(fun c ->
        match binder_instances ~fenv ~defs ~scope c with
        | [] -> c
        | insts ->
            changed := true;
            Atomic.incr binder_instances_added;
            Formula.or_of (c :: insts))
  in
  if !changed then Formula.and_of cs else phi

(* [abstracted_weakening ~defs ~keep phi]: a formula implied by the
   negation of [phi] in which no counted function is applied, or [None] when
   nothing would be left.  The conjuncts of [nnf (not phi)] that [keep]
   rejects are dropped; in the others every application of a counted function
   outside every binder is replaced by a fresh variable (one per distinct
   application, by its printed form); a conjunct that still applies a counted
   function (under a binder) is dropped too.

   Contract.  If the result is unsatisfiable, [phi] is valid: the kept
   conjuncts are implied by [nnf (not phi)], and a model of them is a model
   of their abstraction once each fresh variable takes the value of the
   application it replaced, which the model fixes, since an application
   outside every binder has only free variables in its arguments.  Nothing
   else may be read from the result: a model of it need not satisfy what was
   dropped or abstracted.  Why: a constraint whose quantified lemma premise
   was instantiated at its own application ([binder_instances]) is decided
   by that instance and the rest without the definition, and Z3 asked the
   rest with the recursive definition in context did not answer it within
   2 s (the definition is unfolded while the instance already decides). *)
let abstracted_weakening ~defs ~keep phi =
  let applies_counted psi =
    Set.exists (Formula.fvar_apps_of psi) ~f:(function
      | Term.FunApp (FVar (g, _, _), _, _) -> Map.Poly.mem defs g
      | _ -> false)
  in
  let taken = ref (Formula.tvs_of phi) in
  let fresh = Hashtbl.Poly.create () in
  let abstract psi =
    Formula.map_term_no_binders psi ~f:(fun t ->
        match t with
        | Term.FunApp (FVar (g, _, _), _, _) when Map.Poly.mem defs g -> (
            let key = str_key t in
            match Hashtbl.find fresh key with
            | Some v -> v
            | None ->
                let x =
                  Ident.mk_fresh_tvar_avoiding ~prefix:"rfg_abs"
                    ~taken:(Set.mem !taken) ()
                in
                taken := Set.add !taken x;
                let v = Term.mk_var x (Term.sort_of t) in
                Hashtbl.set fresh ~key ~data:v;
                v)
        | _ -> t)
  in
  let kept =
    List.filter_map
      (Formula.conjuncts_list_of (Formula.nnf_of (Formula.negate phi)))
      ~f:(fun c ->
        if not (keep c) then None
        else
          let c' = abstract c in
          if applies_counted c' then None else Some c')
  in
  if List.is_empty kept then None else Some (Formula.and_of kept)

let instantiate d ~args ~counter t =
  let map =
    Map.Poly.of_alist_exn
    @@ List.mapi d.params ~f:(fun i (x, _) ->
        (x, if i = d.pos then counter else List.nth_exn args i))
  in
  Evaluator.simplify_term (Term.subst map t)

type group = {
  def : counted;
  counter : Term.t;  (** [t] *)
  apps : Term.t list;  (** distinct, in order of first occurrence *)
}

(* One conjunct: [None] when it holds no candidate application; otherwise the
   rewritten goal with its variable environment, and the base and step
   constraints of each group with theirs. *)
let encode_conjunct ~fenv ~defs ~uni_senv ~taken_pred c =
  let scope = Map.key_set uni_senv in
  let apps = candidate_apps ~fenv ~defs ~scope c in
  if List.is_empty apps then None
  else
    let groups =
      List.fold apps ~init:[] ~f:(fun gs app ->
          let g, args =
            match app with
            | Term.FunApp (FVar (g, _, _), args, _) -> (g, args)
            | _ -> assert false
          in
          let def = Map.Poly.find_exn defs g in
          let counter = List.nth_exn args def.pos in
          let same gr =
            Ident.tvar_equal gr.def.name g
            && String.equal (str_key gr.counter) (str_key counter)
          in
          match List.find gs ~f:same with
          | Some gr ->
              if
                List.exists gr.apps ~f:(fun a ->
                    String.equal (str_key a) (str_key app))
              then gs
              else
                List.map gs ~f:(fun gr' ->
                    if same gr' then { gr' with apps = gr'.apps @ [ app ] }
                    else gr')
          | None -> gs @ [ { def; counter; apps = [ app ] } ])
    in
    let taken_var = ref scope in
    let fresh prefix =
      let v =
        Ident.mk_fresh_tvar_avoiding ~prefix ~taken:(Set.mem !taken_var) ()
      in
      taken_var := Set.add !taken_var v;
      v
    in
    let replace = Hashtbl.Poly.create () in
    let groups =
      List.map groups ~f:(fun gr ->
          let rs =
            List.map gr.apps ~f:(fun app ->
                let r = fresh "r" in
                Hashtbl.set replace ~key:(str_key app)
                  ~data:(Term.mk_var r gr.def.sret);
                (r, gr.def.sret))
          in
          let vs =
            Set.to_list
            @@ Set.Poly.union_list
                 (List.map (gr.counter :: gr.apps) ~f:(fun a ->
                      Set.inter (Term.tvs_of a) scope))
          in
          let vs =
            List.map vs ~f:(fun x -> (x, Map.Poly.find_exn uni_senv x))
          in
          let pred = taken_pred () in
          (gr, rs, vs, pred))
    in
    let c' =
      Formula.map_term_no_binders c ~f:(fun t ->
          match Hashtbl.find replace (str_key t) with Some r -> r | None -> t)
    in
    let pvar_app pred sorts args =
      Formula.mk_atom @@ Atom.mk_pvar_app (Ident.tvar_to_pvar pred) sorts args
    in
    let disjuncts = Formula.disjuncts_list_of c in
    let goal =
      Formula.or_of
        (c'
        :: List.map groups ~f:(fun (gr, rs, vs, pred) ->
            let sorts =
              List.map vs ~f:snd @ [ T_int.SInt ] @ List.map rs ~f:snd
            in
            Formula.mk_neg
            @@ pvar_app pred sorts
                 (List.map vs ~f:(fun (x, s) -> Term.mk_var x s)
                 @ [ gr.counter ]
                 @ List.map rs ~f:(fun (r, s) -> Term.mk_var r s))))
    in
    let goal_senv =
      List.fold groups ~init:uni_senv ~f:(fun senv (_, rs, _, _) ->
          List.fold rs ~init:senv ~f:(fun senv (r, s) ->
              Map.Poly.set senv ~key:r ~data:s))
    in
    let side =
      List.concat_map groups ~f:(fun (gr, rs, vs, pred) ->
          let d = gr.def in
          let vset = Set.Poly.of_list (List.map vs ~f:fst) in
          let guard =
            List.filter disjuncts ~f:(fun phi ->
                Set.is_subset (Formula.tvs_of phi) ~of_:vset
                && String.equal (Formula.str_of phi)
                     (Formula.str_of
                        (Formula.map_term_no_binders phi ~f:(fun t ->
                             match Hashtbl.find replace (str_key t) with
                             | Some r -> r
                             | None -> t))))
          in
          let sorts =
            List.map vs ~f:snd @ [ T_int.SInt ] @ List.map rs ~f:snd
          in
          let vterms = List.map vs ~f:(fun (x, s) -> Term.mk_var x s) in
          let j = fresh "j" in
          let jt = Term.mk_var j T_int.SInt in
          let c = T_int.mk_int d.bound in
          let args_of app =
            match app with
            | Term.FunApp (_, args, _) -> args
            | _ -> assert false
          in
          let start =
            if
              T_int.is_int gr.counter
              && Z.geq (T_int.let_int gr.counter) d.bound
            then Formula.eq jt c
            else Formula.mk_atom (T_int.mk_leq jt c)
          in
          let base =
            Formula.or_of
              (guard
              @ [
                  Formula.mk_neg start;
                  pvar_app pred sorts
                    (vterms @ [ jt ]
                    @ List.map gr.apps ~f:(fun app ->
                        instantiate d ~args:(args_of app) ~counter:jt d.base));
                ])
          in
          let base_senv =
            Map.Poly.set ~key:j ~data:T_int.SInt @@ Map.Poly.of_alist_exn vs
          in
          let next = T_int.mk_add jt (T_int.from_int 1) in
          let step =
            Formula.or_of
              [
                Formula.mk_neg
                @@ pvar_app pred sorts
                     (vterms @ [ jt ]
                     @ List.map rs ~f:(fun (r, s) -> Term.mk_var r s));
                Formula.mk_atom (T_int.mk_gt c jt);
                Formula.mk_atom (T_int.mk_gt next gr.counter);
                pvar_app pred sorts
                  (vterms @ [ next ]
                  @ List.map2_exn gr.apps rs ~f:(fun app (r, s) ->
                      let body =
                        Term.map_term true d.step ~f:(fun t ->
                            if String.equal (str_key t) (str_key d.rec_call)
                            then Term.mk_var r s
                            else t)
                      in
                      instantiate d ~args:(args_of app) ~counter:next body));
              ]
          in
          let step_senv =
            List.fold rs ~init:base_senv ~f:(fun senv (r, s) ->
                Map.Poly.set senv ~key:r ~data:s)
          in
          [ (base_senv, base); (step_senv, step) ])
    in
    (* the graph of each group's calls over the unknown's own parameters
       [(v, j, r_1 .. r_m)]: the atoms [r_i = f(a_i[j / t])], whose
       conjunction is the solution Lemma GRAPH (in [encode]) names *)
    let graphs =
      List.map groups ~f:(fun (gr, rs, vs, pred) ->
          let j = fresh "j" in
          let jt = Term.mk_var j T_int.SInt in
          let atoms =
            List.map2_exn gr.apps rs ~f:(fun app (r, s) ->
                match app with
                | Term.FunApp (sym, args, info) ->
                    Formula.eq (Term.mk_var r s)
                      (Term.mk_fsym_app ~info sym
                         (List.mapi args ~f:(fun i a ->
                              if i = gr.def.pos then jt else a)))
                | _ -> assert false)
          in
          (pred, (vs @ [ (j, T_int.SInt) ] @ rs, atoms)))
    in
    Some
      ( (goal_senv, goal) :: side,
        List.map groups ~f:(fun (_, _, vs, pred) -> (pred, List.map vs ~f:snd)),
        List.map groups ~f:(fun (_, rs, _, _) -> List.map rs ~f:snd),
        graphs )

(* how many calls of [encode] (resp. [encode_clauses]) have introduced at
   least one unknown in this process: instruments for tests that check which
   readings of an input were encoded, and at which stage; nothing reads them
   to decide *)
let encodings_introducing = Atomic.make 0
let clause_encodings_introducing = Atomic.make 0

(* [graph_candidates]: each unknown [G] introduced is given, as its declared
   candidate atoms ([Params.candidate_atoms]), the atoms
   [r_i = f(a_i[j / t])] over its parameters [(v, j, r_1 .. r_m)], and every
   function those atoms apply stays in the problem's environment.  The
   qualifier generator then offers them to [G]'s hypothesis space and the
   Houdini pre-pass starts [G] from their conjunction.

   LEMMA GRAPH (why this keeps the encoding exact).  [G(v, j, r) :=
   /\ r_i = f(a_i[j / t])] satisfies the base and the step clause of its
   group in every model of the background theory, and substituted into the
   goal gives back the constraint as it was before the encoding.
   Proof.  Base: its premise [J(j)] gives [j <= c], where the definition is
   [base], so [f(a_i[j / t]) = base[a_i, j]] -- the head's arguments.  Step:
   from [r_i = f(a_i[j / t])] and [c <= j], the counter [j + 1] exceeds [c],
   where the definition is [step] over the call at [j], which is [r_i]; so
   [f(a_i[j + 1 / t]) = step[a_i, j + 1, r_i]] -- the head's arguments.  Goal:
   [C[r / f(a, t)] \/ not G(v, t, r)] with [G] the graph holds iff for all
   [r], [r_i = f(a_i, t)] for every [i] implies [C[r / f(a, t)]], which is [C].
   QED.  So the encoded problem has a solution exactly where the original
   has one (one direction is the equisatisfiability argument above, the other
   this lemma), and the atoms change neither: they are hints, never
   constraints, and anything proposed from them is validated against the
   clauses like any other candidate.  Keeping [f] in the environment is what
   lets the atoms be read at all; it changes no constraint either. *)

(* whether the constraint [t] mentions an unknown of [exi_senv] *)
let mentions_unknown exi_senv t =
  Set.exists (Logic.ExtTerm.fvs_of t) ~f:(Map.Poly.mem exi_senv)

(* The step both entry points share.  Each constraint of [phis] whose flag is
   [true] is encoded conjunct by conjunct as stated at the top; the result
   gives, per constraint and in order, [`Kept] (no conjunct held a candidate
   application, or the flag was [false]: the constraint stays as it was) or
   [`New fmls] (its replacement), with the sorts of the unknowns introduced
   and each one's graph (see [graph_candidates] above).  Each constraint is
   encoded on its own, with unknowns of its own, so encoding any subset of
   them keeps the problem equisatisfiable. *)
let encode_constraints (params : Params.t) defs phis =
  let fenv = params.Params.fenv in
  let exi_senv = params.Params.senv in
  let new_senv = ref Map.Poly.empty in
  let taken_pred () =
    let v =
      Ident.mk_fresh_tvar_avoiding ~prefix:"recgraph"
        ~taken:(fun v ->
          Map.Poly.mem exi_senv v || Map.Poly.mem !new_senv v
          || Map.Poly.mem fenv v)
        ()
    in
    new_senv := Map.Poly.set !new_senv ~key:v ~data:Logic.BoolTerm.SBool;
    v
  in
  let graphs = ref [] in
  let encode_formula (uni_senv, t) =
    let old_senv = Map.Poly.map uni_senv ~f:Logic.ExtTerm.to_old_sort in
    let phi = Formula.nnf_of @@ Logic.ExtTerm.to_old_fml exi_senv uni_senv t in
    let phi =
      with_binder_instances ~fenv ~defs ~scope:(Map.key_set old_senv) phi
    in
    let outs =
      List.map (Formula.conjuncts_list_of phi) ~f:(fun c ->
          match encode_conjunct ~fenv ~defs ~uni_senv:old_senv ~taken_pred c with
          | None -> `Kept c
          | Some (fmls, preds, results, gs) ->
              graphs := gs @ !graphs;
              List.iter2_exn preds results ~f:(fun (pred, vsorts) rsorts ->
                  new_senv :=
                    Map.Poly.set !new_senv ~key:pred
                      ~data:
                        (Logic.Sort.mk_fun
                           (List.map
                              (vsorts @ [ T_int.SInt ] @ rsorts)
                              ~f:Logic.ExtTerm.of_old_sort
                           @ [ Logic.BoolTerm.SBool ])));
              `New fmls)
    in
    if
      List.for_all outs ~f:(function
        | `Kept _ -> true
        | `New _ -> false)
    then `Kept
    else
      `New
        (List.concat_map outs ~f:(function
          | `Kept c -> [ Logic.ExtTerm.of_old (old_senv, c) ]
          | `New fmls -> List.map fmls ~f:Logic.ExtTerm.of_old))
  in
  let outs =
    List.map phis ~f:(fun (try_it, phi) ->
        if try_it then encode_formula phi else `Kept)
  in
  (outs, !new_senv, !graphs)

(* The parameters of an encoded problem: [params] with the introduced
   unknowns of sorts [new_senv] (kind [Ord]) and, unless [keep_functions],
   the function environment cut down to the definitions the formulas
   [applied_in] (the encoded problem's constraints) still apply, directly or
   through the bodies of those they apply.  Every solver query declares the
   environment's definitions, and a recursive definition in a synthesis or
   validation query slows Z3 down even when nothing applies it: a
   three-clause linear loop answered in 2 s is not answered in 60 s once one
   unused [define-fun-rec] is beside it.  Dropping a definition nothing
   applies changes no constraint; keeping one changes none either. *)
let encoded_params ~graph_candidates ~keep_functions (params : Params.t)
    new_senv graphs ~applied_in =
  let fenv = params.Params.fenv in
  let added = Map.Poly.key_set new_senv in
  let params =
    {
      params with
      Params.senv = Map.force_merge params.Params.senv new_senv;
      kind_map = Kind.add_kinds added Kind.Ord params.Params.kind_map;
    }
  in
  let applied t =
    Set.Poly.filter_map (Term.fvar_apps_of t) ~f:(function
      | Term.FunApp (FVar (g, _, _), _, _) -> Some g
      | _ -> None)
  in
  let rec close seen = function
    | [] -> seen
    | g :: rest when Set.mem seen g -> close seen rest
    | g :: rest -> (
        let seen = Set.add seen g in
        match Map.Poly.find fenv g with
        | Some (_, _, body, _, _) ->
            close seen (Set.to_list (applied body) @ rest)
        | None -> close seen rest)
  in
  let fvars phi =
    Set.Poly.filter_map (Formula.fvar_apps_of phi) ~f:(function
      | Term.FunApp (FVar (g, _, _), _, _) -> Some g
      | _ -> None)
  in
  let fenv' =
    if keep_functions then fenv
    else
      let used =
        close Set.Poly.empty @@ Set.to_list @@ Set.Poly.union_list
        @@ List.map
             (applied_in params
             @
             if graph_candidates then
               List.concat_map graphs ~f:(fun (_, (_, atoms)) -> atoms)
             else [])
             ~f:fvars
      in
      Map.Poly.filter_keys fenv ~f:(Set.mem used)
  in
  {
    params with
    Params.fenv = fenv';
    candidate_atoms =
      (if graph_candidates then
         List.fold graphs ~init:params.Params.candidate_atoms
           ~f:(fun m (pred, entry) -> Map.Poly.set m ~key:pred ~data:entry)
       else params.Params.candidate_atoms);
  }

(* The problem with every counted application encoded as stated at the top,
   and the names of the unknowns introduced; the problem itself, and no name,
   when it holds none (or is already in clause form: [encode_clauses] is the
   entry point for a problem in clause form).
   [unknown_free_only]: only the constraints that mention no unknown are
   encoded; every other constraint is kept as it is.  Encoding fewer
   constraints keeps the result equisatisfiable, since each constraint is
   encoded on its own with unknowns of its own.  The point is the problem
   whose recursive function is applied only beside unknowns that predicate
   elimination removes: as given, every unknown is eliminated and the
   remaining validity question unfolds the definition once; encoded, the
   graph unknown is recursive, elimination stops at it, and the synthesiser
   has to find an invariant for what needed no induction.
   [keep_functions]: as for [encode_clauses]. *)
let encode ?guarded_counter ?(unknown_free_only = false) ?(graph_candidates = false)
    ?(keep_functions = false) (pcsp : Problem.t) =
  if not (Problem.is_raw pcsp) then (pcsp, [])
  else
    let params = Problem.params_of pcsp in
    let defs = counted_defs ?guarded_counter params.Params.fenv in
    if Map.Poly.is_empty defs then (pcsp, [])
    else
      let phis =
        Set.to_list @@ Problem.formulas_of ~full_clauses:false pcsp
      in
      let outs, new_senv, graphs =
        encode_constraints params defs
          (List.map phis ~f:(fun ((_, t) as phi) ->
               ( not
                   (unknown_free_only
                   && mentions_unknown params.Params.senv t),
                 phi )))
      in
      if Map.Poly.is_empty new_senv then (pcsp, [])
      else
        let phis' =
          Set.Poly.of_list
          @@ List.concat_map (List.zip_exn phis outs) ~f:(function
            | phi, `Kept -> [ phi ]
            | _, `New fmls -> fmls)
        in
        let params =
          encoded_params ~graph_candidates ~keep_functions params
            new_senv graphs ~applied_in:(fun params ->
              Set.to_list
              @@ Problem.old_formulas_of (Problem.of_formulas ~params phis'))
        in
        Atomic.incr encodings_introducing;
        (Problem.of_formulas ~params phis', Set.to_list (Map.key_set new_senv))

(* The counted applications a clause could have encoded: [true] exactly when
   [encode_clauses] picking [cl] would replace it (some conjunct of its
   negation normal form holds a candidate application in the sense of the
   top of this file).  [encodable_clauses] is the same test over a set, with
   the counted definitions of [params]'s environment read once. *)
let encodable_formula ~fenv ~defs (params : Params.t) (uni_senv, t) =
  let old_senv = Map.Poly.map uni_senv ~f:Logic.ExtTerm.to_old_sort in
  let phi =
    Formula.nnf_of @@ Logic.ExtTerm.to_old_fml params.Params.senv uni_senv t
  in
  List.exists (Formula.conjuncts_list_of phi) ~f:(fun c ->
      not
        (List.is_empty
           (candidate_apps ~fenv ~defs ~scope:(Map.key_set old_senv) c)))

let encodable_clauses ?guarded_counter (params : Params.t) clauses =
  let fenv = params.Params.fenv in
  let defs = counted_defs ?guarded_counter fenv in
  if Map.Poly.is_empty defs then Set.Poly.empty
  else
    Set.filter clauses ~f:(fun cl ->
        encodable_formula ~fenv ~defs params (Clause.to_senv_formula cl))

(* [drop_valid_encodable ~valid p]: [p] without each constraint that mentions
   no unknown of [p], that an encoding would rewrite (it holds a candidate
   application of a counted function, as [encodable_clauses] tests), and that
   [valid] proves valid; with the number dropped.  [valid] is given the
   constraint as a first-order formula whose free variables are read
   universally, and must answer [true] only for a formula valid in every
   model.  Contract: the result has the solutions of [p] (a valid constraint
   constrains no unknown), the same signature, parameters and function
   environment, and the same form (clauses or formulas); [p] itself, as the
   same value, when nothing is dropped.  Why: such a constraint, once encoded,
   turns into a graph unknown whose invariant the loop has to find, although
   it may need no induction at all (a property of the function the clauses
   only carry, or unfold once). *)
let drop_valid_encodable ?guarded_counter ~valid (pcsp : Problem.t) =
  let params = Problem.params_of pcsp in
  let fenv = params.Params.fenv in
  let defs = counted_defs ?guarded_counter fenv in
  if Map.Poly.is_empty defs then (pcsp, 0)
  else
    let droppable ((uni_senv, t) as phi) =
      (not (mentions_unknown params.Params.senv t))
      && encodable_formula ~fenv ~defs params phi
      &&
      (* asked with the binder instances of [with_binder_instances], an
         equivalent formula: a lemma premise quantified over the sequence the
         constraint also applies the function at is then usable without
         instantiating a quantifier *)
      let phi = Logic.ExtTerm.to_old_fml params.Params.senv uni_senv t in
      let nnf = Formula.nnf_of phi in
      let phi' =
        with_binder_instances ~fenv ~defs ~scope:(Map.key_set uni_senv) nnf
      in
      valid (if phys_equal phi' nnf then phi else phi')
    in
    match Problem.clauses_of_opt ~full_clauses:false pcsp with
    | Some clauses ->
        let dropped, kept =
          Set.partition_tf clauses ~f:(fun cl ->
              droppable (Clause.to_senv_formula cl))
        in
        if Set.is_empty dropped then (pcsp, 0)
        else (Problem.of_clauses ~params kept, Set.length dropped)
    | None ->
        if not (Problem.is_raw pcsp) then (pcsp, 0)
        else
          let phis = Problem.formulas_of ~full_clauses:false pcsp in
          let dropped, kept = Set.partition_tf phis ~f:droppable in
          if Set.is_empty dropped then (pcsp, 0)
          else (Problem.of_formulas ~params kept, Set.length dropped)

(* The entry point for a problem in CLAUSE form, which is the form the
   preprocessor hands the CEGIS loop.  Contract: the result is the problem
   with each clause that [only] picks (and, under [unknown_free_only], that
   mentions no unknown of the problem it is given) replaced by the clauses of
   its encoding, every other clause and every stable clause kept as the very
   value it was; the names of the unknowns introduced; and the problem
   itself, with no name, when it is not in clause form or no picked clause
   holds a candidate application.  The encoding's own clauses are put
   through the normalisations the preprocessor ends with ([Problem.normalize],
   negation and clausal normal form), since nothing after this point applies
   them.  Equisatisfiable in every model, by the argument at the top for
   each encoded clause separately and Lemma GRAPH for the converse; the
   unknowns the clause shared with the rest of the problem are untouched,
   so a solution of the result restricted to them solves the problem given,
   and a solution of the problem given extended by the graphs solves the
   result.  [keep_functions]: the function environment is kept whole rather
   than cut down to what the result applies (a caller that holds examples
   mentioning a function must keep its definition: an example over [f]'s
   terms is a statement in every model only while [f] denotes its
   definition). *)
let encode_clauses ?guarded_counter ?(unknown_free_only = false) ?(only = fun _ -> true)
    ?(graph_candidates = false) ?(keep_functions = false) (pcsp : Problem.t) =
  match Problem.clauses_of_opt ~full_clauses:false pcsp with
  | None -> (pcsp, [])
  | Some clauses ->
      let params = Problem.params_of pcsp in
      let defs = counted_defs ?guarded_counter params.Params.fenv in
      if Map.Poly.is_empty defs then (pcsp, [])
      else
        let cls = Set.to_list clauses in
        let outs, new_senv, graphs =
          encode_constraints params defs
            (List.map cls ~f:(fun cl ->
                 let ((_, t) as phi) = Clause.to_senv_formula cl in
                 ( only cl
                   && not
                        (unknown_free_only
                        && mentions_unknown params.Params.senv t),
                   phi )))
        in
        if Map.Poly.is_empty new_senv then (pcsp, [])
        else
          let kept, fresh =
            List.partition_map (List.zip_exn cls outs) ~f:(function
              | cl, `Kept -> First cl
              | _, `New fmls -> Second fmls)
          in
          let params' =
            {
              params with
              Params.senv = Map.force_merge params.Params.senv new_senv;
              kind_map =
                Kind.add_kinds (Map.key_set new_senv) Kind.Ord
                  params.Params.kind_map;
            }
          in
          let fresh_clauses =
            Problem.clauses_of ~full_clauses:false
            @@ Problem.to_cnf @@ Problem.to_nnf @@ Problem.normalize
            @@ Problem.of_formulas
                 ~params:{ params' with Params.stable_clauses = Set.Poly.empty }
            @@ Set.Poly.of_list (List.concat fresh)
          in
          let clauses' = Set.union (Set.Poly.of_list kept) fresh_clauses in
          let params =
            encoded_params ~graph_candidates ~keep_functions params new_senv
              graphs ~applied_in:(fun params ->
                Set.to_list
                @@ Problem.old_formulas_of (Problem.of_clauses ~params clauses'))
          in
          Atomic.incr clause_encodings_introducing;
          ( Problem.of_clauses ~params clauses',
            Set.to_list (Map.key_set new_senv) )
