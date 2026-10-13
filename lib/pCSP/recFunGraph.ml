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

(* [Some] exactly for a definition of the COUNTED shape stated above whose body
   is closed: every variable it mentions is a parameter or a function of
   [fenv].  The encoding substitutes the body at new arguments into clauses
   whose variables are the arguments' variables, so a variable free in the
   body would enter a clause unbound -- a universal the definition shares with
   the clauses, which only the clause's own copy of it may stand for. *)
let counted_of ~(fenv : FunEnv.t) name (params, sret, body, is_rec, _) =
  let closed () =
    Set.for_all (Term.tvs_of body) ~f:(fun x ->
        List.exists params ~f:(fun (y, _) -> Ident.tvar_equal x y)
        || Map.Poly.mem fenv x)
  in
  if not (is_rec && closed ()) then None
  else
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

let counted_defs (fenv : FunEnv.t) =
  Map.Poly.filter_mapi fenv ~f:(fun ~key ~data -> counted_of ~fenv key data)

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
let encode ?(unknown_free_only = false) ?(graph_candidates = false)
    ?(keep_functions = false) (pcsp : Problem.t) =
  if not (Problem.is_raw pcsp) then (pcsp, [])
  else
    let params = Problem.params_of pcsp in
    let defs = counted_defs params.Params.fenv in
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
let encodable_clauses (params : Params.t) clauses =
  let fenv = params.Params.fenv in
  let defs = counted_defs fenv in
  if Map.Poly.is_empty defs then Set.Poly.empty
  else
    Set.filter clauses ~f:(fun cl ->
        let uni_senv, t = Clause.to_senv_formula cl in
        let old_senv = Map.Poly.map uni_senv ~f:Logic.ExtTerm.to_old_sort in
        let phi =
          Formula.nnf_of
          @@ Logic.ExtTerm.to_old_fml params.Params.senv uni_senv t
        in
        List.exists (Formula.conjuncts_list_of phi) ~f:(fun c ->
            not
              (List.is_empty
                 (candidate_apps ~fenv ~defs ~scope:(Map.key_set old_senv) c))))

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
let encode_clauses ?(unknown_free_only = false) ?(only = fun _ -> true)
    ?(graph_candidates = false) ?(keep_functions = false) (pcsp : Problem.t) =
  match Problem.clauses_of_opt ~full_clauses:false pcsp with
  | None -> (pcsp, [])
  | Some clauses ->
      let params = Problem.params_of pcsp in
      let defs = counted_defs params.Params.fenv in
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
