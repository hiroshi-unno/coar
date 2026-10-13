(* Quantified satisfiability by strategy improvement.

   This implements Azadeh Farzan and Zachary Kincaid, "Linear Arithmetic
   Satisfiability via Strategy Improvement", IJCAI-16, pp. 735-743: a quantified
   formula is read as a game between two players -- [SAT] and [UNSAT] below --
   and the procedure improves candidate strategies for both until one is
   winning, so that an SMT solver is only ever asked about the ground fragment
   and no quantifier is eliminated explicitly.

   [select] in the functor argument is the paper's model-guided term selection
   function: given a ground formula F, a model M of F and a variable x, it
   returns a term t with x not in t and M |= F[x := t].  The paper's own
   remark is that this is inspired by model-based projection (Komuravelli,
   Gurfinkel and Chaki, CAV 2014) and by Weispfenning's decision procedure for
   linear real arithmetic; a neighbouring file takes the projection route
   instead, and returns a region where this returns a term.

   [LIA] implements the paper's VIRTUAL term selection -- a term is a triple
   (affine expression, divisor, offset), and the divisibility modulus [delta]
   is what makes the integer case work -- while [LRA] returns ordinary terms.
   [QBF] is a stub. *)
open Core
open Common.Ext
open Common.Combinator
open Logic

(* Quantified Satisfiability Modulo Theories *)
module PreFormula = struct
  type binder = Forall | Exists
  type var = sort_bind

  type 'a formula =
    | Atom of 'a
    | And of 'a formula list
    | Or of 'a formula list
    | Bind of binder * var * 'a formula

  let neg_binder = function Forall -> Exists | Exists -> Forall

  let rec atoms = function
    | Atom a -> [ a ]
    | And l | Or l -> List.concat_map ~f:atoms l
    | Bind (_, _, f) -> atoms f

  let rec term_of_formula term_of_atom = function
    | Atom a -> term_of_atom a
    | And l -> BoolTerm.and_of (List.map ~f:(term_of_formula term_of_atom) l)
    | Or l -> BoolTerm.or_of (List.map ~f:(term_of_formula term_of_atom) l)
    | Bind (bind, (var, sort), f) ->
        Term.mk_bind
          (match bind with Forall -> Logic.Forall | Exists -> Logic.Exists)
          var sort
          (term_of_formula term_of_atom f)

  let rec neg_formula neg_atom = function
    | Atom a -> neg_atom a
    | And l -> Or (List.map ~f:(neg_formula neg_atom) l)
    | Or l -> And (List.map ~f:(neg_formula neg_atom) l)
    | Bind (b, v, f) -> Bind (neg_binder b, v, neg_formula neg_atom f)
end

module StrategySynthesis (A : sig
  type domain
  type term
  type atom

  val default_value : domain
  val sort : Sort.t
  val neg_atom : atom -> atom PreFormula.formula
  val subst_atom : Ident.tvar -> term -> atom -> atom PreFormula.formula
  val term_equal : term -> term -> bool
  val eval_term : (Ident.tvar, domain) Map.Poly.t -> term -> domain
  val rename_var_atom : Ident.tvar -> Ident.tvar -> atom -> atom
  val term_of_atom : atom -> Logic.term

  val select :
    (Ident.tvar, domain) Map.Poly.t ->
    Ident.tvar ->
    atom PreFormula.formula ->
    term

  val check_sat :
    (sort_env_list ->
    Logic.term ->
    (Ident.tvar * Logic.term option) list option) ->
    atom PreFormula.formula ->
    sort_env_list ->
    (Ident.tvar, domain) Map.Poly.t option

  val term_of_term : term -> Logic.term
end) =
struct
  open PreFormula

  let rec subst_formula tvar t = function
    | Atom a -> A.subst_atom tvar t a
    | And l -> And (List.map ~f:(subst_formula tvar t) l)
    | Or l -> Or (List.map ~f:(subst_formula tvar t) l)
    | Bind (b, u, f) -> Bind (b, u, subst_formula tvar t f)

  let rec rename_var_formula v v' = function
    | Atom a -> Atom (A.rename_var_atom v v' a)
    | And l -> And (List.map ~f:(rename_var_formula v v') l)
    | Or l -> Or (List.map ~f:(rename_var_formula v v') l)
    | Bind (b, u, f) -> Bind (b, u, rename_var_formula v v' f)

  type depforest = deptree list

  and deptree =
    | ForallDep of PreFormula.var * depforest
    | ExistsDep of PreFormula.var * depforest

  type ssforest = sstree list

  and sstree =
    | ForallSS of PreFormula.var * ssforest
    | ExistsSS of
        PreFormula.var * (A.term * ssforest) list (*this list must be nonempty*)

  let rec merge_ssforest f f' = List.zip_exn f f' |> List.map ~f:merge_sstree

  and merge_sstree = function
    | ForallSS (v, f), ForallSS (v', f') ->
        assert (Stdlib.(v = v'));
        ForallSS (v, merge_ssforest f f')
    | ExistsSS (v, l), ExistsSS (v', l') ->
        assert (Stdlib.(v = v'));
        let rec unify_term_forest_list l = function
          | [] -> l
          | (t', ssf') :: l' -> (
              let lt, lf =
                List.partition_tf ~f:(fun (t, _) -> A.term_equal t t') l
              in
              match lt with
              | [] -> (t', ssf') :: unify_term_forest_list l l'
              | [ (t, ssf) ] ->
                  (t, merge_ssforest ssf ssf') :: unify_term_forest_list lf l'
              | _ -> assert false)
        in
        ExistsSS (v, unify_term_forest_list l l')
    | _, _ -> assert false

  let merge_ssforest_option f f' =
    match (f, f') with
    | Some f, Some f' -> Some (merge_ssforest f f')
    | None, _ -> f'
    | _, None -> f

  let rec merge_ssforest_nonempty_list = function
    | [] -> assert false
    | [ s ] -> s
    | s :: l -> merge_ssforest s (merge_ssforest_nonempty_list l)

  let herbrandize position tvar =
    let suffix =
      List.rev position |> String.concat_map_list ~sep:"_" ~f:string_of_int
    in
    Ident.Tvar (Ident.name_of_tvar tvar ^ "_" ^ suffix)

  let remove_forall v s =
    List.find_map_exn s ~f:(function
      | ForallSS (u, s') when Stdlib.(v = u) -> Some s'
      | _ -> None)

  let remove_exists v s =
    List.find_map_exn s ~f:(function
      | ExistsSS (u, l) when Stdlib.(v = u) -> Some l
      | _ -> None)

  let rec winning_formula (position : int list) (s : ssforest) = function
    | Atom a -> (Atom a, [])
    | And l ->
        let fs, vars =
          List.mapi ~f:(fun i f -> winning_formula (i :: position) s f) l
          |> List.unzip
        in
        (And fs, List.concat vars)
    | Or l ->
        let fs, vars =
          List.mapi ~f:(fun i f -> winning_formula (i :: position) s f) l
          |> List.unzip
        in
        (Or fs, List.concat vars)
    | Bind (Forall, v, f) ->
        let s' = remove_forall v s in
        let tvar, _ = v in
        let herbrand = herbrandize position tvar in
        let f, vars = winning_formula (0 :: position) s' f in
        (rename_var_formula tvar herbrand f, herbrand :: vars)
    | Bind (Exists, v, f) ->
        let tvar, _ = v in
        let fs, vars =
          remove_exists v s
          |> List.mapi ~f:(fun i (t, s) ->
                 let f, vars = winning_formula (i :: position) s f in
                 (subst_formula tvar t f, vars))
          |> List.unzip
        in
        (Or fs, List.concat vars)

  let rec css (position : int list) (f : A.atom formula) model model'
      (s : ssforest) =
    match f with
    | Atom _ -> ([], neg_formula A.neg_atom f)
    | And l ->
        let ss, gs =
          List.mapi ~f:(fun i f -> css (i :: position) f model model' s) l
          |> List.unzip
        in
        (List.concat ss, Or gs)
    | Or l ->
        let ss, gs =
          List.mapi ~f:(fun i f -> css (i :: position) f model model' s) l
          |> List.unzip
        in
        (List.concat ss, And gs)
    | Bind (Forall, v, f) ->
        let tvar, _ = v in
        let herbrand = herbrandize position tvar in
        let model' =
          Map.Poly.add_exn model' ~key:tvar
            ~data:
              (match Map.Poly.find model herbrand with
              | Some v -> v
              | None -> A.default_value)
        in
        let s' = remove_forall v s in
        let u, g = css (0 :: position) f model model' s' in
        let tvar, _ = v in
        let t = A.select model' tvar g in
        ([ ExistsSS (v, [ (t, u) ]) ], subst_formula tvar t g)
    | Bind (Exists, v, f) ->
        let tvar, _ = v in
        let us, gs =
          remove_exists v s
          |> List.mapi ~f:(fun i (t, s') ->
                 let model' =
                   Map.Poly.add_exn model' ~key:tvar
                     ~data:(A.eval_term model' t)
                 in
                 let u, g = css (i :: position) f model model' s' in
                 (u, subst_formula tvar t g))
          |> List.unzip
        in
        ([ ForallSS (v, merge_ssforest_nonempty_list us) ], And gs)

  let has_counter_strategy solve (s : ssforest) (f : A.atom formula) =
    let win, vars = winning_formula [] s f in
    let senv = List.map ~f:(fun v -> (v, IntTerm.SInt)) vars in
    match A.check_sat solve (neg_formula A.neg_atom win) senv with
    | None -> None
    | Some model ->
        let u, _ = css [] f model Map.Poly.empty s in
        Some u

  type player = SAT | UNSAT

  let rec remove_bind = function
    | Atom a -> (Atom a, [])
    | And l ->
        let fs, vars = List.map ~f:remove_bind l |> List.unzip in
        (And fs, List.concat vars)
    | Or l ->
        let fs, vars = List.map ~f:remove_bind l |> List.unzip in
        (Or fs, List.concat vars)
    | Bind (_, v, f) ->
        let f, vars = remove_bind f in
        (f, v :: vars)

  let initial_strategy solve f =
    let f', senv = remove_bind f in
    match A.check_sat solve f' senv with
    | None -> None
    | Some model ->
        let rec build_strategy = function
          | Atom a -> ([], Atom a)
          | And l ->
              let ss, gs = List.map ~f:build_strategy l |> List.unzip in
              (List.concat ss, And gs)
          | Or l ->
              let ss, gs = List.map ~f:build_strategy l |> List.unzip in
              (List.concat ss, Or gs)
          | Bind (b, v, f) ->
              let s, g = build_strategy f in
              let tvar, _ = v in
              let t = A.select model tvar g in
              let g = subst_formula tvar t g in
              ( [
                  (match b with
                  | Forall -> ForallSS (v, s)
                  | Exists -> ExistsSS (v, [ (t, s) ]));
                ],
                g )
        in
        let s, _ = build_strategy f in
        Some s

  let nondet_strategy_synthesis solve f =
    let nf = neg_formula A.neg_atom f in
    match initial_strategy solve f with
    | None -> (UNSAT, Option.value_exn (initial_strategy solve nf))
    | Some _ as s ->
        let u = None in
        let rec loop p s u f nf =
          match has_counter_strategy solve (Option.value_exn s) f with
          | Some _ as u' ->
              loop
                (match p with SAT -> UNSAT | UNSAT -> SAT)
                (merge_ssforest_option u u')
                s nf f
          | None -> (p, Option.value_exn s)
        in
        loop SAT s u f nf

  let rec loseCHC vars s = function
    | Atom a -> (BoolTerm.neg_of (A.term_of_atom a), [], Map.Poly.empty, [])
    | And l ->
        let fmls, chc, strategies, params =
          List.map ~f:(loseCHC vars s) l |> List.unzip4
        in
        ( BoolTerm.or_of fmls,
          List.concat chc,
          Map.force_merge_list strategies,
          List.concat params )
    | Or l ->
        let fmls, chc, strategies, params =
          List.map ~f:(loseCHC vars s) l |> List.unzip4
        in
        ( BoolTerm.and_of fmls,
          List.concat chc,
          Map.force_merge_list strategies,
          List.concat params )
    | Bind (Forall, v, f) ->
        let s' = remove_forall v s in
        let fml, chc, strategies, params = loseCHC (v :: vars) s' f in
        let pvar = Ident.mk_fresh_tvar () in
        let tvs, sorts = List.unzip vars in
        let sort = Sort.mk_fun (sorts @ [ BoolTerm.SBool ]) in
        let p = Term.mk_var pvar in
        let pfml = Term.mk_apps p (List.map ~f:Term.mk_var tvs) in
        let chc =
          ( Map.of_list_exn (v :: vars),
            Term.mk_apps (BoolTerm.mk_imply ()) [ fml; pfml ] )
          :: chc
        in
        (pfml, chc, strategies, (pvar, sort) :: params)
    | Bind (Exists, v, f) -> (
        let l = remove_exists v s in
        let tvar, _ = v in
        let l' =
          List.map l ~f:(fun (t, s') ->
              let fml, chc, strategy, params = loseCHC (v :: vars) s' f in
              ( Term.subst
                  (Map.Poly.singleton tvar (A.term_of_term t))
                  fml (* this should be equivalent to subst_formula *),
                chc,
                Map.Poly.add_exn ~key:tvar
                  ~data:(Map.of_list_exn vars, A.term_of_term t)
                  strategy,
                params ))
        in
        let pvar = Ident.mk_fresh_tvar () in
        let tvs, sorts = List.unzip vars in
        let sort = Sort.mk_fun (sorts @ [ BoolTerm.SBool ]) in
        let p = Term.mk_var pvar in
        let pfml = Term.mk_apps p (List.map ~f:Term.mk_var tvs) in
        let fmls, chcs, _, params = List.unzip4 l' in
        let chc =
          ( Map.of_list_exn (v :: vars),
            Term.mk_apps (BoolTerm.mk_imply ()) [ BoolTerm.and_of fmls; pfml ]
          )
          :: List.concat chcs
        in
        match l' with
        | [] -> assert false
        | (_, _, strategy, _) :: l' ->
            let newstrategy =
              List.fold l' ~init:strategy ~f:(fun s (fml, _, s', _) ->
                  Map.Poly.merge s s' ~f:(fun ~key:_ -> function
                    | `Both ((senv, t), (senv', t')) ->
                        assert (Map.Poly.equal Stdlib.( = ) senv senv');
                        Some
                          ( senv,
                            Term.mk_apps (BoolTerm.mk_ite A.sort) [ fml; t; t' ]
                          )
                    | _ -> assert false))
            in
            (pfml, chc, newstrategy, (pvar, sort) :: List.concat params))
end

module LIA = struct
  open PreFormula

  type domain = Z.t
  type atom = Gt0 of Affine.t | Div of Z.t * Affine.t
  type term = Affine.t * Z.t * Z.t
  type formula = atom PreFormula.formula

  let default_value = Z.zero
  let sort = IntTerm.SInt

  let term_equal (t, a, b) (t', a', b') =
    Affine.(t = t') && Z.Compare.(a = a') && Z.Compare.(b = b')

  let term_of_term (a, b, c) =
    let a' = Affine.term_of a in
    let b' = IntTerm.mk_int b in
    let c' = IntTerm.mk_int c in
    if Z.Compare.(b = Z.one) then Term.mk_apps (IntTerm.mk_add ()) [ a'; c' ]
    else
      Term.mk_apps (IntTerm.mk_add ())
        [ Term.mk_apps (IntTerm.mk_div Value.Euclidean) [ a'; b' ]; c' ]

  let atom_to_string = function
    | Gt0 a -> Affine.to_string a ^ " > 0"
    | Div (d, a) -> Z.to_string d ^ " | " ^ Affine.to_string a

  let term_to_string (t, a, b) =
    sprintf "[(%s) / %s] %s %s" (Affine.to_string t) (Z.to_string a)
      (if Z.(Compare.(b < zero)) then "-" else "+")
      (Z.abs b |> Z.to_string)

  let list_init_z n ~f =
    let rec loop n' =
      if Z.Compare.(n' < n) then f n' :: loop Z.(n' + one) else []
    in
    loop Z.zero

  let neg_atom = function
    | Gt0 a -> Atom (Gt0 Affine.(of_z Z.one - a))
    | Div (d, a) ->
        Or
          (list_init_z
             Z.(d - one)
             ~f:(fun n -> Atom (Div (d, Affine.(of_z Z.(n + one) + a)))))

  let find_var_affine tvar a =
    match Affine.get_coeff_of tvar a with
    | None -> None
    | Some c -> Some (c, Affine.remove tvar a)

  let subst_atom tvar (t, a, b) = function
    | Gt0 s -> (
        match find_var_affine tvar s with
        | None -> Atom (Gt0 s)
        | Some (c, rest) ->
            if Z.(Compare.(c = zero)) then Atom (Gt0 rest)
            else
              Or
                (list_init_z a ~f:(fun i ->
                     let div = Div (a, Affine.(t - of_z i)) in
                     let gt0 =
                       Gt0
                         Affine.(mul a rest + mul c (t + of_z Z.((a * b) - i)))
                     in
                     And [ Atom div; Atom gt0 ])))
    | Div (d, s) -> (
        match find_var_affine tvar s with
        | None -> Atom (Div (d, s))
        | Some (c, rest) ->
            Or
              (list_init_z a ~f:(fun i ->
                   let div = Div (a, Affine.(t - of_z i)) in
                   let div' =
                     Div
                       ( Z.(a * d),
                         Affine.(mul a rest + mul c (t + of_z Z.((a * b) - i)))
                       )
                   in
                   And [ Atom div; Atom div' ])))

  let eval_affine m a = Affine.eval ~default_value:(Some default_value) m a

  let eval_term m (a, b, c) =
    let a' = eval_affine m a in
    Z.((a' /< b) + c)

  let rename_var_affine t s a =
    match Affine.get_coeff_of t a with
    | None -> a
    | Some c ->
        Affine.remove t a |> Affine.( + ) (Affine.make [ (s, c) ] Z.zero)

  let rename_var_atom t s = function
    | Gt0 a -> Gt0 (rename_var_affine t s a)
    | Div (d, a) -> Div (d, rename_var_affine t s a)

  (* TODO: support divisibility *)
  let rec formula_of_term = function
    | Bin (b, var, sort, term, _)
      when match b with Forall | Exists -> true | _ -> false -> (
        Option.(
          formula_of_term term >>= fun f ->
          match b with
          | Forall -> return (Bind (Forall, (var, sort), f))
          | Exists -> return (Bind (Exists, (var, sort), f))
          | _ -> assert false))
    | App (Con (BoolTerm.Not, _), t, _) ->
        Option.(formula_of_term t >>= fun f -> return (neg_formula neg_atom f))
    | App (App (Con ((BoolTerm.(And | Or | Imply) as r), _), t1, _), t2, _) -> (
        Option.(
          formula_of_term t1 >>= fun f1 ->
          formula_of_term t2 >>= fun f2 ->
          match r with
          | BoolTerm.And -> return (And [ f1; f2 ])
          | BoolTerm.Or -> return (Or [ f1; f2 ])
          | BoolTerm.Imply -> return (Or [ neg_formula neg_atom f1; f2 ])
          | _ -> assert false))
    | App (App (Con ((ExtTerm.(Gt | Lt | Geq | Leq) as r), _), t1, _), t2, _)
      -> (
        Option.(
          Affine.of_term t1 >>= fun a1 ->
          Affine.of_term t2 >>= fun a2 ->
          match r with
          | ExtTerm.Gt -> return (Atom (Gt0 Affine.(a1 - a2)))
          | ExtTerm.Lt -> return (Atom (Gt0 Affine.(a2 - a1)))
          | ExtTerm.Geq -> return (Atom (Gt0 Affine.(a1 - a2 + of_z Z.one)))
          | ExtTerm.Leq -> return (Atom (Gt0 Affine.(a2 - a1 + of_z Z.one)))
          | _ -> assert false))
    | App
        ( App
            (TyApp (Con ((ExtTerm.(Eq | Neq) as r), _), IntTerm.SInt, _), t1, _),
          t2,
          _ ) -> (
        Option.(
          Affine.of_term t1 >>= fun a1 ->
          Affine.of_term t2 >>= fun a2 ->
          match r with
          | ExtTerm.Eq ->
              let ge = Atom (Gt0 Affine.(a1 - a2 + of_z Z.one)) in
              let le = Atom (Gt0 Affine.(a2 - a1 + of_z Z.one)) in
              return (And [ ge; le ])
          | ExtTerm.Neq ->
              let gt = Atom (Gt0 Affine.(a1 - a2)) in
              let lt = Atom (Gt0 Affine.(a2 - a1)) in
              return (Or [ gt; lt ])
          | _ -> assert false))
    | App
        ( App
            ( TyApp (Con ((ExtTerm.(Eq | Neq) as r), _), BoolTerm.SBool, _),
              t1,
              _ ),
          t2,
          _ ) -> (
        Option.(
          formula_of_term t1 >>= fun a1 ->
          formula_of_term t2 >>= fun a2 ->
          match r with
          | ExtTerm.Eq ->
              let tt = And [ a1; a2 ] in
              let ff =
                And [ neg_formula neg_atom a1; neg_formula neg_atom a2 ]
              in
              return (Or [ tt; ff ])
          | ExtTerm.Neq ->
              let tf = And [ a1; neg_formula neg_atom a2 ] in
              let ft = And [ neg_formula neg_atom a1; a2 ] in
              return (Or [ tf; ft ])
          | _ -> assert false))
    | App (App (Con (ExtTerm.PDiv, _), Con (IntTerm.Int n, _), _), t, _) ->
        Option.(Affine.of_term t >>= fun a -> return (Atom (Div (n, a))))
    | _ -> None

  let term_of_atom = function
    | Gt0 a ->
        Term.mk_apps (ExtTerm.mk_gt ()) [ Affine.term_of a; IntTerm.zero () ]
    | Div (d, a) ->
        if Z.(Compare.(d = one)) then BoolTerm.mk_bool true
        else
          Term.mk_apps
            (BoolTerm.mk_eq IntTerm.SInt)
            [
              Term.mk_apps
                (IntTerm.mk_rem Value.Euclidean)
                [ Affine.term_of a; IntTerm.mk_int d ];
              IntTerm.zero ();
            ]

  let ub model tvar f =
    List.filter_map (atoms f) ~f:(function
      | Gt0 a ->
          if Z.Compare.(eval_affine model a > Z.zero) then
            match find_var_affine tvar a with
            | None -> None
            | Some (c, s) ->
                if Z.Compare.(c < Z.zero) then Some (c, s) else None
          else None
      | _ -> None)

  let lb model tvar f =
    List.filter_map (atoms f) ~f:(function
      | Gt0 a ->
          if Z.Compare.(eval_affine model a > Z.zero) then
            match find_var_affine tvar a with
            | None -> None
            | Some (c, s) ->
                if Z.Compare.(c > Z.zero) then Some (c, s) else None
          else None
      | _ -> None)

  let div model tvar f =
    List.filter_map (atoms f) ~f:(function
      | Div (d, a) ->
          if Z.(Compare.(erem (eval_affine model a) d = zero)) then
            match find_var_affine tvar a with
            | None -> None
            | Some (c, s) ->
                if Z.Compare.(c <> Z.zero) then Some (d, (c, s)) else None
          else None
      | _ -> None)

  let lcm_of_list l = List.fold ~init:Z.one ~f:Z.lcm l

  let delta model tvar f =
    div model tvar f
    |> List.map ~f:(fun (d, (c, _)) -> Z.(d /| Z.gcd (abs c) d))
    |> lcm_of_list

  let lub model tvar f =
    let delta = delta model tvar f in
    List.map (ub model tvar f) ~f:(fun (a, t) ->
        let a = Z.(~-a) in
        let ev_tvar =
          match Map.Poly.find model tvar with
          | Some v -> v
          | None -> default_value
        in
        let t_minus_one = Affine.(t - of_z Z.one) in
        let b =
          Z.(erem ((eval_affine model t_minus_one /< a) - ev_tvar) delta)
        in
        assert (Z.(Compare.( >= ) b zero));
        let term = (t_minus_one, a, Z.(~-b)) in
        term)
    |> List.min_elt ~compare:(fun t1 t2 ->
           Z.compare (eval_term model t1) (eval_term model t2))

  let glb model tvar f =
    let delta = delta model tvar f in
    List.map (lb model tvar f) ~f:(fun (a, t) ->
        let t = Affine.(~-t) in
        let ev_tvar =
          match Map.Poly.find model tvar with
          | Some v -> v
          | None -> default_value
        in
        let b = Z.(erem (ev_tvar - (eval_affine model t /< a) - one) delta) in
        assert (Z.(Compare.( >= ) b zero));
        let term = (t, a, Z.(b + one)) in
        term)
    |> List.max_elt ~compare:(fun t1 t2 ->
           Z.compare (eval_term model t1) (eval_term model t2))

  let select model tvar f =
    match lub model tvar f with
    | Some t -> t
    | None -> (
        match glb model tvar f with
        | Some t -> t
        | None ->
            let ev_tvar =
              match Map.Poly.find model tvar with
              | Some v -> v
              | None -> default_value
            in
            let delta = delta model tvar f in
            (Affine.of_z Z.zero, Z.one, Z.(erem ev_tvar delta)))

  (* [select_bounds M x F], beside [select] and not used by it: when [F]
     bounds [x] at [M] from both sides, the two extreme terms [lub] and [glb]
     as a pair (the one nearer [M(x)] first, the upper one on a tie), else
     [None].  Each satisfies [select]'s contract -- free of [x], and
     [M |= F[x := t]] -- because both are the model's value moved to the
     extreme of its congruence class modulo the divisibility atoms' period
     inside every bound that holds at [M]: the atoms true at [M] stay true,
     and [F] has negation only inside atoms, so an atom that becomes true
     cannot falsify it.  A caller that wants a move at the edge of the
     admissible interval rather than [select]'s preference uses it. *)
  let select_bounds model tvar f =
    match (lub model tvar f, glb model tvar f) with
    | Some u, Some l ->
        let v =
          match Map.Poly.find model tvar with
          | Some v -> v
          | None -> default_value
        in
        if Z.Compare.(Z.(eval_term model u - v) <= Z.(v - eval_term model l))
        then Some (u, l)
        else Some (l, u)
    | _ -> None

  let check_sat solve f senv =
    match solve senv (term_of_formula (fun x -> term_of_atom x) f) with
    | None -> None
    | Some model ->
        let let_int t =
          match Term.let_con t with ExtTerm.Int n, _ -> n | _ -> assert false
        in
        let remove_dontcare (tvar, v) =
          match v with
          | None -> (tvar, Z.zero)
          | Some term -> (tvar, let_int term)
        in
        let model =
          List.map ~f:remove_dontcare model |> Map.Poly.of_alist_exn
        in
        Some model
end

module LIAStrategySynthesis = struct
  include StrategySynthesis (LIA)
  open PreFormula

  let player_to_string = function SAT -> "SAT" | UNSAT -> "UNSAT"

  let rec formula_to_string = function
    | Atom a -> LIA.atom_to_string a
    | And l ->
        String.concat_map_list ~sep:" /\\ "
          ~f:(formula_to_string >> String.paren)
          l
    | Or l ->
        String.concat_map_list ~sep:" \\/ "
          ~f:(formula_to_string >> String.paren)
          l
    | Bind (b, (tvar, _), f) ->
        (match b with Forall -> "forall" | Exists -> "exists")
        ^ " " ^ Ident.name_of_tvar tvar ^ ". " ^ formula_to_string f

  (* let rec sstree_to_formatter ppf = function
     | ForallSS ((tvar, _), f) ->
         Format.open_vbox 1;
         Format.fprintf ppf "forall %s@," (Ident.name_of_tvar tvar);
         ssforest_to_formatter ppf f;
         Format.close_box ()
     | ExistsSS ((tvar, _), l) ->
         Format.open_vbox 1;
         Format.fprintf ppf "exists %s@," (Ident.name_of_tvar tvar);
         List.iter l ~f:(fun (t, f) ->
           Format.open_vbox 1;
           Format.fprintf ppf "%s@," (LIA.term_to_string t);
           ssforest_to_formatter ppf f;
           Format.close_box ());
         Format.close_box ()
       and ssforest_to_formatter ppf f =
         Format.open_vbox 0;
         List.iter f ~f:(sstree_to_formatter ppf);
         Format.close_box ()
     let ssforest_to_string f =
     let buf = Buffer.create 0 in
     let ppf = Format.formatter_of_buffer buf in
     ssforest_to_formatter ppf f;
     Format.pp_print_flush ppf ();
     Buffer.contents buf*)
  let rec sstree_to_string ?(indent = 0) = function
    | ForallSS ((tvar, _), f) ->
        sprintf "%sforall %s\n%s" (String.make indent ' ')
          (Ident.name_of_tvar tvar)
          (ssforest_to_string ~indent:(indent + 1) f)
    | ExistsSS ((tvar, _), l) ->
        sprintf "%sexists %s\n%s" (String.make indent ' ')
          (Ident.name_of_tvar tvar)
          (List.map l ~f:(fun (t, f) ->
               sprintf "%s%s\n%s"
                 (String.make (indent + 1) ' ')
                 (LIA.term_to_string t)
                 (ssforest_to_string ~indent:(indent + 2) f))
          |> String.concat)

  and ssforest_to_string ?(indent = 0) f =
    List.map f ~f:(sstree_to_string ~indent) |> String.concat
end

module RTerm = struct
  type t = (Ident.tvar option, Q.t) Map.Poly.t

  let of_q r = Map.Poly.singleton None r
  let of_var v = Map.Poly.of_alist_exn [ (None, Q.zero); (Some v, Q.one) ]

  let ( + ) a b =
    Map.Poly.merge a b ~f:(fun ~key:_ -> function
      | `Left c | `Right c -> Some c
      | `Both (c1, c2) -> Some Q.(c1 + c2))

  let ( ~- ) a = Map.Poly.map a ~f:Q.neg
  let ( - ) a b = a + ~-b
  let mul r a = Map.Poly.map a ~f:(fun data -> Q.(r * data))
  let div a r = Map.Poly.map a ~f:(fun data -> Q.(data / r))

  let to_string a =
    Map.Poly.to_alist a
    |> String.concat_map_list ~sep:" + " ~f:(fun (key, data) ->
           match key with
           | None -> Q.to_string data
           | Some tvar -> Q.to_string data ^ "*" ^ Ident.name_of_tvar tvar)

  let ( = ) : t -> t -> bool = Map.Poly.equal Q.( = )

  let term_of a =
    Map.Poly.to_alist a
    |> List.map ~f:(fun (key, data) ->
           match key with
           | None -> RealTerm.mk_real data
           | Some tvar ->
               Term.mk_apps (RealTerm.mk_rmul ())
                 [ RealTerm.mk_real data; Term.mk_var tvar ])
    |> RealTerm.sum

  let rec of_term = function
    | Con (RealTerm.Real r, _) -> Some (of_q r)
    | Con (IntTerm.Int n, _) -> Some (of_q @@ Q.of_bigint n)
    | Var (var, _) -> Some (of_var var)
    | App (App (Con (RealTerm.RAdd, _), t1, _), t2, _)
    | App (App (Con (IntTerm.Add, _), t1, _), t2, _) ->
        Option.(
          of_term t1 >>= fun a1 ->
          of_term t2 >>= fun a2 -> return (a1 + a2))
    | App (App (Con (RealTerm.RSub, _), t1, _), t2, _)
    | App (App (Con (IntTerm.Sub, _), t1, _), t2, _) ->
        Option.(
          of_term t1 >>= fun a1 ->
          of_term t2 >>= fun a2 -> return (a1 - a2))
    | App (App (Con (RealTerm.RMul, _), Con (RealTerm.Real r, _), _), t, _)
    | App (App (Con (RealTerm.RMul, _), t, _), Con (RealTerm.Real r, _), _) ->
        Option.(of_term t >>= fun a -> return (mul r a))
    | App (App (Con (RealTerm.RDiv, _), t, _), Con (RealTerm.Real r, _), _) ->
        Option.(of_term t >>= fun a -> return (div a r))
    | App (Con (RealTerm.RNeg, _), t, _) | App (Con (IntTerm.Neg, _), t, _) ->
        Option.(of_term t >>= fun a -> return ~-a)
    | _ -> None
end

module LRA = struct
  open PreFormula

  type domain = Q.t
  type atom = Eq0 of RTerm.t | Gt0 of RTerm.t
  type term = RTerm.t
  type formula = atom PreFormula.formula

  let default_value = Q.zero
  let sort = RealTerm.SReal
  let term_equal t t' = RTerm.( = ) t t'
  let term_of_term t = RTerm.term_of t

  let atom_to_string = function
    | Eq0 t -> RTerm.to_string t ^ " = 0"
    | Gt0 t -> RTerm.to_string t ^ " > 0"

  let term_to_string t = RTerm.to_string t

  let neg_atom = function
    | Eq0 t -> Or [ Atom (Gt0 t); Atom (Gt0 RTerm.(-t)) ]
    | Gt0 t -> Or [ Atom (Eq0 t); Atom (Gt0 RTerm.(-t)) ]

  let find_var_term tvar a =
    match Map.Poly.find a (Some tvar) with
    | None -> None
    | Some c -> Some (c, Map.Poly.remove a (Some tvar))

  let subst_atom tvar t = function
    | Eq0 s -> (
        match find_var_term tvar s with
        | None -> Atom (Eq0 s)
        | Some (c, rest) ->
            if Q.(c = zero) then Atom (Eq0 rest)
            else Atom (Eq0 RTerm.(rest + RTerm.mul c t)))
    | Gt0 s -> (
        match find_var_term tvar s with
        | None -> Atom (Gt0 s)
        | Some (c, rest) ->
            if Q.(c = zero) then Atom (Gt0 rest)
            else Atom (Gt0 RTerm.(rest + RTerm.mul c t)))

  let eval_term m t =
    Map.Poly.fold t ~init:Q.zero ~f:(fun ~key ~data sum ->
        match key with
        | None -> Q.(sum + data)
        | Some tvar ->
            let v =
              match Map.Poly.find m tvar with
              | Some v -> v
              | None -> default_value
            in
            Q.(sum + (data * v)))

  let rename_var_term v v' t =
    match Map.Poly.find t (Some v) with
    | None -> t
    | Some c ->
        Map.Poly.remove t (Some v) |> Map.Poly.add_exn ~key:(Some v') ~data:c

  let rename_var_atom v v' = function
    | Eq0 t -> Eq0 (rename_var_term v v' t)
    | Gt0 t -> Gt0 (rename_var_term v v' t)

  let rec formula_of_term = function
    | Bin (((Forall | Exists) as b), var, sort, term, _) -> (
        Option.(
          formula_of_term term >>= fun f ->
          match b with
          | Forall -> return (Bind (Forall, (var, sort), f))
          | Exists -> return (Bind (Exists, (var, sort), f))
          | _ -> assert false))
    | App (Con (BoolTerm.Not, _), t, _) ->
        Option.(formula_of_term t >>= fun f -> return (neg_formula neg_atom f))
    | App (App (Con ((BoolTerm.(And | Or | Imply) as r), _), t1, _), t2, _) -> (
        Option.(
          formula_of_term t1 >>= fun f1 ->
          formula_of_term t2 >>= fun f2 ->
          match r with
          | BoolTerm.And -> return (And [ f1; f2 ])
          | BoolTerm.Or -> return (Or [ f1; f2 ])
          | BoolTerm.Imply -> return (Or [ neg_formula neg_atom f1; f2 ])
          | _ -> assert false))
    | App
        ( App
            ( Con
                ( (ExtTerm.(
                     ( Gt | Lt | Geq | Leq (*TODO: remove*)
                     | RGt | RLt | RGeq | RLeq )) as r),
                  _ ),
              t1,
              _ ),
          t2,
          _ ) -> (
        Option.(
          RTerm.of_term t1 >>= fun a1 ->
          RTerm.of_term t2 >>= fun a2 ->
          match r with
          | ExtTerm.(Gt | RGt) -> return (Atom (Gt0 RTerm.(a1 - a2)))
          | ExtTerm.(Lt | RLt) -> return (Atom (Gt0 RTerm.(a2 - a1)))
          | ExtTerm.(Geq | RGeq) ->
              return
                (Or [ Atom (Eq0 RTerm.(a1 - a2)); Atom (Gt0 RTerm.(a1 - a2)) ])
          | ExtTerm.(Leq | RLeq) ->
              return
                (Or [ Atom (Eq0 RTerm.(a2 - a1)); Atom (Gt0 RTerm.(a2 - a1)) ])
          | _ -> assert false))
    | App
        ( App
            ( TyApp (Con ((ExtTerm.(Eq | Neq) as r), _), RealTerm.SReal, _),
              t1,
              _ ),
          t2,
          _ ) -> (
        Option.(
          RTerm.of_term t1 >>= fun a1 ->
          RTerm.of_term t2 >>= fun a2 ->
          match r with
          | ExtTerm.Eq -> return (Atom (Eq0 RTerm.(a1 - a2)))
          | ExtTerm.Neq ->
              return
                (Or [ Atom (Gt0 RTerm.(a1 - a2)); Atom (Gt0 RTerm.(a2 - a1)) ])
          | _ -> assert false))
    | App
        ( App
            ( TyApp (Con ((ExtTerm.(Eq | Neq) as r), _), BoolTerm.SBool, _),
              t1,
              _ ),
          t2,
          _ ) -> (
        Option.(
          formula_of_term t1 >>= fun a1 ->
          formula_of_term t2 >>= fun a2 ->
          match r with
          | ExtTerm.Eq ->
              let tt = And [ a1; a2 ] in
              let ff =
                And [ neg_formula neg_atom a1; neg_formula neg_atom a2 ]
              in
              return (Or [ tt; ff ])
          | ExtTerm.Neq ->
              let tf = And [ a1; neg_formula neg_atom a2 ] in
              let ft = And [ neg_formula neg_atom a1; a2 ] in
              return (Or [ tf; ft ])
          | _ -> assert false))
    | t ->
        if false then print_endline @@ Logic.ExtTerm.str_of t;
        None

  let term_of_atom = function
    | Eq0 t ->
        Term.mk_apps
          (ExtTerm.mk_eq RealTerm.SReal)
          [ RTerm.term_of t; RealTerm.rzero () ]
    | Gt0 t ->
        Term.mk_apps (ExtTerm.mk_gt ()) [ RTerm.term_of t; RealTerm.rzero () ]

  let eq_atom model tvar = function
    | Eq0 t -> (
        match find_var_term tvar t with
        | None -> None
        | Some (c, rest) ->
            if Q.(c = zero) then None
            else
              let s = RTerm.div rest Q.(-c) in
              if Q.(Map.Poly.find_exn model tvar = eval_term model s) then
                Some s
              else None)
    | Gt0 _ -> None

  let rec eq model tvar = function
    | Atom a -> eq_atom model tvar a
    | And l -> List.find_map l ~f:(eq model tvar)
    | Or l -> List.find_map l ~f:(eq model tvar)
    | Bind (_, _, f) -> eq model tvar f

  let ub_atom model tvar = function
    | Eq0 _ -> Set.Poly.empty
    | Gt0 t -> (
        match find_var_term tvar t with
        | None -> Set.Poly.empty
        | Some (c, rest) ->
            if Q.(c >= zero) then Set.Poly.empty
            else
              let s = RTerm.div rest Q.(-c) in
              if Q.(Map.Poly.find_exn model tvar < eval_term model s) then
                Set.Poly.singleton s
              else Set.Poly.empty)

  let lb_atom model tvar = function
    | Eq0 _ -> Set.Poly.empty
    | Gt0 t -> (
        match find_var_term tvar t with
        | None -> Set.Poly.empty
        | Some (c, rest) ->
            if Q.(c <= zero) then Set.Poly.empty
            else
              let s = RTerm.div rest Q.(-c) in
              if Q.(Map.Poly.find_exn model tvar > eval_term model s) then
                Set.Poly.singleton s
              else Set.Poly.empty)

  let rec ub_and_lb model tvar = function
    | Atom a -> (ub_atom model tvar a, lb_atom model tvar a)
    | And l | Or l ->
        List.fold l ~init:(Set.Poly.empty, Set.Poly.empty) ~f:(fun (ub, lb) a ->
            let newub, newlb = ub_and_lb model tvar a in
            (Set.union ub newub, Set.union lb newlb))
    | Bind (_, _, f) -> ub_and_lb model tvar f

  let lub model ub =
    let m_lub =
      Set.fold ub ~init:Q.inf ~f:(fun lub t -> Q.min lub (eval_term model t))
    in
    Set.find ub ~f:(fun t -> Q.(m_lub = eval_term model t))

  let glb model lb =
    let m_glb =
      Set.fold lb ~init:Q.minus_inf ~f:(fun glb t ->
          Q.max glb (eval_term model t))
    in
    Set.find lb ~f:(fun t -> Q.(m_glb = eval_term model t))

  let select model tvar f =
    match eq model tvar f with
    | Some t -> t
    | None -> (
        let ub, lb = ub_and_lb model tvar f in
        match (lub model ub, glb model lb) with
        | Some lub, Some glb -> RTerm.div RTerm.(lub + glb) (Q.of_float 2.0)
        | Some lub, None -> RTerm.(lub - RTerm.of_q Q.one)
        | None, Some glb -> RTerm.(glb + RTerm.of_q Q.one)
        | None, None -> RTerm.of_q default_value)

  (* [M |= F] for a ground formula; [false] on a binder, which the callers
     below never pass *)
  let rec holds model = function
    | Atom (Eq0 t) -> Q.(eval_term model t = zero)
    | Atom (Gt0 t) -> Q.(eval_term model t > zero)
    | And l -> List.for_all l ~f:(holds model)
    | Or l -> List.exists l ~f:(holds model)
    | Bind _ -> false

  (* [select_bounds M x F], beside [select] and not used by it: when no
     equality fixes [x] at [M] and [F] bounds it from both sides there, a pair
     of terms at the two ends of the admissible interval, the end nearer
     [M(x)] first (the upper one on a tie), else [None].  The bounds [ub_and_lb]
     collects come from strict atoms [t > 0], so the bound itself need not be
     admissible: an end is the bound [b] when [M |= F[x := b]] (as when the
     input said [x <= b], which reaches here as [b - x = 0 \/ b - x > 0]),
     and otherwise the point [(7 b + b') / 8] a little inside it, [b'] the
     other bound.  That point lies strictly between the tightest lower and
     upper bounds at [M], so every atom true at [M] that mentions [x] stays
     true (an equality true at [M] would have been [eq]'s case), and an atom
     that becomes true cannot falsify [F], whose negations are inside atoms.
     Both ends therefore satisfy [select]'s contract. *)
  let select_bounds model tvar f =
    match eq model tvar f with
    | Some _ -> None
    | None -> (
        let ub, lb = ub_and_lb model tvar f in
        match (lub model ub, glb model lb) with
        | Some u, Some l ->
            let at t =
              Map.Poly.set model ~key:tvar ~data:(eval_term model t)
            in
            let end_at b other =
              if holds (at b) f then b
              else RTerm.div RTerm.(RTerm.mul (Q.of_int 7) b + other) (Q.of_int 8)
            in
            let u' = end_at u l and l' = end_at l u in
            let v = Map.Poly.find_exn model tvar in
            let mid = Q.((eval_term model u + eval_term model l) / of_int 2) in
            if Q.(v >= mid) then Some (u', l') else Some (l', u')
        | _ -> None)

  let check_sat solve f senv =
    match solve senv (term_of_formula (fun x -> term_of_atom x) f) with
    | None -> None
    | Some model ->
        let let_real t =
          match Term.let_con t with
          | ExtTerm.Real r, _ -> r
          | ExtTerm.Int n, _ -> Q.of_bigint n
          | _ -> assert false
        in
        let remove_dontcare (tvar, v) =
          match v with
          | None -> (tvar, Q.zero)
          | Some term -> (tvar, let_real term)
        in
        let model =
          List.map ~f:remove_dontcare model |> Map.Poly.of_alist_exn
        in
        Some model
end

module LRAStrategySynthesis = struct
  include StrategySynthesis (LRA)
  open PreFormula

  let player_to_string = function SAT -> "SAT" | UNSAT -> "UNSAT"

  let rec formula_to_string = function
    | Atom a -> LRA.atom_to_string a
    | And l ->
        String.concat_map_list ~sep:" /\\ "
          ~f:(formula_to_string >> String.paren)
          l
    | Or l ->
        String.concat_map_list ~sep:" \\/ "
          ~f:(formula_to_string >> String.paren)
          l
    | Bind (b, (tvar, _), f) ->
        (match b with Forall -> "forall" | Exists -> "exists")
        ^ " " ^ Ident.name_of_tvar tvar ^ ". " ^ formula_to_string f

  let rec sstree_to_string ?(indent = 0) = function
    | ForallSS ((tvar, _), f) ->
        sprintf "%sforall %s\n%s" (String.make indent ' ')
          (Ident.name_of_tvar tvar)
          (ssforest_to_string ~indent:(indent + 1) f)
    | ExistsSS ((tvar, _), l) ->
        sprintf "%sexists %s\n%s" (String.make indent ' ')
          (Ident.name_of_tvar tvar)
          (List.map l ~f:(fun (t, f) ->
               sprintf "%s%s\n%s"
                 (String.make (indent + 1) ' ')
                 (LRA.term_to_string t)
                 (ssforest_to_string ~indent:(indent + 2) f))
          |> String.concat)

  and ssforest_to_string ?(indent = 0) f =
    List.map f ~f:(sstree_to_string ~indent) |> String.concat
end

module QBF = struct
  open PreFormula

  type domain = bool
  type atom = True | False | Var of Ident.tvar | NVar of Ident.tvar
  type term = atom
  type formula = atom PreFormula.formula

  let default_value = true
  let sort = BoolTerm.SBool
  let term_equal t t' = Stdlib.(t = t')

  let atom_to_string = function
    | True -> "True"
    | False -> "False"
    | Var v -> Ident.name_of_tvar v
    | NVar v -> "Not " ^ Ident.name_of_tvar v

  let term_to_string = atom_to_string

  let neg_term = function
    | True -> False
    | False -> True
    | Var v -> NVar v
    | NVar v -> Var v

  let neg_atom atom = Atom (neg_term atom)

  let subst_atom tvar t = function
    | Var v when Stdlib.(v = tvar) -> Atom t
    | NVar v when Stdlib.(v = tvar) -> Atom (neg_term t)
    | atom -> Atom atom

  let eval_term m = function
    | True -> true
    | False -> false
    | Var v -> (
        match Map.Poly.find m v with Some b -> b | None -> default_value)
    | NVar v -> (
        match Map.Poly.find m v with
        | Some b -> not b
        | None -> not default_value)

  let rename_var_atom v v' = function
    | Var tvar when Stdlib.(tvar = v) -> Var v'
    | NVar tvar when Stdlib.(tvar = v) -> NVar v'
    | atom -> atom

  let rec formula_of_term = function
    | Bin (b, var, sort, term, _)
      when match b with Forall | Exists -> true | _ -> false -> (
        Option.(
          formula_of_term term >>= fun f ->
          match b with
          | Forall -> return (Bind (Forall, (var, sort), f))
          | Exists -> return (Bind (Exists, (var, sort), f))
          | _ -> assert false))
    | App (Con (BoolTerm.Not, _), t, _) ->
        Option.(formula_of_term t >>= fun f -> return (neg_formula neg_atom f))
    | App (App (Con (r, _), t1, _), t2, _)
      when match r with
           | BoolTerm.And | BoolTerm.Or | BoolTerm.Imply -> true
           | _ -> false -> (
        Option.(
          formula_of_term t1 >>= fun f1 ->
          formula_of_term t2 >>= fun f2 ->
          match r with
          | BoolTerm.And -> return (And [ f1; f2 ])
          | BoolTerm.Or -> return (Or [ f1; f2 ])
          | BoolTerm.Imply -> return (Or [ neg_formula neg_atom f1; f2 ])
          | _ -> assert false))
    | Con (BoolTerm.True, _) -> Some (Atom True)
    | Con (BoolTerm.False, _) -> Some (Atom False)
    | Var (var, _) -> Some (Atom (Var var))
    | _ -> None

  let term_of_atom = function
    | True -> BoolTerm.mk_bool true
    | False -> BoolTerm.mk_bool false
    | Var v -> Term.mk_var v
    | NVar v -> Term.mk_app (BoolTerm.mk_not ()) (Term.mk_var v)

  let term_of_term = term_of_atom
  let select _model _tvar _f = assert false (*ToDo*)

  let check_sat solve f senv =
    match solve senv (term_of_formula (fun x -> term_of_atom x) f) with
    | None -> None
    | Some model ->
        let let_bool t =
          match Term.let_con t with
          | ExtTerm.True, _ -> true
          | ExtTerm.False, _ -> false
          | _ -> assert false
        in
        let remove_dontcare (tvar, v) =
          match v with
          | None -> (tvar, true)
          | Some term -> (tvar, let_bool term)
        in
        let model =
          List.map ~f:remove_dontcare model |> Map.Poly.of_alist_exn
        in
        Some model
end

module QBFStrategySynthesis = struct
  include StrategySynthesis (QBF)
  open PreFormula

  let player_to_string = function SAT -> "SAT" | UNSAT -> "UNSAT"

  let rec formula_to_string = function
    | Atom a -> LRA.atom_to_string a
    | And l ->
        String.concat_map_list ~sep:" /\\ "
          ~f:(formula_to_string >> String.paren)
          l
    | Or l ->
        String.concat_map_list ~sep:" \\/ "
          ~f:(formula_to_string >> String.paren)
          l
    | Bind (b, (tvar, _), f) ->
        (match b with Forall -> "forall" | Exists -> "exists")
        ^ " " ^ Ident.name_of_tvar tvar ^ ". " ^ formula_to_string f

  let rec sstree_to_string ?(indent = 0) = function
    | ForallSS ((tvar, _), f) ->
        sprintf "%sforall %s\n%s" (String.make indent ' ')
          (Ident.name_of_tvar tvar)
          (ssforest_to_string ~indent:(indent + 1) f)
    | ExistsSS ((tvar, _), l) ->
        sprintf "%sexists %s\n%s" (String.make indent ' ')
          (Ident.name_of_tvar tvar)
          (List.map l ~f:(fun (t, f) ->
               sprintf "%s%s\n%s"
                 (String.make (indent + 1) ' ')
                 (QBF.term_to_string t)
                 (ssforest_to_string ~indent:(indent + 2) f))
          |> String.concat)

  and ssforest_to_string ?(indent = 0) f =
    List.map f ~f:(sstree_to_string ~indent) |> String.concat
end

(* Model-guided term selection reached from the first-order representation.

   The procedure above is written over [Logic]'s terms, while the
   quantified-satisfiability loop that wants witness terms is written over
   [LogicOld]'s.  [select_terms] converts across: the conjunction of [atoms]
   becomes this file's formula once, a term is chosen for each variable in
   turn, and only the terms are converted back.

   The variables are eliminated in sequence and each is chosen against the
   formula with the earlier choices already substituted, because [select]
   guarantees only that the model satisfies the formula with its own variable
   replaced: two terms chosen independently against one formula need not
   satisfy it together.  The substitution is [subst_atom]'s, which case-splits
   on the residue of the virtual term's divisor and scales, so the formula
   stays inside the linear-plus-divisibility fragment -- converting the term
   back and substituting over the first-order terms instead leaves a division
   the reader below cannot take.  A term chosen earlier may mention a variable
   eliminated later, so the terms are composed as they are collected.

   [None] where the variables are not all of one sort this file implements --
   the integer and the real fragment are different representations and a
   formula cannot be in both -- where the conjunction is outside the fragment
   the reader accepts, or where any of it raises.  A caller that gets [None]
   does whatever it would have done with no terms at all.

   One shape is declined often enough to be worth naming: the reader has no
   case for integer division, and resolving a variable's bounds against each
   other -- the other way to eliminate a variable, which a caller normally
   falls back to -- puts a quotient into the atoms it leaves behind.  Those
   atoms reach a later conjunction through the lemmas they enter, so a caller
   that mixes the two ways sees this decline a quarter of the time (measured at
   161 against 52 over six two-coin Frobenius problems), and the problems where
   it declines most are the ones where the terms help least.  Reading a
   quotient would mean giving it a variable of its own with the two bounds that
   define it, which is a change to the shared reader rather than to this
   module.

   The contract is the one [select] states: a variable does not occur in its
   own term, and the model satisfies the conjunction once the terms are put
   in.  Nothing here re-checks that.

   The model is read only for the variables it gives a value of the right sort
   to.  A variable of another sort cannot occur in an atom this reader accepts,
   so dropping those loses nothing; a variable of the right sort that the model
   does not mention is one [select] gives its own default value. *)
module Old = struct
  (* The strategy synthesis functor has this recursion too, on a path another
     solver uses; this is a separate copy rather than a shared one so that the
     entry points here cannot change what that path does. *)
  let rec subst_in ~subst_atom tvar t = function
    | PreFormula.Atom a -> subst_atom tvar t a
    | PreFormula.And l ->
        PreFormula.And (List.map l ~f:(subst_in ~subst_atom tvar t))
    | PreFormula.Or l ->
        PreFormula.Or (List.map l ~f:(subst_in ~subst_atom tvar t))
    | PreFormula.Bind (b, u, f) ->
        PreFormula.Bind (b, u, subst_in ~subst_atom tvar t f)

  let senv_of_atoms atoms =
    Set.fold atoms ~init:Map.Poly.empty ~f:(fun senv atm ->
        Set.fold (LogicOld.Atom.term_sort_env_of atm) ~init:senv
          ~f:(fun senv (x, s) ->
            Map.Poly.set senv ~key:x ~data:(ExtTerm.of_old_sort s)))

  let term_of_atoms atoms =
    ExtTerm.of_old_formula @@ LogicOld.Formula.and_of
    @@ List.map ~f:LogicOld.Formula.mk_atom
    @@ Set.to_list atoms

  let model_of ~f model =
    Map.Poly.filter_map model ~f:(fun t ->
        match Evaluator.eval_term t with v -> f v | exception _ -> None)

  (* one theory's sequence of choices, given that theory's reader, selection,
     substitution and term conversion *)
  let run ~formula_of_term ~select ~subst_atom ~term_of_term ~model xs atoms =
    let senv = senv_of_atoms atoms in
    Option.map (formula_of_term (term_of_atoms atoms)) ~f:(fun f ->
        fst
        @@ List.fold xs ~init:(Map.Poly.empty, f) ~f:(fun (sub, f) x ->
               let t = select model x f in
               let told =
                 ExtTerm.to_old_trm Map.Poly.empty senv (term_of_term t)
               in
               let one = Map.Poly.singleton x told in
               ( Map.Poly.set
                   (Map.Poly.map sub ~f:(LogicOld.Term.subst one))
                   ~key:x ~data:told,
                 subst_in ~subst_atom x t f )))

  let select_terms model xs atoms =
    try
      let sorts_are p = List.for_all xs ~f:(fun (_, s) -> p s) in
      let names = List.map xs ~f:fst in
      if List.is_empty xs then Some Map.Poly.empty
      else if sorts_are LogicOld.Term.is_int_sort then
        run ~formula_of_term:LIA.formula_of_term ~select:LIA.select
          ~subst_atom:LIA.subst_atom ~term_of_term:LIA.term_of_term
          ~model:(model_of model ~f:(function Value.Int i -> Some i | _ -> None))
          names atoms
      else if sorts_are LogicOld.Term.is_real_sort then
        run ~formula_of_term:LRA.formula_of_term ~select:LRA.select
          ~subst_atom:LRA.subst_atom ~term_of_term:LRA.term_of_term
          ~model:
            (model_of model ~f:(function Value.Real r -> Some r | _ -> None))
          names atoms
      else None
    with e when not (Common.Timer.is_async e) -> None
end
