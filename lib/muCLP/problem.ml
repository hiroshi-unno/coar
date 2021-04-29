open Core
open Common
open Util
open Ast
open LogicOld


(* TODO : should be replaced with appropriate configuration (dummy instantiation) *)
module Debug = Debug.Make(val Debug.Config.disable)

type entrypoint = Formula.t
type func = (Predicate.fixpoint * Ident.pvar * SortEnv.t * Formula.t)
type t = MuCLP of func list * entrypoint
type solution = Valid | Invalid | Unknown

exception Timeout

let make funcs entry = MuCLP (funcs, entry)
let mk_func fix pvar args formula : func = (fix, pvar, args, formula)

let flip_solution = function
  | Valid -> Invalid
  | Invalid -> Valid
  | x -> x

let str_of_solution = function
  | Valid -> "valid"
  | Invalid -> "invalid"
  | Unknown -> "unknown"

let get_functions = function MuCLP (funs, _) -> funs
let get_entrypoint = function MuCLP (_, entry) -> entry
let get_fixpoint_of_function = function (fix, _, _, _) -> fix
let get_pvar_of_function = function (_, pvar, _, _) -> pvar
let get_args_of_function = function (_, _, args, _) -> args
let get_body_of_function = function (_, _, _, body) -> body
let get_size = function MuCLP (funs, _) -> List.length funs

let let_muclp = function MuCLP (funcs, entry) -> (funcs, entry)
let let_function = function func -> func

let avoid_dup pvar pvars =
  if not @@ List.exists ~f:(fun pvar' -> Stdlib.(=) (Ident.name_of_pvar pvar') (Ident.name_of_pvar pvar)) pvars then
    pvar
  else
    let suffix = ref 2 in
    while List.exists ~f:(fun pvar' -> Stdlib.(=) (Ident.name_of_pvar pvar') (Ident.name_of_pvar pvar ^ (string_of_int !suffix))) pvars do
      suffix := !suffix + 1
    done;
    Ident.Pvar (Ident.name_of_pvar pvar ^ (string_of_int !suffix))

(* Usage: let entry, funcs, _ = muclp_of_formula_with_env fml [] Env.empty Env.empty *)
(* Note: bound_tvars: term variables bound by fixpoint predicates *)
let rec of_formula_with_env fml funcs env used_pvars bound_tvars =
  let open Formula in
  match fml with
  | Atom (atom, info) -> begin
      match atom with
      | App (Fixpoint (fp, pvar, bounds, body), outer_args, info') ->
        (* (fp pvar(bounds). body)(args) *)
        let new_pvar = avoid_dup pvar used_pvars in
        let used_pvars = new_pvar :: used_pvars in
        let env = Env.update [pvar, new_pvar] env in
        let bound_tvars = Set.Poly.union bound_tvars (SortEnv.set_of bounds) in
        let body, funcs, used_pvars = of_formula_with_env body funcs env used_pvars bound_tvars in

        let fvs_of_body = Formula.term_sort_env_of body in
        let additional_params = SortEnv.of_set @@
          Set.Poly.diff fvs_of_body (Set.Poly.inter bound_tvars (SortEnv.set_of bounds)) in

        let new_bounds = SortEnv.append bounds additional_params in
        let new_outer_args = outer_args @ Term.of_sort_env additional_params in
        let new_inner_args = Term.of_sort_env new_bounds in
        let new_sorts = SortEnv.sorts_of new_bounds in

        let new_pvar_app = Formula.mk_atom (Atom.mk_app (Predicate.Var(new_pvar, new_sorts)) new_inner_args) in
        let body = subst_preds (Map.Poly.singleton pvar (bounds, new_pvar_app)) body in
        let funcs = (mk_func fp new_pvar new_bounds body) :: funcs in
        let fml' = Formula.mk_atom
            (Atom.mk_app
               (Predicate.mk_var new_pvar new_sorts)
               new_outer_args ~info:info')
            ~info in
        fml', funcs, used_pvars
      | App (Var (pvar, sorts), args, info') ->
        let new_pred = Predicate.mk_var (Env.lookup_exn pvar env) sorts in
        let fml' = Formula.mk_atom (Atom.mk_app new_pred args ~info:info') ~info in
        fml', funcs, used_pvars
      | _ -> fml, funcs, used_pvars
    end
  | UnaryOp (op, fml, info) ->
    let entry, funcs, used_pvars = of_formula_with_env fml funcs env used_pvars bound_tvars in
    let fml' = Formula.mk_unop op entry ~info in
    fml', funcs, used_pvars
  | BinaryOp (op, lhs, rhs, info) ->
    let left_entry, funcs, used_pvars = of_formula_with_env lhs funcs env used_pvars bound_tvars in
    let right_entry, funcs, used_pvars = of_formula_with_env rhs funcs env used_pvars bound_tvars in
    let fml' = Formula.mk_binop op left_entry right_entry ~info in
    fml', funcs, used_pvars
  | Bind (binder, bounds, body, info) ->
    let entry, funcs, used_pvars = of_formula_with_env body funcs env used_pvars bound_tvars in
    let fml' = Formula.mk_bind binder bounds entry ~info in
    fml', funcs, used_pvars
  | LetRec (letrec_funcs, body, _) ->
    let env, used_pvars = List.fold ~init:(env, used_pvars) letrec_funcs
        ~f:(fun (env, used_pvars) (_, pvar, _, _) ->
            let new_pvar = avoid_dup pvar used_pvars in
            let used_pvars = new_pvar :: used_pvars in
            Env.update [pvar, new_pvar] env, used_pvars)
    in
    let entry, funcs, used_pvars = of_formula_with_env body funcs env used_pvars bound_tvars in
    let funcs, used_pvars = List.fold ~init:(funcs, used_pvars) letrec_funcs
        ~f:(fun (funcs, used_pvars) (fp, pvar, bounds, body) ->
            let body, funcs, used_pvars = of_formula_with_env body funcs env used_pvars bound_tvars in
            mk_func fp (Env.lookup_exn pvar env) bounds body :: funcs, used_pvars)
    in
    entry, funcs, used_pvars

let of_formula fml =
  let entry, funcs, _ = of_formula_with_env fml [] Env.empty [] Set.Poly.empty in
  make funcs entry

let to_formula _ = assert false (* TODO *)

let str_of_func func =
  let fix, Ident.Pvar pvar_name, args, body = let_function func in
  Printf.sprintf
    "%s%s: bool =%s %s;"
    pvar_name
    (if SortEnv.length args > 0 then " " ^ SortMap.str_of Term.str_of_sort (Map.Poly.of_alist_exn @@ SortEnv.list_of args) else "")
    (Predicate.str_of_fixpoint fix)
    (Formula.str_of body)

let str_of_func_list funcs = List.map ~f:str_of_func funcs |> String.concat ~sep:"\n"

let str_of muclp =
  let funcs, entry = let_muclp muclp in
  (Formula.str_of entry) ^ "\n"
  ^ "s.t.\n"
  ^ str_of_func_list funcs
(*  ^ (String.concat "\n"
       (List.map
          (fun func ->
             let fix, Ident.Pvar pvar_name, args, body = let_function func in
             pvar_name
             ^ "(" ^ (String.concat "," (List.map (fun (Ident.Tvar var_name, _) -> var_name) args)) ^ ")"
             ^ " =" ^ (PrinterHum.str_of_fixpoint fix) ^ " "
             ^ (Formula.str_of body)
          ) funcs)
    ) *)

let is_onlymu = function MuCLP (funs, _) ->
  List.for_all ~f:(fun (fixpoint, _, _, _) -> Stdlib.(=) fixpoint Predicate.Mu) funs
let is_onlynu = function MuCLP (funs, _) -> 
  List.for_all ~f:(fun (fixpoint, _, _, _) -> Stdlib.(=) fixpoint Predicate.Nu) funs
let is_onlyexists muclp =
  let funcs, entry = let_muclp muclp in
  let rec check fml =
    if Formula.is_atom fml then
      true
    else if Formula.is_and fml || Formula.is_or fml then
      let _, fml_left, fml_right, _ = Formula.let_binop fml in
      check fml_left && check fml_right
    else if Formula.is_forall fml then
      false
    else if Formula.is_exists fml then
      let _, fml, _ = Formula.let_exists fml in
      check fml
    else
      ((*Debug.print @@ lazy (Printf.sprintf "not implemented for: %s" @@ Formula.str_of fml);*)
        failwith "not implemented")
  in
  List.for_all ~f:(fun fml -> check @@ Evaluator.simplify fml)
  @@ entry :: List.map ~f:(fun (_, _, _, body) -> body) funcs
let is_onlyforall muclp =
  let funcs, entry = let_muclp muclp in
  let rec check fml =
    if Formula.is_atom fml then
      true
    else if Formula.is_and fml || Formula.is_or fml then
      let _, fml_left, fml_right, _ = Formula.let_binop fml in
      check fml_left && check fml_right
    else if Formula.is_forall fml then
      let _, fml, _ = Formula.let_forall fml in
      check fml
    else if Formula.is_exists fml then
      false
    else
      failwith "not implemented"
  in
  List.for_all ~f:check
  @@ entry :: List.map ~f:(fun (_, _, _, body) -> body) funcs
let is_noquantifier muclp = is_onlyexists muclp && is_onlyforall muclp

let aconv_tvar (MuCLP (funcs, entry)) =
  let open Core in
  let entry' = Formula.aconv_tvar entry in
  let funcs' =
    List.map funcs ~f:(fun (fp, pvar, params, phi) ->
        let pmap = 
          SortEnv.map params ~f:(fun (x, sort) -> (x, sort, Ident.mk_fresh_tvar ()))
        in 
        let map = List.map pmap ~f:(fun (x, sort, x') -> (x, Term.mk_var x' sort)) in
        let params' = SortEnv.of_list @@ List.map pmap ~f:(fun (_, sort, x') -> x', sort) in
        let phi' = Formula.subst (Map.Poly.of_alist_exn map) @@ Formula.aconv_tvar phi in
        (fp, pvar, params', phi'))
  in
  MuCLP (funcs', entry')

let move_quantifiers_to_front muclp =
  let funcs, entry = let_muclp muclp in
  make
    (List.map funcs
       ~f:(fun func ->
           let fix, pvar, args, body = let_function func in
           mk_func fix pvar args @@ FormulaUtil.move_quantifiers_to_front body))
  @@ FormulaUtil.move_quantifiers_to_front entry

let rm_forall (MuCLP (funcs, entry)) =
  let _, entry' = Formula.rm_forall entry in
  let funcs' =
    List.map funcs ~f:(fun (fp, pvar, params, phi) ->
        (fp, pvar, params, snd @@ Formula.rm_forall phi)) in
  MuCLP (funcs', entry')

let penv_of ?(init=Map.Poly.empty) (MuCLP (funcs, _entry)) =
  let rec inner map = function
    | [] -> map
    | (_, pvar, params, _)::funcs ->
      let sorts = SortEnv.sorts_of params in
      let map' = Map.Poly.add_exn map ~key:pvar ~data:sorts in
      inner map' funcs
  in
  inner init funcs

let complete_tsort (MuCLP (funcs, entry)) =
  MuCLP
    (List.map funcs ~f:(fun (fp, pvar, params, phi) ->
         (fp, pvar, params, Formula.complete_tsort phi)),
     Formula.complete_tsort entry)

(* TODO : this should be applied to hes Parser *)
let complete_psort uninterp_pvs (MuCLP (funcs, entry)) =
  let map = penv_of ~init:uninterp_pvs (MuCLP (funcs, entry)) in
  MuCLP
    (List.map funcs ~f:(fun (fp, pvar, params, phi) ->
         (fp, pvar, params, Formula.complete_psort map phi)),
     Formula.complete_psort map entry)

let simplify muclp =
  let funcs, entry = let_muclp muclp in
  make
    (List.map funcs
       ~f:(fun (fixpoint, pvar, args, formula) ->
           (fixpoint, pvar, args, Evaluator.simplify formula)))
    (Evaluator.simplify entry)

let get_dual muclp =
  let funcs, entry = let_muclp muclp in
  let pvars = List.map funcs ~f:(fun (_, pvar, _, _) -> pvar) in
  let subst formula = List.fold ~init:formula pvars ~f:(fun fml pvar -> Formula.subst_neg pvar fml) in
  make
    (List.map funcs
       ~f:(fun (fixpoint, pvar, args, formula) ->
           (Predicate.flip_fixpoint fixpoint,
            pvar, args, Evaluator.simplify_neg (subst formula))))
    (Evaluator.simplify_neg (subst entry))

let get_greatest_approx muclp =
  let funcs, entry = let_muclp muclp in
  make (List.map funcs ~f:(fun (_, pvar, args, formula) -> (Predicate.Nu, pvar, args, formula))) entry

let rec replace_app (replacer: Formula.t -> Formula.t) formula =
  if Formula.is_atom formula then
    let atom, info = Formula.let_atom formula in
    let formula = Formula.mk_atom atom ~info in
    if Atom.is_app atom then
      let pred, _, _ = Atom.let_app atom in
      if Predicate.is_var pred then
        replacer formula
      else formula
    else
      formula
  else if Formula.is_binop formula then
    let binop, left, right, info = Formula.let_binop formula in
    Formula.mk_binop binop (replace_app replacer left) (replace_app replacer right) ~info
  else if Formula.is_unop formula then
    let unop, body, info = Formula.let_unop formula in
    Formula.mk_unop unop (replace_app replacer body) ~info
  else if Formula.is_bind formula then
    let binder, bounds, body, info = Formula.let_bind formula in
    Formula.mk_bind binder bounds (replace_app replacer body) ~info
  else assert false

let get_next_funcs fml =
  let res = ref [] in
  let _ = replace_app (fun fml ->
      let atom, _ = Formula.let_atom fml in
      let pred, _, _ = Atom.let_app atom in
      let pvar, _ = Predicate.let_var pred in
      res := pvar :: !res;
      fml
    ) fml
  in
  Stdlib.List.sort_uniq Ident.pvar_compare !res

let replace_app_add formula arg sort =
  replace_app (fun fml ->
      let atom, info = Formula.let_atom fml in
      let pred, args, info' = Atom.let_app atom in
      let pvar, arg_sorts = Predicate.let_var pred in
      Formula.mk_atom
        (Atom.mk_app
           (Predicate.mk_var pvar (sort :: arg_sorts))
           (arg :: args)
           ~info:info'
        ) ~info
    ) formula

let elim_mu_from_funcs_with_rec funcs tvar_rec =
  List.map ~f:(fun func ->
      let fix, pvar, args, body = (let_function func) in
      let args = SortEnv.append (SortEnv.singleton tvar_rec T_int.SInt) args in
      let term = Term.mk_var tvar_rec T_int.SInt in
      if Stdlib.(=) fix Predicate.Nu then
        let body = replace_app_add body term T_int.SInt in
        mk_func Predicate.Nu pvar args body
      else
        (* replace all F X Y --> F (rec_ - 1) X Y in body*)
        let term = Term.mk_fsym_app T_int.Sub [term; T_int.one ()] in
        let body = replace_app_add body term T_int.SInt in
        (* body --> rec_ > 0 /\ body *)
        let body = Formula.mk_and (Formula.mk_atom (T_int.mk_gt term (T_int.zero ()))) body in
        mk_func Predicate.Nu pvar args body
    ) funcs

let rename_args group =
  let (_, a1, _, _) = List.hd_exn group in
  match a1 |> Set.Poly.to_list with
  | [] ->
    List.map group ~f:(fun (senv, ps, ns, phi) ->
        assert (Set.Poly.is_empty ps);
        senv, None, ns, Evaluator.simplify_neg phi)
  | [Atom.App(Predicate.Var(_, sorts), args0, _)] ->
    let new_vars = List.map2_exn ~f:(fun _ s -> Ident.mk_fresh_tvar (), s) args0 sorts in
    let args' = List.map new_vars ~f:(uncurry Term.mk_var) in
    List.map group ~f:(fun (uni_senv, ps, ns, phi) ->
        match Set.Poly.to_list ps with
        | [Atom.App(Predicate.Var(p, _), args, _)] ->
          Logic.SortMap.merge uni_senv
            (Logic.SortMap.of_set @@ Set.Poly.of_list @@ List.map ~f:(Pair.map_snd Logic.ExtTerm.of_old_sort) new_vars),
          Some (p, SortEnv.of_list new_vars),
          ns,
          Formula.and_of @@ Evaluator.simplify_neg phi :: List.map2_exn args args' ~f:Formula.eq
        | _ -> assert false)
  | _ -> assert false

(*let detect_arity0_preds (MuCLP (funcs, entry)) =
  if List.exists ~f:(fun (_, _, params, _) -> List.length params = 0) funcs
  then failwith "arity0 predicates is not supported."
  else MuCLP (funcs, entry)*)

let detect_undefined_preds (MuCLP (funcs, entry)) =
  let check map formula =
    let fpv = LogicOld.Formula.pvs_of formula in
    (*Debug.print @@
      lazy (Printf.sprintf "fpvs: %s" @@ String.concat ~sep:"," @@
          Set.Poly.to_list @@
          Set.Poly.map ~f:(fun (Ident.Pvar pid) -> pid) fpv);*)
    match Set.Poly.find ~f:(fun pvar -> not @@ Map.Poly.mem map pvar) fpv with
    | Some (Ident.Pvar pid) -> failwith @@ "undefined predicates: " ^ pid
    | None -> ()
  in
  let rec mk_env map = function
    | [] -> map
    | (_, pvar, _, _)::xs ->
      mk_env (Map.Poly.add_exn map ~key:pvar ~data:pvar) xs
  in
  let map = mk_env Map.Poly.empty funcs in
  check map entry;
  List.iter ~f:(fun (_, _, _, phi) -> check map phi) funcs;
  MuCLP (funcs, entry)

let _check_problem muclp =
  muclp
  (*|> detect_arity0_preds*)
  |> detect_undefined_preds
let check_problem muclp = muclp

let of_chc chc =
  let chc = chc |> PCSP.Problem.to_nnf |> PCSP.Problem.to_cnf in
  let groups =
    chc
    |> PCSP.Problem.clauses_of
    |> Ast.ClauseSet.to_old_clause_set (PCSP.Problem.senv_of chc)
    |> Set.to_list
    |> List.classify (fun (_, ps1, _, _)  (_, ps2, _, _) ->
        match Set.Poly.to_list ps1, Set.Poly.to_list ps2 with
        | [], [] -> true
        | [atm1], [atm2] ->
          assert (Atom.is_app atm1 && Atom.is_app atm2);
          let p1, _, _ = Atom.let_app atm1 in
          let p2, _, _ = Atom.let_app atm2 in
          assert (Predicate.is_var p1 && Predicate.is_var p2);
          let pred1 = Predicate.let_var p1 in
          let pred2 = Predicate.let_var p2 in
          Stdlib.(=) pred1 pred2
        | _, _ -> false)
    |> List.map ~f:rename_args
  in
  let goals, defs = List.partition_tf groups ~f:(function
      | [] -> assert false
      | ((_senv, p, _ns, _phi) :: _group) -> Option.is_none p) in
  let make_func = function
    | ((_, Some (p, args), _, _) :: _) as group ->
      mk_func Predicate.Mu p args
        (Formula.or_of @@
         List.map group ~f:(fun (senv, _, ns, phi) ->
             let phi = Formula.and_of @@ Evaluator.simplify phi :: List.map (Set.Poly.to_list ns) ~f:Formula.mk_atom in
             let senv =
               let fvs = Formula.fvs_of phi in
               Logic.SortMap.filter_keys senv ~f:(Set.Poly.mem fvs) in
             let senv, phi = Pair.map_snd Evaluator.simplify_neg @@
               Ast.Qelim.qelim_old (Logic.SortMap.of_set @@ Set.Poly.of_list @@ Logic.ExtTerm.of_old_sort_env args) (PCSP.Problem.senv_of chc) (senv, Evaluator.simplify_neg phi) in
             let unbound =
               Logic.SortMap.to_old_sort_env Logic.ExtTerm.to_old_sort @@
               Logic.SortMap.filter_keys senv ~f:(fun x -> not @@ SortEnv.mem args x) in
             Formula.exists unbound phi))
    | _ -> assert false
  in
  let funcs = List.map ~f:make_func defs in
  let query =
    match goals with
    | [] -> Formula.mk_false ()
    | [goals] ->
      Formula.or_of @@
      List.map goals ~f:(fun (senv, _, ns, phi) ->
          let phi = Formula.and_of @@ Evaluator.simplify phi :: List.map (Set.Poly.to_list ns) ~f:Formula.mk_atom in
          let senv = let ftvs = Formula.tvs_of phi(*ToDo:also use pvs?*) in Logic.SortMap.filter_keys senv ~f:(Set.Poly.mem ftvs) in
          let senv, phi = Pair.map_snd Evaluator.simplify_neg @@
            Ast.Qelim.qelim_old Logic.SortMap.empty (PCSP.Problem.senv_of chc) (senv, Evaluator.simplify_neg phi) in
          let unbound = SortEnv.of_list @@ List.map ~f:(fun (x, s) -> x, Logic.ExtTerm.to_old_sort s) @@ Logic.SortMap.to_alist senv in
          Formula.exists unbound phi)
    | _ -> assert false
  in
  let undef_funcs =
    let def_funcs = List.map ~f:(fun (_, p, _, _) -> p) funcs in 
    let senv = Logic.SortMap.filter_keys ~f:(fun x -> not @@ List.mem def_funcs ~equal:Stdlib.(=) (Ident.Pvar (Ident.name_of_tvar x))) @@ PCSP.Problem.senv_of chc in
    Logic.SortMap.mapi senv ~f:(fun ~key:(Ident.Tvar n) ~data ->
        let sorts = List.map ~f:Logic.ExtTerm.to_old_sort @@ Logic.Sort.args_of data in
        let args sorts =
          let flag = ref 0 in
          List.map sorts ~f:(fun sort ->
              let _ = flag := !flag + 1 in
              Ident.Tvar("x" ^ (string_of_int !flag)), sort)
        in
        mk_func Predicate.Mu (Ident.Pvar n) (SortEnv.of_list @@ args sorts) (Formula.mk_false()))
    |> Logic.SortMap.to_alist |> List.map ~f:snd in
  get_dual @@ make (funcs @ undef_funcs) query
(* |>( fun res -> let _ = Printf.printf "\n\n-------------->>>before res<<<--------\n\n%s\n" @@ str_of res in res) *)
(* |>( fun res -> let _ = Printf.printf "\n\n-------------->>>after res<<<--------\n\n%s\n" @@ str_of res in res) *)

let rec of_lts ?(live_vars=None) ?(cut_points=None) = function
  | lts, LTS.Problem.Term ->
    let (start, (*ignore*)_error, (*ignore*)_cutpoint, transitions) = lts in
    let pvar_of s = Ident.Pvar ("state_" ^ s) in
    let tenv_of =
      match live_vars with
      | None ->
        let tenv = SortEnv.of_set @@ Set.Poly.filter ~f:(fun (x, _) -> not @@ String.is_prefix ~prefix:LTS.Problem.nondet_prefix @@ Ident.name_of_tvar x) @@ LTS.Problem.term_sort_env_of lts in
        fun _ -> tenv
      | Some live_vars -> fun s -> try SortEnv.of_set (live_vars s) with Caml.Not_found -> failwith ("not found: " ^ s)
    in
    Debug.print @@ lazy (Printf.sprintf "LTS:\n%s" @@ LTS.Problem.str_of_lts lts);
    let funcs =
      Common.Util.List.classify (fun (s1, _, _) (s2, _, _) -> String.(s1 = s2)) transitions
      |> List.map ~f:(function
          | [] -> assert false
          | (from, c, to_) :: trs ->
            let next =
              (c, to_) :: List.map trs ~f:(fun (_, c, to_) -> c, to_)
              |> List.map ~f:(fun (c, to_) ->
                  let pvar = pvar_of to_ in
                  let tenv = tenv_of to_ in
                  let phi = LTS.Problem.wp c
                      (Formula.mk_atom @@ Atom.mk_pvar_app pvar (SortEnv.sorts_of tenv) (Term.of_sort_env tenv)) in
                  let nondet_tenv = SortEnv.of_set @@
                    Set.Poly.filter (Formula.term_sort_env_of phi) ~f:(fun (x, _) ->
                        String.is_prefix ~prefix:LTS.Problem.nondet_prefix @@ Ident.name_of_tvar x)
                  in
                  Formula.mk_forall_if_bounded nondet_tenv phi)
              |> Formula.and_of
            in
            mk_func
              (match cut_points with None -> Predicate.Mu | Some cut_points -> if Set.Poly.mem cut_points from then Predicate.Mu else Predicate.Nu)
              (pvar_of from)
              (tenv_of from)
              next)
    in
    (match start with
     | None ->
       assert (List.is_empty transitions);
       make [] (Formula.mk_true ())
     | Some start ->
       let undef_funcs =
         Set.Poly.diff
           (Set.Poly.add (Set.Poly.of_list @@ List.map transitions ~f:(fun (_, _, _to) -> _to)) start)
           (Set.Poly.of_list @@ List.map transitions ~f:(fun (from, _, _) -> from))
         |> Set.Poly.map ~f:(fun from -> mk_func Predicate.Mu (pvar_of from) (tenv_of from) (Formula.mk_true ()))
         |> Set.Poly.to_list
       in
       let query =
         let tenv = tenv_of start in
         Formula.mk_forall_if_bounded tenv @@
         Formula.mk_atom @@
         Atom.mk_pvar_app (pvar_of start) (SortEnv.sorts_of tenv) (Term.of_sort_env tenv) in
       make (funcs @ undef_funcs) query)
  | lts, LTS.Problem.NonTerm -> get_dual @@ of_lts ~live_vars ~cut_points (lts, LTS.Problem.Term)
  | _, LTS.Problem.CondTerm -> assert false
