open Core
open Common
open Common.Util
open Logic


let verbose = false
module Debug = Debug.Make (val Debug.Config.(if verbose then enable else disable))

type t = SortMap.t * term Set.Poly.t * term Set.Poly.t * term
(* assume: (ps, ns, phi): for_all (union ps ns) (BoolTerm.is_atom exi_senv) *)

let of_old_clause (uni_senv, pos, neg, phi) =
  uni_senv,
  Set.Poly.map pos ~f:ExtTerm.of_old_atom,
  Set.Poly.map neg ~f:ExtTerm.of_old_atom,
  ExtTerm.of_old_formula phi
let to_old_clause exi_senv (uni_senv, pos, neg, phi) =
  let senv = SortMap.merge exi_senv uni_senv in
  uni_senv,
  Set.Poly.map pos ~f:(fun phi -> ExtTerm.to_old_atom senv phi []),
  Set.Poly.map neg ~f:(fun phi -> ExtTerm.to_old_atom senv phi []),
  ExtTerm.to_old_formula senv phi []

let lift exi_senv f c = of_old_clause (f (to_old_clause exi_senv c))
let unlift exi_senv f c = to_old_clause exi_senv (f (of_old_clause c))

let sort_env_of ((senv, _, _, _) : t) = senv
let pvs_of ((_, ps, ns, _) : t) =
  let ps_fpvs = Set.Poly.map ps ~f:Term.pvar_of_atom in
  let ns_fpvs = Set.Poly.map ns ~f:Term.pvar_of_atom in
  Set.Poly.union ps_fpvs ns_fpvs
let fvs_of ((_, ps, ns, phi) : t) =
  Set.Poly.union_list
    [Term.fvs_of phi;
     Set.concat_map ~f:Term.fvs_of ps;
     Set.concat_map ~f:Term.fvs_of ns]
(** non-predicate function variables *)
let npfvs_of (c : t) =
  Set.Poly.diff
    (Set.Poly.diff (fvs_of c) (pvs_of c))
    (Set.Poly.of_list @@ SortMap.keys @@ sort_env_of c)

let to_formula ((_, ps, ns, phi) : t)  =
  BoolTerm.or_of @@
  phi :: (Set.Poly.to_list @@ Set.Poly.union ps @@ Set.Poly.map ~f:BoolTerm.neg_of ns)

let is_goal ((_, ps, _, _) : t) = Set.Poly.is_empty ps
let is_definite pvar ((_, ps, _, _) : t) =
  Stdlib.(=) (Set.Poly.length ps) 1 &&
  match Set.Poly.choose ps with
  | None -> assert false
  | Some atm ->
    let pvar', _ = Term.let_var_app atm in
    Stdlib.(=) pvar pvar'
let pos_pvars ((_, ps, _, _) : t) =
  Set.Poly.map ps ~f:(fun atm -> fst @@ Term.let_var_app atm)
let neg_pvars ((_, _, ns, _) : t) =
  Set.Poly.map ns ~f:(fun atm -> fst @@ Term.let_var_app atm)

let pred_of_definite exi_senv (uni_senv, pos, neg, phi) =
  assert (Stdlib.(=) (Set.Poly.length pos) 1);
  match Set.Poly.choose pos with
  | None -> assert false
  | Some atm ->
    let pvar, args = Term.let_var_app atm in
    let sorts = Sort.args_of @@ SortMap.find_exn exi_senv pvar in
    let env = List.map sorts ~f:(fun s -> Ident.mk_fresh_tvar (), s) in
    let neqs = List.map2_exn args env ~f:(fun arg (x, s) -> Term.mk_apps (BoolTerm.mk_neq s) [arg; Term.mk_var x]) in
    let map = SortMap.of_set (Set.Poly.of_list env) in
    let _, phi' =
      Qelim.qelim map exi_senv @@ 
      (SortMap.merge map uni_senv, BoolTerm.or_of @@ phi :: neqs @ (Set.Poly.to_list neg |> List.map ~f:BoolTerm.neg_of))
    in
    pvar, (env, BoolTerm.exists (SortMap.to_alist uni_senv) phi')

(*let str_of cls = ExtTerm.str_of @@ to_formula cls*)
let str_of exi_senv (c : t) =
  LogicOld.Formula.str_of @@
  ExtTerm.to_old_formula (SortMap.merge exi_senv (sort_env_of c)) (to_formula c) []

let simplify_with positive negative ((senv, c_pos, c_neg, c_phi) : t) =
  (* ToDo: improve this to exploit parametric examples *)
  let positive = Set.Poly.map ~f:snd positive in
  let negative = Set.Poly.map ~f:snd negative in
  if Set.Poly.is_empty (Set.Poly.inter positive c_pos) &&
     Set.Poly.is_empty (Set.Poly.inter negative c_neg)
  then Some (senv, Set.Poly.diff c_pos negative, Set.Poly.diff c_neg positive, c_phi)
  else None

let resolve_one_step mode (param_senv, (papp: term)) exi_senv ((uni_senv, c_pos, c_neg, c_phi) as cl : t) =
  Debug.print @@ lazy ("cl: " ^ str_of exi_senv cl);
  let atm1 = ExtTerm.to_old_atom (SortMap.merge exi_senv param_senv) papp [] in
  let uni_senv' = SortMap.merge uni_senv param_senv in
  let senv = SortMap.merge exi_senv uni_senv' in
  (if Stdlib.(=) mode `Forward
   then let _ = Debug.print @@ lazy "forward:" in c_neg
   else let _ = Debug.print @@ lazy "backward:" in c_pos)
  |> Set.Poly.filter_map ~f:(fun papp' ->
      let atm2 = ExtTerm.to_old_atom senv papp' [] in
      Debug.print @@ lazy ("atm1: " ^ LogicOld.Atom.str_of atm1);
      Debug.print @@ lazy ("atm2: " ^ LogicOld.Atom.str_of atm2);
      (*ExtTerm.unify*)LogicOld.Atom.unify (SortMap.key_set exi_senv) atm2 atm1 >>= fun theta (*ToDo*) ->
      let theta = Map.Poly.map ~f:ExtTerm.of_old_term theta in
      let c_pos' =
        Set.Poly.map (if Stdlib.(=) mode `Backward then Set.Poly.remove c_pos papp' else c_pos) ~f:(fun atm ->
            atm |> ExtTerm.subst theta |> flip (ExtTerm.to_old_atom senv) [] |>
            Normalizer.normalize_atom |> ExtTerm.of_old_atom) in
      let c_neg' =
        Set.Poly.map (if Stdlib.(=) mode `Forward then Set.Poly.remove c_neg papp' else c_neg) ~f:(fun atm ->
            atm |> ExtTerm.subst theta |> flip (ExtTerm.to_old_atom senv) [] |>
            Normalizer.normalize_atom |> ExtTerm.of_old_atom) in
      let c_phi' = ExtTerm.subst theta c_phi |> flip (ExtTerm.to_old_formula senv) []
                   |> Evaluator.simplify |> ExtTerm.of_old_formula in
      let cl' = uni_senv', c_pos', c_neg', c_phi' in
      Debug.print @@ lazy ("cl': " ^ str_of exi_senv cl');
      Some (cl', Map.Poly.map theta ~f:(flip (ExtTerm.to_old_term (SortMap.merge exi_senv uni_senv')) [])))

(* val resolve: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t Set.Poly.t *)
let resolve_one_step_all positive negative exi_senv (c : t) =
  let cs_b = Set.Poly.fold negative ~init:Set.Poly.empty
      ~f:(fun acc neg -> Set.Poly.union (resolve_one_step `Backward neg exi_senv c) acc) in
  let cs_f = Set.Poly.fold positive ~init:Set.Poly.empty
      ~f:(fun acc pos -> Set.Poly.union (resolve_one_step `Forward pos exi_senv c) acc) in
  Set.Poly.union cs_b cs_f |> Set.Poly.filter ~f:(fun ((_, _, _, t), _) -> not @@ BoolTerm.is_true t)

let is_only_pure ((_, pos, neg, _) : t) = Set.Poly.is_empty pos && Set.Poly.is_empty neg
let is_unit ((_, pos, neg, _) : t) = Set.Poly.length pos + Set.Poly.length neg = 1

let is_query wfpvs fnpvs ((_, pos, _, _) : t) =
  Set.Poly.for_all pos ~f:(fun atm ->
      let p = BoolTerm.pvar_of_atom atm in Set.Poly.mem wfpvs p || Set.Poly.mem fnpvs p)

let refresh_pvar_args exi_senv ((senv, ps, ns, phi) : t) =
  let ps', pres = Set.unzip @@ Set.Poly.map ps ~f:(fun atm ->
      let pvar, args = Term.let_var_app atm in
      let sorts = Sort.args_of @@ Logic.SortMap.find_exn exi_senv pvar in
      let env = List.map sorts ~f:(fun s -> Ident.mk_fresh_tvar (), s) in
      let args' = List.map env ~f:(fun (x, _) -> Term.mk_var x) in
      Term.mk_var_app pvar args', (env, List.map2_exn args env ~f:(fun arg (x, s) -> Term.mk_apps (BoolTerm.mk_neq s) [Term.mk_var x; arg]))) in
  let xss1, pneqss = Set.unzip pres in
  let ns', nres = Set.unzip @@ Set.Poly.map ns ~f:(fun atm ->
      let pvar, args = Term.let_var_app atm in
      let sorts = Sort.args_of @@ Logic.SortMap.find_exn exi_senv pvar in
      let env = List.map sorts ~f:(fun s -> Ident.mk_fresh_tvar (), s) in
      let args' = List.map env ~f:(fun (x, _) -> Term.mk_var x) in
      Term.mk_var_app pvar args', (env, List.map2_exn args env ~f:(fun arg (x, s) -> Term.mk_apps (BoolTerm.mk_neq s) [Term.mk_var x; arg]))) in
  let xss2, nneqss = Set.unzip nres in
  let senv' = Logic.SortMap.merge senv
      (Logic.SortMap.of_set @@
       Set.concat_map ~f:Set.Poly.of_list (Set.Poly.union xss1 xss2)) in
  senv', ps', ns', BoolTerm.or_of @@ phi :: List.concat (Set.Poly.to_list pneqss) @ List.concat (Set.Poly.to_list nneqss)

(*val refresh_tvar: (Atom.t list * Atom.t list * t) -> (Atom.t list * Atom.t list * t)*)
let refresh_tvar ((senv, ps, ns, phi) : t) =
  let map =
    fvs_of (senv, ps, ns, phi)
    |> Set.Poly.map ~f:(fun x -> x, Ident.mk_fresh_tvar())
    |> Map.of_set
  in
  SortMap.rename_keys_map map senv,
  Set.Poly.map ~f:(Term.rename map) ps,
  Set.Poly.map ~f:(Term.rename map) ns,
  Term.rename map phi

let fvs_new (_, ps, ns, phi) =
  let ps' = Set.Poly.to_list ps in
  let ns' = Set.Poly.to_list ns in
  let ss = ExtTerm.fvs_of phi :: (List.map ~f:ExtTerm.fvs_of ps') @ (List.map ~f:ExtTerm.fvs_of ns') in
  Set.Poly.union_list ss
let reduce_sort_map (senv, ps, ns, phi) =
  let ftvs = fvs_new (senv, ps, ns, phi) in
  Map.Poly.filter_keys senv ~f:(Set.Poly.mem ftvs), ps, ns, phi

let subst exi_senv sub ((uni_senv, ps, ns, phi) : t) : t =
  let ps1, ps2 = Set.Poly.partition_tf ~f:(BoolTerm.is_atom exi_senv uni_senv) @@ Set.Poly.map ps ~f:(Term.subst sub) in
  let ns1, ns2 = Set.Poly.partition_tf ~f:(BoolTerm.is_atom exi_senv uni_senv) @@ Set.Poly.map (Set.Poly.map ns ~f:BoolTerm.neg_of) ~f:(Term.subst sub) in
  uni_senv, ps1, ns1, BoolTerm.or_of @@ Set.Poly.to_list @@ Set.Poly.union_list [ps2; ns2; Set.Poly.singleton @@ Term.subst sub phi]
