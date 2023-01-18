open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld

let verbose = false
module Debug = Debug.Make (val Debug.Config.(if verbose then enable else disable))

type examples = ClauseGraph.t
type hspace = (* hypothesis space for a function evariable*)
  int(*depth*) *
  sort_env_list(*params*) *
  Formula.t Set.Poly.t(*quals*) *
  (Formula.t, QDep.t) Map.Poly.t(*qdeps*) *
  Term.t Set.Poly.t(*terms*)
type hspaces = (Ident.tvar, hspace) Hashtbl.Poly.t
type truth_table = TruthTable.t
type labeling = (Ident.pvar, (int, int) Map.Poly.t) Map.Poly.t * bool
type heat_map = (unit * (string, int) Hashtbl.Poly.t) option ref
type fenv = FunEnv.t
type uenv = UTermEnv.t
type learned_clauses = Clause.t Hash_set.Poly.t
type lower_bounds = (Ident.tvar, Logic.term) Hashtbl.Poly.t
type upper_bounds = (Ident.tvar, Logic.term) Hashtbl.Poly.t
type t = {
  examples    : examples;
  hspaces     : hspaces;
  truth_table : truth_table;
  labelings   : labeling list;
  heat_map    : heat_map;
  fenv        : fenv;
  uenv        : uenv;
  oracle      : PCSP.Problem.oracle;
  learned_clauses : learned_clauses;
  lower_bounds : lower_bounds; (* learned clauses by primal *)
  upper_bounds : upper_bounds; (* learned clauses by dual *)
}

let init oracle = {
  examples = ClauseGraph.create ();
  hspaces = Hashtbl.Poly.create ();
  truth_table = TruthTable.create ();
  labelings = [Map.Poly.empty(*ToDo*), false(*ToDo*)];
  heat_map = ref None;
  fenv = Map.Poly.empty;
  uenv = UTermEnv.create ();
  oracle = oracle;
  learned_clauses = Hash_set.Poly.create ();
  lower_bounds = Hashtbl.Poly.create ();
  upper_bounds = Hashtbl.Poly.create ()
}

let clone t = {
  examples = ClauseGraph.clone t.examples;
  hspaces = Hashtbl.Poly.copy t.hspaces;
  truth_table = TruthTable.clone t.truth_table;
  labelings = t.labelings;
  heat_map = ref !(t.heat_map);
  fenv = t.fenv;
  uenv = UTermEnv.clone t.uenv;
  oracle = t.oracle;
  learned_clauses = Hash_set.Poly.copy t.learned_clauses;
  lower_bounds = Hashtbl.Poly.copy t.lower_bounds;
  upper_bounds = Hashtbl.Poly.copy t.upper_bounds
}

let example_graph_of t = t.examples
let examples_of t = ClauseGraph.examples_of t.examples
let pos_neg_und_examples_of t = ClauseGraph.pos_neg_und_examples_of t.examples
let hspaces_of t = t.hspaces
let hspace_of_pvar (Ident.Pvar name) t =
  match Hashtbl.Poly.find t.hspaces (Ident.Tvar name) with
  | Some cs -> cs
  | None ->
    let new_comp = (-1, [], Set.Poly.empty, Map.Poly.empty, Set.Poly.empty) in
    Hashtbl.Poly.add_exn t.hspaces ~key:(Ident.Tvar name) ~data:new_comp;
    new_comp
let depth_of_hspace (depth, _, _, _, _) = depth
let params_of_hspace (_, params, _, _, _) = params
let quals_of_hspace (_, _, quals, _, _) = quals
let qdeps_of_hspace (_, _, _, qdeps, _) = qdeps
let terms_of_hspace (_, _, _, _, terms) = terms
let terms_of_pvar pvar t = terms_of_hspace @@ hspace_of_pvar pvar t
let reduced_terms_of_pvar pvar t = (*ToDo*)terms_of_hspace @@ hspace_of_pvar pvar t
let qdeps_of pvar t = qdeps_of_hspace @@ hspace_of_pvar pvar t
let quals_map_of t =
  Hashtbl.Poly.map t.hspaces ~f:quals_of_hspace
  |> Hashtbl.to_alist
  |> List.map ~f:(fun (v, q) -> Ident.tvar_to_pvar v, q)
  |> Hashtbl.Poly.of_alist_exn
let truth_table_of t = t.truth_table
let labelings_of t = t.labelings
let fenv_of t = t.fenv
let uenf_of t = t.uenv
let oracle_of t = t.oracle
let learned_clauses_of t = t.learned_clauses
let lower_bounds_of t = t.lower_bounds
let upper_bounds_of t = t.upper_bounds

let add_examples t examples =
  Set.Poly.iter examples ~f:(fun (ex, srcs) -> ClauseGraph.add_ex_from t.examples ex srcs)
let set_examples examples t = { t with examples = examples }
let set_pos_neg_und_examples examples t = { t with examples = examples }
let update_hspace pvar (depth, params, quals, qdeps, terms) t =
  match Hashtbl.Poly.find t.hspaces pvar with
  | None ->
    Hashtbl.Poly.add_exn t.hspaces ~key:pvar ~data:(depth, params, quals, qdeps, terms)
  | Some (_, _, quals', qdeps', terms') ->
    Hashtbl.Poly.set t.hspaces ~key:pvar
      ~data:(depth, params, Set.Poly.union quals quals', Map.force_merge qdeps qdeps', Set.Poly.union terms terms')
let set_truth_table truth_table t = { t with truth_table = truth_table }
let update_truth_table ~id t =
  Hashtbl.Poly.iteri t.hspaces ~f:(fun ~key:(Ident.Tvar name) ~data:(_, env, quals, qdeps, _) ->
      TruthTable.update_map_with_qualifiers ~id t.truth_table t.fenv qdeps ((*ToDo*)Ident.Pvar name) (env, quals));
  TruthTable.update_map_with_examples ~id t.truth_table t.fenv t.hspaces @@ examples_of t
let set_labelings labelings t = { t with labelings = labelings }
let set_label ~id t label labeling atom =
  match ExAtom.pvar_of atom with
  | None -> labeling
  | Some pvar ->
    let ai = TruthTable.index_of_atom ~id (TruthTable.get_table (truth_table_of t) pvar) (fenv_of t) (qdeps_of pvar t) atom in
    match Map.Poly.find labeling pvar with
    | None -> Map.Poly.add_exn labeling ~key:pvar ~data:(Map.Poly.singleton ai label)
    | Some l -> Map.Poly.set labeling ~key:pvar ~data:(Map.Poly.set l ~key:ai ~data:label)
let map ~f vs =
  let examples', labelings' = f ~examples:(examples_of vs) ~labelings:(labelings_of vs) in
  set_labelings labelings' @@ set_examples examples' vs
let set_fenv fenv t = { t with fenv = fenv }
let update_uenv_by_model model t = UTermEnv.update_by_model t.uenv model

let add_learned_clause id t (uni_senv, ps, ns, phi) =
  match Hash_set.find t.learned_clauses ~f:(fun (_, ps1, ns1, _) ->
      Set.Poly.equal ps ps1 && Set.Poly.equal ns ns1) with
  | Some (uni_senv1, ps1, ns1, phi1) ->
    let uni_senv' = Map.force_merge uni_senv uni_senv1 in
    let phi' =
      Logic.ExtTerm.to_old_formula Map.Poly.empty uni_senv' (Logic.ExtTerm.and_of [phi1; phi]) []
      |> Evaluator.simplify
      |> Z3Smt.Z3interface.z3_simplify ~id (Atomic.get LogicOld.ref_fenv)
      |> Logic.ExtTerm.of_old_formula
    in
    Hash_set.remove t.learned_clauses (uni_senv1, ps1, ns1, phi1);
    Hash_set.add t.learned_clauses (uni_senv', ps1, ns1,  phi')
  | None -> Hash_set.Poly.add t.learned_clauses (uni_senv, ps, ns, phi)
let add_learned_clauses id t = Set.Poly.iter ~f:(add_learned_clause id t)
let add_lower_bound t (key, term) =
  Hashtbl.Poly.update t.lower_bounds key ~f:(function
      | None -> term
      | Some old_term ->
        let params =
          List.mapi ~f:(fun i (_, s) -> Ident.Tvar (sprintf "x%d" (i + 1)) , s) @@
          fst @@ Logic.ExtTerm.let_lam term
        in
        let args = List.map params ~f:(fun (v, _) -> Logic.ExtTerm.mk_var v) in
        Logic.ExtTerm.mk_lambda params @@
        Logic.ExtTerm.or_of
          [Logic.ExtTerm.beta_reduction term args;
           Logic.ExtTerm.beta_reduction old_term args])
let lower_bound_of t = Hashtbl.Poly.find t.lower_bounds
let add_upper_bound t (key, term) =
  Hashtbl.Poly.update t.upper_bounds key ~f:(function
      | None -> term
      | Some old_term ->
        let params =
          List.mapi ~f:(fun i (_, s) -> Ident.Tvar (sprintf "x%d" (i + 1)) , s) @@
          fst @@ Logic.ExtTerm.let_lam term
        in
        let args = List.map params ~f:(fun (v, _) -> Logic.ExtTerm.mk_var v) in
        Logic.ExtTerm.mk_lambda params @@
        Logic.ExtTerm.and_of
          [Logic.ExtTerm.beta_reduction term args;
           Logic.ExtTerm.beta_reduction old_term args])
let upper_bound_of t = Hashtbl.Poly.find t.upper_bounds

let add_bound_as_learned_clause id pfwcsp vs pvar (arity, (param_senv, term)) upper =
  Debug.print @@ lazy (sprintf "*** a new %s bound of [%s]" (if upper then "upper" else "lower") @@ Ident.name_of_tvar pvar);
  (*Debug.print @@ lazy
    (sprintf "%s (%d) (%s) := %s" (Ident.name_of_tvar pvar) arity
       (String.concat_map_list ~sep:"," param_senv ~f:(fun (v, _) -> Ident.name_of_tvar v))
       (Logic.ExtTerm.str_of term));*)
  match Map.Poly.find (PCSP.Problem.senv_of pfwcsp) pvar with
  | None -> ()
  | Some _ ->
    let args_log, sargs = Map.Poly.find_exn (PCSP.Problem.args_record_of pfwcsp) @@ Ident.tvar_to_pvar pvar in
    let params, uni_senv, term =
      let pred_params =
        List.mapi sargs ~f:(fun i s -> Ident.Tvar (sprintf "x%d" (i + 1)), s)
      in
      let term =
        Logic.ExtTerm.beta_reduction term @@
        List.map ~f:(fun (v, _) -> Logic.ExtTerm.mk_var v) @@
        List.drop pred_params (List.length pred_params - arity)
      in
      let aux_params =
        List.filter_mapi pred_params ~f:(fun i (v, s) ->
            if args_log.(i) then None else Some (v, Ident.mk_fresh_tvar (), s))
      in
      let pred_params = List.filteri pred_params ~f:(fun i _ -> args_log.(i)) in
      let uni_senv =
        Map.force_merge param_senv @@
        Map.Poly.of_alist_exn @@ 
        List.append pred_params @@ List.map aux_params ~f:(fun (_, v2, s) -> v2, s)
      in
      let sub =
        Map.Poly.of_alist_exn @@ List.map aux_params ~f:(fun (v1, v2, _) -> v1, Logic.ExtTerm.mk_var v2)
      in
      pred_params, uni_senv, Logic.ExtTerm.subst sub term
    in
    let papp = Logic.ExtTerm.mk_var_app pvar @@ List.map params ~f:(fun (v, _) -> Logic.ExtTerm.mk_var v) in
    if upper then begin
      Debug.print @@ lazy
        (sprintf "added a new learned clause: %s(%s) => %s"
           (Ident.name_of_tvar pvar)
           (String.concat_map_list ~sep:"," params ~f:(fun (v, _) -> Ident.name_of_tvar v))
           (Logic.ExtTerm.str_of_formula (PCSP.Problem.senv_of pfwcsp) uni_senv term));
      add_upper_bound vs (pvar, term);
      add_learned_clause id vs (uni_senv, Set.Poly.empty, Set.Poly.singleton papp, term)
    end else if upper(* use only upper bounds as learned clauses *) then begin
      Debug.print @@ lazy
        (sprintf "added a new learned clause: %s => %s(%s)"
           (Logic.ExtTerm.str_of_formula (PCSP.Problem.senv_of pfwcsp) uni_senv term)
           (Ident.name_of_tvar pvar)
           (String.concat_map_list ~sep:"," params ~f:(fun (v, _) -> Ident.name_of_tvar v)));
      add_lower_bound vs (pvar, term);
      add_learned_clause id vs (uni_senv, Set.Poly.singleton papp, Set.Poly.empty, Logic.BoolTerm.neg_of term)
    end

let str_of_hspace name (depth, params, quals, qdeps, terms) =
  sprintf "\n===== [%s](%s) =====\n\n*** depth: %d\n*** qualifiers (%d):\n%s \n*** param_qdeps (%d):\n%s\n*** terms (%d):\n%s"
    name
    (str_of_sort_env_list (Term.str_of_sort) params)
    depth
    (Set.Poly.length quals) (String.concat_map_set ~sep:"\n" quals ~f:Formula.str_of)
    (Map.Poly.length qdeps) (String.concat_map_list ~sep:"\n" ~f:(fun (_, qdep) -> QDep.str_of qdep) @@ Map.Poly.to_alist qdeps)
    (Set.Poly.length terms) (String.concat_map_set ~sep:"\n" terms ~f:Term.str_of)
let str_of_examples (decided_pos, decided_neg, undecided) =
  "********* given example instances *********\n"
  ^ (Printf.sprintf "*** decided positive (%d): [\n" @@ Set.Poly.length decided_pos)
  ^ (ExClauseSet.str_of decided_pos)
  ^ (Printf.sprintf "]\n*** decided negative (%d): [\n" @@ Set.Poly.length decided_neg)
  ^ (ExClauseSet.str_of decided_neg)
  ^ (Printf.sprintf "]\n*** undecided (%d): [\n" @@ Set.Poly.length undecided)
  ^ (ExClauseSet.str_of undecided)
  ^ "]\n"
let str_of_number_of_examples (decided_pos, decided_neg, undecided) =
  Printf.sprintf "#decided_positive: %d, #decided_negative: %d, #undecided: %d"
    (Set.Poly.length decided_pos)
    (Set.Poly.length decided_neg)
    (Set.Poly.length undecided)

let str_of_learned_clauses exi_senv learned_clauses =
  "********* learned clauses *********\n" ^
  (String.concat_map_list ~sep:"\n" ~f:(Clause.str_of exi_senv) @@ Hash_set.to_list learned_clauses) ^
  "\n***********************************"

type ex = {
  positive: string list;
  negative: string list;
  undecided: string list
} [@@ deriving to_yojson]
let to_yojson (decided_pos, decided_neg, undecided) =
  ex_to_yojson @@
  { positive = List.map ~f:ExClause.str_of @@ Set.Poly.to_list decided_pos;
    negative = List.map ~f:ExClause.str_of @@ Set.Poly.to_list decided_neg;
    undecided = List.map ~f:ExClause.str_of @@ Set.Poly.to_list undecided }

(** BMI learning for CEGIS *)

let vec_of_exatom ?(enc_bool_to_float = 100.0) ?(ignore_bool_args = false) map a =
  match ExAtom.pvar_of a, ExAtom.sorts_of a, ExAtom.args_of a with
  | Some pvar, Some sorts, Some args ->
    List.mapi ~f:(fun i x -> i, x) @@ List.filter_map ~f:Fn.id @@
    List.map2_exn args sorts ~f:(fun t -> function
        | T_int.SInt -> Some (Z.to_float @@ Value.int_of @@ Term.value_of t)
        | T_real.SReal -> Some (Q.to_float @@ Value.real_of @@ Term.value_of t)
        | T_bool.SBool ->
          if ignore_bool_args then None
          else if Value.bool_of @@ Term.value_of t
          then Some (enc_bool_to_float)
          else Some (-.enc_bool_to_float)
        | _ -> assert false),
    Hashtbl.find_exn map @@ Ident.name_of_pvar pvar
  | _ -> assert false

let bag_of_exclause ?(enc_bool_to_float = 100.0) ?(ignore_bool_args = false) map (cl, weight) =
  List.map cl ~f:(fun (a, pol) -> vec_of_exatom ~enc_bool_to_float ~ignore_bool_args map a, pol),
  weight

let add_vec vec1 vec2 = List.map2_exn vec1 vec2 ~f:Float.add
let sub_vec vec1 vec2 = List.map2_exn vec1 vec2 ~f:Float.sub
let div_vec vec sc = List.map vec ~f:(fun v -> v /. sc)
let average_of_vecs vecs =
  div_vec (List.fold ~init:(List.hd_exn vecs) (List.tl_exn vecs) ~f:add_vec)
    (float_of_int @@ List.length vecs)
let euclid_dist_sq vec1 vec2 =
  List.sum_float @@ List.map (sub_vec vec1 vec2) ~f:Float.square
let variance_of_vecs (pred_num, vecs) =
  let avg = average_of_vecs vecs in
  pred_num, List.average_float @@ List.map vecs ~f:(euclid_dist_sq avg)
let variances_of_bags bags (* ToDo: fix *) =
  List.map ~f:variance_of_vecs @@
  List.map ~f:(fun a ->
      snd @@ List.hd_exn a,
      List.map a ~f:(fun (vecs, _) -> List.map ~f:snd vecs)) @@
  List.classify (fun (_, pred_num1) (_, pred_num2) -> pred_num1 = pred_num2) @@
  List.map ~f:fst @@ List.concat_map ~f:fst bags

(** assume that all predicate variable has at least one numeric argument *)
let update_heat_map ?(enc_bool_to_float = 100.0) ?(ignore_bool_args_variance = false) senv wexs t : unit =
  ignore (enc_bool_to_float, ignore_bool_args_variance, senv, wexs, t); assert false

let get_heat ?(enc_bool_to_float = 100.0) t atom =
  ignore (enc_bool_to_float, t, atom); assert false