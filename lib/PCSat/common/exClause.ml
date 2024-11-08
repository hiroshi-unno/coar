open Core
open Ast
open Ast.LogicOld
open Common.Ext
open Common.Combinator

type t = { positive : ExAtom.t Set.Poly.t; negative : ExAtom.t Set.Poly.t }

let mk_unit_neg atm =
  { positive = Set.Poly.empty; negative = Set.Poly.singleton atm }

let mk_unit_pos atm =
  { positive = Set.Poly.singleton atm; negative = Set.Poly.empty }

(* assume that phi is quantifier-free *)
let make exi_senv ps ns phi =
  let of_old_atom = ExAtom.of_old_atom exi_senv (Formula.mk_true ()) in
  try
    match (*ToDo*) Evaluator.eval phi with
    | true -> None
    | false ->
        Some
          {
            positive = Set.Poly.map ps ~f:of_old_atom;
            negative = Set.Poly.map ns ~f:of_old_atom;
          }
  with _ ->
    let unknowns, params =
      Formula.term_sort_env_of phi
      |> Set.partition_tf ~f:(fst >> Map.Poly.mem exi_senv)
    in
    if Set.is_empty unknowns then (
      (* without function variables *)
      let neg_phi =
        Normalizer.normalize @@ Evaluator.simplify @@ Formula.mk_neg phi
      in
      assert (Fn.non Set.is_empty ps || Fn.non Set.is_empty ns);
      let ps, ns =
        if Set.is_empty params then
          (* without parameters *)
          (*ToDo: reachable if phi has div0, mod0 or evaluation is incomplete? *)
          ( Set.Poly.map ps ~f:(ExAtom.of_old_atom exi_senv neg_phi),
            Set.Poly.map ns ~f:(ExAtom.of_old_atom exi_senv neg_phi) )
        else
          ( Set.Poly.map ps ~f:(ExAtom.of_old_atom exi_senv neg_phi),
            Set.Poly.map ns ~f:(ExAtom.of_old_atom exi_senv neg_phi) )
      in
      if Set.exists ps ~f:ExAtom.is_ppapp || Set.exists ns ~f:ExAtom.is_ppapp
      then Some { positive = ps; negative = ns }
      else
        (* ToDo: reachable here if phi contains a if-expression? *)
        (*failwith @@ "failed to evaluate " ^
                    "phi = " ^ Formula.str_of phi ^ "\n" ^
                    "ps = " ^ String.concat_set ~sep:"," (Set.Poly.map ~f:ExAtom.str_of ps) ^ "\n" ^
                    "ns = " ^ String.concat_set ~sep:"," (Set.Poly.map ~f:ExAtom.str_of ns);*)
        Some { positive = ps; negative = ns })
    else if Set.is_empty params then
      (* with function variables and without parameters *)
      Some
        {
          positive =
            Set.add
              (Set.Poly.map ps ~f:of_old_atom)
              (ExAtom.mk_fcon (Map.Poly.empty, phi));
          negative = Set.Poly.map ns ~f:of_old_atom;
        }
    else
      (* with function variables and parameters *)
      Some
        {
          positive =
            Set.add
              (Set.Poly.map ps ~f:of_old_atom)
              (ExAtom.mk_fcon (Map.of_set_exn params, phi));
          negative = Set.Poly.map ns ~f:of_old_atom;
        }

let is_unit_positive (clause : t) =
  Set.is_empty clause.negative && Set.length clause.positive = 1

let is_unit_negative (clause : t) =
  Set.is_empty clause.positive && Set.length clause.negative = 1

let is_unit (clause : t) =
  Set.length clause.positive + Set.length clause.negative = 1

(* contradiction *)
let is_empty (clause : t) =
  Set.(is_empty clause.positive && is_empty clause.negative)

let pvs_of (clause : t) : Ident.pvar Set.Poly.t =
  Set.union
    (Set.Poly.filter_map ~f:ExAtom.pvar_of clause.positive)
    (Set.Poly.filter_map ~f:ExAtom.pvar_of clause.negative)

let pvar_sorts_of (clause : t) =
  Set.union
    (Set.Poly.filter_map ~f:ExAtom.pvar_sorts_of clause.positive)
    (Set.Poly.filter_map ~f:ExAtom.pvar_sorts_of clause.negative)

let tvs_of (clause : t) : Ident.tvar Set.Poly.t =
  Set.concat
  @@ Set.union
       (Set.Poly.map ~f:ExAtom.tvs_of clause.positive)
       (Set.Poly.map ~f:ExAtom.tvs_of clause.negative)

let params_of clause =
  Map.of_set_exn
  @@ Set.concat_map ~f:Set.of_map
  @@ Set.union
       (Set.Poly.map ~f:ExAtom.params_of clause.positive)
       (Set.Poly.map ~f:ExAtom.params_of clause.negative)

let exatoms_of clause = Set.union clause.negative clause.positive

(* Assuming that uclause is a unit clause *)
let exatom_of_uclause (uclause : t) =
  assert (is_unit uclause);
  match (Set.choose uclause.positive, Set.choose uclause.negative) with
  | Some (ExAtom.PApp _ as atm), None
  | Some (ExAtom.FCon _ as atm), None
  | Some (ExAtom.PPApp (_, _) as atm), None
  | None, Some (ExAtom.PApp _ as atm)
  | None, Some (ExAtom.FCon _ as atm)
  | None, Some (ExAtom.PPApp (_, _) as atm) ->
      atm
  | _, _ -> assert false

let papp_of_uclause (uclause : t) =
  match exatom_of_uclause uclause with
  | ExAtom.PApp papp -> Some papp
  | _ -> None

let ppapp_of_uclause (uclause : t) =
  match exatom_of_uclause uclause with
  | ExAtom.PPApp (pred, papp) ->
      Some (pred, papp)
      (*ToDo: rename parameters to avoid introducing unnecessary dependency*)
  | _ -> None

let old_atom_of_papp ((pvar, sorts), terms) = Atom.mk_pvar_app pvar sorts terms

let old_atom_of_uclause (uclause : t) =
  uclause |> papp_of_uclause |> function
  | None -> (
      match ppapp_of_uclause uclause with
      | None -> None
      | Some ((param_senv, phi), papp) ->
          if Formula.is_true phi then Some (param_senv, old_atom_of_papp papp)
          else None (*ToDo*))
  | Some papp -> Some (Map.Poly.empty, old_atom_of_papp papp)

let atom_of_uclause uc =
  Option.(
    old_atom_of_uclause uc >>= fun (params, atm) ->
    Some
      ( Logic.of_old_sort_env_map params,
        Logic.ExtTerm.of_old_atom atm ))

let to_old_formula clause =
  let params_pos, positives =
    Set.unzip @@ Set.Poly.map clause.positive ~f:(ExAtom.to_old_formula true)
  in
  let params_neg, negatives =
    Set.unzip @@ Set.Poly.map clause.negative ~f:(ExAtom.to_old_formula false)
  in
  ( Map.of_set_exn
    @@ Set.concat_map ~f:Set.of_map
    @@ Set.union params_pos params_neg,
    Formula.or_of @@ Set.to_list @@ Set.union positives negatives )

let to_formula clause =
  let param_senv, phi = to_old_formula clause in
  ( Logic.of_old_sort_env_map param_senv,
    Logic.ExtTerm.of_old_formula @@ Evaluator.simplify phi )

let rename map cl =
  {
    positive = Set.Poly.map ~f:(ExAtom.rename map) cl.positive;
    negative = Set.Poly.map ~f:(ExAtom.rename map) cl.negative;
  }

let iterate_senv cl =
  let senv =
    Set.fold cl.negative ~init:([], Set.Poly.empty) ~f:ExAtom.iterate_senv
  in
  Set.fold cl.positive ~init:senv ~f:ExAtom.iterate_senv |> fst |> List.rev

let iterate_vars unknowns cl =
  let bvs, tvs =
    Set.fold cl.negative ~init:(unknowns, []) ~f:(fun (bvs, tvs) atm ->
        let bvs', tvs' = ExAtom.iterate_vars bvs atm in
        (bvs', tvs @ tvs'))
  in
  Set.fold cl.positive ~init:(bvs, tvs) ~f:(fun (bvs, tvs) atm ->
      let bvs', tvs' = ExAtom.iterate_vars bvs atm in
      (bvs', tvs @ tvs'))

let normalize_atoms cl =
  {
    positive = Set.Poly.map ~f:ExAtom.normalize cl.positive;
    negative = Set.Poly.map ~f:ExAtom.normalize cl.negative;
  }

let normalize_params unknowns cl =
  let cl = normalize_atoms cl in
  let _, tvs = iterate_vars unknowns cl in
  let map =
    Map.Poly.of_alist_exn
    @@ List.mapi tvs ~f:(fun i x ->
           (x, Ident.mk_dontcare (string_of_int (i + 1))))
  in
  rename map cl

let refresh_params senv cl =
  let map =
    Map.of_set_exn
    @@ Set.Poly.filter_map ~f:(fun x ->
           if Map.Poly.mem senv x then None
           else Some (x, Ident.mk_fresh_dontcare ""))
    @@ tvs_of cl
  in
  rename map cl

let str_of cl =
  let pos =
    cl.positive
    |> Set.Poly.map ~f:ExAtom.str_of
    |> String.concat_set ~sep:" \\/ "
  in
  let neg =
    cl.negative
    |> Set.Poly.map ~f:ExAtom.str_of
    |> String.concat_set ~sep:" /\\ "
  in
  String.paren @@ sprintf "%s => %s" neg pos

let normalize cl =
  {
    positive = Set.Poly.map ~f:ExAtom.normalize cl.positive;
    negative = Set.Poly.map ~f:ExAtom.normalize cl.negative;
  }

let instantiate cl =
  {
    positive = Set.Poly.map ~f:ExAtom.instantiate cl.positive;
    negative = Set.Poly.map ~f:ExAtom.instantiate cl.negative;
  }

let matched_by ?(check_inst = false) unknowns atms atm =
  (*ToDo: ExAtom.to_old_atom ignores conditional parametric*)
  match ExAtom.to_old_atom atm with
  | None -> Set.find atms ~f:(fst >> ExAtom.equal atm) (*ToDo*)
  | Some (_params (*ToDo*), atm) ->
      Set.find atms ~f:(fun (atm', _src) ->
          (*ToDo: ExAtom.to_old_atom ignores conditional parametric*)
          match ExAtom.to_old_atom atm' with
          | None -> false (*ToDo*)
          | Some (_params' (*ToDo*), atm') ->
              ((not check_inst)
              || Stdlib.(
                   Atom.str_of @@ Atom.instantiate atm'
                   = Atom.str_of @@ Atom.instantiate atm))
              && (Option.is_some @@ Atom.pattern_match unknowns atm' atm))

let simplify unknowns pos neg (clause, srcs) =
  let srcs = ref srcs in
  let cl_pos =
    Set.filter clause.positive ~f:(fun cl ->
        match matched_by unknowns neg cl with
        | Some (_, src) ->
            srcs := src @ !srcs;
            false
        | None -> true)
  in
  let cl_neg =
    Set.filter clause.negative ~f:(fun cl ->
        match matched_by unknowns pos cl with
        | Some (_, src) ->
            srcs := src @ !srcs;
            false
        | None -> true)
  in
  if
    Set.exists cl_pos
      ~f:(matched_by unknowns pos ~check_inst:true >> Option.is_some)
    (* clause is subsumed by pos *)
    || Set.exists cl_neg
         ~f:(matched_by unknowns neg ~check_inst:true >> Option.is_some)
    (* clause is subsumed by neg *)
    || (*ToDo: this never holds?*)
    (Fn.non Set.is_empty @@ Set.inter cl_pos cl_neg (* clause is tautology *))
  then None
  else
    Some
      (normalize_params unknowns { positive = cl_pos; negative = cl_neg }, !srcs)

let rec simplify_nepvs nepvs clause =
  if
    Fn.non Set.is_empty clause.positive
    || not
         (Set.for_all clause.negative ~f:(fun atm ->
              match ExAtom.pvar_of atm with
              | None -> false
              | Some p -> Set.mem nepvs @@ Ident.pvar_to_tvar p))
  then clause
  else
    match Set.find clause.negative ~f:(ExAtom.is_empty_atm nepvs) with
    | None -> clause
    | Some neatm ->
        simplify_nepvs nepvs
          { clause with negative = Set.remove clause.negative neatm }

let subst sub clause =
  {
    positive = Set.Poly.map clause.positive ~f:(ExAtom.subst sub);
    negative = Set.Poly.map clause.negative ~f:(ExAtom.subst sub);
  }

let add_cond phi clause =
  if Formula.is_true phi then clause
  else
    {
      positive = clause.positive;
      negative = Set.add clause.negative (ExAtom.mk_fcon (Map.Poly.empty, phi));
    }

let exists ~f clause =
  Set.exists ~f clause.positive || Set.exists ~f clause.negative

let equal e1 e2 =
  Set.equal e1.positive e2.positive && Set.equal e1.negative e2.negative
