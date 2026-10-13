open Core
open Common.Ext
open Ast
open Ast.LogicOld

(** A detected [Y(x) = q Y(a(x)) + R(x)] acceleration candidate. *)
type detection = {
  self_pred : Ident.tvar;
  exit_pred : Ident.tvar;
  exit_body : Term.t option;

  normalized_exit_body : Term.t;
  params : sort_env_list;
  guard : Formula.t list;
  residual_body : Term.t option;
  recursive_coeff : Q.t;
  exit_probability : Q.t;
  recursive_update : Term.t list;
  exit_update : Term.t list;
}

type closed_form_status = ClosedFormGenerated | NeedClosedForm

type block_reason =
  | InvalidProbability
  | NoClosedForm
  | GuardStabilityNotChecked
  | GuardStabilityFailed
  | UnsupportedUpdate
  | UnsupportedGuard

type guard_stability_vc = {
  guard : Formula.t;
  guard_after_recursive_update : Formula.t;
  condition : Formula.t;
}

type verification_condition = GuardStability of guard_stability_vc

type applicability =
  | Applicable
  | ConditionallyApplicable of verification_condition list
  | Blocked of block_reason list

(** The geometric-expectation IR constructed from an applicable detection. *)
type geo_expectation = {
  self_pred : Ident.tvar;
  exit_pred : Ident.tvar;
  guard : Formula.t option;
  residual_body : Term.t option;
  exit_body : Term.t option;
  (** Authoritative [R / p] before substituting the iterated recursive update. *)
  normalized_exit_body : Term.t;
  p : Q.t;
  recursive_coeff : Q.t;
  k_var : Ident.tvar;
  original_params : sort_env_list;
  original_args : Term.t list;
  recursive_update : Term.t list;
  exit_update : Term.t list;
  accelerated_exit_args : Term.t list option;
  accelerated_exit_body : Term.t option;
  status : closed_form_status;
  verification_conditions : verification_condition list;
}

type accel_rhs =
  | Plain of Term.t
  | GeoExpectation of geo_expectation
  | IfThenElse of {
      guard : Term.t;
      then_rhs : accel_rhs;
      else_rhs : accel_rhs;
    }

type accel_action = ReplacedByGeoExpectation | KeepOriginalBody

type accel_candidate = {
  geo : geo_expectation;
  applicability : applicability;
  action : accel_action;
}

type accel_pred = {
  original_pred : Pred.t;
  body : accel_rhs;
  candidates : accel_candidate list;
  detection_fallback_reasons : string list;
}

type accel_problem = {
  original_problem : Problem.t;
  preds : accel_pred list;
  query : Problem.query;
}

type accel_expr =
  | TermExpr of Term.t
  | GeoExpectationExpr of {
      k_var : Ident.tvar;
      p : Q.t;
      body : Term.t;
    }

type accel_vc =
  | Inequality of {
      lhs : Term.t;
      rhs : accel_expr;
    }
  | Imply of {
      cond : Term.t;
      vc : accel_vc;
    }
  | And of accel_vc list

type lowered_accel_vc = Lowered of accel_vc | NotLowered of string * accel_vc

type template_config = {
  num_conds : int;
  use_orig_ite : bool;
  cond_degree : int;
  term_degree : int;
}

type template_env = {
  templ_params : sort_env_map;
  templ_preds : (Ident.tvar * (sort_env_list * Term.t)) list;
  templ_subst : (Ident.tvar, sort_env_list * Term.t) Map.Poly.t;
}

type accel_formula =
  | AccelFormula of Formula.t list * string list
  | SkippedAcceleratedVC of string * accel_vc

let q_to_string q =
  if Z.equal (Q.den q) Z.one then Z.to_string (Q.num q) else Q.to_string q

let str_of_update args =
  sprintf "(%s)" (String.concat_map_list ~sep:", " args ~f:Term.str_of)

let str_of_params params =
  sprintf "(%s)"
    (String.concat_map_list ~sep:", " params ~f:(fun (x, _) ->
         Ident.name_of_tvar x))

let guard_formula guard = Formula.and_of guard

let is_unguarded guard =
  Formula.is_true @@ Evaluator.simplify @@ guard_formula guard

let str_of_guard guard =
  if is_unguarded guard then "true" else Formula.str_of @@ guard_formula guard

let guard_option_of_list guard =
  if is_unguarded guard then None else Some (guard_formula guard)

let str_of_guard_option = function
  | None -> "none"
  | Some phi -> Formula.str_of phi

let str_of_residual_body = function
  | None -> "none"
  | Some term -> Term.str_of term

let subst_params params args phi =
  Formula.subst
    (Map.Poly.of_alist_exn
    @@ List.map2_exn params args ~f:(fun (param, _) arg -> (param, arg)))
    phi

let guard_stability_condition params recursive_update guard =
  let phi = guard_formula guard in
  Formula.mk_imply phi (subst_params params recursive_update phi)

let guard_stability_vc params recursive_update guard =
  let guard_after_recursive_update =
    subst_params params recursive_update guard
  in
  {
    guard;
    guard_after_recursive_update;
    condition = Formula.mk_imply guard guard_after_recursive_update;
  }

let verification_conditions_of_guard params recursive_update = function
  | None -> []
  | Some guard -> [ GuardStability (guard_stability_vc params recursive_update guard) ]

(* A formula can sit INSIDE a term -- one of the two function symbols that bind
   carries one -- so a hand-written walk over a term's arguments does not see
   everything the term contains, and answering "no" here is the direction that
   costs something: two of the callers ask whether an exit body mentions the
   predicate being accelerated.  The library walk already descends into that
   formula and into every argument, so it is used instead of a local copy. *)
let term_contains_fvar name term =
  Set.exists (Term.fvar_apps_of term) ~f:(function
    | Term.FunApp (FVar (f, _, _), _, _) -> Ident.tvar_equal f name
    | _ -> false)

let str_of_detection (det : detection) =
  sprintf
    "geometric PLA candidate:\n\
    \  candidate kind: %s\n\
    \  self predicate: %s\n\
    \  exit predicate: %s\n\
    \  exit body: %s\n\
    \  normalized exit body R/p: %s\n\
    \  normalized exit body contains self exit call: %b\n\
    \  guard: %s\n\
    \  residual body: %s\n\
    \  recursive coefficient: %s\n\
    \  exit probability p: %s\n\
    \  recursive update b%s = %s\n\
    \  exit update a%s = %s\n\
    \  required guard-stability condition: %s"
    (if is_unguarded det.guard then "unguarded" else "guarded")
    (Ident.name_of_tvar det.self_pred)
    (Ident.name_of_tvar det.exit_pred)
    (Option.value_map det.exit_body ~default:"none" ~f:Term.str_of)
    (Term.str_of det.normalized_exit_body)
    (term_contains_fvar det.self_pred det.normalized_exit_body)
    (str_of_guard det.guard)
    (str_of_residual_body det.residual_body)
    (q_to_string det.recursive_coeff)
    (q_to_string det.exit_probability)
    (str_of_params det.params)
    (str_of_update det.recursive_update)
    (str_of_params det.params)
    (str_of_update det.exit_update)
    (Formula.str_of
    @@ guard_stability_condition det.params det.recursive_update det.guard)

let str_of_term_list args =
  String.concat_map_list ~sep:", " args ~f:Term.str_of

let term_of_param (x, sort) = Term.mk_var x sort

let str_of_update_map params args =
  String.concat_map_list ~sep:", "
    (List.zip_exn params args)
    ~f:(fun ((x, _), arg) -> sprintf "%s -> %s" (Ident.name_of_tvar x) (Term.str_of arg))

let indent_lines spaces s =
  let padding = String.make spaces ' ' in
  String.concat_map_list ~sep:"\n" (String.split_lines s) ~f:(fun line ->
      padding ^ line)

let str_of_closed_form_status = function
  | ClosedFormGenerated -> "closed form generated"
  | NeedClosedForm -> "closed form not generated"

let str_of_block_reason = function
  | InvalidProbability -> "invalid probability or coefficient"
  | NoClosedForm -> "closed form not generated"
  | GuardStabilityNotChecked -> "guard-stability not checked"
  | GuardStabilityFailed -> "guard-stability failed"
  | UnsupportedUpdate -> "unsupported update"
  | UnsupportedGuard -> "unsupported guard"

let str_of_reasons = function
  | [] -> "none"
  | reasons ->
      sprintf "\n%s"
      @@ String.concat_map_list ~sep:"\n" reasons ~f:(fun reason ->
             sprintf "    - %s" (str_of_block_reason reason))

let str_of_verification_condition = function
  | GuardStability vc ->
      sprintf
        "[guard-stability]\n\
        \    guard: %s\n\
        \    after recursive update: %s\n\
        \    condition: %s"
        (Formula.str_of vc.guard)
        (Formula.str_of vc.guard_after_recursive_update)
        (Formula.str_of vc.condition)

let str_of_verification_conditions = function
  | [] -> "none"
  | vcs ->
      sprintf "\n%s"
      @@ String.concat_map_list ~sep:"\n" vcs
           ~f:(fun vc -> indent_lines 4 @@ str_of_verification_condition vc)

let str_of_geo_body (geo : geo_expectation) =
  match (geo.accelerated_exit_body, geo.accelerated_exit_args) with
  | Some body, _ -> Term.str_of body
  | None, Some args ->
      sprintf "%s(%s)" (Ident.name_of_tvar geo.exit_pred)
        (str_of_term_list args)
  | None, None ->
      sprintf "%s((a o b^k)%s)" (Ident.name_of_tvar geo.exit_pred)
        (str_of_params geo.original_params)

let str_of_accelerated_form (geo : geo_expectation) =
  let lhs =
    sprintf "%s%s" (Ident.name_of_tvar geo.self_pred)
      (str_of_params geo.original_params)
  in
  let expectation =
    sprintf "E_{%s ~ Geo(%s)} [ %s ]" (Ident.name_of_tvar geo.k_var)
      (q_to_string geo.p) (str_of_geo_body geo)
  in
  match geo.guard with
  | None -> sprintf "%s = %s" lhs expectation
  | Some phi ->
      sprintf "%s = if %s then\n    %s\n  else\n    %s" lhs
        (Formula.str_of phi) expectation
        (Option.value_map geo.residual_body ~default:"<unchanged>"
           ~f:Term.str_of)

let str_of_geo_expectation (geo : geo_expectation) =
  sprintf
    "geometric PLA accelerated candidate:\n\
    \  self predicate: %s\n\
    \  exit predicate: %s\n\
    \  exit body: %s\n\
    \  normalized exit body R/p: %s\n\
    \  normalized exit body contains self exit call: %b\n\
    \  guard: %s\n\
    \  residual body: %s\n\
    \  p: %s\n\
    \  recursive coefficient: %s\n\
    \  recursive update: %s\n\
    \  exit update: %s\n\
    \  closed form status: %s\n\
    \  verification conditions: %s\n\
    \  %s"
    (Ident.name_of_tvar geo.self_pred)
    (Ident.name_of_tvar geo.exit_pred)
    (Option.value_map geo.exit_body ~default:"none" ~f:Term.str_of)
    (Term.str_of geo.normalized_exit_body)
    (term_contains_fvar geo.self_pred geo.normalized_exit_body)
    (str_of_guard_option geo.guard)
    (str_of_residual_body geo.residual_body)
    (q_to_string geo.p)
    (q_to_string geo.recursive_coeff)
    (str_of_update_map geo.original_params geo.recursive_update)
    (str_of_update_map geo.original_params geo.exit_update)
    (str_of_closed_form_status geo.status)
    (str_of_verification_conditions geo.verification_conditions)
    (sprintf "accelerated form:\n%s"
       (indent_lines 4 @@ str_of_accelerated_form geo))

let rec rational_of_term = function
  | Term.FunApp (T_real.Real q, [], _) -> Some q
  | Term.FunApp (T_int.Int z, [], _) -> Some (Q.of_string (Z.to_string z))
  | Term.FunApp (T_num.Value (s, _), [], _) -> Common.Timer.try_with_sync (fun () -> Q.of_string s)
  | Term.FunApp ((T_real.RNeg | T_int.Neg | T_num.NNeg _), [ t ], _) ->
      Option.map (rational_of_term t) ~f:Q.neg
  | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _) ->
      Option.map2 (rational_of_term t1) (rational_of_term t2) ~f:Q.add
  | Term.FunApp ((T_real.RSub | T_int.Sub | T_num.NSub _), [ t1; t2 ], _) ->
      Option.map2 (rational_of_term t1) (rational_of_term t2) ~f:Q.sub
  | Term.FunApp ((T_real.RMul | T_int.Mul | T_num.NMul _), [ t1; t2 ], _) ->
      Option.map2 (rational_of_term t1) (rational_of_term t2) ~f:Q.mul
  | Term.FunApp ((T_real.RDiv | T_int.Div _ | T_num.NDiv _), [ t1; t2 ], _) ->
      Option.bind (rational_of_term t2) ~f:(fun q2 ->
          if Q.equal q2 Q.zero then None
          else Option.map (rational_of_term t1) ~f:(fun q1 -> Q.div q1 q2))
  | _ -> None

let rational_zero = Q.zero

let term_as_var_plus_const term =
  let var_const var c =
    match var with
    | Term.Var (x, _, _) -> Some (x, c)
    | _ -> None
  in
  match term with
  | Term.Var _ -> var_const term rational_zero
  | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _) -> (
      match (var_const t1 rational_zero, rational_of_term t2) with
      | Some (x, c1), Some c2 -> Some (x, Q.add c1 c2)
      | _ -> (
          match (var_const t2 rational_zero, rational_of_term t1) with
          | Some (x, c2), Some c1 -> Some (x, Q.add c1 c2)
          | _ -> None))
  | Term.FunApp ((T_real.RSub | T_int.Sub | T_num.NSub _), [ t1; t2 ], _) -> (
      match (var_const t1 rational_zero, rational_of_term t2) with
      | Some (x, c1), Some c2 -> Some (x, Q.sub c1 c2)
      | _ -> None)
  | _ -> None

let lower_bound_terms_of_formula = function
  | Formula.Atom (Atom.App (Predicate.Psym T_real.RGeq, [ lhs; rhs ], _), _) ->
      Some (lhs, rhs, false)
  | Formula.Atom (Atom.App (Predicate.Psym T_real.RGt, [ lhs; rhs ], _), _) ->
      Some (lhs, rhs, true)
  | Formula.Atom (Atom.App (Predicate.Psym T_real.RLeq, [ lhs; rhs ], _), _) ->
      Some (rhs, lhs, false)
  | Formula.Atom (Atom.App (Predicate.Psym T_real.RLt, [ lhs; rhs ], _), _) ->
      Some (rhs, lhs, true)
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Geq, [ lhs; rhs ], _), _) ->
      Some (lhs, rhs, false)
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Gt, [ lhs; rhs ], _), _) ->
      Some (lhs, rhs, true)
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Leq, [ lhs; rhs ], _), _) ->
      Some (rhs, lhs, false)
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Lt, [ lhs; rhs ], _), _) ->
      Some (rhs, lhs, true)
  | Formula.Atom
      (Atom.App (Predicate.Psym (T_num.NGeq _), [ lhs; rhs ], _), _) ->
      Some (lhs, rhs, false)
  | Formula.Atom
      (Atom.App (Predicate.Psym (T_num.NGt _), [ lhs; rhs ], _), _) ->
      Some (lhs, rhs, true)
  | Formula.Atom
      (Atom.App (Predicate.Psym (T_num.NLeq _), [ lhs; rhs ], _), _) ->
      Some (rhs, lhs, false)
  | Formula.Atom
      (Atom.App (Predicate.Psym (T_num.NLt _), [ lhs; rhs ], _), _) ->
      Some (rhs, lhs, true)
  | _ -> None

let rec conjuncts_of_formula phi =
  if Formula.is_and phi then
    let phi1, phi2, _ = Formula.let_and phi in
    conjuncts_of_formula phi1 @ conjuncts_of_formula phi2
  else [ phi ]

let atom_guard_stability guard_conjuncts after =
  if List.exists guard_conjuncts ~f:(fun guard ->
         Stdlib.(Evaluator.simplify guard = Evaluator.simplify after))
  then true
  else
    List.exists guard_conjuncts ~f:(fun guard ->
        match (lower_bound_terms_of_formula guard, lower_bound_terms_of_formula after) with
        | Some (guard_lhs, guard_rhs, guard_strict), Some (after_lhs, after_rhs, after_strict)
          when Stdlib.(guard_rhs = after_rhs) -> (
            match
              (term_as_var_plus_const guard_lhs, term_as_var_plus_const after_lhs)
            with
            | Some (x1, c1), Some (x2, c2)
              when Ident.tvar_equal x1 x2
                   && (Q.(c2 > c1)
                      || (Q.equal c2 c1
                         && (guard_strict || not after_strict))) ->
                true
            | _ -> false)
        | _ -> false)

let syntactically_discharged_guard_stability vc =
  if Formula.is_true @@ Evaluator.simplify vc.condition then true
  else
    let guard_conjuncts = conjuncts_of_formula vc.guard in
    List.for_all (conjuncts_of_formula vc.guard_after_recursive_update)
      ~f:(atom_guard_stability guard_conjuncts)

let probability_reasons geo =
  let expected_recursive_coeff = Q.(one - geo.p) in
  if
    Q.(geo.p > zero)
    && Q.(geo.p <= one)
    && Q.equal geo.recursive_coeff expected_recursive_coeff
  then []
  else [ InvalidProbability ]

let closed_form_reasons geo =
  match (geo.status, geo.accelerated_exit_args, geo.accelerated_exit_body) with
  | ClosedFormGenerated, Some _, _ | ClosedFormGenerated, _, Some _ -> []
  | NeedClosedForm, _, _ -> [ NoClosedForm ]
  | ClosedFormGenerated, None, None -> [ NoClosedForm; UnsupportedUpdate ]

let guard_stability_vcs vcs =
  List.filter_map vcs ~f:(function
    | GuardStability vc -> Some vc)

let guard_reasons geo =
  match geo.guard with
  | None -> []
  | Some _ ->
      if List.is_empty geo.verification_conditions then
        [ GuardStabilityNotChecked ]
      else []

let applicability_of_geo_expectation geo =
  let blocking_reasons =
    List.concat
      [ probability_reasons geo; closed_form_reasons geo; guard_reasons geo ]
  in
  if not (List.is_empty blocking_reasons) then Blocked blocking_reasons
  else
    match geo.guard with
    | None -> Applicable
    | Some _ ->
        let undischarged =
          List.filter geo.verification_conditions ~f:(function
            | GuardStability vc ->
                not (syntactically_discharged_guard_stability vc))
        in
        if List.is_empty undischarged then Applicable
        else ConditionallyApplicable undischarged

let str_of_applicability = function
  | Applicable ->
      "geometric PLA applicability:\n  status: applicable\n  reasons: none"
  | Blocked reasons ->
      sprintf
        "geometric PLA applicability:\n  status: blocked\n  reasons: %s"
        (str_of_reasons reasons)
  | ConditionallyApplicable vcs ->
      let guard_stability =
        guard_stability_vcs vcs
        |> List.map ~f:(fun vc -> Formula.str_of vc.condition)
      in
      sprintf
        "geometric PLA applicability:\n\
        \  status: conditionally applicable\n\
        \  guard-stability:%s\n\
        \  note: guard-stability condition generated but not fully discharged"
        (match guard_stability with
        | [] -> " none"
        | conds ->
            sprintf "\n%s"
            @@ String.concat_map_list ~sep:"\n" conds ~f:(fun cond ->
                   sprintf "    %s" cond))

let str_of_geo_expectation_with_applicability geo =
  sprintf "%s\n%s" (str_of_geo_expectation geo)
    (str_of_applicability @@ applicability_of_geo_expectation geo)

let str_of_geo_expectation_body geo =
  sprintf "E_{%s ~ Geo(%s)} [ %s ]" (Ident.name_of_tvar geo.k_var)
    (q_to_string geo.p) (str_of_geo_body geo)

let str_of_guard_term guard =
  Formula.str_of @@ Formula.of_bool_term guard

let rec str_of_accel_rhs = function
  | Plain term -> Term.str_of term
  | GeoExpectation geo -> str_of_geo_expectation_body geo
  | IfThenElse { guard; then_rhs; else_rhs } ->
      sprintf "if %s then\n%s\nelse\n%s" (str_of_guard_term guard)
        (indent_lines 2 @@ str_of_accel_rhs then_rhs)
        (indent_lines 2 @@ str_of_accel_rhs else_rhs)

let str_of_accel_expr = function
  | TermExpr term -> Term.str_of term
  | GeoExpectationExpr { k_var; p; body } ->
      sprintf "E_{%s ~ Geo(%s)} [ %s ]" (Ident.name_of_tvar k_var)
        (q_to_string p) (Term.str_of body)

let rec str_of_accel_vc = function
  | Inequality { lhs; rhs } ->
      sprintf "%s >= %s" (Term.str_of lhs) (str_of_accel_expr rhs)
  | Imply { cond; vc } ->
      sprintf "%s =>\n%s" (str_of_guard_term cond)
        (indent_lines 2 @@ str_of_accel_vc vc)
  | And vcs -> String.concat_map_list ~sep:"\n\n" vcs ~f:str_of_accel_vc

let str_of_accel_vcs vcs =
  match vcs with
  | [] -> "accelerated prefixpoint VCs:\n  none"
  | _ ->
      sprintf "accelerated prefixpoint VCs:\n%s"
        (indent_lines 2
        @@ String.concat_map_list ~sep:"\n\n" vcs ~f:str_of_accel_vc)

let real_of_q q = T_real.mk_real q

let real_zero () = real_of_q Q.zero

let real_one () = real_of_q Q.one

let real_mul_q q term =
  if Q.equal q Q.zero then real_zero ()
  else if Q.equal q Q.one then term
  else T_real.mk_rmul (real_of_q q) term

let real_add t1 t2 = Evaluator.simplify_term @@ T_real.mk_radd t1 t2

let real_sub t1 t2 = Evaluator.simplify_term @@ T_real.mk_rsub t1 t2

let real_mul t1 t2 = Evaluator.simplify_term @@ T_real.mk_rmul t1 t2

let real_add_q term q =
  if Q.equal q Q.zero then term
  else
    match term_as_var_plus_const term with
    | Some (x, c) ->
        let var = Term.mk_var x T_real.SReal in
        let c = Q.add c q in
        if Q.equal c Q.zero then var
        else if Q.(c > zero) then real_add var (real_of_q c)
        else real_sub var (real_of_q (Q.neg c))
    | None -> real_add term (real_of_q q)

let real_template_coeff template index =
  let name = Ident.name_of_tvar template in
  Term.mk_var (Ident.Tvar (sprintf "a_%s_%d" name index)) T_real.SReal

let real_template_const template =
  let name = Ident.name_of_tvar template in
  Term.mk_var (Ident.Tvar ("b_" ^ name)) T_real.SReal

let linear_template_term template args =
  let weighted_args =
    List.mapi args ~f:(fun i arg ->
        real_mul (real_template_coeff template (i + 1)) arg)
  in
  List.fold weighted_args ~init:(real_template_const template) ~f:real_add

let is_template_name name = String.is_prefix (Ident.name_of_tvar name) ~prefix:"T"

let template_app_of_term = function
  | Term.FunApp (FVar (name, _, _), args, _) when is_template_name name ->
      Some (name, args)
  | _ -> None

let lower_template_calls_linear term =
  Term.map_term true term ~f:(fun term ->
      match template_app_of_term term with
      | Some (name, args) -> linear_template_term name args
      | None -> term)

let term_contains_var var term = Set.mem (Term.fvs_of term) var

let rec affine_in_k k_var term =
  if not (term_contains_var k_var term) then Some (term, Q.zero)
  else
    match term with
    | Term.Var (x, _, _) when Ident.tvar_equal x k_var ->
        Some (real_zero (), Q.one)
    | Term.FunApp ((T_real.RAdd | T_num.NAdd _), [ t1; t2 ], _) ->
        Option.map2 (affine_in_k k_var t1) (affine_in_k k_var t2)
          ~f:(fun (base1, coeff1) (base2, coeff2) ->
            (real_add base1 base2, Q.add coeff1 coeff2))
    | Term.FunApp ((T_real.RSub | T_num.NSub _), [ t1; t2 ], _) ->
        Option.map2 (affine_in_k k_var t1) (affine_in_k k_var t2)
          ~f:(fun (base1, coeff1) (base2, coeff2) ->
            (real_sub base1 base2, Q.sub coeff1 coeff2))
    | Term.FunApp ((T_real.RNeg | T_num.NNeg _), [ t ], _) ->
        Option.map (affine_in_k k_var t) ~f:(fun (base, coeff) ->
            (real_mul_q Q.minus_one base, Q.neg coeff))
    | Term.FunApp ((T_real.RMul | T_num.NMul _), [ t1; t2 ], _) -> (
        match (rational_of_term t1, affine_in_k k_var t2) with
        | Some q, Some (base, coeff) ->
            Some (real_mul_q q base, Q.mul q coeff)
        | _ -> (
            match (rational_of_term t2, affine_in_k k_var t1) with
            | Some q, Some (base, coeff) ->
                Some (real_mul_q q base, Q.mul q coeff)
            | _ -> None))
    | Term.FunApp ((T_real.RDiv | T_num.NDiv _), [ t1; t2 ], _) -> (
        match (affine_in_k k_var t1, rational_of_term t2) with
        | Some (base, coeff), Some q when not (Q.equal q Q.zero) ->
            Some (real_mul_q (Q.inv q) base, Q.div coeff q)
        | _ -> None)
    | _ -> None

let lower_geo_expectation_linear ~k_var ~p body =
  match template_app_of_term body with
  | None -> None
  | Some (template, args) ->
      Option.map (Option.all @@ List.map args ~f:(affine_in_k k_var))
        ~f:(fun affine_args ->
          let expected_k = Q.div Q.(one - p) p in
          let expected_args =
            List.map affine_args ~f:(fun (base, coeff) ->
                real_add_q base (Q.mul coeff expected_k))
          in
          linear_template_term template expected_args)

(** Eliminates an affine geometric expectation using [E[k] = (1-p)/p]. *)
let lower_affine_geo_expectation_term ~k_var ~p body =
  Option.map (affine_in_k k_var body) ~f:(fun (base, coeff) ->
      let expected_k = Q.div Q.(one - p) p in
      real_add_q base (Q.mul coeff expected_k))

let lower_accel_expr_linear = function
  | TermExpr term -> Some (lower_template_calls_linear term)
  | GeoExpectationExpr { k_var; p; body } ->
      lower_geo_expectation_linear ~k_var ~p body

let rec lower_accel_vc_linear = function
  | Inequality { lhs; rhs } as vc -> (
      match lower_accel_expr_linear rhs with
      | Some rhs ->
          Lowered
            (Inequality
            {
              lhs = lower_template_calls_linear lhs;
              rhs = TermExpr rhs;
            })
      | None -> NotLowered ("unsupported GeoExpectation lowering", vc))
  | Imply { cond; vc } -> (
      match lower_accel_vc_linear vc with
      | Lowered vc -> Lowered (Imply { cond; vc })
      | NotLowered (reason, vc) -> NotLowered (reason, Imply { cond; vc }))
  | And vcs ->
      let lowered = List.map vcs ~f:lower_accel_vc_linear in
      let reasons, vcs =
        List.fold_right lowered ~init:([], []) ~f:(fun lowered (reasons, vcs) ->
            match lowered with
            | Lowered vc -> (reasons, vc :: vcs)
            | NotLowered (reason, vc) -> (reason :: reasons, vc :: vcs))
      in
      if List.is_empty reasons then Lowered (And vcs)
      else NotLowered (String.concat ~sep:"; " reasons, And vcs)

let lower_accel_vcs_linear vcs = List.map vcs ~f:lower_accel_vc_linear

let str_of_lowered_accel_vc = function
  | Lowered vc -> str_of_accel_vc vc
  | NotLowered (reason, vc) ->
      sprintf "not lowered (%s):\n%s" reason (indent_lines 2 @@ str_of_accel_vc vc)

let str_of_lowered_accel_vcs vcs =
  match vcs with
  | [] -> "single linear template lowering:\n  none"
  | _ ->
      sprintf
        "multi-argument linear template lowering:\n\
        \  assumption: each template TX(z1, ..., zn) has the form\n\
        \    a_TX_1 * z1 + ... + a_TX_n * zn + b_TX\n\
        \  TODO: for piecewise linear templates, if g(x,k) stays in one partition,\n\
        \    lower that partition as a single linear template; if it crosses\n\
        \    partitions, split the infinite geometric sum by the corresponding k ranges.\n%s"
        (indent_lines 2
        @@ String.concat_map_list ~sep:"\n\n" vcs ~f:str_of_lowered_accel_vc)

let template_name name = Ident.Tvar ("T" ^ Ident.name_of_tvar name)

let template_env_of_accel_problem config accel_problem =
  let templ_paramss, templ_preds =
    List.unzip
    @@ List.map accel_problem.preds ~f:(fun pred ->
           let original_pred = pred.original_pred in
           let template =
             Templ.gen_quant_template ~num_conds:config.num_conds
               ~use_orig_ite:config.use_orig_ite
               ~cond_degree:config.cond_degree ~term_degree:config.term_degree
               original_pred.args original_pred.body original_pred.annots
           in
           ( template.templ_params,
             (original_pred.name, (original_pred.args, template.quant_pred)) ))
  in
  let templ_aliases =
    List.concat_map templ_preds ~f:(fun (name, templ) ->
        [ (name, templ); (template_name name, templ) ])
  in
  {
    templ_params = Map.force_merge_list templ_paramss;
    templ_preds;
    templ_subst = Map.Poly.of_alist_exn templ_aliases;
  }

let template_env_of_prefp_templates templ_params templ_preds =
  let templ_aliases =
    List.concat_map templ_preds ~f:(fun (name, templ) ->
        [ (name, templ); (template_name name, templ) ])
  in
  {
    templ_params;
    templ_preds;
    templ_subst = Map.Poly.of_alist_exn templ_aliases;
  }

let str_of_template_env template_env =
  sprintf "accelerated VC template env:\n%s"
  @@ indent_lines 2
  @@ String.concat_map_list ~sep:"\n" template_env.templ_preds
       ~f:(fun (name, (args, body)) ->
         sprintf "%s %s |-> %s" (Ident.name_of_tvar name)
           (str_of_sort_env_list Term.str_of_sort args)
           (Term.str_of body))

let real_div t1 t2 = Evaluator.simplify_term @@ T_real.mk_rdiv t1 t2

let real_expectation_of_affine ~p base coeff =
  real_add base (real_mul coeff (real_of_q (Q.div Q.(one - p) p)))

let rec affine_term_in_k k_var term =
  if not (term_contains_var k_var term) then
    Some (term, real_zero ())
  else
    match term with
    | Term.Var (x, _, _) when Ident.tvar_equal x k_var ->
        Some (real_zero (), real_of_q Q.one)
    | Term.FunApp ((T_real.RAdd | T_num.NAdd _), [ t1; t2 ], _) ->
        Option.map2 (affine_term_in_k k_var t1) (affine_term_in_k k_var t2)
          ~f:(fun (base1, coeff1) (base2, coeff2) ->
            (real_add base1 base2, real_add coeff1 coeff2))
    | Term.FunApp ((T_real.RSub | T_num.NSub _), [ t1; t2 ], _) ->
        Option.map2 (affine_term_in_k k_var t1) (affine_term_in_k k_var t2)
          ~f:(fun (base1, coeff1) (base2, coeff2) ->
            (real_sub base1 base2, real_sub coeff1 coeff2))
    | Term.FunApp ((T_real.RNeg | T_num.NNeg _), [ t ], _) ->
        Option.map (affine_term_in_k k_var t) ~f:(fun (base, coeff) ->
            (real_mul_q Q.minus_one base, real_mul_q Q.minus_one coeff))
    | Term.FunApp ((T_real.RMul | T_num.NMul _), [ t1; t2 ], _) -> (
        match (term_contains_var k_var t1, term_contains_var k_var t2) with
        | false, true ->
            Option.map (affine_term_in_k k_var t2) ~f:(fun (base, coeff) ->
                (real_mul t1 base, real_mul t1 coeff))
        | true, false ->
            Option.map (affine_term_in_k k_var t1) ~f:(fun (base, coeff) ->
                (real_mul base t2, real_mul coeff t2))
        | _ -> None)
    | Term.FunApp ((T_real.RDiv | T_num.NDiv _), [ t1; t2 ], _)
      when not (term_contains_var k_var t2) ->
        Option.map (affine_term_in_k k_var t1) ~f:(fun (base, coeff) ->
            (real_div base t2, real_div coeff t2))
    | _ -> None

type comparison = GeqZero | GtZero | LtZero | LeqZero

type linear = { const : Q.t; coeffs : (Ident.tvar * Q.t) list }

let zero_linear = { const = Q.zero; coeffs = [] }

let add_coeff coeffs x q =
  if Q.equal q Q.zero then coeffs
  else
    Map.Poly.to_alist
    @@ Map.update
         (Map.Poly.of_alist_fold coeffs ~init:Q.zero ~f:Q.add)
         x ~f:(function None -> q | Some old -> Q.add old q)

let add_linear l1 l2 =
  {
    const = Q.add l1.const l2.const;
    coeffs = List.fold l2.coeffs ~init:l1.coeffs ~f:(fun acc (x, q) ->
        add_coeff acc x q);
  }

let mul_linear q l =
  {
    const = Q.mul q l.const;
    coeffs = List.filter_map l.coeffs ~f:(fun (x, coeff) ->
        let coeff = Q.mul q coeff in
        if Q.equal coeff Q.zero then None else Some (x, coeff));
  }

let sub_linear l1 l2 = add_linear l1 (mul_linear Q.minus_one l2)

let rec linear_of_term = function
  | term when Option.is_some (rational_of_term term) ->
      Some { zero_linear with const = Option.value_exn (rational_of_term term) }
  | Term.Var (x, _, _) -> Some { zero_linear with coeffs = [ (x, Q.one) ] }
  | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _) ->
      Option.map2 (linear_of_term t1) (linear_of_term t2) ~f:add_linear
  | Term.FunApp ((T_real.RSub | T_int.Sub | T_num.NSub _), [ t1; t2 ], _) ->
      Option.map2 (linear_of_term t1) (linear_of_term t2) ~f:sub_linear
  | Term.FunApp ((T_real.RNeg | T_int.Neg | T_num.NNeg _), [ t ], _) ->
      Option.map (linear_of_term t) ~f:(mul_linear Q.minus_one)
  | Term.FunApp ((T_real.RMul | T_int.Mul | T_num.NMul _), [ t1; t2 ], _) -> (
      match (rational_of_term t1, linear_of_term t2) with
      | Some q, Some l -> Some (mul_linear q l)
      | _ -> (
          match (rational_of_term t2, linear_of_term t1) with
          | Some q, Some l -> Some (mul_linear q l)
          | _ -> None))
  | Term.FunApp ((T_real.RDiv | T_num.NDiv _), [ t1; t2 ], _) -> (
      match (linear_of_term t1, rational_of_term t2) with
      | Some l, Some q when not (Q.equal q Q.zero) ->
          Some (mul_linear (Q.inv q) l)
      | _ -> None)
  | _ -> None

let linear_of_diff lhs rhs =
  Option.map2 (linear_of_term lhs) (linear_of_term rhs) ~f:sub_linear

let comparison_of_formula = function
  | Formula.Atom (Atom.App (Predicate.Psym T_real.RGeq, [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff lhs rhs) ~f:(fun lin -> (GeqZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym T_real.RGt, [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff lhs rhs) ~f:(fun lin -> (GtZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym T_real.RLeq, [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff rhs lhs) ~f:(fun lin -> (GeqZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym T_real.RLt, [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff rhs lhs) ~f:(fun lin -> (GtZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Geq, [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff lhs rhs) ~f:(fun lin -> (GeqZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Gt, [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff lhs rhs) ~f:(fun lin -> (GtZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Leq, [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff rhs lhs) ~f:(fun lin -> (GeqZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym T_int.Lt, [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff rhs lhs) ~f:(fun lin -> (GtZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym (T_num.NGeq _), [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff lhs rhs) ~f:(fun lin -> (GeqZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym (T_num.NGt _), [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff lhs rhs) ~f:(fun lin -> (GtZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym (T_num.NLeq _), [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff rhs lhs) ~f:(fun lin -> (GeqZero, lin))
  | Formula.Atom (Atom.App (Predicate.Psym (T_num.NLt _), [ lhs; rhs ], _), _) ->
      Option.map (linear_of_diff rhs lhs) ~f:(fun lin -> (GtZero, lin))
  | _ -> None

let comparison_of_bool_term term =
  comparison_of_formula
  @@ Evaluator.simplify
  @@ Normalizer.normalize
  @@ Formula.of_bool_term term

let invert_comparison = function
  | GeqZero -> LtZero
  | GtZero -> LeqZero
  | LtZero -> GeqZero
  | LeqZero -> GtZero

type bounds = {
  lower : (Ident.tvar, Q.t) Map.Poly.t;
  upper : (Ident.tvar, Q.t) Map.Poly.t;
}

let empty_bounds = { lower = Map.Poly.empty; upper = Map.Poly.empty }

let update_bound map key value ~better =
  Map.update map key ~f:(function
    | None -> value
    | Some old -> if better value old then value else old)

let bound_of_single_var lin =
  match lin.coeffs with
  | [ (x, coeff) ] when not (Q.equal coeff Q.zero) ->
      Some (x, Q.div (Q.neg lin.const) coeff, Q.(coeff > zero))
  | _ -> None

let add_path_comparison bounds (cmp, lin) =
  match bound_of_single_var lin with
  | None -> bounds
  | Some (x, bound, positive_coeff) -> (
      match (cmp, positive_coeff) with
      | (GeqZero | GtZero), true ->
          {
            bounds with
            lower = update_bound bounds.lower x bound ~better:Q.( > );
          }
      | (GeqZero | GtZero), false ->
          {
            bounds with
            upper = update_bound bounds.upper x bound ~better:Q.( < );
          }
      | (LtZero | LeqZero), true ->
          {
            bounds with
            upper = update_bound bounds.upper x bound ~better:Q.( < );
          }
      | (LtZero | LeqZero), false ->
          {
            bounds with
            lower = update_bound bounds.lower x bound ~better:Q.( > );
          })

let bounds_of_path path =
  List.fold path ~init:empty_bounds ~f:(fun bounds cond ->
      match comparison_of_bool_term cond with
      | Some cmp -> add_path_comparison bounds cmp
      | None -> bounds)

let lower_bound_of_linear bounds k_var lin =
  List.fold_until lin.coeffs ~init:(Some lin.const)
    ~f:(fun acc (x, coeff) ->
      match acc with
      | None -> Stop None
      | Some acc when Q.equal coeff Q.zero -> Continue (Some acc)
      | Some acc when Ident.tvar_equal x k_var && Q.(coeff >= zero) ->
          Continue (Some acc)
      | Some acc when Q.(coeff > zero) -> (
          match Map.find bounds.lower x with
          | Some lower -> Continue (Some Q.(acc + (coeff * lower)))
          | None -> Stop None)
      | Some acc when Q.(coeff < zero) -> (
          match Map.find bounds.upper x with
          | Some upper -> Continue (Some Q.(acc + (coeff * upper)))
          | None -> Stop None)
      | Some _ -> Stop None)
    ~finish:Fn.id

let upper_bound_of_linear bounds k_var lin =
  List.fold_until lin.coeffs ~init:(Some lin.const)
    ~f:(fun acc (x, coeff) ->
      match acc with
      | None -> Stop None
      | Some acc when Q.equal coeff Q.zero -> Continue (Some acc)
      | Some _ when Ident.tvar_equal x k_var && Q.(coeff > zero) -> Stop None
      | Some acc when Ident.tvar_equal x k_var && Q.(coeff <= zero) ->
          Continue (Some acc)
      | Some acc when Q.(coeff > zero) -> (
          match Map.find bounds.upper x with
          | Some upper -> Continue (Some Q.(acc + (coeff * upper)))
          | None -> Stop None)
      | Some acc when Q.(coeff < zero) -> (
          match Map.find bounds.lower x with
          | Some lower -> Continue (Some Q.(acc + (coeff * lower)))
          | None -> Stop None)
      | Some _ -> Stop None)
    ~finish:Fn.id

let prove_comparison bounds k_var (cmp, lin) =
  match cmp with
  | GeqZero ->
      Option.exists (lower_bound_of_linear bounds k_var lin) ~f:(fun lower ->
          Q.(lower >= zero))
  | GtZero ->
      Option.exists (lower_bound_of_linear bounds k_var lin) ~f:(fun lower ->
          Q.(lower > zero))
  | LtZero ->
      Option.exists (upper_bound_of_linear bounds k_var lin) ~f:(fun upper ->
          Q.(upper < zero))
  | LeqZero ->
      Option.exists (upper_bound_of_linear bounds k_var lin) ~f:(fun upper ->
          Q.(upper <= zero))

type strict_bound = { value : Q.t; strict : bool }

type strict_bounds = {
  strict_lower : (Ident.tvar, strict_bound) Map.Poly.t;
  strict_upper : (Ident.tvar, strict_bound) Map.Poly.t;
}

let empty_strict_bounds =
  { strict_lower = Map.Poly.empty; strict_upper = Map.Poly.empty }

let better_lower_bound candidate current =
  Q.(candidate.value > current.value)
  || (Q.equal candidate.value current.value && candidate.strict
     && not current.strict)

let better_upper_bound candidate current =
  Q.(candidate.value < current.value)
  || (Q.equal candidate.value current.value && candidate.strict
     && not current.strict)

let update_strict_bound map key value ~better =
  Map.update map key ~f:(function
    | None -> value
    | Some old -> if better value old then value else old)

let add_strict_path_comparison bounds (cmp, lin) =
  match bound_of_single_var lin with
  | None -> bounds
  | Some (x, value, positive_coeff) -> (
      let lower strict =
        {
          bounds with
          strict_lower =
            update_strict_bound bounds.strict_lower x { value; strict }
              ~better:better_lower_bound;
        }
      in
      let upper strict =
        {
          bounds with
          strict_upper =
            update_strict_bound bounds.strict_upper x { value; strict }
              ~better:better_upper_bound;
        }
      in
      match (cmp, positive_coeff) with
      | GeqZero, true -> lower false
      | GtZero, true -> lower true
      | GeqZero, false -> upper false
      | GtZero, false -> upper true
      | LeqZero, true -> upper false
      | LtZero, true -> upper true
      | LeqZero, false -> lower false
      | LtZero, false -> lower true)

let strict_bounds_of_path path =
  List.fold path ~init:empty_strict_bounds ~f:(fun bounds cond ->
      match comparison_of_bool_term cond with
      | Some cmp -> add_strict_path_comparison bounds cmp
      | None -> bounds)

let add_strict_q_bound acc coeff bound =
  {
    value = Q.(acc.value + (coeff * bound.value));
    strict = acc.strict || bound.strict;
  }

let strict_lower_bound_of_linear bounds _k_var lin =
  List.fold_until lin.coeffs ~init:(Some { value = lin.const; strict = false })
    ~f:(fun acc (x, coeff) ->
      match acc with
      | None -> Stop None
      | Some acc when Q.equal coeff Q.zero -> Continue (Some acc)
      | Some acc when Q.(coeff > zero) -> (
          match Map.find bounds.strict_lower x with
          | Some lower -> Continue (Some (add_strict_q_bound acc coeff lower))
          | None -> Stop None)
      | Some acc when Q.(coeff < zero) -> (
          match Map.find bounds.strict_upper x with
          | Some upper -> Continue (Some (add_strict_q_bound acc coeff upper))
          | None -> Stop None)
      | Some _ -> Stop None)
    ~finish:Fn.id

let strict_upper_bound_of_linear bounds _k_var lin =
  List.fold_until lin.coeffs ~init:(Some { value = lin.const; strict = false })
    ~f:(fun acc (x, coeff) ->
      match acc with
      | None -> Stop None
      | Some acc when Q.equal coeff Q.zero -> Continue (Some acc)
      | Some acc when Q.(coeff > zero) -> (
          match Map.find bounds.strict_upper x with
          | Some upper -> Continue (Some (add_strict_q_bound acc coeff upper))
          | None -> Stop None)
      | Some acc when Q.(coeff < zero) -> (
          match Map.find bounds.strict_lower x with
          | Some lower -> Continue (Some (add_strict_q_bound acc coeff lower))
          | None -> Stop None)
      | Some _ -> Stop None)
    ~finish:Fn.id

let strictly_positive bound =
  Q.(bound.value > zero) || (Q.equal bound.value Q.zero && bound.strict)

let strictly_negative bound =
  Q.(bound.value < zero) || (Q.equal bound.value Q.zero && bound.strict)

let prove_comparison_strict bounds k_var (cmp, lin) =
  match cmp with
  | GeqZero ->
      Option.exists (strict_lower_bound_of_linear bounds k_var lin) ~f:(fun b ->
          Q.(b.value >= zero))
  | GtZero ->
      Option.exists (strict_lower_bound_of_linear bounds k_var lin)
        ~f:strictly_positive
  | LtZero ->
      Option.exists (strict_upper_bound_of_linear bounds k_var lin)
        ~f:strictly_negative
  | LeqZero ->
      Option.exists (strict_upper_bound_of_linear bounds k_var lin) ~f:(fun b ->
          Q.(b.value <= zero))

let str_of_path_condition path =
  match path with
  | [] -> "true"
  | _ ->
      String.concat_map_list ~sep:" /\\ " (List.rev path) ~f:(fun cond ->
          Formula.str_of @@ Formula.of_bool_term cond)

let branch_log path cond selected reason =
  sprintf
    "GeoExpectation ITE branch selection:\n\
    \  path condition: %s\n\
    \  template branch condition: %s\n\
    \  selected branch: %s%s"
    (str_of_path_condition path)
    (Formula.str_of @@ Formula.of_bool_term cond)
    selected
    (match reason with None -> "" | Some reason -> "\n  reason: " ^ reason)

type geo_lowering = GeoLowered of Term.t * string list | GeoUnsupported of string

type upper_case = { region : Formula.t option; upper : Term.t }

type upper_geo_result =
  | UpperGeoBranchFixed of upper_case list * string list
  | UpperGeoFinitePrefixTail of upper_case list * string list
  | UpperGeoUnsupported of string

type iverson_case = {
  case_guard : Term.t list;
  case_body : Term.t;
}

type crossing_branch_order = PrefixThenTailElse | PrefixElseTailThen

type crossing_info = {
  crossing_var : Ident.tvar;
  crossing_bound : int;
  branch_order : crossing_branch_order;
  strict_tail_boundary : bool;
}

let rec select_ite_branches path k_var term =
  match term with
  | Term.FunApp (T_bool.IfThenElse, [ cond; then_; else_ ], _) -> (
      match comparison_of_bool_term cond with
      | None ->
          GeoUnsupported
            (branch_log path cond "unknown"
               (Some "unsupported branch condition"))
      | Some ((cmp_kind, lin) as cmp) ->
          let bounds = bounds_of_path path in
          if prove_comparison bounds k_var cmp then
            match select_ite_branches path k_var then_ with
            | GeoLowered (term, logs) ->
                GeoLowered
                  (term, branch_log path cond "then" None :: logs)
            | GeoUnsupported reason -> GeoUnsupported reason
          else if
            prove_comparison bounds k_var (invert_comparison cmp_kind, lin)
          then
            match select_ite_branches path k_var else_ with
            | GeoLowered (term, logs) ->
                GeoLowered
                  (term, branch_log path cond "else" None :: logs)
            | GeoUnsupported reason -> GeoUnsupported reason
          else
            GeoUnsupported
              (branch_log path cond "unknown"
                 (Some "may cross partitions")))
  | term -> GeoLowered (term, [])

let neg_bool_term cond =
  T_bool.of_formula @@ Formula.mk_neg @@ Formula.of_bool_term cond

let rec iverson_cases_of_ite ?(guard = []) term =
  match term with
  | Term.FunApp (T_bool.IfThenElse, [ cond; then_; else_ ], _) ->
      iverson_cases_of_ite ~guard:(cond :: guard) then_
      @ iverson_cases_of_ite ~guard:(neg_bool_term cond :: guard) else_
  | case_body -> [ { case_guard = List.rev guard; case_body } ]

let str_of_iverson_case { case_guard; case_body } =
  sprintf "[%s] * %s" (str_of_path_condition case_guard) (Term.str_of case_body)

let str_of_iverson_cases cases =
  sprintf
    "GeoExpectation template ITE normal form:\n\
    \  representation: sum of Iverson cases [guard] * body\n%s"
    (String.concat_map_list ~sep:"\n" cases ~f:(fun case ->
         sprintf "  - %s" (str_of_iverson_case case)))

let flatten_bool_path path =
  List.concat_map path ~f:(fun cond ->
      Formula.of_bool_term cond
      |> conjuncts_of_formula
      |> List.map ~f:T_bool.of_formula)

let coeff_map_of_linear lin =
  Map.Poly.of_alist_fold lin.coeffs ~init:Q.zero ~f:Q.add

let positive_int_of_q q =
  if Q.(q > zero) && Z.equal (Q.den q) Z.one then
    Common.Timer.try_with_sync (fun () -> Int.of_string @@ Z.to_string @@ Q.num q)
  else None

let crossing_info_of_condition path k_var cond =
  match comparison_of_bool_term cond with
  | Some (cmp, lin) -> (
      let coeffs = coeff_map_of_linear lin in
      let k_coeff = Map.find coeffs k_var |> Option.value ~default:Q.zero in
      let crossing_shape =
        match (cmp, Q.sign k_coeff) with
        | GtZero, 1 -> Some (lin, PrefixElseTailThen, true)
        | GeqZero, 1 -> Some (lin, PrefixElseTailThen, false)
        | GtZero, -1 -> Some (mul_linear Q.minus_one lin, PrefixThenTailElse, false)
        | GeqZero, -1 -> Some (mul_linear Q.minus_one lin, PrefixThenTailElse, true)
        | _ -> None
      in
      match crossing_shape with
      | Some (lin, branch_order, strict_tail_boundary) ->
        let coeffs = coeff_map_of_linear lin in
        let non_k =
          Map.to_alist coeffs
          |> List.filter ~f:(fun (x, q) ->
                 (not (Ident.tvar_equal x k_var)) && not (Q.equal q Q.zero))
        in
        (match non_k with
        | [ (x, q) ] when Q.equal q Q.one ->
            let bounds = bounds_of_path path in
            let nonnegative_path =
              Option.value_map (Map.find bounds.lower x) ~default:false
                ~f:(fun lower -> Q.(lower >= zero))
            in
            if nonnegative_path then
              Option.map (positive_int_of_q Q.(-lin.const)) ~f:(fun n ->
                  {
                    crossing_var = x;
                    crossing_bound = n;
                    branch_order;
                    strict_tail_boundary;
                  })
            else None
        | _ -> None)
      | None -> None
      )
  | _ -> None

let subst_var x term body = Term.subst (Map.Poly.singleton x term) body

let q_pow q n =
  List.fold (List.init n ~f:Fn.id) ~init:Q.one ~f:(fun acc _ ->
      Q.mul acc q)

let factorial n =
  List.fold (List.init n ~f:Fn.id) ~init:Z.one ~f:(fun acc i ->
      Z.mul acc (Z.of_int (i + 1)))

let stirling_second n k =
  let memo = Hashtbl.Poly.create () in
  let rec aux n k =
    match Hashtbl.find memo (n, k) with
    | Some value -> value
    | None ->
        let value =
          if n = 0 && k = 0 then Z.one
          else if n = 0 || k = 0 || k > n then Z.zero
          else
            Z.add (Z.mul (Z.of_int k) (aux (n - 1) k)) (aux (n - 1) (k - 1))
        in
        Hashtbl.set memo ~key:(n, k) ~data:value;
        value
  in
  if n < 0 || k < 0 then Z.zero else aux n k

let geo_raw_moment ~p ~degree =
  if degree < 0 || Q.equal p Q.zero then None
  else
    let q_over_p = Q.((one - p) / p) in
    Some
      (List.fold (List.init (degree + 1) ~f:Fn.id) ~init:Q.zero
         ~f:(fun acc j ->
           let stirling = stirling_second degree j in
           if Z.equal stirling Z.zero then acc
           else
             Q.(
               acc
               + (of_bigint stirling * of_bigint (factorial j) * q_pow q_over_p j))))

let sum_real_terms = function
  | [] -> real_zero ()
  | term :: terms -> List.fold terms ~init:term ~f:real_add

let mk_interval_region x i =
  let x_term = Term.mk_var x T_real.SReal in
  let lower = real_of_q @@ Q.of_int i in
  let upper = real_of_q @@ Q.of_int (i + 1) in
  Formula.and_of [ Formula.leq lower x_term; Formula.lt x_term upper ]

let mk_geq_region x n =
  Formula.leq (real_of_q @@ Q.of_int n) (Term.mk_var x T_real.SReal)

let mk_gt_region x n =
  Formula.lt (real_of_q @@ Q.of_int n) (Term.mk_var x T_real.SReal)

let mk_eq_region x n =
  let x_term = Term.mk_var x T_real.SReal in
  let n_term = real_of_q @@ Q.of_int n in
  Formula.and_of [ Formula.leq n_term x_term; Formula.leq x_term n_term ]

let lower_affine_expectation ~k_var ~p body =
  Option.map (affine_term_in_k k_var body) ~f:(fun (base, coeff) ->
      real_expectation_of_affine ~p base coeff)

let is_k_var k_var = function
  | Term.Var (x, _, _) -> Ident.tvar_equal x k_var
  | _ -> false

let real_term_of_monomial monomial =
  if Map.Poly.is_empty monomial then real_one () else PolyTerm.real_prod monomial

let lower_monomial_expectation ~k_var ~p monomial coeff =
  let k_degree, rest, unsupported =
    Map.Poly.fold monomial ~init:(0, Map.Poly.empty, false)
      ~f:(fun ~key:term ~data:degree (k_degree, rest, unsupported) ->
        if unsupported then (k_degree, rest, unsupported)
        else if is_k_var k_var term then (k_degree + degree, rest, false)
        else if term_contains_var k_var term then (k_degree, rest, true)
        else (k_degree, Map.Poly.set rest ~key:term ~data:degree, false))
  in
  if unsupported then None
  else
    Option.map (geo_raw_moment ~p ~degree:k_degree) ~f:(fun moment ->
        real_mul_q Q.(Value.real_of coeff * moment)
          (real_term_of_monomial rest))

let lower_expectation_of_fixed_branch ~k_var ~p body =
  Common.Timer.try_with_sync (fun () ->
      Normalizer.real_monomials_of (Value.Real Q.one) body
      |> PolyTerm.real_simplify)
  |> Option.bind ~f:(fun monomials ->
         Map.Poly.to_alist monomials
         |> List.map ~f:(fun (monomial, coeff) ->
                lower_monomial_expectation ~k_var ~p monomial coeff)
         |> Option.all
         |> Option.map ~f:sum_real_terms)

let simplify_formula phi = Evaluator.simplify @@ Normalizer.normalize phi

let imply_antecedents antecedents concl =
  match antecedents with
  | [] -> [ concl ]
  | _ ->
      let antecedent = simplify_formula @@ Formula.and_of @@ List.rev antecedents in
      if Formula.is_false antecedent then []
      else if Formula.is_true antecedent then [ concl ]
      else [ Formula.mk_imply antecedent concl ]

let rec geq_formulas_with_lhs_ite ?(antecedents = []) lhs rhs =
  match lhs with
  | Term.FunApp (T_bool.IfThenElse, [ cond; then_; else_ ], _) ->
      let cond = Formula.of_bool_term cond in
      geq_formulas_with_lhs_ite ~antecedents:(cond :: antecedents) then_
        rhs
      @ geq_formulas_with_lhs_ite
          ~antecedents:(Formula.mk_neg cond :: antecedents)
          else_ rhs
  | lhs -> imply_antecedents antecedents (Formula.geq lhs rhs)

let template_nonnegative_formulas quant_pred =
  geq_formulas_with_lhs_ite quant_pred (T_real.rzero ())

let formulas_of_upper_cases ?(antecedents = []) lhs cases =
  List.concat_map cases ~f:(fun { region; upper } ->
      let antecedents =
        match region with
        | None -> antecedents
        | Some region -> region :: antecedents
      in
      geq_formulas_with_lhs_ite ~antecedents lhs upper)

let rec geq_formulas_with_rhs_ite ?(antecedents = []) lhs rhs =
  match rhs with
  | Term.FunApp (T_bool.IfThenElse, [ cond; then_; else_ ], _) ->
      let cond = Formula.of_bool_term cond in
      geq_formulas_with_rhs_ite ~antecedents:(cond :: antecedents) lhs then_
      @ geq_formulas_with_rhs_ite
          ~antecedents:(Formula.mk_neg cond :: antecedents)
          lhs else_
  | rhs -> imply_antecedents antecedents (Formula.geq lhs rhs)

let formulas_of_lower_cases ?(antecedents = []) lhs cases =
  List.concat_map cases ~f:(fun { region; upper } ->
      let antecedents =
        match region with
        | None -> antecedents
        | Some region -> region :: antecedents
      in
      geq_formulas_with_rhs_ite ~antecedents upper lhs)

let crossing_prefix_rhs ~k_var ~p ~m ~prefix_branch ~tail_branch =
  let q = Q.(one - p) in
  let prefix_terms =
    List.init m ~f:(fun j ->
        let weight = Q.(p * q_pow q j) in
        let branch =
          subst_var k_var (real_of_q @@ Q.of_int j) prefix_branch
        in
        real_mul (real_of_q weight) branch)
  in
  let tail_body =
    subst_var k_var
      (real_add (Term.mk_var k_var T_real.SReal) (real_of_q @@ Q.of_int m))
      tail_branch
  in
  Option.map
    (lower_expectation_of_fixed_branch ~k_var ~p tail_body)
    ~f:(fun tail ->
      real_add (sum_real_terms prefix_terms)
        (real_mul (real_of_q @@ q_pow q m) tail))

let crossing_case_rhs ~k_var ~p ~m ~branch_order then_ else_ =
  match branch_order with
  | PrefixThenTailElse ->
      crossing_prefix_rhs ~k_var ~p ~m ~prefix_branch:then_
        ~tail_branch:else_
  | PrefixElseTailThen ->
      crossing_prefix_rhs ~k_var ~p ~m ~prefix_branch:else_
        ~tail_branch:then_

let crossing_tail_branch branch_order then_ else_ =
  match branch_order with
  | PrefixThenTailElse -> else_
  | PrefixElseTailThen -> then_

type tail_stability =
  | TailStableTrue of int
  | TailStableFalse of int
  | TailStabilityUnknown of string list

let tail_stability_kmax = 8

let nonzero_k_coefficient k_var lin =
  let coeffs = coeff_map_of_linear lin in
  match Map.find coeffs k_var with
  | Some coeff when not (Q.equal coeff Q.zero) -> true
  | _ -> false

let k_geq_term k_var k =
  T_bool.of_formula
  @@ Formula.leq (real_of_q @@ Q.of_int k) (Term.mk_var k_var T_real.SReal)

let prove_tail_implication_at_k ~path ~k_var ~k cond =
  match comparison_of_bool_term cond with
  | None -> TailStabilityUnknown [ "unsupported guard shape" ]
  | Some (cmp_kind, lin) ->
      if not (nonzero_k_coefficient k_var lin) then
        TailStabilityUnknown [ "guard is independent of k" ]
      else
        let tail_path = k_geq_term k_var k :: path in
        let bounds = strict_bounds_of_path tail_path in
        if prove_comparison_strict bounds k_var (cmp_kind, lin) then
          TailStableTrue k
        else if
          prove_comparison_strict bounds k_var (invert_comparison cmp_kind, lin)
        then TailStableFalse k
        else TailStabilityUnknown [ "tail implication not proved" ]

let find_tail_stability ~path ~k_var cond =
  let tries = List.init (tail_stability_kmax + 1) ~f:Fn.id in
  let tried_logs through_k =
    List.init (through_k + 1) ~f:(fun k -> sprintf "  tried K = %d" k)
  in
  let results =
    List.map tries ~f:(fun k -> prove_tail_implication_at_k ~path ~k_var ~k cond)
  in
  match
    List.find_map results ~f:(function
      | TailStableTrue k -> Some (TailStableTrue k)
      | TailStableFalse k -> Some (TailStableFalse k)
      | TailStabilityUnknown _ -> None)
  with
  | Some (TailStableTrue k) ->
      Some
        ( k,
          TailStableTrue k,
          sprintf
            "GeoExpectation tail stability check enabled\n%s\n\
            \  crossing detected by tail stability\n\
            \  tail stable true from K = %d\n\
            \  prefix length used: %d"
            (String.concat ~sep:"\n" (tried_logs k))
            k k )
  | Some (TailStableFalse k) ->
      Some
        ( k,
          TailStableFalse k,
          sprintf
            "GeoExpectation tail stability check enabled\n%s\n\
            \  crossing detected by tail stability\n\
            \  tail stable false from K = %d\n\
            \  prefix length used: %d"
            (String.concat ~sep:"\n" (tried_logs k))
            k k )
  | Some (TailStabilityUnknown _) | None ->
      let reasons =
        List.concat_map results ~f:(function
          | TailStabilityUnknown reasons -> reasons
          | TailStableTrue _ | TailStableFalse _ -> [])
        |> List.stable_dedup ~compare:String.compare
      in
      let reason_log =
        match reasons with
        | [] -> ""
        | _ ->
            sprintf "\n  reason: %s"
              (String.concat ~sep:"; " reasons)
      in
      Some
        ( -1,
          TailStabilityUnknown reasons,
          sprintf
            "GeoExpectation tail stability check enabled\n%s\n\
            \  no stable tail found within Kmax = %d%s"
            (String.concat ~sep:"\n" (tried_logs tail_stability_kmax))
            tail_stability_kmax reason_log )

let lower_tail_stable_ite ~path ~k_var ~p cond then_ else_ =
  match find_tail_stability ~path ~k_var cond with
  | Some (-1, _, log) -> None, [ log ]
  | None -> None, []
  | Some (k, stable, log) ->
      let q = Q.(one - p) in
      let prefix_terms =
        List.init k ~f:(fun j ->
            let weight = Q.(p * q_pow q j) in
            let prefix_body =
              subst_var k_var (real_of_q @@ Q.of_int j)
                (Term.mk_fsym_app ~info:Dummy T_bool.IfThenElse
                   [ cond; then_; else_ ])
            in
            real_mul (real_of_q weight) prefix_body)
      in
      let tail_branch =
        match stable with
        | TailStableTrue _ -> then_
        | TailStableFalse _ -> else_
        | TailStabilityUnknown _ -> assert false
      in
      let tail_body =
        subst_var k_var
          (real_add (Term.mk_var k_var T_real.SReal) (real_of_q @@ Q.of_int k))
          tail_branch
      in
      ( Option.map
          (lower_expectation_of_fixed_branch ~k_var ~p tail_body)
          ~f:(fun tail ->
            let upper =
              real_add (sum_real_terms prefix_terms)
                (real_mul (real_of_q @@ q_pow q k) tail)
            in
            [ { region = None; upper } ]),
        [ log ] )

let str_of_crossing_branch_order = function
  | PrefixThenTailElse -> "prefix then / tail else"
  | PrefixElseTailThen -> "prefix else / tail then"

let lower_crossing_cases_of_expanded ~path ~k_var ~p expanded =
  match expanded with
  | Term.FunApp (T_bool.IfThenElse, [ cond; then_; else_ ], _) -> (
      match crossing_info_of_condition path k_var cond with
      | None -> None
      | Some { crossing_var = x; crossing_bound = n; branch_order;
               strict_tail_boundary } ->
          let prefix_formulas =
            List.map (List.init n ~f:Fn.id) ~f:(fun i ->
                let m = n - i in
                Option.map
                  (crossing_case_rhs ~k_var ~p ~m ~branch_order then_ else_)
                  ~f:(fun upper ->
                    { region = Some (mk_interval_region x i); upper }))
          in
          Option.bind (Option.all prefix_formulas) ~f:(fun prefix_cases ->
              let boundary_case =
                if strict_tail_boundary then
                  Option.map
                    (crossing_case_rhs ~k_var ~p ~m:1 ~branch_order then_
                       else_)
                    ~f:(fun upper ->
                      [ { region = Some (mk_eq_region x n); upper } ])
                else Some []
              in
              let tail_branch = crossing_tail_branch branch_order then_ else_ in
              Option.bind boundary_case ~f:(fun boundary_cases ->
              Option.map (lower_expectation_of_fixed_branch ~k_var ~p tail_branch)
                ~f:(fun final_rhs ->
              let final_region =
                if strict_tail_boundary then mk_gt_region x n
                else mk_geq_region x n
              in
              let cases = prefix_cases @ boundary_cases
                  @ [ { region = Some final_region; upper = final_rhs } ]
              in
              let region_logs =
                List.init n ~f:(fun i ->
                    sprintf "  split region %d: %d <= %s < %d" (i + 1) i
                      (Ident.name_of_tvar x) (i + 1))
                @ (if strict_tail_boundary then
                     [
                       sprintf "  split region %d: %s = %d" (n + 1)
                         (Ident.name_of_tvar x) n;
                       sprintf "  split region %d: %s > %d" (n + 2)
                         (Ident.name_of_tvar x) n;
                     ]
                   else
                     [
                       sprintf "  split region %d: %s >= %d" (n + 1)
                         (Ident.name_of_tvar x) n;
                     ])
              in
              let log =
                sprintf
                  "GeoExpectation crossing lowering:\n\
                  \  crossing detected\n\
                  \  crossing pattern: %s under %s\n\
                  \  crossing bound N: %d\n%s\n\
                  \  crossing branch order: %s\n\
                  \  all regions lowered: yes"
                  (Formula.str_of @@ Formula.of_bool_term cond)
                  (str_of_path_condition path)
                  n
                  (String.concat ~sep:"\n" region_logs)
                  (str_of_crossing_branch_order branch_order)
              in
              (cases, [ log ])))))
  | _ -> None

let guard_contains_var var guard = List.exists guard ~f:(term_contains_var var)

let region_of_case_guard = function
  | [] -> None
  | guard ->
      Some
        (simplify_formula
        @@ Formula.and_of @@ List.map guard ~f:Formula.of_bool_term)

let lower_branch_fixed_iverson_cases ~k_var ~p cases =
  if List.exists cases ~f:(fun case -> guard_contains_var k_var case.case_guard)
  then None
  else
    Option.map
      (Option.all
      @@ List.map cases ~f:(fun case ->
             Option.map
               (lower_expectation_of_fixed_branch ~k_var ~p case.case_body)
               ~f:(fun upper ->
                 { region = region_of_case_guard case.case_guard; upper })))
      ~f:(fun upper_cases ->
        let log =
          sprintf
            "%s\n\
            \  GeoExpectation branch-fixed lowering:\n\
            \  all case guards are independent of %s\n\
            \  all cases lowered: yes"
            (str_of_iverson_cases cases)
            (Ident.name_of_tvar k_var)
        in
        (upper_cases, [ log ]))

let lower_crossing_formulas_with_template_env template_env ~path ~lhs ~k_var ~p
    body =
  let expanded = Term.subst_funcs template_env.templ_subst body in
  Option.map
    (lower_crossing_cases_of_expanded ~path ~k_var ~p expanded)
    ~f:(fun (cases, logs) -> (formulas_of_upper_cases lhs cases, logs))

let unsupported_geo_lowering_reason ~k_var = function
  | Term.FunApp (T_bool.IfThenElse, [ cond; _; _ ], _)
    when term_contains_var k_var cond ->
      "unsupported GeoExpectation lowering: unsupported crossing / lowering shape"
  | _ -> "unsupported GeoExpectation lowering"

let lower_tail_stable_cases_of_expanded ~path ~k_var ~p = function
  | Term.FunApp (T_bool.IfThenElse, [ cond; then_; else_ ], _) ->
      let path = flatten_bool_path path in
      let cases, logs =
        lower_tail_stable_ite ~path ~k_var ~p cond then_ else_
      in
      Option.map cases ~f:(fun cases -> (cases, logs))
  | _ -> None

let lower_tail_or_crossing_cases ~path ~k_var ~p expanded =
  let iverson_cases = iverson_cases_of_ite expanded in
  let tail () =
    Option.map
      (lower_tail_stable_cases_of_expanded ~path ~k_var ~p expanded)
      ~f:(fun (cases, logs) -> (cases, str_of_iverson_cases iverson_cases :: logs))
  in
  let crossing () =
    Option.map
      (lower_crossing_cases_of_expanded ~path ~k_var ~p expanded)
      ~f:(fun (cases, logs) -> (cases, str_of_iverson_cases iverson_cases :: logs))
  in
  match crossing () with Some result -> Some result | None -> tail ()

let upper_geo_with_template_env template_env ~path ~k_var ~p body =
  let expanded = Term.subst_funcs template_env.templ_subst body in
  let iverson_cases = iverson_cases_of_ite expanded in
  match select_ite_branches path k_var expanded with
  | GeoLowered (selected_branch, logs) -> (
      match lower_branch_fixed_iverson_cases ~k_var ~p iverson_cases with
      | Some (cases, case_logs) -> UpperGeoBranchFixed (cases, case_logs)
      | None -> (
      match lower_expectation_of_fixed_branch ~k_var ~p selected_branch with
      | Some upper -> UpperGeoBranchFixed ([ { region = None; upper } ], logs)
      | None -> (
          match
            lower_tail_stable_cases_of_expanded ~path ~k_var ~p expanded
          with
          | Some (cases, logs) ->
              UpperGeoFinitePrefixTail
                (cases, str_of_iverson_cases iverson_cases :: logs)
          | None -> (
          match
            lower_crossing_cases_of_expanded ~path ~k_var ~p expanded
          with
          | Some (cases, logs) ->
              UpperGeoFinitePrefixTail
                (cases, str_of_iverson_cases iverson_cases :: logs)
          | None ->
              UpperGeoUnsupported
                (unsupported_geo_lowering_reason ~k_var expanded)))))
  | GeoUnsupported reason -> (
      match lower_tail_or_crossing_cases ~path ~k_var ~p expanded with
      | Some (cases, logs) -> UpperGeoFinitePrefixTail (cases, logs)
      | None ->
          let crossing_reason = unsupported_geo_lowering_reason ~k_var expanded in
          let reason =
            if String.equal crossing_reason "unsupported GeoExpectation lowering"
            then reason
            else sprintf "%s; %s" reason crossing_reason
          in
          UpperGeoUnsupported reason)

let lower_geo_expr_with_template_env template_env ~path ~k_var ~p body =
  match upper_geo_with_template_env template_env ~path ~k_var ~p body with
  | UpperGeoBranchFixed ([ { region = None; upper } ], logs) -> Ok (upper, logs)
  | UpperGeoBranchFixed _ -> Error "unsupported GeoExpectation lowering"
  | UpperGeoFinitePrefixTail _ ->
      Error "unsupported GeoExpectation lowering"
  | UpperGeoUnsupported reason -> Error reason

let term_of_accel_expr_with_template_env template_env ~path = function
  | TermExpr term -> Ok (Term.subst_funcs template_env.templ_subst term, [])
  | GeoExpectationExpr { k_var; p; body } ->
      lower_geo_expr_with_template_env template_env ~path ~k_var ~p body

let rec formula_of_accel_vc template_env ?(path = []) ?(antecedents = []) =
  function
  | Inequality { lhs; rhs } as vc -> (
      let lhs = Term.subst_funcs template_env.templ_subst lhs in
      match term_of_accel_expr_with_template_env template_env ~path rhs with
      | Ok (rhs, logs) ->
          AccelFormula
            (geq_formulas_with_lhs_ite ~antecedents lhs rhs, logs)
      | Error reason -> (
          match rhs with
          | GeoExpectationExpr { k_var; p; body } -> (
              match
                upper_geo_with_template_env template_env ~path ~k_var ~p body
              with
              | UpperGeoBranchFixed (cases, logs) ->
                  AccelFormula
                    (formulas_of_upper_cases ~antecedents lhs cases, logs)
              | UpperGeoFinitePrefixTail (cases, logs) ->
                  AccelFormula
                    (formulas_of_upper_cases ~antecedents lhs cases, logs)
              | UpperGeoUnsupported _ -> SkippedAcceleratedVC (reason, vc))
          | TermExpr _ -> SkippedAcceleratedVC (reason, vc)))
  | Imply { cond; vc } -> (
      match
        formula_of_accel_vc template_env ~path:(cond :: path)
          ~antecedents:(Formula.of_bool_term cond :: antecedents)
          vc
      with
      | AccelFormula (phis, logs) -> AccelFormula (phis, logs)
      | SkippedAcceleratedVC (reason, vc) ->
          SkippedAcceleratedVC (reason, Imply { cond; vc }))
  | And vcs ->
      let formulas =
        List.map vcs ~f:(formula_of_accel_vc template_env ~path ~antecedents)
      in
      let skipped =
        List.filter_map formulas ~f:(function
          | AccelFormula _ -> None
          | SkippedAcceleratedVC (reason, vc) -> Some (reason, vc))
      in
      if List.is_empty skipped then
        AccelFormula
          ( List.concat_map formulas ~f:(function
                 | AccelFormula (phis, _) -> phis
                 | SkippedAcceleratedVC _ -> []),
            List.concat_map formulas ~f:(function
              | AccelFormula (_, logs) -> logs
              | SkippedAcceleratedVC _ -> []) )
      else
        let reasons = String.concat ~sep:"; " @@ List.map skipped ~f:fst in
        SkippedAcceleratedVC (reasons, And (List.map skipped ~f:snd))

let formulas_of_accel_vcs template_env vcs =
  List.map vcs ~f:(formula_of_accel_vc template_env)

let rec formula_of_accel_vc_lower template_env ?(path = []) ?(antecedents = [])
    = function
  | Inequality { lhs; rhs } as vc -> (
      let lhs = Term.subst_funcs template_env.templ_subst lhs in
      match term_of_accel_expr_with_template_env template_env ~path rhs with
      | Ok (rhs, logs) ->
          AccelFormula
            (geq_formulas_with_rhs_ite ~antecedents rhs lhs, logs)
      | Error reason -> (
          match rhs with
          | GeoExpectationExpr { k_var; p; body } -> (
              match
                upper_geo_with_template_env template_env ~path ~k_var ~p body
              with
              | UpperGeoBranchFixed (cases, logs) ->
                  AccelFormula
                    (formulas_of_lower_cases ~antecedents lhs cases, logs)
              | UpperGeoFinitePrefixTail (cases, logs) ->
                  AccelFormula
                    (formulas_of_lower_cases ~antecedents lhs cases, logs)
              | UpperGeoUnsupported _ -> SkippedAcceleratedVC (reason, vc))
          | TermExpr _ -> SkippedAcceleratedVC (reason, vc)))
  | Imply { cond; vc } -> (
      match
        formula_of_accel_vc_lower template_env ~path:(cond :: path)
          ~antecedents:(Formula.of_bool_term cond :: antecedents)
          vc
      with
      | AccelFormula (phis, logs) -> AccelFormula (phis, logs)
      | SkippedAcceleratedVC (reason, vc) ->
          SkippedAcceleratedVC (reason, Imply { cond; vc }))
  | And vcs ->
      let formulas =
        List.map vcs ~f:(formula_of_accel_vc_lower template_env ~path ~antecedents)
      in
      let skipped =
        List.filter_map formulas ~f:(function
          | AccelFormula _ -> None
          | SkippedAcceleratedVC (reason, vc) -> Some (reason, vc))
      in
      if List.is_empty skipped then
        AccelFormula
          ( List.concat_map formulas ~f:(function
                 | AccelFormula (phis, _) -> phis
                 | SkippedAcceleratedVC _ -> []),
            List.concat_map formulas ~f:(function
              | AccelFormula (_, logs) -> logs
              | SkippedAcceleratedVC _ -> []) )
      else
        let reasons = String.concat ~sep:"; " @@ List.map skipped ~f:fst in
        SkippedAcceleratedVC (reasons, And (List.map skipped ~f:snd))

let formulas_of_accel_vcs_lower template_env vcs =
  List.map vcs ~f:(formula_of_accel_vc_lower template_env)

let str_of_accel_formula = function
  | AccelFormula (phis, logs) ->
      sprintf "%s%s"
        (if List.is_empty logs then ""
         else
           sprintf "GeoExpectation lowering debug:\n%s\n"
           @@ indent_lines 2
           @@ String.concat ~sep:"\n" logs)
        (String.concat_map_list ~sep:"\n\n" phis ~f:Formula.str_of)
  | SkippedAcceleratedVC (reason, vc) ->
      sprintf "skipped accelerated VC:\n  reason: %s\n%s" reason
        (indent_lines 2 @@ str_of_accel_vc vc)

let str_of_accel_formulas formulas =
  match formulas with
  | [] -> "accelerated Formula.t constraints:\n  none"
  | _ ->
      sprintf "accelerated Formula.t constraints:\n%s"
      @@ indent_lines 2
      @@ String.concat_map_list ~sep:"\n\n" formulas ~f:str_of_accel_formula

let template_call name args =
  Term.mk_fvar_app (template_name name)
    (List.map args ~f:Term.sort_of)
    T_real.SReal args

let template_call_of_senv name params =
  template_call name (List.map params ~f:term_of_param)

let template_subst_of_preds preds =
  Map.Poly.of_alist_exn
  @@ List.map preds ~f:(fun pred ->
         (pred.original_pred.name,
          (pred.original_pred.args,
           template_call_of_senv pred.original_pred.name pred.original_pred.args)))

let template_subst_term template_subst term =
  Term.subst_funcs template_subst term

let pred_call name args =
  Term.mk_fvar_app name (List.map args ~f:Term.sort_of) T_real.SReal args

let rec vc_of_accel_rhs template_subst lhs = function
  | Plain term ->
      Inequality { lhs; rhs = TermExpr (template_subst_term template_subst term) }
  | GeoExpectation geo ->
      let body =
        match (geo.accelerated_exit_body, geo.accelerated_exit_args) with
        | Some body, _ -> template_subst_term template_subst body
        | None, Some args -> template_call geo.exit_pred args
        | None, None ->
            template_call geo.exit_pred
              (List.map geo.original_params ~f:term_of_param)
      in
      Inequality
        { lhs; rhs = GeoExpectationExpr { k_var = geo.k_var; p = geo.p; body } }
  | IfThenElse { guard; then_rhs; else_rhs } ->
      And
        [
          Imply { cond = guard; vc = vc_of_accel_rhs template_subst lhs then_rhs };
          Imply
            {
              cond = T_bool.negate guard;
              vc = vc_of_accel_rhs template_subst lhs else_rhs;
            };
        ]

let vc_of_accel_pred template_subst pred =
  let lhs =
    template_call_of_senv pred.original_pred.name pred.original_pred.args
  in
  vc_of_accel_rhs template_subst lhs pred.body

let vc_of_accel_problem accel_problem =
  let template_subst = template_subst_of_preds accel_problem.preds in
  List.map accel_problem.preds ~f:(vc_of_accel_pred template_subst)

let rec accel_formulas_of_accel_vc template_env = function
  | And vcs -> List.concat_map vcs ~f:(accel_formulas_of_accel_vc template_env)
  | vc -> [ formula_of_accel_vc template_env vc ]

let combined_subst template_env fsub =
  let templ_keys = Map.key_set template_env.templ_subst in
  let fsub =
    Map.filter_keys fsub ~f:(fun key -> not (Set.mem templ_keys key))
  in
  Map.force_merge fsub template_env.templ_subst

let rec vc_of_accel_rhs_with_subst subst lhs = function
  | Plain term ->
      Inequality { lhs; rhs = TermExpr (Term.subst_funcs subst term) }
  | GeoExpectation geo ->
      let body =
        match (geo.accelerated_exit_body, geo.accelerated_exit_args) with
        | Some body, _ -> Term.subst_funcs subst body
        | None, Some args -> Term.subst_funcs subst @@ pred_call geo.exit_pred args
        | None, None ->
            let args = List.map geo.original_params ~f:term_of_param in
            Term.subst_funcs subst @@ pred_call geo.exit_pred args
      in
      Inequality
        { lhs; rhs = GeoExpectationExpr { k_var = geo.k_var; p = geo.p; body } }
  | IfThenElse { guard; then_rhs; else_rhs } ->
      And
        [
          Imply
            {
              cond = guard;
              vc = vc_of_accel_rhs_with_subst subst lhs then_rhs;
            };
          Imply
            {
              cond = T_bool.negate guard;
              vc = vc_of_accel_rhs_with_subst subst lhs else_rhs;
            };
        ]

let vc_of_accel_pred_with_subst subst pred =
  let lhs =
    template_call_of_senv pred.original_pred.name pred.original_pred.args
  in
  vc_of_accel_rhs_with_subst subst lhs pred.body

(* same reason as [term_contains_fvar] above: the walk has to enter a formula
   carried inside a term *)
let term_has_predicate_call term = Fn.non Set.is_empty @@ Term.fvar_apps_of term

let rec delta_term_of_exit_body term =
  let zero () = T_real.rzero () in
  let map2 t1 t2 ~f =
    Option.map2
      (delta_term_of_exit_body t1) (delta_term_of_exit_body t2) ~f
  in
  match term with
  | Term.FunApp (FVar _, args, _) ->
      if List.exists args ~f:term_has_predicate_call then None
      else Some term
  | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _) ->
      map2 t1 t2 ~f:T_real.mk_radd
  | Term.FunApp ((T_real.RSub | T_int.Sub | T_num.NSub _), [ t1; t2 ], _) ->
      map2 t1 t2 ~f:T_real.mk_rsub
  | Term.FunApp ((T_real.RNeg | T_int.Neg | T_num.NNeg _), [ t ], _) ->
      Option.map (delta_term_of_exit_body t) ~f:T_real.mk_rneg
  | Term.FunApp ((T_real.RMul | T_int.Mul | T_num.NMul _), [ t1; t2 ], _) -> (
      match (rational_of_term t1, rational_of_term t2) with
      | Some coeff, _ ->
          Option.map (delta_term_of_exit_body t2) ~f:(real_mul_q coeff)
      | _, Some coeff ->
          Option.map (delta_term_of_exit_body t1) ~f:(real_mul_q coeff)
      | None, None ->
          if term_has_predicate_call term then None else Some (zero ()))
  | Term.FunApp ((T_real.RDiv | T_int.Div _ | T_num.NDiv _), [ num; den ], _)
    -> (
      match rational_of_term den with
      | Some coeff when not (Q.equal coeff Q.zero) ->
          Option.map (delta_term_of_exit_body num)
            ~f:(real_mul_q Q.(one / coeff))
      | _ -> if term_has_predicate_call term then None else Some (zero ()))
  | _ -> if term_has_predicate_call term then None else Some (zero ())

let rank_delta_body_of_geo geo =
  match (geo.accelerated_exit_body, geo.accelerated_exit_args) with
  | Some body, _ -> delta_term_of_exit_body body
  | None, Some args ->
      if Ident.tvar_equal geo.exit_pred geo.self_pred then None
      else Some (pred_call geo.exit_pred args)
  | None, None -> None

let rec rank_delta_vc_of_accel_rhs subst lhs = function
  | Plain _ -> Inequality { lhs; rhs = TermExpr (T_real.rzero ()) }
  | GeoExpectation geo ->
      let body =
        Term.subst_funcs subst @@ Option.value_exn (rank_delta_body_of_geo geo)
      in
      Inequality
        { lhs; rhs = GeoExpectationExpr { k_var = geo.k_var; p = geo.p; body } }
  | IfThenElse { guard; then_rhs; else_rhs } ->
      And
        [
          Imply
            {
              cond = guard;
              vc = rank_delta_vc_of_accel_rhs subst lhs then_rhs;
            };
          Imply
            {
              cond = T_bool.negate guard;
              vc = rank_delta_vc_of_accel_rhs subst lhs else_rhs;
            };
        ]

let rank_delta_vc_of_accel_pred subst pred =
  let lhs =
    template_call_of_senv pred.original_pred.name pred.original_pred.args
  in
  rank_delta_vc_of_accel_rhs subst lhs pred.body

let fallback_prefixpoint_constraints subst (pred : Pred.t) =
  List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
      let body = Term.subst_funcs subst body in
      let lhs =
        Term.subst_funcs subst
        @@ Term.fvar_app_of_senv pred.name pred.args T_real.SReal
      in
      Formula.geq lhs body)

let has_replaced_candidate pred =
  List.exists pred.candidates ~f:(fun candidate ->
      match (candidate.action, candidate.applicability) with
      | ReplacedByGeoExpectation, Applicable -> true
      | _ -> false)

let has_accelerated_body (pred : accel_pred) =
  match pred.body with
  | Plain term -> not ((Stdlib.( = )) term pred.original_pred.body)
  | GeoExpectation _ | IfThenElse _ -> true

let str_of_string_reasons = function
  | [] -> "none"
  | reasons ->
      sprintf "\n%s"
      @@ String.concat_map_list ~sep:"\n"
           (List.stable_dedup reasons ~compare:String.compare)
           ~f:(fun reason -> sprintf "    - %s" reason)

let constraints_of_accel_pred template_env subst pred =
  if (not (has_replaced_candidate pred)) && not (has_accelerated_body pred) then
    ( fallback_prefixpoint_constraints subst pred.original_pred,
      sprintf
        "predicate %s:\n\
        \  acceleration not used\n\
        \  reason: no applicable replaced candidate\n\
        \  detection fallback reasons: %s\n\
        \  fallback: original prefixpoint constraint"
        (Ident.name_of_tvar pred.original_pred.name)
        (str_of_string_reasons pred.detection_fallback_reasons) )
  else
    let vc = vc_of_accel_pred_with_subst subst pred in
    let formulas = accel_formulas_of_accel_vc template_env vc in
    let skipped =
      List.filter_map formulas ~f:(function
        | AccelFormula _ -> None
        | SkippedAcceleratedVC (reason, _) -> Some reason)
      in
      if List.is_empty skipped then
        ( List.concat_map formulas ~f:(function
          | AccelFormula (phis, _) ->
              phis
          | SkippedAcceleratedVC _ -> []),
        sprintf
          "predicate %s:\n\
          \  acceleration used\n\
          \  reason: applicable and GeoExpectation lowering succeeded"
          (Ident.name_of_tvar pred.original_pred.name) )
    else
      ( fallback_prefixpoint_constraints subst pred.original_pred,
        sprintf
          "predicate %s:\n\
          \  acceleration detected but not used\n\
          \  reason: %s\n\
          \  lowering fallback reason: %s\n\
          \  fallback: original prefixpoint constraint"
          (Ident.name_of_tvar pred.original_pred.name)
          (String.concat ~sep:"; " skipped)
          (String.concat ~sep:"; " skipped) )

let constraints_of_accel_problem ?active_pred_names ?(fsub = Map.Poly.empty)
    template_env accel_problem =
  let subst = combined_subst template_env fsub in
  let is_active =
    match active_pred_names with
    | None -> fun _ -> true
    | Some names -> fun pred -> Set.mem names pred.original_pred.name
  in
  let constrs, reports =
    List.unzip
    @@ List.map accel_problem.preds
         ~f:(fun pred ->
           if is_active pred then
             constraints_of_accel_pred template_env subst pred
           else
             ( [],
               sprintf
                 "predicate %s:\n\
                 \  acceleration not used\n\
                 \  reason: predicate unfolded into fsub\n\
                 \  fallback: inlined at use sites"
                 (Ident.name_of_tvar pred.original_pred.name) ))
  in
  (List.concat constrs, String.concat ~sep:"\n" reports)

let fallback_postfixpoint_constraints subst (pred : Pred.t) =
  List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
      let body = Term.subst_funcs subst body in
      let lhs =
        Term.subst_funcs subst
        @@ Term.fvar_app_of_senv pred.name pred.args T_real.SReal
      in
      Formula.geq body lhs)

let constraints_of_accel_pred_lower template_env subst pred =
  if (not (has_replaced_candidate pred)) && not (has_accelerated_body pred) then
    ( fallback_postfixpoint_constraints subst pred.original_pred,
      sprintf
        "predicate %s:\n\
        \  lower-bound acceleration not used\n\
        \  reason: no applicable replaced candidate\n\
        \  detection fallback reasons: %s\n\
        \  fallback: original postfixpoint constraint"
        (Ident.name_of_tvar pred.original_pred.name)
        (str_of_string_reasons pred.detection_fallback_reasons) )
  else
    let vc = vc_of_accel_pred_with_subst subst pred in
    let formulas = formulas_of_accel_vcs_lower template_env [ vc ] in
    let skipped =
      List.filter_map formulas ~f:(function
        | AccelFormula _ -> None
        | SkippedAcceleratedVC (reason, _) -> Some reason)
    in
    if List.is_empty skipped then
      ( List.concat_map formulas ~f:(function
          | AccelFormula (phis, _) -> phis
          | SkippedAcceleratedVC _ -> []),
        sprintf
          "predicate %s:\n\
          \  lower-bound acceleration used\n\
          \  reason: applicable and GeoExpectation lowering succeeded"
          (Ident.name_of_tvar pred.original_pred.name) )
    else
      ( fallback_postfixpoint_constraints subst pred.original_pred,
        sprintf
          "predicate %s:\n\
          \  lower-bound acceleration detected but not used\n\
          \  reason: %s\n\
          \  lowering fallback reason: %s\n\
          \  fallback: original postfixpoint constraint"
          (Ident.name_of_tvar pred.original_pred.name)
          (String.concat ~sep:"; " skipped)
          (String.concat ~sep:"; " skipped) )

(** Generates accelerated postfixpoint constraints for lower-bound checking. *)
let constraints_of_accel_problem_lower ?active_pred_names
    ?(fsub = Map.Poly.empty) template_env accel_problem =
  let subst = combined_subst template_env fsub in
  let is_active =
    match active_pred_names with
    | None -> fun _ -> true
    | Some names -> fun pred -> Set.mem names pred.original_pred.name
  in
  let constrs, reports =
    List.unzip
    @@ List.map accel_problem.preds ~f:(fun pred ->
           if is_active pred then
             constraints_of_accel_pred_lower template_env subst pred
           else
             ( [],
               sprintf
                 "predicate %s:\n\
                 \  lower-bound acceleration not used\n\
                 \  reason: predicate unfolded into fsub\n\
                 \  fallback: inlined at use sites"
                 (Ident.name_of_tvar pred.original_pred.name) ))
  in
  (List.concat constrs, String.concat ~sep:"\n" reports)

let rank_geq_formulas ~antecedents lhs rhs =
  let lhs_cases = iverson_cases_of_ite lhs in
  let rhs_cases = iverson_cases_of_ite rhs in
  List.concat_map lhs_cases ~f:(fun lhs_case ->
      List.concat_map rhs_cases ~f:(fun rhs_case ->
          imply_antecedents
            (antecedents
            @ List.map lhs_case.case_guard ~f:Formula.of_bool_term
            @ List.map rhs_case.case_guard ~f:Formula.of_bool_term)
            (Formula.geq lhs_case.case_body rhs_case.case_body)))

let formulas_of_rank_cases ~antecedents lhs prefp cases =
  List.concat_map cases ~f:(fun { region; upper } ->
      let antecedents =
        match region with None -> antecedents | Some phi -> phi :: antecedents
      in
      rank_geq_formulas ~antecedents lhs (T_real.mk_radd upper prefp))

let rec supports_rank_delta = function
  | Plain _ -> true
  | GeoExpectation geo -> Option.is_some (rank_delta_body_of_geo geo)
  | IfThenElse { then_rhs; else_rhs; _ } ->
      supports_rank_delta then_rhs && supports_rank_delta else_rhs

let rec rank_delta_body_logs = function
  | Plain _ -> []
  | GeoExpectation geo ->
      Option.to_list
      @@ Option.map (rank_delta_body_of_geo geo) ~f:(fun body ->
             sprintf "rank delta body: %s" (Term.str_of body))
  | IfThenElse { then_rhs; else_rhs; _ } ->
      rank_delta_body_logs then_rhs @ rank_delta_body_logs else_rhs

let rec formula_of_accel_rank_vc rank_template_env prefp_template_env ?(path = [])
    ?(antecedents = []) =
  function
  | Inequality { lhs; rhs } as vc -> (
      let rank_lhs = Term.subst_funcs rank_template_env.templ_subst lhs in
      let prefp = Term.subst_funcs prefp_template_env.templ_subst lhs in
      match term_of_accel_expr_with_template_env rank_template_env ~path rhs with
      | Ok (rhs, logs) ->
          AccelFormula
            (rank_geq_formulas ~antecedents rank_lhs
               (T_real.mk_radd rhs prefp),
             logs)
      | Error reason -> (
          match rhs with
          | GeoExpectationExpr { k_var; p; body } -> (
              match
                upper_geo_with_template_env rank_template_env ~path ~k_var ~p
                  body
              with
              | UpperGeoBranchFixed (cases, logs) ->
                  AccelFormula
                    ( formulas_of_rank_cases ~antecedents rank_lhs prefp cases,
                      logs )
              | UpperGeoFinitePrefixTail (cases, logs) ->
                  AccelFormula
                    ( formulas_of_rank_cases ~antecedents rank_lhs prefp cases,
                      logs )
              | UpperGeoUnsupported _ -> SkippedAcceleratedVC (reason, vc))
          | TermExpr _ -> SkippedAcceleratedVC (reason, vc)))
  | Imply { cond; vc } -> (
      match
        formula_of_accel_rank_vc rank_template_env prefp_template_env
          ~path:(cond :: path)
          ~antecedents:(Formula.of_bool_term cond :: antecedents)
          vc
      with
      | AccelFormula (phis, logs) -> AccelFormula (phis, logs)
      | SkippedAcceleratedVC (reason, vc) ->
          SkippedAcceleratedVC (reason, Imply { cond; vc }))
  | And vcs ->
      let formulas =
        List.map vcs
          ~f:
            (formula_of_accel_rank_vc rank_template_env prefp_template_env ~path
               ~antecedents)
      in
      let skipped =
        List.filter_map formulas ~f:(function
          | AccelFormula _ -> None
          | SkippedAcceleratedVC (reason, vc) -> Some (reason, vc))
      in
      if List.is_empty skipped then
        AccelFormula
          ( List.concat_map formulas ~f:(function
                 | AccelFormula (phis, _) -> phis
                 | SkippedAcceleratedVC _ -> []),
            List.concat_map formulas ~f:(function
              | AccelFormula (_, logs) -> logs
              | SkippedAcceleratedVC _ -> []) )
      else
        let reasons = String.concat ~sep:"; " @@ List.map skipped ~f:fst in
        SkippedAcceleratedVC (reasons, And (List.map skipped ~f:snd))

let constraints_of_accel_pred_rank rank_template_env prefp_template_env subst
    pred =
  if (not (has_replaced_candidate pred)) && not (has_accelerated_body pred) then
    ( [],
      sprintf
        "predicate %s:\n\
        \  accelerated ranking not used\n\
        \  reason: no applicable replaced candidate"
        (Ident.name_of_tvar pred.original_pred.name) )
  else if not (supports_rank_delta pred.body) then
    ( [],
      sprintf
        "predicate %s:\n\
        \  accelerated ranking not used\n\
        \  reason: exit body rank delta contains a self call or unsupported \
         predicate-dependent term"
        (Ident.name_of_tvar pred.original_pred.name) )
  else
    let vc = rank_delta_vc_of_accel_pred subst pred in
    let formula =
      formula_of_accel_rank_vc rank_template_env prefp_template_env
        ~antecedents:pred.original_pred.arg_constrs vc
    in
    match formula with
    | AccelFormula (phis, logs) ->
        let logs = rank_delta_body_logs pred.body @ logs in
        ( phis,
          sprintf
            "predicate %s:\n\
            \  accelerated ranking used\n\
            \  reason: GeoExpectation rank delta lowering succeeded%s"
            (Ident.name_of_tvar pred.original_pred.name)
            (if List.is_empty logs then ""
             else sprintf "\n%s" (indent_lines 2 @@ String.concat ~sep:"\n" logs))
        )
    | SkippedAcceleratedVC (reason, _) ->
        ( [],
          sprintf
            "predicate %s:\n\
            \  accelerated ranking not used\n\
            \  reason: %s"
            (Ident.name_of_tvar pred.original_pred.name)
            reason )

(** Generates accelerated ranking constraints for lower-bound checking. *)
let constraints_of_accel_problem_rank ?active_pred_names ?(fsub = Map.Poly.empty)
    rank_template_env prefp_template_env accel_problem =
  let subst = combined_subst rank_template_env fsub in
  let is_active =
    match active_pred_names with
    | None -> fun _ -> true
    | Some names -> fun pred -> Set.mem names pred.original_pred.name
  in
  let constrs, reports =
    List.unzip
    @@ List.map accel_problem.preds ~f:(fun pred ->
           if is_active pred then
             constraints_of_accel_pred_rank rank_template_env prefp_template_env
               subst pred
           else
             ( [],
               sprintf
                 "predicate %s:\n\
                 \  accelerated ranking not used\n\
                 \  reason: predicate unfolded into fsub"
                 (Ident.name_of_tvar pred.original_pred.name) ))
  in
  (List.concat constrs, String.concat ~sep:"\n" reports)

let active_geo_expectations ?active_pred_names accel_problem =
  let is_active =
    match active_pred_names with
    | None -> fun _ -> true
    | Some names -> fun pred -> Set.mem names pred.original_pred.name
  in
  List.concat_map accel_problem.preds ~f:(fun pred ->
      if not (is_active pred) then []
      else
        List.filter_map pred.candidates ~f:(fun candidate ->
            match (candidate.action, candidate.applicability) with
            | ReplacedByGeoExpectation, Applicable -> Some candidate.geo
            | _ -> None))

let body_nonnegative_formulas ?active_pred_names ?(fsub = Map.Poly.empty)
    accel_problem =
  active_geo_expectations ?active_pred_names accel_problem
  |> List.concat_map ~f:(fun geo ->
         let arg_constrs =
           match
             List.find accel_problem.preds ~f:(fun pred ->
                 Ident.tvar_equal pred.original_pred.name geo.self_pred)
           with
           | Some pred -> pred.original_pred.arg_constrs
           | None -> []
         in
         let bodies =
           Option.to_list geo.exit_body @ Option.to_list geo.residual_body
         in
         List.concat_map bodies ~f:(fun body ->
             Problem.nonnegative_formulas_of_term ~antecedents:arg_constrs
               (Term.subst_funcs fsub body)))
  |> List.stable_dedup ~compare:(fun phi1 phi2 ->
         String.compare (Formula.str_of phi1) (Formula.str_of phi2))

let str_of_accel_formula_debug config accel_problem =
  let template_env = template_env_of_accel_problem config accel_problem in
  let vcs = vc_of_accel_problem accel_problem in
  sprintf "%s\n\n%s" (str_of_template_env template_env)
    (str_of_accel_formulas @@ formulas_of_accel_vcs template_env vcs)

let str_of_accel_action = function
  | ReplacedByGeoExpectation -> "replaced by GeoExpectation"
  | KeepOriginalBody -> "keep original body"

let str_of_applicability_status = function
  | Applicable -> "applicable"
  | ConditionallyApplicable _ -> "conditionally applicable"
  | Blocked _ -> "blocked"

let str_of_applicability_reasons = function
  | Applicable -> "none"
  | ConditionallyApplicable vcs ->
      sprintf "\n%s"
      @@ String.concat_map_list ~sep:"\n" vcs ~f:(fun vc ->
             sprintf "    - %s" (str_of_verification_condition vc))
  | Blocked reasons -> str_of_reasons reasons

let str_of_accel_candidate candidate =
  sprintf
    "geometric PLA candidate for %s:\n\
    \  status: %s\n\
    \  reasons: %s\n\
    \  action: %s"
    (Ident.name_of_tvar candidate.geo.self_pred)
    (str_of_applicability_status candidate.applicability)
    (str_of_applicability_reasons candidate.applicability)
    (str_of_accel_action candidate.action)

let str_of_accel_pred pred =
  sprintf "%s %s : real =%s\n%s;"
    (Ident.name_of_tvar pred.original_pred.name)
    (if List.length pred.original_pred.args > 0 then
       str_of_sort_env_list Term.str_of_sort pred.original_pred.args
     else "")
    (Predicate.str_of_fop pred.original_pred.kind)
    (indent_lines 2 @@ str_of_accel_rhs pred.body)

let str_of_accel_problem accel_problem =
  let candidate_logs =
    accel_problem.preds
    |> String.concat_map_list ~sep:"\n" ~f:(fun pred ->
           let logs =
             String.concat_map_list ~sep:"\n" pred.candidates
               ~f:str_of_accel_candidate
           in
           let applicable_count =
             List.count pred.candidates ~f:(fun candidate ->
                 match candidate.applicability with
                 | Applicable -> true
                 | ConditionallyApplicable _ | Blocked _ -> false)
           in
           if applicable_count <= 1 then logs
           else
             sprintf
               "%s\nmultiple geometric PLA candidates possible for %s: %d \
                applicable; deterministic first applicable candidate selected"
               logs
               (Ident.name_of_tvar pred.original_pred.name)
               applicable_count)
  in
  let vcs = vc_of_accel_problem accel_problem in
  sprintf
    "%s%saccelerated QFL problem:\n\n%s\ns.t.\n%s\n\n[5. Lowering / \
     accelerated constraints]\n%s\n\n%s"
    (if String.is_empty candidate_logs then "" else candidate_logs)
    (if String.is_empty candidate_logs then "" else "\n\n")
    (Problem.str_of_query accel_problem.query)
    (String.concat_map_list ~sep:"\n" accel_problem.preds ~f:str_of_accel_pred)
    (str_of_accel_vcs vcs)
    (str_of_lowered_accel_vcs @@ lower_accel_vcs_linear vcs)

let str_of_disabled_report accel_problem =
  String.concat_map_list ~sep:"\n" accel_problem.preds ~f:(fun pred ->
      let name = Ident.name_of_tvar pred.original_pred.name in
      match pred.candidates with
      | [] ->
          sprintf
            "predicate %s:\n\
            \  acceleration enabled/disabled: disabled\n\
            \  candidate: not found\n\
            \  detection fallback reasons: %s\n\
            \  action: fallback to original prefixpoint constraint"
            name
            (str_of_string_reasons pred.detection_fallback_reasons)
      | candidates ->
          sprintf
            "predicate %s:\n\
            \  acceleration enabled/disabled: disabled\n\
            \  candidate: found\n\
            \  applicability: %s\n\
            \  reasons: %s\n\
            \  action: fallback to original prefixpoint constraint"
            name
            (String.concat_map_list ~sep:", " candidates
               ~f:(fun candidate ->
                 str_of_applicability_status candidate.applicability))
            (String.concat_map_list ~sep:"; " candidates
               ~f:(fun candidate ->
                 str_of_applicability_reasons candidate.applicability)))

let query_predicate = function
  | Problem.Check query -> Some query.name
  | Problem.DistCheck query -> Some query.name
  | Problem.ASAT (Some (name, _), _, _) -> Some name
  | Problem.ASAT (None, _, _) -> None

let rec accel_rhs_contains_pred name = function
  | Plain term -> term_contains_fvar name term
  | GeoExpectation geo ->
      Ident.tvar_equal geo.exit_pred name
      || Option.value_map geo.accelerated_exit_body ~default:false
           ~f:(term_contains_fvar name)
      || List.exists
           (Option.value geo.accelerated_exit_args
              ~default:(List.map geo.original_params ~f:term_of_param))
           ~f:(fun arg -> Set.mem (Term.fvs_of arg) name)
  | IfThenElse { guard; then_rhs; else_rhs } ->
      Set.mem (Term.fvs_of guard) name
      || accel_rhs_contains_pred name then_rhs
      || accel_rhs_contains_pred name else_rhs

let inlineable_accel_rhs pred =
  if has_replaced_candidate pred
     && not (accel_rhs_contains_pred pred.original_pred.name pred.body)
  then Some (pred.original_pred.args, pred.body)
  else None

let subst_params_in_term params args term =
  Term.subst
    (Map.Poly.of_alist_exn
    @@ List.map2_exn params args ~f:(fun (param, _) arg -> (param, arg)))
    term

let subst_params_in_geo params args geo =
  {
    geo with
    original_args = List.map geo.original_args ~f:(subst_params_in_term params args);
    recursive_update =
      List.map geo.recursive_update ~f:(subst_params_in_term params args);
    exit_update = List.map geo.exit_update ~f:(subst_params_in_term params args);
    accelerated_exit_args =
      Option.map geo.accelerated_exit_args ~f:(fun geo_args ->
          List.map geo_args ~f:(subst_params_in_term params args));
    accelerated_exit_body =
      Option.map geo.accelerated_exit_body ~f:(subst_params_in_term params args);
    guard =
      Option.map geo.guard ~f:(fun guard ->
          Formula.subst
            (Map.Poly.of_alist_exn
            @@ List.map2_exn params args ~f:(fun (param, _) arg -> (param, arg)))
            guard);
    residual_body =
      Option.map geo.residual_body ~f:(subst_params_in_term params args);
    exit_body = Option.map geo.exit_body ~f:(subst_params_in_term params args);
    normalized_exit_body =
      subst_params_in_term params args geo.normalized_exit_body;
  }

let rec subst_params_in_accel_rhs params args = function
  | Plain term -> Plain (subst_params_in_term params args term)
  | GeoExpectation geo -> GeoExpectation (subst_params_in_geo params args geo)
  | IfThenElse { guard; then_rhs; else_rhs } ->
      IfThenElse
        {
          guard = subst_params_in_term params args guard;
          then_rhs = subst_params_in_accel_rhs params args then_rhs;
          else_rhs = subst_params_in_accel_rhs params args else_rhs;
        }

let subst_inlineable_calls inline_map term =
  let rec aux term =
    match term with
    | Term.FunApp (FVar (name, _, _), args, _) -> (
        match Map.find inline_map name with
        | Some (params, rhs) -> subst_params_in_accel_rhs params args rhs
        | None -> Plain term)
    | _ -> (
        match term with
        | Term.FunApp (T_bool.IfThenElse, [ cond; then_; else_ ], _) ->
            IfThenElse
              {
                guard = cond;
                then_rhs = aux then_;
                else_rhs = aux else_;
              }
        | _ -> Plain term)
  in
  aux term

let rec inline_accel_rhs inline_map = function
  | Plain term -> subst_inlineable_calls inline_map term
  | GeoExpectation geo -> GeoExpectation geo
  | IfThenElse { guard; then_rhs; else_rhs } ->
      IfThenElse
        {
          guard;
          then_rhs = inline_accel_rhs inline_map then_rhs;
          else_rhs = inline_accel_rhs inline_map else_rhs;
        }

let eliminate_inlineable_preds accel_problem =
  let query_name = query_predicate accel_problem.query in
  let inline_map =
    accel_problem.preds
    |> List.filter_map ~f:(fun pred ->
           if
             Option.exists query_name ~f:(fun name ->
                 Ident.tvar_equal name pred.original_pred.name)
           then None
           else
             Option.map (inlineable_accel_rhs pred) ~f:(fun rhs ->
                 (pred.original_pred.name, rhs)))
    |> Map.Poly.of_alist_exn
  in
  if Map.is_empty inline_map then accel_problem
  else
    {
      accel_problem with
      preds =
        accel_problem.preds
        |> List.filter ~f:(fun pred ->
               not (Map.mem inline_map pred.original_pred.name))
        |> List.map ~f:(fun pred ->
               { pred with body = inline_accel_rhs inline_map pred.body });
    }
let fvar_app_of_term = function
  | Term.FunApp (FVar (name, _, _), args, _) -> Some (name, args)
  | _ -> None

type weighted_call = {
  coeff : Q.t;
  pred_name : Ident.tvar;
  call_args : Term.t list;
}

type weighted_sum_nf = {
  calls : weighted_call list;
  residuals : Term.t list;
  reasons : string list;
}

let empty_weighted_sum_nf = { calls = []; residuals = []; reasons = [] }

let append_weighted_sum_nf nf1 nf2 =
  {
    calls = nf1.calls @ nf2.calls;
    residuals = nf1.residuals @ nf2.residuals;
    reasons = nf1.reasons @ nf2.reasons;
  }

let scale_weighted_sum_nf q nf =
  {
    calls = List.map nf.calls ~f:(fun call -> { call with coeff = Q.mul q call.coeff });
    residuals =
      List.map nf.residuals ~f:(fun term -> real_mul_q q term);
    reasons = nf.reasons;
  }

let scaled_call_of_term term =
  match fvar_app_of_term term with
  | Some (name, args) -> Some { coeff = Q.one; pred_name = name; call_args = args }
  | None -> (
      match term with
      | Term.FunApp ((T_real.RMul | T_int.Mul | T_num.NMul _), [ t1; t2 ], _) -> (
          match (rational_of_term t1, fvar_app_of_term t2) with
          | Some coeff, Some (name, args) ->
              Some { coeff; pred_name = name; call_args = args }
          | _ -> (
              match (rational_of_term t2, fvar_app_of_term t1) with
              | Some coeff, Some (name, args) ->
                  Some { coeff; pred_name = name; call_args = args }
              | _ -> None))
      | _ -> None)

(* this was a second copy of [term_has_predicate_call] above, with the same
   blind spot; one definition now, so the two cannot answer differently *)
let has_predicate_call = term_has_predicate_call

let is_product_with_predicate_call = function
  | Term.FunApp ((T_real.RMul | T_int.Mul | T_num.NMul _), [ t1; t2 ], _) ->
      has_predicate_call t1 || has_predicate_call t2
  | _ -> false

let rec weighted_predicate_call_sum_nf term =
  match term with
  | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _) ->
      append_weighted_sum_nf (weighted_predicate_call_sum_nf t1)
        (weighted_predicate_call_sum_nf t2)
  | Term.FunApp ((T_real.RSub | T_int.Sub | T_num.NSub _), [ t1; t2 ], _) ->
      append_weighted_sum_nf (weighted_predicate_call_sum_nf t1)
        (scale_weighted_sum_nf Q.minus_one (weighted_predicate_call_sum_nf t2))
  | Term.FunApp ((T_real.RNeg | T_int.Neg | T_num.NNeg _), [ t ], _) ->
      scale_weighted_sum_nf Q.minus_one (weighted_predicate_call_sum_nf t)
  | _ -> (
      match scaled_call_of_term term with
      | Some call -> { empty_weighted_sum_nf with calls = [ call ] }
      | None -> (
          match rational_of_term term with
          | Some q when Q.equal q Q.zero -> empty_weighted_sum_nf
          | _ ->
              let reason =
                if is_product_with_predicate_call term then
                  "non-constant coefficient"
                else if has_predicate_call term then "unsupported RHS normal form"
                else "residual term exists"
              in
              { empty_weighted_sum_nf with residuals = [ term ]; reasons = [ reason ] }))

let same_weighted_call_target call1 call2 =
  Ident.tvar_equal call1.pred_name call2.pred_name
  && Stdlib.(call1.call_args = call2.call_args)

let combine_weighted_calls calls =
  List.fold calls ~init:[] ~f:(fun acc call ->
      let matched, acc =
        List.fold acc ~init:(false, []) ~f:(fun (matched, acc) old ->
            if (not matched) && same_weighted_call_target old call then
              ( true,
                { old with coeff = Q.add old.coeff call.coeff } :: acc )
            else (matched, old :: acc))
      in
      if matched then List.rev acc else call :: List.rev acc)
  |> List.rev
  |> List.filter ~f:(fun call -> not (Q.equal call.coeff Q.zero))

let normalized_weighted_predicate_call_sum_nf term =
  let nf = weighted_predicate_call_sum_nf term in
  { nf with calls = combine_weighted_calls nf.calls }

let is_residual_exit_shape self_calls exit_calls nf =
  List.length self_calls = 1
  && List.is_empty exit_calls
  && not (List.is_empty nf.residuals)

let rec contains_ite = function
  | Term.FunApp (T_bool.IfThenElse, _, _) -> true
  (* a conditional can be inside a formula that is itself inside a term, and
     this used to stop at the term *)
  | Term.FunApp (T_bool.Formula phi, args, _) ->
      (Fn.non Set.is_empty
      @@ Formula.filtered_terms_of phi ~f:(function
           | Term.FunApp (T_bool.IfThenElse, _, _) -> true
           | _ -> false))
      || List.exists args ~f:contains_ite
  | Term.FunApp (_, args, _) -> List.exists args ~f:contains_ite
  | Term.LetTerm (_, _, def, body, _) -> contains_ite def || contains_ite body
  | Term.Var _ -> false

let detection_failure_reasons_of_body (pred : Pred.t) body =
  let nf = normalized_weighted_predicate_call_sum_nf body in
  let self_calls, exit_calls =
    List.partition_tf nf.calls ~f:(fun call ->
        Ident.tvar_equal call.pred_name pred.name)
  in
  let residual_exit_shape = is_residual_exit_shape self_calls exit_calls nf in
  let nf_reasons =
    if residual_exit_shape then
      List.filter nf.reasons ~f:(fun reason ->
          not (String.equal reason "residual term exists"))
    else nf.reasons
  in
  nf_reasons
  @
  (if List.is_empty nf.residuals then []
   else if residual_exit_shape then []
   else [ "residual term exists" ])
  @
  (if List.length nf.calls = 2
      || residual_exit_shape
   then []
   else [ "predicate call count is not two" ])
  @
  (match List.length self_calls with
  | 1 -> []
  | 0 -> [ "missing self call" ]
  | _ -> [ "multiple self calls" ])
  @
  (match List.length exit_calls with
  | 1 -> []
  | 0 ->
      if List.length self_calls = 1 && not (List.is_empty nf.residuals) then []
      else [ "missing exit call" ]
  | _ -> [ "multiple exit calls" ])
  @
  if List.exists nf.calls ~f:(fun call -> Q.(call.coeff < zero)) then
    [ "negative coefficient" ]
  else []

let coefficient_failure_reasons self_call exit_call =
  let recursive_coeff = self_call.coeff in
  let exit_probability = exit_call.coeff in
  let recursive_update = self_call.call_args in
  let exit_update = exit_call.call_args in
  (if List.exists (recursive_update @ exit_update) ~f:contains_ite then
     [ "unsupported RHS normal form" ]
   else [])
  @
  if not (Q.equal Q.(recursive_coeff + exit_probability) Q.one) then
    [ "coefficient sum is not one" ]
  else []

let residual_exit_body_of_nf recursive_coeff nf =
  let exit_probability = Q.(one - recursive_coeff) in
  if Q.(exit_probability <= zero) || Q.(exit_probability > one) then
    Error [ "invalid probability or coefficient" ]
  else if List.is_empty nf.residuals then Error [ "missing residual exit" ]
  else if List.exists nf.residuals ~f:has_predicate_call then
    Error [ "unsupported RHS normal form" ]
  else
    let residual =
      List.fold nf.residuals ~init:(real_zero ()) ~f:real_add
    in
    Ok (exit_probability, real_mul_q Q.(one / exit_probability) residual)

let residual_fvar_app = function
  | Some term -> fvar_app_of_term term
  | None -> None

let subst_params_in_terms params args terms =
  let subst =
    Map.Poly.of_alist_exn
    @@ List.map2_exn params args ~f:(fun (param, _) arg -> (param, arg))
  in
  List.map terms ~f:(Term.subst subst)

let guard_false_after_update params update guard =
  let subst =
    Map.Poly.of_alist_exn
    @@ List.map2_exn params update ~f:(fun (param, _) arg -> (param, arg))
  in
  Formula.is_false
  @@ Evaluator.simplify
  @@ Normalizer.normalize
  @@ Formula.and_of
  @@ List.map guard ~f:(Formula.subst subst)

let exit_call_via_guard_false pred guard residual_body call =
  match residual_fvar_app residual_body with
  | Some (exit_pred, residual_args)
    when guard_false_after_update pred.Pred.args call.call_args guard ->
      Some
        {
          call with
          pred_name = exit_pred;
          call_args =
            subst_params_in_terms pred.Pred.args call.call_args residual_args;
        }
  | _ -> None

let detection_failure_reasons_of_pattern (pred : Pred.t) body =
  let nf = normalized_weighted_predicate_call_sum_nf body in
  let self_calls, exit_calls =
    List.partition_tf nf.calls ~f:(fun call ->
        Ident.tvar_equal call.pred_name pred.name)
  in
  match (detection_failure_reasons_of_body pred body, self_calls, exit_calls) with
  | [], [ self_call ], [ exit_call ] ->
      coefficient_failure_reasons self_call exit_call
  | [], [ self_call ], [] -> (
      match residual_exit_body_of_nf self_call.coeff nf with
      | Ok _ -> []
      | Error reasons -> reasons)
  | reasons, _, _ -> reasons

let detection_of_exit_call pred guard residual_body self_call exit_call =
  let recursive_coeff = self_call.coeff in
  let exit_probability = exit_call.coeff in
  let recursive_update = self_call.call_args in
  let exit_update = exit_call.call_args in
  let normalized_exit_body = pred_call exit_call.pred_name exit_update in
  let reasons = coefficient_failure_reasons self_call exit_call in
  if List.is_empty reasons then
    Some
      {
        self_pred = pred.Pred.name;
        exit_pred = exit_call.pred_name;
        exit_body = None;
        normalized_exit_body;
        params = pred.args;
        guard;
        residual_body;
        recursive_coeff;
        exit_probability;
        recursive_update;
        exit_update;
      }
  else None

let detection_of_residual_exit pred guard residual_body nf self_call =
  let recursive_coeff = self_call.coeff in
  let recursive_update = self_call.call_args in
  if List.exists recursive_update ~f:contains_ite then None
  else
    match residual_exit_body_of_nf recursive_coeff nf with
    | Error _ -> None
    | Ok (exit_probability, exit_body) ->
        Some
          {
            self_pred = pred.Pred.name;
            exit_pred = pred.Pred.name;
            exit_body = Some exit_body;
            normalized_exit_body = exit_body;
            params = pred.args;
            guard;
            residual_body;
            recursive_coeff;
            exit_probability;
            recursive_update;
            exit_update = List.map pred.args ~f:term_of_param;
          }

let term_of_weighted_call call =
  real_mul_q call.coeff (pred_call call.pred_name call.call_args)

let exit_remainder_of_nf exit_calls residuals =
  List.fold
    (List.map exit_calls ~f:term_of_weighted_call @ residuals)
    ~init:(real_zero ()) ~f:real_add

(** Normalizes all non-continuation terms as the exit body [R / (1-q)]. *)
let detection_of_exit_remainder pred guard residual_body nf self_call exit_calls =
  let recursive_coeff = self_call.coeff in
  let exit_probability = Q.(one - recursive_coeff) in
  let recursive_update = self_call.call_args in
  let exit_remainder = exit_remainder_of_nf exit_calls nf.residuals in
  let self_exit_calls =
    List.filter exit_calls ~f:(fun call ->
        Ident.tvar_equal call.pred_name pred.Pred.name)
  in
  if
    Q.(recursive_coeff < zero)
    || Q.(recursive_coeff >= one)
    || List.exists recursive_update ~f:contains_ite
    || List.exists exit_calls ~f:(fun call -> Q.(call.coeff < zero))
    || List.exists exit_calls ~f:(fun call ->
           List.exists call.call_args ~f:contains_ite)
    || List.length self_exit_calls > 1
    || List.exists nf.residuals
         ~f:(term_contains_fvar pred.Pred.name)
  then None
  else
    let normalized_exit_body =
      Evaluator.simplify_term
      @@ Normalizer.normalize_term
      @@ real_mul_q Q.(one / exit_probability) exit_remainder
    in
    Some
      {
        self_pred = pred.Pred.name;
        (* Compatibility metadata only.  General self-free exits are represented
           authoritatively by [normalized_exit_body]. *)
        exit_pred = pred.Pred.name;
        exit_body = Some normalized_exit_body;
        normalized_exit_body;
        params = pred.args;
        guard;
        residual_body;
        recursive_coeff;
        exit_probability;
        recursive_update;
        exit_update = List.map pred.args ~f:term_of_param;
      }

let detect_pattern (pred : Pred.t) guard residual_body body =
  let nf = normalized_weighted_predicate_call_sum_nf body in
  let self_calls, exit_calls =
    List.partition_tf nf.calls ~f:(fun call ->
        Ident.tvar_equal call.pred_name pred.name)
  in
  let guard_classified =
    match (self_calls, exit_calls) with
    | [ self_call1; self_call2 ], [] -> (
        match
          ( exit_call_via_guard_false pred guard residual_body self_call1,
            exit_call_via_guard_false pred guard residual_body self_call2 )
        with
        | Some exit_call, None -> Some (self_call2, exit_call)
        | None, Some exit_call -> Some (self_call1, exit_call)
        | _ -> None)
    | _ -> None
  in
  match guard_classified with
  | Some (self_call, exit_call) ->
      Option.to_list
      @@ detection_of_exit_call pred guard residual_body self_call exit_call
  | None -> (
      match self_calls with
      | [ self_call ] -> (
          match (exit_calls, nf.residuals) with
          | [ exit_call ], [] ->
              Option.to_list
              @@ detection_of_exit_call pred guard residual_body self_call
                   exit_call
          | [], _ :: _ ->
              Option.to_list
              @@ detection_of_residual_exit pred guard residual_body nf self_call
          | _, _ ->
              Option.to_list
              @@ detection_of_exit_remainder pred guard residual_body nf self_call
                   exit_calls)
      | [ _; _ ] ->
          List.filter_mapi self_calls ~f:(fun continuation_index self_call ->
              let remaining_self_calls =
                List.filteri self_calls ~f:(fun i _ -> i <> continuation_index)
              in
              detection_of_exit_remainder pred guard residual_body nf self_call
                (remaining_self_calls @ exit_calls))
      | _ -> [])

let rec detect_in_term (pred : Pred.t) guard residual_body = function
  | Term.FunApp (T_bool.IfThenElse, [ cond; then_; else_ ], _) ->
      let phi = Formula.of_bool_term cond in
      detect_in_term pred (guard @ [ phi ]) (Some else_) then_
      @ detect_in_term pred
          (guard @ [ Formula.negate phi ])
          (Some then_) else_
  | body -> detect_pattern pred guard residual_body body

let detect_pred (pred : Pred.t) =
  detect_in_term pred [] None pred.body

let rec detection_fallback_reasons_in_term pred = function
  | Term.FunApp (T_bool.IfThenElse, [ _cond; then_; else_ ], _) ->
      detection_fallback_reasons_in_term pred then_
      @ detection_fallback_reasons_in_term pred else_
  | body ->
      if not (List.is_empty (detect_pattern pred [] None body)) then []
      else detection_failure_reasons_of_pattern pred body

let str_of_detection_fallback_reasons pred =
  let reasons =
    detection_fallback_reasons_in_term pred pred.body
    |> List.filter ~f:(Fn.non String.is_empty)
    |> List.stable_dedup ~compare:String.compare
  in
  match reasons with
  | [] -> "none"
  | _ ->
      sprintf "\n%s"
      @@ String.concat_map_list ~sep:"\n" reasons ~f:(fun reason ->
             sprintf "    - %s" reason)

let detect_geometric (qfl : Problem.t) =
  List.concat_map qfl.preds ~f:detect_pred

let str_of_detections detections =
  String.concat_map_list ~sep:"\n" detections ~f:str_of_detection

let zero_of_sort = function
  | T_int.SInt -> Some (T_int.zero ())
  | T_real.SReal -> Some (T_real.rzero ())
  | _ -> None

let add_of_sort sort =
  match sort with
  | T_int.SInt -> Some T_int.mk_add
  | T_real.SReal -> Some T_real.mk_radd
  | _ -> None

let sub_of_sort sort =
  match sort with
  | T_int.SInt -> Some T_int.mk_sub
  | T_real.SReal -> Some T_real.mk_rsub
  | _ -> None

let mul_of_sort sort =
  match sort with
  | T_int.SInt -> Some T_int.mk_mul
  | T_real.SReal -> Some T_real.mk_rmul
  | _ -> None

let translation_delta (x, sort) update =
  let var = term_of_param (x, sort) in
  if Stdlib.(update = var) then zero_of_sort sort
  else
    match update with
    | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _)
      when Stdlib.(t1 = var) ->
        Some t2
    | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _)
      when Stdlib.(t2 = var) ->
        Some t1
    | Term.FunApp ((T_real.RSub | T_int.Sub | T_num.NSub _), [ t1; t2 ], _)
      when Stdlib.(t1 = var) ->
        Option.bind (sub_of_sort sort) ~f:(fun sub ->
            Option.map (zero_of_sort sort) ~f:(fun zero -> sub zero t2))
    | _ -> None

let iterated_recursive_args params recursive_update k_var =
  let k = Term.mk_var k_var T_real.SReal in
  Common.Timer.try_with_sync (fun () ->
      List.map2_exn params recursive_update ~f:(fun ((x, sort) as param) update ->
          let var = term_of_param param in
          let delta = Option.value_exn (translation_delta (x, sort) update) in
          if
            match zero_of_sort sort with
            | Some zero -> Stdlib.(delta = zero)
            | None -> false
          then var
          else
            let mul = Option.value_exn (mul_of_sort sort) in
            let add = Option.value_exn (add_of_sort sort) in
            let k =
              match sort with
              | T_real.SReal -> k
              | T_int.SInt -> Term.mk_var k_var T_int.SInt
              | _ -> k
            in
            Evaluator.simplify_term @@ add var (mul k delta)))

let accelerated_exit_args params recursive_update exit_update k_var =
  Option.bind
    (iterated_recursive_args params recursive_update k_var)
    ~f:(fun iter_args ->
      let subst =
        Map.Poly.of_alist_exn
        @@ List.map2_exn params iter_args ~f:(fun (param, _) arg -> (param, arg))
      in
      Some
        (List.map exit_update ~f:(fun arg ->
             Evaluator.simplify_term @@ Term.subst subst arg)))

let accelerated_exit_body params recursive_update exit_body k_var =
  Option.bind exit_body ~f:(fun exit_body ->
      Option.bind
        (iterated_recursive_args params recursive_update k_var)
        ~f:(fun iter_args ->
          let subst =
            Map.Poly.of_alist_exn
            @@ List.map2_exn params iter_args ~f:(fun (param, _) arg ->
                   (param, arg))
          in
          Some (Evaluator.simplify_term @@ Term.subst subst exit_body)))

(** Iterates the recursive update and constructs its geometric expectation. *)
let geo_expectation_of_detection ?(k_var = Ident.Tvar "k") (det : detection) =
  let accelerated_exit_args =
    if Option.is_some det.exit_body then None
    else accelerated_exit_args det.params det.recursive_update det.exit_update k_var
  in
  let accelerated_exit_body =
    accelerated_exit_body det.params det.recursive_update
      (Some det.normalized_exit_body) k_var
  in
  let guard = guard_option_of_list det.guard in
  {
    self_pred = det.self_pred;
    exit_pred = det.exit_pred;
    exit_body = det.exit_body;
    normalized_exit_body = det.normalized_exit_body;
    guard;
    residual_body = det.residual_body;
    p = det.exit_probability;
    recursive_coeff = det.recursive_coeff;
    k_var;
    original_params = det.params;
    original_args = List.map det.params ~f:term_of_param;
    recursive_update = det.recursive_update;
    exit_update = det.exit_update;
    accelerated_exit_args;
    accelerated_exit_body;
    status =
      (match (accelerated_exit_args, accelerated_exit_body) with
      | Some _, _ | _, Some _ -> ClosedFormGenerated
      | None, None -> NeedClosedForm);
    verification_conditions =
      verification_conditions_of_guard det.params det.recursive_update guard;
  }

let geo_expectations_of_detections =
  List.map ~f:geo_expectation_of_detection

let accel_rhs_of_geo original_body geo =
  match geo.guard with
  | None -> GeoExpectation geo
  | Some guard ->
      IfThenElse
        {
          guard = T_bool.of_formula guard;
          then_rhs = GeoExpectation geo;
          else_rhs =
            Plain (Option.value geo.residual_body ~default:original_body);
        }

let accelerate_pred pred =
  let geos = geo_expectations_of_detections @@ detect_pred pred in
  (* TODO: support multiple Applicable candidates in one predicate. *)
  let replacement =
    List.find_mapi geos ~f:(fun i geo ->
        match applicability_of_geo_expectation geo with
        | Applicable -> Some (i, geo)
        | ConditionallyApplicable _ | Blocked _ -> None)
  in
  let body =
    match replacement with
    | Some (_, geo) -> accel_rhs_of_geo pred.body geo
    | None -> Plain pred.body
  in
  let candidates =
    List.mapi geos ~f:(fun i geo ->
        let applicability = applicability_of_geo_expectation geo in
        let action =
          match replacement with
          | Some (j, _) when i = j -> ReplacedByGeoExpectation
          | _ -> KeepOriginalBody
        in
        { geo; applicability; action })
  in
  let detection_fallback_reasons =
    if List.is_empty candidates then
      detection_fallback_reasons_in_term pred pred.body
      |> List.stable_dedup ~compare:String.compare
    else []
  in
  { original_pred = pred; body; candidates; detection_fallback_reasons }

let accelerate_applicable (qfl : Problem.t) =
  eliminate_inlineable_preds {
    original_problem = qfl;
    preds = List.map qfl.preds ~f:accelerate_pred;
    query = qfl.query;
  }

let detect_geometric_expectations qfl =
  geo_expectations_of_detections @@ detect_geometric qfl

let active_original_preds accel_problem =
  List.map accel_problem.preds ~f:(fun pred -> pred.original_pred)

let active_pred_names accel_problem =
  Set.Poly.of_list
  @@ List.map accel_problem.preds ~f:(fun pred -> pred.original_pred.name)

let rec exact_term_of_accel_rhs = function
  | Plain term -> Some term
  | GeoExpectation geo ->
      Option.bind geo.accelerated_exit_body ~f:(fun body ->
          lower_affine_geo_expectation_term ~k_var:geo.k_var ~p:geo.p body)
  | IfThenElse { guard; then_rhs; else_rhs } ->
      Option.map2 (exact_term_of_accel_rhs then_rhs)
        (exact_term_of_accel_rhs else_rhs) ~f:(fun then_ else_ ->
          T_bool.mk_if_then_else guard then_ else_)

let has_applicable_replacement pred =
  List.exists pred.candidates ~f:(fun candidate ->
      match (candidate.action, candidate.applicability) with
      | ReplacedByGeoExpectation, Applicable -> true
      | _ -> false)

let accelerated_problem_to_qfl_if_exact accel_problem =
  if not (List.exists accel_problem.preds ~f:has_applicable_replacement) then None
  else
    Option.map
      (Option.all
      @@ List.map accel_problem.preds ~f:(fun pred ->
             Option.map (exact_term_of_accel_rhs pred.body) ~f:(fun body ->
                 { pred.original_pred with body })))
      ~f:(fun preds -> { accel_problem.original_problem with preds })

let verification_conditions_of_geo_expectations geos =
  List.concat_map geos ~f:(fun geo -> geo.verification_conditions)

let detect_geometric_verification_conditions qfl =
  verification_conditions_of_geo_expectations
  @@ detect_geometric_expectations qfl

let applicability_of_geo_expectations =
  List.map ~f:applicability_of_geo_expectation

let detect_geometric_applicabilities qfl =
  applicability_of_geo_expectations @@ detect_geometric_expectations qfl

let str_of_geo_expectations geos =
  String.concat_map_list ~sep:"\n" geos
    ~f:str_of_geo_expectation_with_applicability

let str_of_all_verification_conditions vcs =
  String.concat_map_list ~sep:"\n" vcs ~f:str_of_verification_condition

let str_of_applicabilities applicabilities =
  String.concat_map_list ~sep:"\n" applicabilities ~f:str_of_applicability
