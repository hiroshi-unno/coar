open Core
open Common.Ext
open Common.Util
open Common.Combinator

(** First-Order Fixpoint Logic with Theories *)

module Priority = struct
  type t = int
  let comma = 2
  let let_forall_exists = comma + 2
  let imply_iff_xor = let_forall_exists + 2
  let binary_or = imply_iff_xor + 2
  let binary_and = binary_or + 2
  let eq_neq_lt_leq_gt_geq = binary_and + 2
  let add_sub = eq_neq_lt_leq_gt_geq + 2
  let mult_div_mod = add_sub + 2
  let neg_abs = mult_div_mod + 2
  let power = neg_abs + 2
  let fun_app = power + 2

  let add_bracket outer_priority inner_priority inner_str =
    if inner_priority < outer_priority then
      "(" ^ inner_str ^ ")"
    else inner_str
end

module Value = struct
  type t = Bool of bool | Int of Z.t | Real of Q.t

  let neg = function
    | Int i -> Int (Z.neg i) | Real r -> Real (Q.neg r)
    | Bool _ -> failwith "type error @ Value.neg"
  let abs = function
    | Int i -> Int (Z.abs i) | Real r -> Real (Q.abs r)
    | Bool _ -> failwith "type error @ Value.abs"

  let compare opi opr ?(opb=fun _ _ -> assert false) t1 t2 =
    match t1, t2 with
    | Int i1, Int i2 -> opi i1 i2
    | Real r1, Real r2 -> opr r1 r2
    | Bool b1, Bool b2 -> opb b1 b2
    | Int i, Real r -> opr (Q.of_bigint i) r
    | Real r, Int i -> opr r (Q.of_bigint i)
    | _ -> failwith "type error @ Value.compare"

  let bop opi opr ?(opb=fun _ _ -> assert false) t1 t2 =
    match t1, t2 with
    | Int i1, Int i2 -> Int (opi i1 i2)
    | Real r1, Real r2 -> Real (opr r1 r2)
    | Bool b1, Bool b2 -> Bool (opb b1 b2)
    | Int i, Real r -> Real (opr (Q.of_bigint i) r)
    | Real r, Int i -> Real (opr r (Q.of_bigint i))
    | _ -> failwith "type error @ Value.app_op"
  let add = bop (Z.(+)) (Q.(+))
  let sub = bop (Z.(-)) (Q.(-))
  let mult = bop (Z.( * )) (Q.( * ))
  let div = bop Z.ediv (Q.(/))
  let bmod = bop Z.erem (fun _a _b -> assert false(*Q.of_float @@ Float.mod_float (Q.to_float a) (Q.to_float b)*))
  let pow = bop (fun n1 n2 -> Z.pow n1 (Z.to_int n2)) (fun _ _ -> failwith "Value.pow for real numbers not implemented" (*ToDo*))

  let ite cond_ then_ else_ =
    match cond_ with
    | Bool true -> then_
    | Bool false -> else_
    | _ -> failwith "type error @ Value.ite"

  let str_of = function
    | Bool b -> string_of_bool b
    | Int n -> Z.to_string n
    | Real r -> Q.to_string r

  let bool_of = function
    | Bool b -> b
    | _ -> assert false
  let int_of = function
    | Int n -> n
    | _ -> assert false
  let real_of = function
    | Real r -> r
    | _ -> assert false
end

module Sort = struct
  type t = .. and e = .. and o = ..
  type t +=
    | SVar of Ident.svar
    | SArrow of t * (o * t * e)
    | SPoly of Ident.svar Set.Poly.t * t
  type e +=
    | EVar of Ident.evar
    | Pure
    | Eff of o * t * e * o * t * e
  type o +=
    | OpSig of (string, t) ALMap.t * Ident.rvar option (* Some r: open / None: closed *)

  (** Construction *)
  let empty_closed_opsig = OpSig (ALMap.empty, None)
  let mk_fresh_empty_open_opsig () = OpSig (ALMap.empty, Some (Ident.mk_fresh_rvar ()))
  let mk_empty_open_opsig_from_rvar rv = OpSig (ALMap.empty, Some rv)

  let mk_fresh_evar () = EVar (Ident.mk_fresh_evar ())

  let mk_fresh_svar () = SVar (Ident.mk_fresh_svar ())
  let mk_arrow s1 s2 = SArrow (s1, (empty_closed_opsig, s2, Pure))
  let rec mk_fun = function
    | [s] -> s
    | s :: ss -> mk_arrow s (mk_fun ss)
    | _ -> assert false
  let rec of_args_ret_pure args ret =
    match args with
    | [] -> ret
    | hd :: tl -> SArrow (hd, (mk_fresh_empty_open_opsig (), of_args_ret_pure tl ret, Pure))
  let rec of_args_ret ?opsig sargs sret =
    match sargs with
    | [] -> [], [], sret
    | sarg :: sargs' ->
      let evar = mk_fresh_evar () in
      let ovar =
        match opsig with
        | Some opsig -> opsig
        | None -> mk_fresh_empty_open_opsig ()
      in
      let ovars, evars, sret' = of_args_ret ?opsig sargs' sret in
      ovar :: ovars,
      evar :: evars,
      SArrow (sarg, (ovar, sret', evar))
  let mk_poly svs s = if Set.Poly.is_empty svs then s else SPoly (svs, s)

  (** Observation *)
  let is_empty_closed_opsig = function
    | OpSig (map, None) -> ALMap.is_empty map
    | _ -> false
  let is_empty_opsig = function
    | OpSig (map, _) -> ALMap.is_empty map
    | _ -> false

  let is_pure = function Pure -> true | _ -> false

  let is_svar = function
    | SVar _ -> true
    | _ -> false
  let is_arrow = function
    | SArrow _ -> true
    | _ -> false
  let rec arity_of = function
    | SArrow (_s1, (_, s2, _)) -> 1 + arity_of s2
    | _ -> 0 (* assert false*)
  let rec ret_of = function
    | SArrow (_s1, (_, s2, _)) -> ret_of s2
    | sort -> sort
  let rec args_of = function
    | SArrow (s1, (_, s2, _)) ->
      let args = args_of s2 in
      s1 :: args
    | _ -> []
  let rec args_ret_of = function
    | SArrow (s1, (_, s2, _)) ->
      let args, ret = args_ret_of s2 in
      s1 :: args, ret
    | s -> [], s
  let rec mono_type_of = function
    | SPoly (_, s) -> mono_type_of s
    | s -> s
  let rec poly_env_of = function
    | SPoly (svs, s) -> Set.Poly.union svs (poly_env_of s)
    | _ -> Set.Poly.empty
end

type sort_bind = Ident.tvar * Sort.t
type sort_env_set = sort_bind Set.Poly.t
type sort_env_list = sort_bind list
type sort_env_map = (Ident.tvar, Sort.t) Map.Poly.t

type pred_bind = Ident.pvar * Sort.t list
type pred_sort_env_set = pred_bind Set.Poly.t
type pred_sort_env_list = pred_bind list
type pred_sort_env_map = (Ident.pvar, Sort.t list) Map.Poly.t

let str_of_pred_sort_env_set str_of_sort penv =
  String.concat_map_set ~sep:", " penv ~f:(fun (ident, sorts) ->
      Printf.sprintf "(%s: %s)" (Ident.name_of_pvar ident) @@
      String.concat_map_list ~sep:" -> " ~f:str_of_sort sorts)

type sort_subst = (Ident.svar, Sort.t) Map.Poly.t
type eff_subst = (Ident.evar, Sort.e) Map.Poly.t
type opsig_subst = (Ident.rvar, Sort.o) Map.Poly.t

let str_of_sort_env_list str_of_sort senv =
  String.concat_map_list ~sep:" " senv ~f:(fun (tvar, sort) ->
      Printf.sprintf "(%s: %s)" (Ident.name_of_tvar tvar) (str_of_sort sort))
let str_of_sort_env_map str_of_sort senv =
  String.concat_map_list ~sep:" " (Map.Poly.to_alist senv) ~f:(fun (tvar, sort) ->
      Printf.sprintf "(%s: %s)" (Ident.name_of_tvar tvar) (str_of_sort sort))
let str_of_sort_subst str_of_sort sub =
  String.concat_map_list ~sep:", " (Map.Poly.to_alist sub) ~f:(fun (svar, sort) ->
      Printf.sprintf "(%s |-> %s)" (Ident.name_of_svar svar) (str_of_sort sort))

let update_sort_subst subst_sorts_sort smap svar sort =
  Map.Poly.add_exn
    (Map.Poly.map smap ~f:(subst_sorts_sort (Map.Poly.singleton svar sort)))
    ~key:svar ~data:sort

let mk_fresh_sort_env_list sorts =
  List.map sorts ~f:(fun sort -> Ident.mk_fresh_tvar (), sort)
(* val sort_env_list_of_sorts: ?pre:string -> Sort.t list -> sort_env_list *)
let sort_env_list_of_sorts ?(pre="") sorts =
  let param_ident_count = ref 0 in
  let mk_param_ident () =
    incr param_ident_count;
    Ident.Tvar (pre ^ "x" ^ string_of_int !param_ident_count)
  in
  List.map sorts ~f:(fun sort -> mk_param_ident (), sort)
(*val refresh_sort_env_list : sort_env_list -> sort_env_list * Ident.tvar_map*)
let refresh_sort_env_list senv =
  let senv' = List.map ~f:(fun (_, s) -> Ident.mk_fresh_tvar (), s) senv in
  let rename = List.zip_exn senv senv'
               |> List.map ~f:(fun ((x, _), (x', _)) -> x, x')
               |> Map.Poly.of_alist_exn in
  senv', rename
(*val normalize_sort_env_list : sort_env_list -> sort_env_list * Ident.tvar_map*)
let normalize_sort_env_list senv =
  let senv' = sort_env_list_of_sorts @@ List.map ~f:snd senv in
  let rename = List.zip_exn senv senv'
               |> List.map ~f:(fun ((x, _), (x', _)) -> x, x')
               |> Map.Poly.of_alist_exn in
  senv', rename
(* val tvar_map_of_sort_env_list : sort_env_list -> sort_env_list -> Ident.tvar_map *)
let tvar_map_of_sort_env_list senv1 senv2 =
  Map.Poly.of_alist_exn @@ List.map2_exn senv1 senv2 ~f:(fun (x1, _) (x2, _) -> x1, x2)

type info = ..
type info += Dummy
type fun_sym = ..
type fun_sym += FunCall of string | FVar of Ident.tvar * Sort.t list
type pred_sym = ..

let defined_fvars: Ident.tvar Hash_set.Poly.t = Hash_set.Poly.create ()

module Type = struct
  module type TermType = sig
    type atom
    type formula
    type termSubst
    type predSubst
    type dtenv

    type t =
      | Var of Ident.tvar * Sort.t * info
      | FunApp of fun_sym * t list * info
      | LetTerm of Ident.tvar * Sort.t * t * t * info

    (** Construction *)
    val mk_var : ?info:info -> Ident.tvar -> Sort.t -> t
    val mk_fresh_var : Sort.t -> t
    val mk_fsym_app : ?info:info -> fun_sym -> t list -> t
    val mk_fvar_app : ?info:info -> Ident.tvar -> Sort.t list -> t list -> t
    val mk_let_term : ?info:info -> Ident.tvar -> Sort.t -> t -> t -> t
    val insert_let_term : Ident.tvar -> Sort.t -> t -> info -> t -> t
    val mk_dummy : Sort.t -> t
    val of_value : Value.t -> t
    val of_sort_env : sort_env_list -> t list

    (** Observation *)
    val is_fvar_sym : fun_sym -> bool

    val is_var : t -> bool
    val is_app : t -> bool
    val is_funcall: t -> bool
    val is_fvar_app : t -> bool
    val is_let_term : t -> bool
    val is_numerical_compound : t -> bool
    val is_pathexp : t -> bool
    val is_uninterpreted_term : t -> bool

    val tvs_of : t -> Ident.tvar Set.Poly.t
    val pvs_of : t -> Ident.pvar Set.Poly.t
    val fvs_of : t -> Ident.tvar Set.Poly.t
    val svs_of : t -> Ident.svar Set.Poly.t
    val funsyms_of : t -> fun_sym Set.Poly.t
    val term_sort_env_of : t -> sort_env_set
    val pred_sort_env_of : ?bpvs:(Ident.pvar Set.Poly.t) -> t -> pred_sort_env_set
    val sort_env_of : ?bpvs:(Ident.pvar Set.Poly.t) -> t -> sort_env_set
    val fvar_apps_of : t -> t Set.Poly.t
    val pathexps_of : t -> t Set.Poly.t
    val filtered_terms_of : t -> f:(t -> bool) -> t Set.Poly.t
    val atoms_of : ?pos:bool -> t -> atom Set.Poly.t * atom Set.Poly.t
    val body_of_let : t -> t
    val number_of_pvar_apps : bool -> t -> int
    val ast_size : t -> int
    val occur_times : ?map:(Ident.tvar, int) Map.Poly.t -> Ident.tvar -> t -> int

    val occurs : Sort.t -> Sort.t -> bool
    val occurs_cont : Sort.t -> Sort.e -> bool
    val occurs_opsig : Sort.t -> Sort.o -> bool
    val value_of: t -> Value.t

    val is_bool_sort : Sort.t -> bool
    val is_int_sort : Sort.t -> bool
    val is_int_ref_sort : Sort.t -> bool
    val is_real_sort : Sort.t -> bool

    val sort_of : t -> Sort.t
    val sorts_of_sort : Sort.t -> Sort.t Set.Poly.t
    val svs_of_cont : Sort.e -> Ident.svar Set.Poly.t
    val svs_of_sort : Sort.t -> Ident.svar Set.Poly.t
    val svs_of_opsig : Sort.o -> Ident.svar Set.Poly.t
    val evs_of_cont : Sort.e -> Ident.evar Set.Poly.t
    val evs_of_sort : Sort.t -> Ident.evar Set.Poly.t
    val evs_of_opsig : Sort.o -> Ident.evar Set.Poly.t
    val rvs_of_cont : Sort.e -> Ident.rvar Set.Poly.t
    val rvs_of_sort : Sort.t -> Ident.rvar Set.Poly.t
    val rvs_of_opsig : Sort.o -> Ident.rvar Set.Poly.t

    (** Destruction *)
    val let_var : t -> sort_bind * info
    val let_app : t -> fun_sym * t list * info
    val let_fvar_app : t -> Ident.tvar * Sort.t list * t list * info
    val let_funcall: t -> string * t list * info
    val let_let_term : t -> Ident.tvar * Sort.t * t * t * info

    (** Substitution *)
    val rename : Ident.tvar_map -> t -> t
    val rename_pvars : Ident.pvar_map -> t -> t
    val rename_sorted_pvars : ((string * Sort.t list), Ident.pvar) Map.Poly.t -> t -> t
    val rename_fun_sym : Ident.tvar_map -> fun_sym -> fun_sym
    val alpha_rename_let : ?map:Ident.tvar_map -> t -> t
    val replace_let_formula_body : formula -> t -> t
    val replace_let_body : t -> t -> t
    val subst : termSubst -> t -> t
    val subst_preds : predSubst -> t -> t
    val subst_fun_sym : termSubst -> fun_sym -> fun_sym
    val subst_sorts : sort_subst -> t -> t
    val subst_sorts_fun_sym : sort_subst -> fun_sym -> fun_sym
    val subst_sorts_cont : sort_subst -> Sort.e -> Sort.e
    val subst_sorts_sort : sort_subst -> Sort.t -> Sort.t
    val subst_sorts_opsig : sort_subst -> Sort.o -> Sort.o
    val subst_conts : eff_subst -> t -> t
    val subst_conts_fun_sym : eff_subst -> fun_sym -> fun_sym
    val subst_conts_cont : eff_subst -> Sort.e -> Sort.e
    val subst_conts_sort : eff_subst -> Sort.t -> Sort.t
    val subst_conts_opsig : eff_subst -> Sort.o -> Sort.o
    val subst_opsigs : opsig_subst -> t -> t
    val subst_opsigs_fun_sym : opsig_subst -> fun_sym -> fun_sym
    val subst_opsigs_sort : opsig_subst -> Sort.t -> Sort.t
    val subst_opsigs_cont : opsig_subst -> Sort.e -> Sort.e
    val subst_opsigs_opsig : opsig_subst -> Sort.o -> Sort.o
    val subst_cont : opsig_subst * sort_subst * eff_subst -> Sort.e -> Sort.e
    val subst_sort : opsig_subst * sort_subst * eff_subst -> Sort.t -> Sort.t
    val subst_opsig : opsig_subst * sort_subst * eff_subst -> Sort.o -> Sort.o
    val subst_all : opsig_subst * sort_subst * eff_subst -> t -> t
    val aconv_tvar : t -> t
    val aconv_pvar : t -> t
    val fresh_conts_sort : Sort.t -> Sort.t
    val fresh_rvs_sort : Sort.t -> Sort.t
    val fresh_rvs_cont : Sort.e -> Sort.e
    val fresh_rvs_opsig : Sort.o -> Sort.o

    (** Transformation *)
    val elim_neq : t -> t
    val elim_ite : t -> (formula * t) list
    val elim_pvars : Ident.tvar Set.Poly.t -> t -> t
    val elim_let_with_unknowns : ?map:termSubst -> Ident.tvar Set.Poly.t -> t -> t
    val elim_let : ?map:termSubst -> t -> t
    val has_let : ?map:termSubst -> t -> bool
    val let_env_of : ?map:termSubst -> t -> termSubst
    val let_sort_env_of : ?map:sort_env_map -> t -> sort_env_map
    val instantiate_div0_mod0 : t -> t
    val extend_pred_params : Ident.pvar -> sort_env_list -> t -> t
    val find_div_mod : t list -> (t * t) Set.Poly.t
    val replace_div_mod : ((t * t), (Ident.tvar * Ident.tvar)) Map.Poly.t -> t -> t
    val rm_boolean_term : t -> formula
    val replace_papps : (atom, atom) Map.Poly.t -> t -> t
    val complete_psort : pred_sort_env_map -> t -> t
    val complete_tsort : termSubst -> t -> t

    val fold : t ->
      f: <
        ftvar : Ident.tvar -> Sort.t -> 'a;
        fvar : Ident.tvar -> Sort.t list -> 'a list -> 'a;
        fint : Z.t -> 'a;
        freal : Q.t -> 'a;
        fiadd : 'a -> 'a -> 'a;
        fisub : 'a -> 'a -> 'a;
        fimult : 'a -> 'a -> 'a;
        fidiv : 'a -> 'a -> 'a;
        fipower : 'a -> 'a -> 'a;
        fineg : 'a -> 'a;
        fimod : 'a -> 'a -> 'a;
        fradd : 'a -> 'a -> 'a;
        frsub : 'a -> 'a -> 'a;
        frmult : 'a -> 'a -> 'a;
        frdiv : 'a -> 'a -> 'a;
        frpower : 'a -> 'a -> 'a;
        frneg : 'a -> 'a;
        fformula : formula -> 'a;
        fite : 'a -> 'a -> 'a -> 'a;
        fdtcons : string -> Sort.t -> 'a list -> 'a;
        fdtsel : string -> Sort.t -> 'a -> 'a;
        fastore : 'a -> 'a -> 'a -> 'a;
        faselect : 'a -> 'a -> 'a
      > -> 'a
    val map_term : f:(t -> t) -> t -> t
    val iter_term : f:(t -> unit) -> t -> unit

    (** Printing *)
    val str_of_funsym : fun_sym -> string
    val str_of_triple : Sort.o * Sort.t * Sort.e -> string
    val str_of_sort : Sort.t -> string
    val str_of_cont : Sort.e -> string
    val str_of_opsig : Sort.o -> string
    val short_name_of_sort : Sort.t -> string
    val str_of : ?priority:Priority.t -> t -> string

    (** Unification and Pattern Matching *)
    val unify : Ident.tvar Set.Poly.t -> t -> t -> termSubst option
    val pattern_match : Ident.tvar Set.Poly.t -> t -> t -> termSubst option
    val pat_match_sort : Sort.t -> Sort.t -> opsig_subst * sort_subst * eff_subst
    val pat_match_cont : Sort.e -> Sort.e -> opsig_subst * sort_subst * eff_subst
    val pat_match_opsig : Sort.o -> Sort.o -> opsig_subst * sort_subst * eff_subst
  end

  module type PredicateType = sig
    type fixpoint = Mu | Nu

    type formula
    type term

    type t =
      | Var of pred_bind
      | Psym of pred_sym
      | Fixpoint of fixpoint * Ident.pvar * sort_env_list * formula

    (** Construction *)
    val mk_var: Ident.pvar -> Sort.t list -> t
    val mk_psym: pred_sym -> t
    val mk_fix: fixpoint -> Ident.pvar -> sort_env_list -> formula -> t

    (** Observation *)
    val is_var: t -> bool
    val is_psym: t -> bool
    val is_fix: t -> bool

    val tvs_of: t -> Ident.tvar Set.Poly.t
    val pvs_of: t -> Ident.pvar Set.Poly.t
    val fvs_of: t -> Ident.tvar Set.Poly.t
    val svs_of: t -> Ident.svar Set.Poly.t
    val term_sort_env_of: t -> sort_env_set
    val pred_sort_env_of: ?bpvs:(Ident.pvar Set.Poly.t) -> t -> pred_sort_env_set
    val sort_env_of: ?bpvs:(Ident.pvar Set.Poly.t) -> t -> sort_env_set
    val terms_of: t -> term Set.Poly.t
    val fvar_apps_of: t -> term Set.Poly.t

    val nesting_level: t -> int
    val number_of_quantifiers: t -> int

    (** Destruction *)
    val let_var: t -> pred_bind
    val let_psym: t -> pred_sym
    val let_fix: t -> fixpoint * Ident.pvar * sort_env_list * formula

    (** Substitution *)
    val rename: Ident.tvar_map -> t -> t
    val rename_pvars: Ident.pvar_map -> t -> t
    val rename_sorted_pvars : ((string * Sort.t list), Ident.pvar) Map.Poly.t -> t -> t
    val subst_neg: Ident.pvar -> t -> t
    val subst_sorts : sort_subst -> t -> t
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs : opsig_subst -> t -> t
    val aconv_tvar: t -> t
    val aconv_pvar: t -> t

    (** Transformation *)
    val negate: ?negate_formula:(formula -> formula) -> t -> t
    val complete_psort: pred_sort_env_map -> t -> t
    val flip_fixpoint: fixpoint -> fixpoint
    val extend_pred_params: Ident.pvar -> sort_env_list -> t -> t

    (** Printing *)
    val str_of_predsym: pred_sym -> string
    val str_of: t -> string
    val str_of_fixpoint: fixpoint -> string
  end

  module type AtomType = sig
    type predicate
    type term
    type termSubst
    type predSubst
    type formula

    type t =
      | True of info
      | False of info
      | App of predicate * term list * info

    (** Construction *)
    val mk_true : ?info:info -> unit -> t
    val mk_false : ?info:info -> unit -> t
    val mk_app : ?info:info -> predicate -> term list -> t
    val mk_psym_app : ?info:info -> pred_sym -> term list -> t
    val mk_pvar_app : ?info:info -> Ident.pvar -> Sort.t list -> term list -> t
    val pvar_app_of_senv : Ident.pvar * sort_env_list -> t
    val of_bool_var : Ident.tvar -> t
    val of_neg_bool_var : Ident.tvar -> t
    val of_bool_term : term -> t
    val of_neg_bool_term : term -> t
    val insert_let_pvar_app : Ident.tvar -> Sort.t -> term -> info -> t -> t

    (** Observation *)
    val is_true : t -> bool
    val is_false : t -> bool
    val is_app : t -> bool
    val is_psym_app : t -> bool
    val is_pvar_app : t -> bool
    val is_pvar_app_of : Ident.pvar -> t -> bool
    val occur : Ident.pvar -> t -> bool

    val tvs_of : t -> Ident.tvar Set.Poly.t
    val pvs_of : t -> Ident.pvar Set.Poly.t
    val fvs_of : t -> Ident.tvar Set.Poly.t
    val svs_of : t -> Ident.svar Set.Poly.t
    val funsyms_of : t -> fun_sym Set.Poly.t
    val term_sort_env_of : t -> sort_env_set
    val pred_sort_env_of : ?bpvs:(Ident.pvar Set.Poly.t) -> t -> pred_sort_env_set
    val sort_env_of : ?bpvs:(Ident.pvar Set.Poly.t) -> t -> sort_env_set
    val pathexps_of : t -> term Set.Poly.t
    val filtered_terms_of: t -> f:(term -> bool) -> term Set.Poly.t

    val terms_of : t -> term Set.Poly.t
    val fvar_apps_of : t -> term Set.Poly.t

    val nesting_level : t -> int
    val number_of_quantifiers : t -> int
    val number_of_pvar_apps : bool -> t -> int
    val count_pvar_apps : t -> (Ident.pvar * (int * int)) list
    val ast_size : t -> int

    (** Destruction *)
    val let_app : t -> predicate * term list * info
    val let_psym_app : t -> pred_sym * term list * info
    val let_pvar_app : t -> Ident.pvar * Sort.t list * term list * info
    val info_of_true : t -> info
    val info_of_false : t -> info
    val info_of : t -> info
    val pvar_of : t -> Ident.pvar

    (** Substitution *)
    val rename : Ident.tvar_map -> t -> t
    val rename_pvars : Ident.pvar_map -> t -> t
    val rename_sorted_pvars : ((string * Sort.t list), Ident.pvar) Map.Poly.t -> t -> t
    val alpha_rename_let : ?map:Ident.tvar_map -> t -> t
    val subst : termSubst -> t -> t
    val subst_preds : predSubst -> t -> formula
    val subst_neg : Ident.pvar -> t -> t
    val subst_sorts : sort_subst -> t -> t
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs : opsig_subst -> t -> t

    val aconv_tvar : t -> t
    val aconv_pvar : t -> t
    (** Transformation *)
    val refresh_tvar : sort_env_map * t -> sort_env_map * t
    val negate : ?negate_formula:(formula -> formula) -> t -> t
    val complete_psort : pred_sort_env_map -> t -> t
    val elim_neq : t -> formula
    val elim_ite : t -> formula
    val has_let : ?map:termSubst -> t -> bool
    val let_env_of : ?map:termSubst -> t -> termSubst
    val let_sort_env_of : ?map:sort_env_map -> t -> sort_env_map
    val instantiate_div0_mod0 : t -> t
    val find_div_mod : t -> (term * term) Set.Poly.t
    val replace_div_mod : ((term * term), (Ident.tvar * Ident.tvar)) Map.Poly.t -> t -> t
    val rm_boolean_term : t -> formula
    val extend_pred_params : Ident.pvar -> sort_env_list -> t -> t
    val occur_times : ?map:(Ident.tvar, int) Map.Poly.t -> Ident.tvar -> t -> int

    val instantiate : t -> t
    val map_term : f:(term -> term) -> t -> t
    val iter_term : f:(term -> unit) -> t -> unit
    val fold :
      f: <
        ftrue : unit -> 'a;
        ffalse : unit -> 'a;
        feq : term -> term -> 'a;
        fneq : term -> term -> 'a;
        fileq : term -> term -> 'a;
        frleq : term -> term -> 'a;
        figeq : term -> term -> 'a;
        frgeq : term -> term -> 'a;
        filt : term -> term -> 'a;
        frlt : term -> term -> 'a;
        figt : term -> term -> 'a;
        frgt : term -> term -> 'a;
        fipdiv : term -> term -> 'a;
        finpdiv : term -> term -> 'a;
        fpvar : Ident.pvar -> Sort.t list -> term list -> 'a
      > -> t -> 'a
    val fold_map_term :
      f: <
        ftrue : unit -> 'a;
        ffalse : unit -> 'a;
        feq : term -> term -> 'a;
        fneq : term -> term -> 'a;
        fileq : term -> term -> 'a;
        frleq : term -> term -> 'a;
        figeq : term -> term -> 'a;
        frgeq : term -> term -> 'a;
        filt : term -> term -> 'a;
        frlt : term -> term -> 'a;
        figt : term -> term -> 'a;
        frgt : term -> term -> 'a;
        fipdiv : term -> term -> 'a;
        finpdiv : term -> term -> 'a;
        fpvar : Ident.pvar -> Sort.t list -> term list -> 'a
      > -> ft: (term -> term) -> t -> 'a

    (* Printing *)
    val str_of : ?priority:Priority.t -> t -> string

    (* Unification and Pattern Matching *)
    val unify : Ident.tvar Set.Poly.t -> t -> t -> termSubst option
    val pattern_match : Ident.tvar Set.Poly.t -> t -> t -> termSubst option
  end

  module type FormulaType = sig
    type term
    type atom
    type rand
    type predicate_fixpoint
    type termSubst
    type predSubst

    type unop = Not
    type binop = And | Or | Imply | Iff | Xor
    type binder = Forall | Exists | Random of rand

    type t =
      | Atom of atom * info
      | UnaryOp of unop * t * info
      | BinaryOp of binop * t * t * info
      | Bind of binder * sort_env_list * t * info
      | LetRec of (predicate_fixpoint * Ident.pvar * sort_env_list * t) list * t * info
      | LetFormula of Ident.tvar * Sort.t * term * t * info

    (** Construction *)
    val mk_atom : ?info:info -> atom -> t
    val mk_unop : ?info:info -> unop -> t -> t

    val mk_neg :?info:info -> t -> t
    val mk_binop : ?info:info -> binop -> t -> t -> t
    val mk_and : ?info:info -> t -> t -> t
    val mk_or : ?info:info -> t -> t -> t
    val mk_imply : ?info:info -> t -> t -> t
    val mk_iff : ?info:info -> t -> t -> t
    val mk_xor : ?info:info -> t -> t -> t

    val mk_bind : ?info:info -> binder -> sort_env_list -> t -> t
    val mk_forall : ?info:info -> sort_env_list -> t -> t
    val mk_bind_if_bounded : ?info:info -> binder -> sort_env_list -> t -> t
    val mk_exists : ?info:info -> sort_env_list -> t -> t
    val mk_random : ?info:info -> rand -> sort_env_list -> t -> t
    val mk_forall_if_bounded : ?info:info -> sort_env_list -> t -> t
    val mk_exists_if_bounded : ?info:info -> sort_env_list -> t -> t
    val mk_binds : (binder * sort_env_list) list -> t -> t
    val mk_randoms : (Ident.tvar * rand) list -> t -> t
    val mk_let_formula : ?info:info -> Ident.tvar -> Sort.t -> term -> t -> t
    val insert_let_formula : Ident.tvar -> Sort.t -> term -> info -> t -> t

    val mk_letrec : ?info:info -> (predicate_fixpoint * Ident.pvar * sort_env_list * t) list -> t -> t
    val mk_false : ?info:info -> unit -> t
    val mk_true : ?info:info -> unit -> t

    val bind : ?info:info -> binder -> sort_env_list -> t -> t
    val forall : ?info:info -> sort_env_list -> t -> t
    val exists : ?info:info -> sort_env_list -> t -> t
    val bind_fvs : binder -> t -> t
    val bind_fvs_with_forall : t -> t
    val bind_fvs_with_exists : t -> t
    val or_of : ?info:info -> t list -> t
    val and_of : ?info:info -> t list -> t
    val xor_of : ?info:info -> t list -> t
    val of_bool_var : Ident.tvar -> t
    val of_neg_bool_var : Ident.tvar -> t
    val of_bool_term : term -> t
    val of_neg_bool_term : term -> t

    val geq : term -> term -> t
    val gt : term -> term -> t
    val leq : term -> term -> t
    val lt : term -> term -> t
    val eq : term -> term -> t
    val neq : term -> term -> t
    val mk_range : term -> Z.t -> Z.t -> t list
    val mk_range_opt : term -> Z.t option -> Z.t option -> t list

    (** Observation *)
    val is_atom : t -> bool
    val is_true : t -> bool
    val is_false : t -> bool
    val is_eq : t -> bool
    val is_unop : t -> bool
    val is_neg : t -> bool
    val is_binop : t -> bool
    val is_and : t -> bool
    val is_or : t -> bool
    val is_imply : t -> bool
    val is_iff : t -> bool
    val is_xor : t -> bool
    val is_bind : t -> bool
    val is_forall : t -> bool
    val is_exists : t -> bool
    val is_random : binder -> bool
    val is_letrec : t -> bool
    val is_let_formula : t -> bool

    val tvs_of : t -> Ident.tvar Set.Poly.t
    val pvs_of : t -> Ident.pvar Set.Poly.t
    val fvs_of : t -> Ident.tvar Set.Poly.t
    val svs_of : t -> Ident.svar Set.Poly.t
    val funsyms_of : t -> fun_sym Set.Poly.t
    val term_sort_env_of : t -> sort_env_set
    val pred_sort_env_of : ?bpvs:(Ident.pvar Set.Poly.t) -> t -> pred_sort_env_set
    val sort_env_of : ?bpvs:(Ident.pvar Set.Poly.t) -> t -> sort_env_set
    val pathexps_of : t -> term Set.Poly.t
    val body_of_let : t -> t

    val conjuncts_of : t -> t Set.Poly.t
    val disjuncts_of : t -> t Set.Poly.t

    val nesting_level : t -> int
    val number_of_quantifiers : t -> int
    val number_of_pvar_apps : bool -> t -> int
    val count_pvar_apps : t -> (Ident.pvar * (int * int)) list
    val ast_size : t -> int

    (** Destruction *)
    val let_atom : t -> atom * info
    val let_eq : t -> term * term * info
    val let_unop : t -> unop * t * info
    val let_neg : t -> t * info
    val let_binop : t -> binop * t * t * info
    val let_and : t -> t * t * info
    val let_or : t -> t * t * info
    val let_imply : t -> t * t * info
    val let_iff : t -> t * t * info
    val let_xor : t -> t * t * info
    val let_bind : t -> binder * sort_env_list * t * info
    val let_forall : t -> sort_env_list * t * info
    val let_exists : t -> sort_env_list * t * info
    val let_forall_or_formula : t -> sort_env_list * t * info
    val let_exists_or_formula : t -> sort_env_list * t * info
    val let_letrec : t -> (predicate_fixpoint * Ident.pvar * sort_env_list * t) list * t * info

    (** Substitution *)
    val rename : Ident.tvar_map -> t -> t
    val rename_pvars : Ident.pvar_map -> t -> t
    val rename_sorted_pvars : ((string * Sort.t list), Ident.pvar) Map.Poly.t -> t -> t
    val alpha_rename_let : ?map:Ident.tvar_map -> t -> t
    val replace_let_body : t -> t -> t
    val replace_let_term_body : term -> t -> t
    val subst : termSubst -> t -> t
    val subst_sorts_bounds : sort_subst -> sort_env_list -> sort_env_list
    val subst_sorts : sort_subst -> t -> t
    val subst_conts_bounds : eff_subst -> sort_env_list -> sort_env_list
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs_bounds : opsig_subst -> sort_env_list -> sort_env_list
    val subst_opsigs : opsig_subst -> t -> t
    val subst_preds : predSubst -> t -> t
    val subst_pvar : (Ident.pvar, t) Map.Poly.t -> t -> t
    val subst_neg : Ident.pvar -> t -> t
    val replace_papps : (atom, atom) Map.Poly.t -> t -> t
    val aconv_tvar : t -> t
    val aconv_pvar : t -> t

    (** Transformation *)
    val flip_quantifier : binder -> binder
    val reduce_sort_map : sort_env_map * t -> sort_env_map * t
    val refresh_tvar : sort_env_map * t -> sort_env_map * t
    val complete_psort : pred_sort_env_map -> t -> t
    val complete_tsort : t -> t
    val elim_neq : t -> t
    val elim_ite : t -> t
    val elim_pvars : Ident.tvar Set.Poly.t -> t -> t
    val elim_let_with_unknowns : ?map:termSubst -> Ident.tvar Set.Poly.t -> t -> t
    val elim_let : ?map:termSubst -> t -> t
    val elim_unused_bounds : t -> t
    val has_let : ?map:termSubst -> t -> bool
    val let_env_of : ?map:termSubst -> t -> termSubst
    val let_sort_env_of : ?map:sort_env_map -> t -> sort_env_map
    val equivalent_sat : t -> t
    val equivalent_valid : t -> t
    val equivalent_let : bool -> t -> t
    val instantiate_div0_mod0 : t -> t
    val rm_forall : t -> sort_env_set * t
    val move_quantifiers_to_front: t -> t
    val find_div_mod : t -> (term * term) Set.Poly.t
    val replace_div_mod : ((term * term), (Ident.tvar * Ident.tvar)) Map.Poly.t -> t -> t
    val rm_div_mod : t -> t
    val rm_boolean_term : t -> t
    val rm_atom : ?polarity:bool -> ?is_and:bool-> f:(atom-> bool) -> t -> t

    val extend_pred_params : Ident.pvar -> sort_env_list -> t -> t

    val terms_of : t -> term Set.Poly.t
    val atoms_of : ?pos:bool -> t -> atom Set.Poly.t * atom Set.Poly.t
    val fvar_apps_of : t -> term Set.Poly.t
    val psym_pvar_apps_of : ?simplifier:(t -> t) -> t -> atom list * atom list * atom list
    val filtered_terms_of : t -> f:(term -> bool) -> term Set.Poly.t

    val occur_times : ?map:(Ident.tvar, int) Map.Poly.t -> Ident.tvar -> t -> int

    val cnf_of : ?process_pure:bool -> sort_env_map -> t -> (atom Set.Poly.t * atom Set.Poly.t * t) Set.Poly.t
    val dnf_of : ?process_pure:bool -> sort_env_map -> t -> (atom Set.Poly.t * atom Set.Poly.t * t) Set.Poly.t
    val nnf_of : t -> t
    val negate : t -> t
    val to_atom : t -> atom

    val univ_clos : t -> t

    val split_exists : t -> sort_env_list * t
    val split_quantifiers : t -> ((binder * sort_env_list) list * t)
    val pnf_of : t -> t
    val skolemize_fun : t -> sort_env_map * sort_env_list * t
    val skolemize_pred : t -> sort_env_map * (Ident.pvar * Sort.t) list * t

    val fold :
      t ->
      f:<
        fatom : atom -> 'a;
        fbind : binder -> sort_env_list -> 'a -> 'a;
        fletrec : (predicate_fixpoint * Ident.pvar * sort_env_list * 'a) list -> 'a -> 'a;
        fnot : 'a -> 'a;
        fand: 'a -> 'a -> 'a;
        for_ : 'a -> 'a -> 'a;
        fimply : 'a -> 'a -> 'a;
        fiff : 'a -> 'a -> 'a;
        fletformula : Ident.tvar -> Sort.t -> term -> 'a -> 'a
      > -> 'a
    val map_atom : t -> f:(atom -> t) -> t
    val map_atom_polarity : bool -> t -> f:(bool -> atom -> t) -> t
    val map_term : t -> f:(term -> term) -> t
    val iter_term : f:(term -> unit) -> t -> unit
    val iter_pred_app : f:(Ident.pvar -> term list -> unit) -> t -> unit
 
    (** Printing *)
    val str_of_binder : binder -> string
    val str_of_binop : binop -> string
    val str_of_unop : unop -> string
    val str_of : ?priority:Priority.t -> t -> string
  end

  module type T_boolType = sig

    type formula
    type atom
    type term

    type fun_sym += Formula of formula | IfThenElse
    type pred_sym += Eq | Neq
    type Sort.t += SBool

    (** Construction *)
    val of_atom: ?info:info -> atom -> term
    val of_formula : ?info:info -> formula -> term
    val mk_true: ?info:info -> unit -> term
    val mk_false: ?info:info -> unit -> term
    val mk_eq: ?info:info -> term -> term -> atom
    val mk_neq: ?info:info -> term -> term -> atom
    val mk_if_then_else : ?info:info -> term -> term -> term -> term
    val mk_eqs : term list -> atom list
    val ifte: formula -> term -> term -> term
    val neg: term -> term

    (** Observation *)
    val is_atom: term -> bool
    val is_true: term -> bool
    val is_false: term -> bool
    val is_sbool: term -> bool

    (** Destruction *)
    val let_bool: term -> bool
  end

  module type T_intType = sig

    type term
    type atom

    type fun_sym +=
      | Int of Z.t
      | Add | Sub | Mult | Div | Mod | Neg | Abs | Power| Rem
    type pred_sym += Leq | Geq | Lt | Gt | PDiv | NPDiv
    type Sort.t += SInt | SRefInt | SUnrefInt

    (** Construction *)
    val zero: ?info:info -> unit -> term
    val one: ?info:info -> unit -> term
    val hundred: ?info:info -> unit -> term
    val mk_int: ?info:info -> Z.t -> term
    val from_int: ?info:info -> int -> term
    val mk_add: ?info:info -> term -> term -> term
    val mk_sub: ?info:info -> term -> term -> term
    val mk_mult: ?info:info -> term -> term -> term
    val mk_div: ?info:info -> term -> term -> term
    val mk_mod: ?info:info -> term -> term -> term
    val mk_neg: ?info:info -> term -> term
    (*val mk_neg: ?info:info -> Term.t -> Term.t*)
    val mk_abs: ?info:info -> term -> term
    val mk_power: ?info:info -> term -> term -> term
    val mk_rem : ?info:info -> term -> term -> term
    val mk_sum: ?info:info -> term -> term list -> term
    val mk_prod: ?info:info -> term -> term list -> term
    val mk_leq: ?info:info -> term -> term -> atom
    val mk_geq: ?info:info -> term -> term -> atom
    val mk_lt: ?info:info -> term -> term -> atom
    val mk_gt: ?info:info -> term -> term -> atom
    val mk_pdiv: ?info:info -> term -> term -> atom
    val mk_npdiv: ?info:info -> term -> term -> atom

    val abs: term -> term
    val l1_norm: term list -> term
    val l2_norm_sq: term list -> term

    (** Observation *)
    val is_int: term -> bool
    val is_sint: term -> bool
    val is_add: term -> bool
    val is_sub: term -> bool
    val is_mult: term -> bool
    val is_div: term -> bool
    val is_mod: term -> bool
    val is_neg: term -> bool
    val is_abs: term -> bool
    val is_power: term -> bool
    val is_rem : term -> bool
    val is_zero: term -> bool
    val is_unit: term -> bool
    val is_minus_one: term -> bool
    val is_leq: atom -> bool
    val is_geq: atom -> bool
    val is_lt: atom -> bool
    val is_gt: atom -> bool
    val is_pdiv: atom -> bool
    val is_npdiv: atom -> bool

    (** Destruction *)
    val let_int: term -> Z.t
    val let_add: term -> term * term * info
    val let_sub: term -> term * term * info
    val let_mult: term -> term * term * info
    val let_div: term -> term * term * info
    val let_mod: term -> term * term * info
    val let_neg: term -> term * info
    val let_abs: term -> term * info
    val let_power: term -> term * term * info
    val let_rem : term -> term * term * info
    val let_leq: atom -> term * term * info
    val let_geq: atom -> term * term * info
    val let_lt: atom -> term * term * info
    val let_gt: atom -> term * term * info
    val let_pdiv: atom -> term * term * info
    val let_npdiv: atom -> term * term * info

    val neg_fsym: fun_sym -> fun_sym
  end

  module type T_realType = sig

    type rterm
    type ratom

    type fun_sym +=
      | Real of Q.t | Alge of rterm * int
      | RAdd | RSub | RMult | RDiv | RNeg | RAbs | RPower
    type pred_sym += RLeq | RGeq | RLt | RGt
    type Sort.t += SReal

    (** Construction *)
    val rzero: ?info:info -> unit -> rterm
    val rone: ?info:info -> unit -> rterm
    val mk_real: ?info:info -> Q.t -> rterm
    val mk_alge: ?info:info -> rterm -> int -> rterm
    val mk_radd: ?info:info -> rterm -> rterm -> rterm
    val mk_rsub: ?info:info -> rterm -> rterm -> rterm
    val mk_rmult: ?info:info -> rterm -> rterm -> rterm
    val mk_rdiv: ?info:info -> rterm -> rterm -> rterm
    val mk_rneg: ?info:info -> rterm -> rterm
    (*val mk_neg: ?info:info -> Term.t -> Term.t*)
    val mk_rabs: ?info:info -> rterm -> rterm
    val mk_rpower: ?info:info -> rterm -> rterm -> rterm
    val mk_rsum: ?info:info -> rterm -> rterm list -> rterm
    val mk_rprod: ?info:info -> rterm -> rterm list -> rterm
    val mk_rleq: ?info:info -> rterm -> rterm -> ratom
    val mk_rgeq: ?info:info -> rterm -> rterm -> ratom
    val mk_rlt: ?info:info -> rterm -> rterm -> ratom
    val mk_rgt: ?info:info -> rterm -> rterm -> ratom

    val l1_norm: rterm list -> rterm
    val l2_norm_sq: rterm list -> rterm

    (** Observation *)
    val is_real: rterm -> bool
    val is_sreal: rterm -> bool
    val is_alge: rterm -> bool
    val is_radd: rterm -> bool
    val is_rsub: rterm -> bool
    val is_rmult: rterm -> bool
    val is_rdiv: rterm -> bool
    val is_rneg: rterm -> bool
    val is_rabs: rterm -> bool
    val is_rpower: rterm -> bool
    val is_rzero: rterm -> bool
    val is_runit: rterm -> bool
    val is_rminus_one: rterm -> bool
    val is_rleq: ratom -> bool
    val is_rgeq: ratom -> bool
    val is_rlt: ratom -> bool
    val is_rgt: ratom -> bool

    (** Destruction *)
    val let_real: rterm -> Q.t
    val let_alge: rterm -> rterm * int
    val let_radd: rterm -> rterm * rterm * info
    val let_rsub: rterm -> rterm * rterm * info
    val let_rmult: rterm -> rterm * rterm * info
    val let_rdiv: rterm -> rterm * rterm * info
    val let_rneg: rterm -> rterm * info
    val let_rabs: rterm -> rterm * info
    val let_rpower: rterm -> rterm * rterm * info
    val let_rleq: ratom -> rterm * rterm * info
    val let_rgeq: ratom -> rterm * rterm * info
    val let_rlt: ratom -> rterm * rterm * info
    val let_rgt: ratom -> rterm * rterm * info
  end

  module type T_real_intType = sig
    include T_intType
    include T_realType

    type fun_sym +=
      | ToReal | ToInt
    type pred_sym +=
      | IsInt

    val mk_to_real: ?info:info -> term -> rterm
    val mk_to_int: ?info:info -> rterm -> term
    val mk_is_int: ?info:info -> rterm -> atom

    val is_to_real: term -> bool
    val is_to_int: term -> bool
    val is_is_int: atom -> bool

    val let_to_real: term -> rterm * info
    val let_to_int: rterm -> term * info
    val let_is_int: atom -> term * info

    val origin_of: Sort.t list -> term list
  end
  module type T_numType = sig
    include T_real_intType
    type fun_sym +=
      | Value of string * Ident.svar
      | NAdd of Ident.svar
      | NSub of Ident.svar
      | NMult of Ident.svar
      | NDiv of Ident.svar
      | NPower of Ident.svar
      | NNeg of Ident.svar


    type pred_sym +=
      | NLeq of Ident.svar
      | NGeq of Ident.svar
      | NLt of Ident.svar
      | NGt of Ident.svar

    exception NotValue

    (** Construction *)
    val mk_value : ?info:info -> string -> term
    val mk_nadd : ?info:info -> term -> term -> term
    val mk_nsub : ?info:info -> term -> term -> term
    val mk_nmult : ?info:info -> term -> term -> term
    val mk_ndiv : ?info:info -> term -> term -> term
    val mk_npower : ?info:info -> term -> term -> term
    val mk_nneg : ?info:info -> term -> term
    val mk_ngeq : ?info:info -> term -> term -> atom
    val mk_nleq : ?info:info -> term -> term -> atom
    val mk_ngt : ?info:info -> term -> term -> atom
    val mk_nlt : ?info:info -> term -> term -> atom

    (** Observation *)
    val is_nadd : term -> bool
    val is_nsub : term -> bool
    val is_nmult : term -> bool
    val is_ndiv : term -> bool
    val is_npower : term -> bool
    val is_nneg : term -> bool
    val is_ngeq : atom -> bool
    val is_nleq : atom -> bool
    val is_ngt : atom -> bool
    val is_nlt : atom -> bool


    (** Destruction *)
    val let_nadd : term -> term * term * info
    val let_nsub : term -> term * term * info
    val let_nmult : term -> term * term * info
    val let_ndiv : term -> term * term * info
    val let_npower : term -> term * term * info
    val let_nneg : term -> term * info
    val let_ngeq : atom -> term * term * info
    val let_nleq : atom -> term * term * info
    val let_ngt : atom -> term * term * info
    val let_nlt : atom -> term * term * info

    val is_value : term -> bool

    val fsym_of_num_fsym : fun_sym -> Sort.t -> fun_sym
    val psym_of_num_psym : pred_sym -> Sort.t -> pred_sym
  end

  module type T_arrayType = sig
    type term
    type atom

    type fun_sym +=
      | AStore of Sort.t * Sort.t
      | ASelect of Sort.t * Sort.t
      | AConst of Sort.t * Sort.t

    type Sort.t += SArray of Sort.t * Sort.t

    val mk_array_sort : Sort.t -> Sort.t -> Sort.t
    val mk_select :  Sort.t -> Sort.t -> term -> term -> term
    val mk_store :  Sort.t -> Sort.t -> term -> term -> term -> term
    val mk_const_array :  Sort.t -> Sort.t -> term -> term

    val index_sort_of : Sort.t -> Sort.t
    val elem_sort_of : Sort.t -> Sort.t

    val is_select : term -> bool
    val is_store : term -> bool


    val let_select : term -> Sort.t * Sort.t * term * term * info
    val let_store : term -> Sort.t * Sort.t * term * term * term * info
    val eval_select : term -> term -> term option

    val of_arrow : Sort.t -> Sort.t
    val of_fvar_app : term -> term
  end
  module type FunEnvType = sig
    type term
    type formula

    type t = (Ident.tvar, (sort_env_list * Sort.t * term * bool * formula)) Map.Poly.t

    val mk_empty : unit -> t
    val defined_formula_of : t -> formula -> formula
    val str_of : t -> string

  end

  module type T_dtType = sig
    type term
    type atom
    type formula
    type dtenv
    type dt
    type dtcons
    type dtsel
    type flag
    type fun_sym +=
      | DTSel of string * dt * Sort.t
      | DTCons of string * Sort.t list * dt
    type pred_sym +=
      | IsCons of string * dt
      | NotIsCons of string * dt
    type Sort.t +=
      | SDT of dt
      | SUS of string * (Sort.t list)

    val pars_of : Sort.t -> Sort.t list

    val mk_sel : ?info:info -> dt -> string -> term -> term
    val mk_cons : ?info:info -> dt -> string -> term list -> term
    val mk_sel_by_cons : ?info:info -> dt -> string -> int -> term -> term
    val mk_is_cons : ?info:info -> dt -> string -> term -> atom
    val mk_is_not_cons : ?info:info -> dt -> string -> term -> atom
    val mk_dummy : Sort.t -> term
    val is_dt : Sort.t -> bool
    val is_finite_dt : ?his:Sort.t list -> Sort.t -> bool
    val is_codt : Sort.t -> bool
    val is_undef : Sort.t -> bool
    val is_sdt : Sort.t -> bool
    val is_sus : Sort.t -> bool
    val is_cons : term -> bool
    val is_sel : term -> bool
    val is_is_cons : atom -> bool
    val is_is_not_cons : atom -> bool
    val sels_of_cons : fun_sym -> dtsel list
    val base_terms_of : dt -> term list
    val size_of_cons : term -> int
    val inst_unknown_sel_term : (term -> term) -> formula -> formula
  end
  module type DatatypeType = sig
    type term
    type formula

    type sel =
      | Sel  of string * Sort.t
      | InSel of string * string * Sort.t list
    type cons =  {
      name : string ;
      sels : sel list
    }
    type func = | FCons of cons | FSel of sel
    type flag = | FDt | FCodt | Undef | Alias of Sort.t
    type dt = {
      name : string ;
      args : Sort.t list ;
      conses : cons list
    }
    type t = {
      name : string ;
      dts : dt list;
      flag : flag
    }
    val mk_dt : string -> Sort.t list -> dt
    val create : string -> dt list -> flag -> t
    val mk_uninterpreted_datatype : ?numeral:int -> string -> t
    val mk_alias : string -> Sort.t -> t
    val mk_cons : ?sels:sel list -> string -> cons
    val mk_sel : string -> Sort.t -> sel
    val mk_insel : string -> string -> Sort.t list -> sel
    (* val mk_poly_sel : string -> int -> sel *)

    val update_name : t -> string -> t

    val dts_of : t -> dt list
    val full_dts_of : t -> dt list
    val name_of : t -> string
    val flag_of : t -> flag
    val name_of_dt : dt -> string
    val args_of_dt : dt -> Sort.t list
    val conses_of_dt : dt -> cons list
    val sels_of_cons : cons -> sel list
    val name_of_cons : cons -> string
    val name_of_sel : sel -> string

    val look_up_dt : t -> string -> dt option
    val look_up_cons : t -> string -> cons option
    val look_up_sel_of_cons : cons -> string -> sel option
    val look_up_sel : t -> string -> sel option
    val look_up_func : t -> string -> func option
    val look_up_base_cons : t -> cons option
    val look_up_cons_of_sel : t -> string -> cons option

    val dt_of : t -> dt
    val conses_of : t -> cons list
    val sels_of : t -> sel list
    val args_of : t -> Sort.t list
    val full_name_of : t -> string
    val full_name_of_dt : dt -> string
    val short_name_of : t -> string

    val is_dt : t -> bool
    val is_codt : t -> bool
    val is_undef : t -> bool
    val is_alias : t -> bool

    val is_sel : sel -> bool
    val is_insel : sel -> bool

    val is_fcons : func -> bool
    val is_fsel : func -> bool
    val is_poly : t -> bool

    val update_dts : t -> dt list -> t
    val update_dt : t -> dt -> t
    val update_args : t -> Sort.t list -> t
    val update_conses : t -> cons list -> t
    val subst_sorts_dt : sort_subst -> dt -> dt
    val subst_conts_dt : eff_subst -> dt -> dt
    val subst_opsigs_dt : opsig_subst -> dt -> dt
    val subst_dt : opsig_subst * sort_subst * eff_subst -> dt -> dt
    val subst_sorts : sort_subst -> t -> t
    val subst_conts : eff_subst -> t -> t
    val subst_opsigs : opsig_subst -> t -> t
    val subst : opsig_subst * sort_subst * eff_subst -> t -> t
    val fresh_conts_sort : t -> t
    val fresh_conts_sort_dt : dt -> dt
    val fresh_rvs_sort : t -> t
    val fresh_rvs_sort_dt : dt -> dt

    val add_cons : t -> cons -> t
    val add_sel : cons -> sel -> cons

    val str_of_sel : sel -> string
    val str_of_cons : cons -> string
    val str_of_flag : flag -> string
    val str_of : t -> string
    val full_str_of_sel : t -> sel -> string
    val full_str_of_cons : t -> cons -> string

    val sort_of : t -> Sort.t
    val sort_of_sel : t -> sel -> Sort.t
    val sorts_of_cons : t -> cons -> Sort.t list
    val sorts_of_cons_name : t -> string -> Sort.t list

    val svs_of : t -> Ident.svar Set.Poly.t
    val evs_of : t -> Ident.evar Set.Poly.t
    val rvs_of : t -> Ident.rvar Set.Poly.t
    val is_finite : t -> bool
    val is_singleton : Sort.t -> bool
    val fsym_of_cons : t -> cons -> fun_sym
    val fsym_of_sel : t -> sel -> fun_sym
    val fsym_of_func : t -> func -> fun_sym
    val fresh_of : t -> t
    val base_conses_of : t -> cons list
    val used_dt_and_sorts_of : t -> t Set.Poly.t * Sort.t Set.Poly.t

    val size_fun_of : t -> Ident.tvar * (sort_env_list * Sort.t * term * bool * formula)
    val app_size_fun : t -> term -> term

    val pat_match_sort : t -> t -> opsig_subst * sort_subst * eff_subst
  end
  module type DTEnvType = sig
    type flag
    type datatype
    type dtfunc
    type formula

    type t = (string, datatype) Map.Poly.t

    val mk_empty : unit -> t
    val look_up_dt : t -> string -> datatype option
    val look_up_func : t -> string -> (datatype * dtfunc) option
    val look_up_dt_by_cons_name : t -> string -> datatype option
    val update_dt : t -> datatype -> t
    val update_dts : t -> datatype -> t
    val str_of : t -> string
    val name_is_cons : t -> string -> bool
    val name_is_sel : t -> string -> bool
    val name_is_func : t -> string -> bool
    val of_formula : formula -> t
    val force_merge : t -> t -> t
  end

  module type T_tupleType = sig
    type term
    type atom

    type Sort.t += STuple of Sort.t list
    type fun_sym += TupleCons of Sort.t list | TupleSel of Sort.t list * int
    type pred_sym += IsTuple of Sort.t list | NotIsTuple of Sort.t list

    val mk_tuple_cons : Sort.t list -> term list -> term
    val mk_tuple_sel : Sort.t list -> term -> int -> term
    val mk_is_tuple : Sort.t list -> term -> atom
    val mk_is_not_tuple : Sort.t list -> term -> atom
    val let_tuple_cons : term -> Sort.t list * term list * info
    val let_tuple_sel : term -> Sort.t list * int * term * info
    val is_tuple_cons : term -> bool
    val is_tuple_sel : term -> bool
    val eval_sel : term -> term
    val sorts_of : Sort.t -> Sort.t list
  end

  module type T_stringType = sig
    type term

    type Sort.t += SString
    type fun_sym += StringConst of string

    val mk_string_const : string -> term
    val let_string_const : term -> string * info
  end

  module type T_sequenceType = sig
    type term
    type atom

    type Sort.t += SFinSequence | SInfSequence
    type fun_sym += Epsilon | Symbol of string | Concat of bool | LeftQuotient of bool | RightQuotient of bool
    type pred_sym += IsPrefix of bool | NotIsPrefix of bool | InRegExp of bool * string Grammar.RegWordExp.t | NotInRegExp of bool * string Grammar.RegWordExp.t

    val mk_eps : unit -> term
    val mk_symbol : string -> term
    val concat : fin:bool -> term -> term -> term

    val mk_is_prefix : bool -> term -> term -> atom
    val mk_is_not_prefix : bool -> term -> term -> atom
    val mk_is_in_regexp : bool -> string Grammar.RegWordExp.t -> term -> atom
    val mk_is_not_in_regexp : bool -> string Grammar.RegWordExp.t -> term -> atom
  end

  module type SortEnvType = sig
    type term

    type t = sort_env_list
    val sorts_of : t -> Sort.t list
    val args_of : t -> term list
    val str_of: t -> string
  end

  module type TermSubstType = sig
    type term

    type t = (Ident.tvar, term) Map.Poly.t
    val str_of : t -> string
  end

  module type PredSubstType = sig
    type formula

    type t = (Ident.pvar, (sort_env_list * formula)) Map.Poly.t
  end

  module type RandType = sig
    type term
    type formula
    type termSubst
    type t =
      | Uniform of term * term
      | Gauss of term * term
      | IntUniform of term * term

    val mk_uniform: term -> term -> t
    val mk_gauss: term -> term -> t
    val mk_int_uniform: term -> term -> t
    val let_uniform: t -> term * term
    val let_gauss: t -> term * term
    val let_int_uniform: t -> term * term
    val subst: termSubst -> t -> t
    val subst_sorts: sort_subst -> t -> t
    val subst_conts: eff_subst -> t -> t
    val subst_opsigs: opsig_subst -> t -> t
    val sort_of: t -> Sort.t
    val str_of: t -> string
    val rename: Ident.tvar_map -> t -> t
    val mk_uniform_bounds: Ident.tvar list -> t -> formula
  end
end

module rec Term : Type.TermType
  with type atom := Atom.t
   and type formula := Formula.t
   and type termSubst := TermSubst.t
   and type predSubst := PredSubst.t
   and type dtenv := DTEnv.t
= struct
  type t =
    | Var of Ident.tvar * Sort.t * info
    | FunApp of fun_sym * t list * info
    | LetTerm of Ident.tvar * Sort.t * t * t * info

  (** Printer *)
  let rec str_of_triple (o, s, e) =
    (if Sort.is_pure e then
       if Sort.is_empty_closed_opsig o then
         str_of_sort s
       else
         sprintf "(%s |> %s)" (str_of_opsig o) (str_of_sort s)
     else
     if Sort.is_empty_closed_opsig o then
       sprintf "(%s / %s)" (str_of_sort s) (str_of_cont e)
     else
       sprintf "(%s |> %s / %s)" (str_of_opsig o) (str_of_sort s) (str_of_cont e))
  and str_of_sort = function
    | Sort.SVar svar -> Ident.name_of_svar svar
    | Sort.SArrow (s1, (o, s2, e)) ->
      sprintf "%s -> %s"
        (if Sort.is_arrow s1 then sprintf "(%s)" @@ str_of_sort s1 else str_of_sort s1)
        (str_of_triple (o, s2, e))
    | Sort.SPoly (svs, s) ->
      if Set.Poly.is_empty svs then failwith "[str_of_sort.SPoly]"(*str_of_sort s*)
      else if Set.is_singleton svs then
        sprintf "forall %s. %s"
          (Ident.name_of_svar @@ Set.Poly.choose_exn svs)
          (str_of_sort s)
      else
        sprintf "forall (%s). %s"
          (String.concat_map_set ~sep:"," ~f:Ident.name_of_svar svs)
          (str_of_sort s)
    | T_bool.SBool -> "bool"
    | T_int.SInt -> "int"
    | T_int.SRefInt -> "int*"
    | T_real.SReal -> "real"
    | T_tuple.STuple sorts ->
      sprintf "(%s)" @@ String.concat_map_list ~sep:" * " sorts ~f:str_of_sort
    | T_dt.SDT t -> (*Datatype.str_of t*)Datatype.full_name_of t
    | T_dt.SUS (name, args) ->
      if List.is_empty args then name
      else sprintf "(%s) %s" (String.concat_map_list ~sep:", " args ~f:Term.str_of_sort) name
    | T_array.SArray (s1, s2) ->
      sprintf "%s -a> %s"
        (match s1 with
         | T_array.SArray _ -> sprintf "(%s)" @@ str_of_sort s1
         | _ -> str_of_sort s1)
        (str_of_sort s2)
    | T_string.SString -> "string"
    | T_sequence.SFinSequence -> "fin_sequence"
    | T_sequence.SInfSequence -> "inf_sequence"
    | _ -> failwith "[str_of_sort] unknown sort"
  and str_of_cont = function
    | Sort.EVar evar -> Ident.name_of_evar evar
    | Sort.Pure -> "_"
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      str_of_triple (o1, s1, e1) ^ " => " ^ str_of_triple (o2, s2, e2)
    | _ -> failwith "[str_of_cont] unknown control effect"
  and str_of_opsig = function
    | Sort.OpSig (map, rho_opt) ->
      let str_map =
        map
        |> ALMap.to_alist
        |> String.concat_map_list ~sep:", " ~f:(fun (op, sort) -> op ^ ": " ^ str_of_sort sort)
      in
      let str_rho = match rho_opt with
        | Some rvar -> " | " ^ Ident.name_of_rvar rvar
        | None -> ""
      in
      sprintf "{%s%s}" str_map str_rho
    | _ -> failwith "[str_of_opsig]"

  let rec short_name_of_sort = function
    | Sort.SVar svar -> "'" ^ Ident.name_of_svar svar
    | Sort.SArrow (s1, (o, s2, e)) ->
      (if Sort.is_arrow s1 then sprintf "%s" @@ short_name_of_sort s1 else short_name_of_sort s1) ^
      ">" ^ (if Sort.is_empty_opsig o then "" else "_|>") ^ short_name_of_sort s2 ^
      if Sort.is_pure e then "" else "/_"
    | Sort.SPoly (svs, s) ->
      if Set.Poly.is_empty svs then failwith "[short_name_of_sort.SPoly]"(*short_name_of_sort s*)
      else if Set.is_singleton svs then
        sprintf "forall %s. %s"
          (Ident.name_of_svar @@ Set.Poly.choose_exn svs)
          (short_name_of_sort s)
      else
        sprintf "forall (%s). %s"
          (String.concat_map_set ~sep:"," ~f:Ident.name_of_svar svs)
          (short_name_of_sort s)
    | T_bool.SBool -> "b"
    | T_int.SInt -> "i"
    | T_int.SRefInt -> "i*"
    | T_real.SReal -> "r"
    | T_tuple.STuple sorts ->
      sprintf "%s" @@ String.concat_map_list ~sep:"" sorts ~f:short_name_of_sort
    | T_dt.SDT dt -> Datatype.short_name_of dt
    | T_dt.SUS (name, _) -> "u" ^ name
    | T_array.SArray (s1, s2) ->
      (match s1 with T_array.SArray _ -> sprintf "%s" @@ short_name_of_sort s1 | _ -> short_name_of_sort s1) ^
      "}" ^ str_of_sort s2
    | T_string.SString -> "s"
    | T_sequence.SFinSequence -> "fseq"
    | T_sequence.SInfSequence -> "iseq"
    | _ -> failwith "[short_name_of_sort] unknown sort"

  (** Construction *)
  let mk_var ?(info=Dummy) var sort = Var (var, sort, info)
  let mk_fresh_var = mk_var (Ident.mk_fresh_tvar ())
  let mk_fsym_app ?(info=Dummy) sym ts = FunApp (sym, ts, info)
  let mk_fvar_app ?(info=Dummy) tvar sorts ts = FunApp (FVar (tvar, sorts), ts, info)
  let mk_let_term ?(info=Dummy) tvar sort def body = LetTerm (tvar, sort, def, body, info)

  let rec mk_dummy sort=
    match sort with
    | T_bool.SBool -> T_bool.mk_false ()
    | T_int.SInt -> T_int.zero () | T_real.SReal -> T_real.rzero ()
    | T_tuple.STuple sorts -> T_tuple.mk_tuple_cons sorts @@ List.map ~f:mk_dummy sorts
    | T_dt.SDT _ | T_dt.SUS (_, _) -> T_dt.mk_dummy sort
    | T_array.SArray (s1, s2) -> T_array.mk_const_array s1 s2 @@ mk_dummy s2
    | T_string.SString -> mk_fsym_app (T_string.StringConst "") []
    | T_sequence.SFinSequence -> T_sequence.mk_eps ()
    | T_sequence.SInfSequence -> failwith "SInfSequence"
    | s -> failwith @@ "unsupported by mk_dummy: " ^ str_of_sort s
  let of_value = function
    | Value.Int i -> T_int.mk_int i
    | Value.Real r -> T_real.mk_real r
    | Value.Bool b -> T_bool.of_atom (if b then Atom.True Dummy else Atom.False Dummy)
  let of_sort_env = List.map ~f:(uncurry mk_var)

  (** Observation *)

  (** Printing *)
  let str_of_funsym = function
    | FVar (x, _sorts) -> Ident.name_of_tvar x
    | T_int.Int n -> Z.to_string n
    | T_int.Neg -> "-"
    | T_int.Abs -> "abs"
    | T_int.Add -> "+"
    | T_int.Sub -> "-"
    | T_int.Mult -> "*"
    | T_int.Div -> "div"
    | T_int.Mod -> "mod"
    | T_int.Power -> "^"
    | T_int.Rem -> "rem"
    | T_real.Real r -> Q.to_string r
    | T_real.RNeg -> "-"
    | T_real.RAbs -> "abs"
    | T_real.RAdd -> "+"
    | T_real.RSub -> "-"
    | T_real.RMult -> "*"
    | T_real.RDiv -> "/"
    | T_real.RPower -> "^"
    | T_real_int.ToReal -> "to_real"
    | T_real_int.ToInt -> "to_int"
    | T_num.NNeg _svar ->
      (* sprintf "-_%s" (Ident.name_of_svar _svar) *)
      "'-"
    | T_num.NAdd _svar ->
      (* sprintf "+_%s" (Ident.name_of_svar _svar) *)
      "'+"
    | T_num.NSub _svar ->
      (* sprintf "-_%s" (Ident.name_of_svar _svar) *)
      "'-"
    | T_num.NMult _svar ->
      (* sprintf "*_%s" (Ident.name_of_svar _svar) *)
      "'*"
    | T_num.NDiv _svar ->
      (* sprintf "/_%s" (Ident.name_of_svar _svar) *)
      "'/"
    | T_num.NPower _svar ->
      (* sprintf "^_%s" (Ident.name_of_svar _svar) *)
      "'^"
    | T_num.Value (ident, svar) ->
      sprintf "value(%s:%s)" ident (Ident.name_of_svar svar)
    | T_bool.Formula phi ->
      sprintf "Formula(%s)" @@ Formula.str_of ~priority:0 phi
    | T_bool.IfThenElse -> "IfThenElse"
    | T_tuple.TupleCons _ -> "t_cons"
    | T_tuple.TupleSel (_, i) -> sprintf "t_sel.%d" i
    | T_dt.DTCons (name, args, dt) ->
      sprintf "[%s:%s]"
        name
        (List.fold_left args ~init:(short_name_of_sort @@ T_dt.SDT dt) ~f:(fun ret arg ->
             short_name_of_sort arg ^ "->" ^ ret))
    | T_dt.DTSel (name, dt, ret_sort) ->
      sprintf "[%s:%s -> %s]"
        name
        (short_name_of_sort @@ T_dt.SDT dt)
        (short_name_of_sort ret_sort)
    | T_array.ASelect _ -> "select"
    | T_array.AStore _ -> "store"
    | T_array.AConst (s1, s2) ->
      sprintf "const_array[%s->%s]" (str_of_sort s1) (str_of_sort s2)
    | T_string.StringConst str -> sprintf "\"%s\"" str
    | T_sequence.Epsilon -> "eps"
    | T_sequence.Symbol ev -> ev
    | T_sequence.Concat fin -> "concat" ^ if fin then "_fin" else "_inf"
    | T_sequence.LeftQuotient _ -> "left_quot"
    | T_sequence.RightQuotient _ -> "right_quot"
    | _ -> failwith "[str_of_funsym] unknown function symbol"

  let rec str_of ?(priority=20) = function
    | Var (Ident.Tvar ident, T_int.SUnrefInt, _) ->
      "*" ^ ident
    | Var (Ident.Tvar ident, T_int.SRefInt, _) ->
      "&" ^ ident
    | Var (x, sort, _) ->
      sprintf "%s:%s" (Ident.str_of_tvar x) (short_name_of_sort sort)
    | FunApp (FVar (x, _), ts, _) ->
      if List.length ts = 0 then Ident.name_of_tvar x
      else
        Priority.add_bracket priority Priority.fun_app @@
        Printf.sprintf "\\%s %s" (Ident.name_of_tvar x) @@
        String.concat_map_list ~sep:" " ts ~f:(str_of ~priority:(Priority.fun_app+1(*ToDo*)))
    | FunApp (T_bool.Formula phi, [], _) ->
      "<" ^ Formula.str_of ~priority:20 phi ^ ">"
    | FunApp (T_bool.IfThenElse, [cond; then_; else_], _) ->
      Printf.sprintf "(if %s then %s else %s)"
        (str_of ~priority:0 cond)
        (str_of ~priority:0 then_)
        (str_of ~priority:0 else_)
    | FunApp (T_int.Int n, [], info) ->
      if Z.Compare.(n < Z.zero) then
        str_of ~priority @@ T_int.mk_neg @@ FunApp (T_int.Int (Z.neg n), [], info)
      else Z.to_string n
    | FunApp (T_real.Real r, [], _) ->
      "r(" ^ Q.to_string r ^ ")"
    | FunApp (T_real.Alge (t, n), [], _) ->
      "root-obj(" ^ str_of t ^ " " ^ string_of_int n ^ ")"
    | FunApp (T_int.Neg, [t], _) | FunApp (T_real.RNeg, [t], _) | FunApp (T_num.NNeg _, [t], _) ->
      Priority.add_bracket priority Priority.neg_abs @@
      Printf.sprintf "-%s" @@ str_of ~priority:(Priority.neg_abs+1(*ToDo*)) t
    | FunApp (T_real_int.ToReal, [t], _) ->
      Priority.add_bracket priority Priority.neg_abs @@
      Printf.sprintf "to_real %s" @@ str_of ~priority:(Priority.neg_abs+1(*ToDo*)) t
    | FunApp (T_real_int.ToInt, [t], _)->
      Priority.add_bracket priority Priority.neg_abs @@
      Printf.sprintf "to_int %s" @@ str_of ~priority:(Priority.neg_abs+1(*ToDo*)) t
    | FunApp (T_int.Abs, [t], _) | FunApp (T_real.RAbs, [t], _) ->
      Priority.add_bracket priority Priority.neg_abs @@
      Printf.sprintf "abs %s" @@ str_of ~priority:(Priority.neg_abs+1(*ToDo*)) t
    | FunApp (T_int.Add as op, [t1; t2], _) | FunApp (T_real.RAdd as op, [t1; t2], _) | FunApp (T_num.NAdd _ as op, [t1; t2], _)
    | FunApp (T_int.Sub as op, [t1; t2], _) | FunApp (T_real.RSub as op, [t1; t2], _) | FunApp (T_num.NSub _ as op, [t1; t2], _) ->
      Priority.add_bracket priority Priority.add_sub @@
      Printf.sprintf "%s %s %s"
        (str_of ~priority:Priority.add_sub t1)
        (str_of_funsym op)
        (str_of ~priority:Priority.add_sub t2)
    | FunApp (T_int.Mult as op, [t1; t2], _) | FunApp (T_real.RMult as op, [t1; t2], _) | FunApp (T_num.NMult _ as op, [t1; t2], _)
    | FunApp (T_int.Div as op, [t1; t2], _) | FunApp (T_real.RDiv as op, [t1; t2], _) | FunApp (T_num.NDiv _ as op, [t1; t2], _)
    | FunApp (T_int.Mod as op, [t1; t2], _) | FunApp (T_int.Rem as op, [t1; t2], _) ->
      Priority.add_bracket priority Priority.mult_div_mod @@
      Printf.sprintf "%s %s %s"
        (str_of ~priority:Priority.mult_div_mod t1)
        (str_of_funsym op)
        (str_of ~priority:Priority.mult_div_mod t2)
    | FunApp (T_int.Power as op, [t1; t2], _) | FunApp (T_real.RPower as op, [t1; t2], _) | FunApp (T_num.NPower _ as op, [t1; t2], _) ->
      Priority.add_bracket priority Priority.power @@
      Printf.sprintf "%s%s%s"
        (str_of ~priority:Priority.power t1)
        (str_of_funsym op)
        (str_of ~priority:Priority.power t2)
    | FunApp (T_int.Add, _, _) | FunApp (T_real.RAdd, _, _)
    | FunApp (T_int.Mult, _, _) | FunApp (T_real.RMult, _, _) ->
      failwith "add and mult are binary"
    | FunApp (T_num.Value _ as op, _, _) ->
      str_of_funsym op
    | FunApp (T_tuple.TupleCons sorts, ts, _) ->
      sprintf "(%s)" @@ String.concat ~sep:"," @@
      List.map2_exn ts sorts ~f:(fun t s -> str_of t ^ ":" ^ str_of_sort s)
    | FunApp (T_tuple.TupleSel (_, i), [t], _) ->
      sprintf "t_sel.%d %s" i @@ str_of t
    | FunApp (T_dt.DTCons (_, _, _) as fsym, ts, _) ->
      if List.length ts = 0 then
        sprintf "%s" @@ str_of_funsym fsym
      else
        sprintf "(%s%s)"
          (sprintf "%s" @@ str_of_funsym fsym)
          (List.fold_left ts ~init:"" ~f:(fun ret term -> sprintf "%s %s" ret @@ str_of term))
    | FunApp (T_dt.DTSel (_, _, _) as fsym, [t1], _) ->
      sprintf "(%s %s)" (str_of_funsym fsym) (str_of t1)
    | FunApp (T_array.ASelect _, [t1; t2], _) ->
      sprintf "%s[%s]" (str_of t1) (str_of t2)
    | FunApp (T_array.AStore _, [t1; t2; t3], _) ->
      sprintf "(store %s %s %s)" (str_of t1) (str_of t2) (str_of t3)
    | FunApp (T_array.AConst _, [t1], _) ->
      sprintf "ARR{%s}" (str_of t1)
    | FunApp (T_string.StringConst _ as fsym, [], _) ->
      str_of_funsym fsym
    | FunApp (T_sequence.Epsilon as fsym, [], _) ->
      str_of_funsym fsym
    | FunApp (T_sequence.Symbol ev, [], _) ->
      ev
    | FunApp (T_sequence.Concat fin, [t1; t2], _) ->
      "concat_" ^ (if fin then "fin" else "inf") ^ "(" ^ str_of t1 ^ "," ^ str_of t2 ^ ")"
    | FunApp (T_sequence.LeftQuotient fin, [t1; t2], _) ->
      "leftQuot_" ^ (if fin then "fin" else "inf") ^ "(" ^ str_of t1 ^ "," ^ str_of t2 ^ ")"
    | FunApp (T_sequence.RightQuotient fin, [t1; t2], _) ->
      "rightQuot_" ^ (if fin then "fin" else "inf") ^ "(" ^ str_of t1 ^ "," ^ str_of t2 ^ ")"
    | FunApp (f, ts, _) ->
      failwith ("unknown function application: " ^
                String.concat ~sep:" " @@ str_of_funsym f :: List.map ts ~f:str_of)
    | LetTerm (var, _sort, def, body, _) ->
      sprintf "let %s = %s in %s" (Ident.name_of_tvar var) (str_of def) (str_of body)
  (*sprintf "let %s:%s = %s in %s" (Ident.name_of_tvar var) (short_name_of_sort sort) (str_of def) (str_of body)*)

  let is_fvar_sym = function FVar (_, _) -> true | _ -> false
  let is_var = function
    | Var (_, _, _) -> true
    | FunApp (T_bool.Formula (Formula.Atom (Atom.App (Predicate.Var (Ident.Pvar _, []), [], _), _)), _, _) -> true
    | _ -> false

  let is_app = function FunApp (_, _, _) -> true | _ -> false
  let is_fvar_app = function FunApp (FVar (_, _), _, _) -> true | _ -> false
  let is_funcall = function FunApp (FunCall _, _, _) -> true | _ -> false
  let is_let_term = function LetTerm _ -> true | _ -> false
  let rec is_numerical_compound term =
    Fn.non Term.is_bool_sort (Term.sort_of term) &&
    match term with
    | Var _ -> false
    | FunApp ((T_int.Int _| T_real.Real _ | T_real.Alge _ | FVar (_, _)), _, _) -> false
    | FunApp (_, _, _) -> true
    | LetTerm (_, _, _, body, _) -> is_numerical_compound body
  let rec is_pathexp = function
    | Var (_, _, _) -> true
    | FunApp (FVar (_, _), ts, _) -> List.exists ts ~f:is_pathexp
    | FunApp ((T_int.Neg | T_real.RNeg | T_num.NNeg _ | T_real_int.ToReal | T_real_int.ToInt), [t], _) ->
      is_pathexp t
    | FunApp (T_dt.DTSel (sel_name, dt, _), [FunApp (T_dt.DTCons (cons_name, _, _), _, _)], _) ->
      begin match Datatype.look_up_cons dt cons_name with
        | Some cons ->
          let sels = Datatype.sels_of_cons cons in
          not @@ List.exists sels ~f:(fun sel -> Stdlib.(Datatype.name_of_sel sel = sel_name))
        | None -> assert false
      end
    | FunApp (T_dt.DTSel (_, _, _) , [t1], _) -> is_pathexp t1
    | FunApp (T_array.ASelect _, [t1; _], _) -> is_pathexp t1
    | _ -> false

  (* assume [t] is simplified*)
  let is_uninterpreted_term = function
    (* | Var (_, _, _) -> true *)
    | FunApp ((T_int.Div | T_int.Mod), [_; t2], _) -> T_int.is_zero t2
    | FunApp (T_dt.DTSel _, [t1], _) -> T_dt.is_cons t1
    | FunApp (T_array.ASelect _, _, _) -> true
    | _ -> false

  let rec tvs_of = function
    | Var (tvar, _, _) -> Set.Poly.singleton tvar
    | FunApp (FVar (tvar, _), args, _) when not @@ Hash_set.Poly.mem defined_fvars tvar ->
      Set.Poly.union_list @@ Set.Poly.singleton tvar :: List.map args ~f:tvs_of
    | FunApp (T_bool.Formula phi, args, _) ->
      Set.Poly.union_list @@ Formula.tvs_of phi :: List.map args ~f:tvs_of
    | FunApp (_, args, _) ->
      Set.Poly.union_list @@ List.map args ~f:tvs_of
    | LetTerm (tvar, _, def, body, _) ->
      Set.Poly.union (tvs_of def) (Set.Poly.remove (tvs_of body) tvar)
  let rec pvs_of = function
    | Var (_, _, _) -> Set.Poly.empty
    | FunApp (T_bool.Formula phi, args, _) ->
      Set.Poly.union_list @@ Formula.pvs_of phi :: List.map args ~f:pvs_of
    | FunApp (_, args, _) ->
      Set.Poly.union_list @@ List.map args ~f:pvs_of
    | LetTerm (Ident.Tvar name, _, def, body, _) ->
      Set.Poly.union (pvs_of def) (Set.Poly.remove (pvs_of body) (Ident.Pvar name))
  let fvs_of atm =
    Set.Poly.union (tvs_of atm) @@
    (Set.Poly.map ~f:(fun (Ident.Pvar name) -> Ident.Tvar(*ToDo*) name) @@ pvs_of atm)
  let rec svs_of = function
    | Var (_, sort, _) -> (match sort with Sort.SVar svar -> Set.Poly.singleton svar | _ -> Set.Poly.empty)
    | FunApp (T_bool.Formula phi, args, _) ->
      Set.Poly.union_list @@ Formula.svs_of phi :: List.map args ~f:svs_of
    | FunApp (_fsym(* ToDo *), args, _) ->
      Set.Poly.union_list @@ List.map args ~f:svs_of
    | LetTerm (_, sort, def, body, _) ->
      Set.Poly.union_list [svs_of def; svs_of body; match sort with Sort.SVar svar -> Set.Poly.singleton svar | _ -> Set.Poly.empty]
  let rec funsyms_of = function
    | Var _ -> Set.Poly.empty
    | FunApp (sym, args, _) ->
      Set.Poly.add (Set.Poly.union_list @@ List.map args ~f:funsyms_of) sym
    | LetTerm (_, _, def, body, _) ->
      Set.Poly.union (funsyms_of def) (funsyms_of body)

  let term_sort_env_of t =
    let rec term_sort_env_of_aux ~ex = function
      | Var (var, sort, _) ->
        if Set.Poly.mem ex var then Set.Poly.empty else Set.Poly.singleton (var, sort)
      | FunApp (sym, args, _) ->
        Set.Poly.union_list @@
        (match sym with
         | FVar (tvar, sorts) when not @@ Hash_set.Poly.mem defined_fvars tvar ->
           Set.Poly.singleton (tvar, Sort.mk_fun sorts)
         | T_bool.Formula phi -> Formula.term_sort_env_of phi
         | _ -> Set.Poly.empty) ::
        List.map args ~f:(term_sort_env_of_aux ~ex)
      | LetTerm (var, sort, def, body, _) ->
        Set.Poly.remove (Set.Poly.union (term_sort_env_of_aux ~ex def) (term_sort_env_of_aux ~ex:(Set.Poly.add ex var) body)) (var, sort)
    in term_sort_env_of_aux ~ex:Set.Poly.empty t
  let rec pred_sort_env_of ?(bpvs = Set.Poly.empty) = function
    | Var _ -> Set.Poly.empty
    | FunApp (sym, args, _) ->
      Set.Poly.union_list @@
      (match sym with
       | T_bool.Formula phi -> Formula.pred_sort_env_of ~bpvs phi
       | _ -> Set.Poly.empty) ::
      List.map args ~f:(pred_sort_env_of ~bpvs)
    | LetTerm (_, _, def, body, _) ->
      Set.Poly.union (pred_sort_env_of ~bpvs def) (pred_sort_env_of ~bpvs body)
  let sort_env_of ?(bpvs = Set.Poly.empty) t =
    Set.Poly.union (term_sort_env_of t) @@
    (Set.Poly.map ~f:(fun (Ident.Pvar name, sorts) -> Ident.Tvar(*ToDo*) name, Sort.mk_fun (sorts @ [T_bool.SBool])) @@ pred_sort_env_of ~bpvs t)
  let rec fvar_apps_of = function
    | Var _ -> Set.Poly.empty
    | FunApp (sym, args, _) as t ->
      Set.Poly.union_list @@
      (match sym with
       | FVar (_, _) -> Set.Poly.singleton t
       | T_bool.Formula phi -> Formula.fvar_apps_of phi
       | _ -> Set.Poly.empty) :: List.map args ~f:fvar_apps_of
    | LetTerm (_, _, def, body, _) ->
      Set.Poly.union (fvar_apps_of def) (fvar_apps_of body)

  let pathexps_of t =
    let rec pathexps_of_aux ~ex t =
      if is_pathexp t then Set.Poly.singleton t
      else match t with
        | Var (var, _, _) ->
          if Set.Poly.mem ex var then Set.Poly.empty else Set.Poly.singleton t
        | FunApp (sym, args, _) ->
          Set.Poly.union_list @@
          (match sym with
           | FVar (_, _) -> Set.Poly.singleton t
           | T_bool.Formula phi -> Formula.pathexps_of phi
           | _ -> Set.Poly.empty) :: List.map args ~f:(pathexps_of_aux ~ex)
        | LetTerm (var, _, def, body, _) ->
          Set.Poly.union (pathexps_of_aux ~ex def) (pathexps_of_aux ~ex:(Set.Poly.add ex var) body)
    in pathexps_of_aux t ~ex:Set.Poly.empty

  let rec filtered_terms_of t ~f =
    Set.Poly.union (if f t then Set.Poly.singleton t else Set.Poly.empty)
      (match t with
       | FunApp (T_bool.Formula phi, _, _) ->
         Formula.filtered_terms_of ~f phi
       | FunApp (_, args, _) ->
         Set.Poly.union_list @@ List.map args ~f:(filtered_terms_of ~f)
       | LetTerm (_, _, def, body, _) ->
         Set.Poly.union (filtered_terms_of def ~f) (filtered_terms_of body ~f)
       | _ -> Set.Poly.empty)

  let rec atoms_of ?(pos=true) = function
    | Var (_, _, _) ->
      Set.Poly.empty, Set.Poly.empty
    | FunApp (T_bool.Formula phi, args, _) ->
      assert (List.is_empty args);
      Formula.atoms_of ~pos phi
    | FunApp (_, _, _) -> (* ToDo *)
      Set.Poly.empty, Set.Poly.empty
    | LetTerm (_, _, def, body, _) ->
      let pos1, neg1 = atoms_of ~pos def in
      let pos2, neg2 = atoms_of ~pos body in
      Set.Poly.union pos1 pos2, Set.Poly.union neg1 neg2

  let sorts_of_sort sort =
    let rec inner visited sort =
      if Set.Poly.mem visited sort then visited
      else
        let visited' = Set.Poly.add visited sort in
        match sort with
        | T_tuple.STuple sorts -> List.fold sorts ~init:visited' ~f:inner
        | T_dt.SDT dt ->
          let conses = Datatype.conses_of dt in
          let sorts = List.concat_map conses ~f:(Datatype.sorts_of_cons dt) in
          List.fold sorts ~init:visited' ~f:inner
        | T_array.SArray (s1, s2) -> inner (inner visited s1) s2
        | _ -> visited'
    in
    inner Set.Poly.empty sort

  let rec svs_of_cont = function
    | Sort.EVar _ | Sort.Pure -> Set.Poly.empty
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Set.Poly.union_list [svs_of_opsig o1; svs_of_sort s1; svs_of_cont e1;
                           svs_of_opsig o2; svs_of_sort s2; svs_of_cont e2]
    | _ -> failwith "svs_of_cont"
  and svs_of_sort = function
    | Sort.SVar svar -> Set.Poly.singleton svar
    | Sort.SArrow (s1, (o, s2, e)) ->
      Set.Poly.union_list [svs_of_sort s1; svs_of_opsig o; svs_of_sort s2; svs_of_cont e]
    | Sort.SPoly (svs, s) -> Set.Poly.diff (svs_of_sort s) svs
    | T_bool.SBool | T_int.SInt | T_int.SRefInt | T_real.SReal -> Set.Poly.empty
    | T_tuple.STuple sorts -> Set.Poly.union_list (List.map ~f:svs_of_sort sorts)
    | T_dt.SDT dt -> Datatype.svs_of dt
    | T_dt.SUS (_, sorts) -> Set.Poly.union_list (List.map ~f:svs_of_sort sorts)
    | T_array.SArray (s1, s2) -> Set.Poly.union (svs_of_sort s1) (svs_of_sort s2)
    | T_string.SString | T_sequence.SFinSequence | T_sequence.SInfSequence -> Set.Poly.empty
    | _ -> failwith "[svs_of_sort] unknown sort"
  and svs_of_opsig = function
    | Sort.OpSig (map, _) ->
      map
      |> ALMap.data
      |> List.map ~f:svs_of_sort
      |> Set.Poly.union_list
    | _ -> failwith "svs_of_opsig"

  let rec evs_of_cont = function
    | Sort.EVar evar -> Set.Poly.singleton evar
    | Sort.Pure -> Set.Poly.empty
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Set.Poly.union_list
        [evs_of_opsig o1; evs_of_sort s1; evs_of_cont e1;
         evs_of_opsig o2; evs_of_sort s2; evs_of_cont e2]
    | _ -> failwith "svs_of_cont"
  and evs_of_sort = function
    | Sort.SVar _ -> Set.Poly.empty
    | Sort.SArrow (s1, (o, s2, e)) ->
      Set.Poly.union_list [evs_of_sort s1; evs_of_opsig o; evs_of_sort s2; evs_of_cont e]
    | Sort.SPoly (_, s) -> evs_of_sort s
    | T_bool.SBool | T_int.SInt | T_int.SRefInt | T_real.SReal -> Set.Poly.empty
    | T_tuple.STuple sorts -> Set.Poly.union_list (List.map ~f:evs_of_sort sorts)
    | T_dt.SDT dt -> Datatype.evs_of dt
    | T_dt.SUS (_, sorts) -> Set.Poly.union_list (List.map ~f:evs_of_sort sorts)
    | T_array.SArray (s1, s2) -> Set.Poly.union (evs_of_sort s1) (evs_of_sort s2)
    | T_string.SString | T_sequence.SFinSequence | T_sequence.SInfSequence -> Set.Poly.empty
    | _ -> failwith "[evs_of_sort] unknown sort"
  and evs_of_opsig = function
    | Sort.OpSig (map, _) ->
      map
      |> ALMap.data
      |> List.map ~f:evs_of_sort
      |> Set.Poly.union_list
    | _ -> failwith "evs_of_opsig"

  let rec rvs_of_cont = function
    | Sort.EVar _ | Sort.Pure -> Set.Poly.empty
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Set.Poly.union_list
        [rvs_of_opsig o1; rvs_of_sort s1; rvs_of_cont e1;
         rvs_of_opsig o2; rvs_of_sort s2; rvs_of_cont e2]
    | _ -> failwith "rvs_of_cont"
  and rvs_of_sort = function
    | Sort.SVar _ -> Set.Poly.empty
    | Sort.SArrow (s1, (o, s2, e)) ->
      Set.Poly.union_list [rvs_of_sort s1; rvs_of_opsig o; rvs_of_sort s2; rvs_of_cont e]
    | Sort.SPoly (_, s) -> rvs_of_sort s
    | T_bool.SBool | T_int.SInt | T_int.SRefInt | T_real.SReal -> Set.Poly.empty
    | T_tuple.STuple sorts -> Set.Poly.union_list (List.map ~f:rvs_of_sort sorts)
    | T_dt.SDT dt -> Datatype.rvs_of dt
    | T_dt.SUS (_, sorts) -> Set.Poly.union_list (List.map ~f:rvs_of_sort sorts)
    | T_array.SArray (s1, s2) -> Set.Poly.union (rvs_of_sort s1) (rvs_of_sort s2)
    | T_string.SString | T_sequence.SFinSequence | T_sequence.SInfSequence -> Set.Poly.empty
    | _ -> failwith "[rvs_of_sort] unknown sort"
  and rvs_of_opsig = function
    | Sort.OpSig (map, rv_opt) -> 
      Set.Poly.union_list @@
      (match rv_opt with Some rv -> Set.Poly.singleton rv | None -> Set.Poly.empty)
      :: (List.map ~f:rvs_of_sort @@ ALMap.data map)
    | _ -> failwith "rvs_of_opsig"

  (* assume that the argument is let-normalized *)
  let rec body_of_let = function
    | LetTerm (_, _, _, body, _) -> body_of_let body
    | FunApp (T_bool.Formula phi, [], info) ->
      FunApp (T_bool.Formula (Formula.body_of_let phi), [], info)
    | t -> t

  let ast_size t =
    let rec ast_size ~ex = function
      | Var (var, _, _) ->
        begin match Map.Poly.find ex var with | Some size -> size | None -> 1 end
      | FunApp (sym, args, _) ->
        let size_of_args = List.fold ~f:(fun acc term -> acc + ast_size ~ex term) ~init:1 args in
        begin match sym with
          | T_bool.Formula phi -> size_of_args + (Formula.ast_size phi) - 1
          | _ -> size_of_args
        end
      | LetTerm (var, _, def, body, _) ->
        let def_size = ast_size ~ex def in
        ast_size ~ex:(Map.Poly.set ex ~key:var ~data:def_size) body
    in ast_size t ~ex:(Map.Poly.empty)

  let rec occur_times ?(map=Map.Poly.empty) x = function
    | Var (tvar, _, _) ->
      if Stdlib.(x = tvar) then 1 else
        begin match Map.Poly.find map tvar with | Some i -> i | _ -> 0 end
    | FunApp (T_bool.Formula phi, _, _) ->
      Formula.occur_times ~map x phi
    | FunApp (_, ts, _) ->
      List.fold ~init:0 ~f:(fun acc t -> acc + occur_times ~map x t) ts
    | LetTerm (var, _, def, body, _) ->
      let map = Map.Poly.add_exn ~key:var ~data:(occur_times ~map x def) map in
      occur_times ~map x body

  let rec occurs s' s =
    if Stdlib.(s' = s) then true else
      match s with
      | Sort.SArrow (s1, (o, s2, e)) ->
        occurs s' s1
        || occurs_opsig s' o
        || occurs s' s2
        || occurs_cont s' e
      | _ -> false(*ToDo*)
  and occurs_cont s = function
    | Sort.EVar _  | Sort.Pure -> false
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      occurs_opsig s o1
      || occurs s s1
      || occurs_cont s e1
      || occurs_opsig s o2
      || occurs s s2
      || occurs_cont s e2
    | _ -> failwith "occurs_cont"
  and occurs_opsig s = function
    | Sort.OpSig (opmap, _) ->
      opmap |> ALMap.data |> List.exists ~f:(occurs s)
    | _ -> failwith "occurs_opsig"
  let value_of = function
    | FunApp (T_int.Int n, _, _) -> Value.Int n
    | FunApp (T_real.Real r, _, _) -> Value.Real r
    | FunApp (T_bool.Formula (Formula.Atom (Atom.True _, _)), _, _) -> Value.Bool true
    | FunApp (T_bool.Formula (Formula.Atom (Atom.False _, _)), _, _) -> Value.Bool false
    | t ->
      print_string @@ str_of t;
      assert false

  (** Destruction *)
  let let_var = function
    | Var (var, sort, info) -> (var, sort), info
    | FunApp (T_bool.Formula (Formula.Atom (Atom.App (Predicate.Var (Ident.Pvar var, []), [], _), _)), _, info) ->
      (Ident.Tvar var, T_bool.SBool), info
    | _ -> assert false
  let let_app = function
    | FunApp (sym, ts, info) -> (sym, ts, info)
    | _ -> assert false
  let let_fvar_app = function
    | FunApp (FVar (var, sorts), ts, info) -> (var, sorts, ts, info)
    | _ -> assert false
  let let_funcall = function
    | FunApp (FunCall funname, ts, info) -> (funname, ts, info)
    | _ -> assert false
  let let_let_term = function
    | LetTerm (var, sort, def, body, info) -> (var, sort, def, body, info)
    | _ -> assert false

  (** Substitution *)
  let rec rename map = function
    | Var (var', sort, info) as t -> begin
        match Map.Poly.find map var' with
        | None -> t
        | Some var -> Var (var, sort, info)
      end
    | FunApp (sym, ts, info) ->
      FunApp (rename_fun_sym map sym, List.map ~f:(rename map) ts, info)
    | LetTerm (var, sort, def, body, info) ->
      match Map.Poly.find map var with
      | Some var -> LetTerm (var, sort, rename map def, rename map body, info)
      | None -> LetTerm (var, sort, rename map def, rename map body, info)
  and rename_fun_sym map = function
    | FVar (var', sorts) as fsym -> begin
        match Map.Poly.find map var' with
        | None -> fsym
        | Some var -> FVar (var, sorts)
      end
    | T_bool.Formula phi -> T_bool.Formula (Formula.rename map phi)
    | fsym -> fsym
  let rec rename_pvars map = function
    | FunApp (sym, args, info) ->
      FunApp (rename_pvars_fun_sym map sym, List.map ~f:(rename_pvars map) args, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, rename_pvars map def, rename_pvars map body, info)
    | t -> t
  and rename_pvars_fun_sym map = function
    | T_bool.Formula phi -> T_bool.Formula (Formula.rename_pvars map phi)
    | fsym -> fsym
  let rec rename_sorted_pvars map = function
    | FunApp (sym, args, info) ->
      FunApp (rename_sorted_pvars_fun_sym map sym, List.map ~f:(rename_sorted_pvars map) args, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, rename_sorted_pvars map def, rename_sorted_pvars map body, info)
    | t -> t
  and rename_sorted_pvars_fun_sym map = function
    | T_bool.Formula phi -> T_bool.Formula (Formula.rename_sorted_pvars map phi)
    | fsym -> fsym

  let rec subst map = function
    | Var (var', sort, info) -> begin
        match Map.Poly.find map var' with
        | None -> Var (var', sort, info)
        | Some t -> t
      end
    | FunApp (sym, ts, info) ->
      FunApp (subst_fun_sym map sym, List.map ~f:(subst map) ts, info)
    | LetTerm (var, sort, def, body, info) ->
      assert (not @@ Map.Poly.mem map var);
      LetTerm (var, sort, (subst map def), (subst map body), info)
  and subst_fun_sym map = function
    | FVar (var', sorts) -> begin
        match Map.Poly.find map var' with
        | None -> FVar (var', sorts)
        | Some t ->
          try
            let (var, _), _ = let_var t in
            FVar (var, sorts)
          with _ -> failwith @@ sprintf "subst_fun_sym : [%s] -> %s" (Ident.name_of_tvar var') (str_of t)
      end
    | T_bool.Formula phi -> T_bool.Formula (Formula.subst map phi)
    | sym -> sym
  let rec subst_preds map = function
    | Var (var, sort, info) ->
      let pvar = Ident.tvar_to_pvar var in
      (match Map.Poly.find map pvar with
       | Some (sortenv, phi) ->
         if List.is_empty sortenv then T_bool.of_formula (Formula.subst_preds map phi)
         else assert false
       | None -> Var (var, sort, info))
    | FunApp (sym, args, info) ->
      let sym = match sym with
        | T_bool.Formula phi -> T_bool.Formula (Formula.subst_preds map phi)
        | sym -> sym
      in
      FunApp (sym, List.map ~f:(subst_preds map) args, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, (subst_preds map def), (subst_preds map body), info)
  let subst_sorts_fun_sym map = function
    | FVar (var, sorts) ->
      FVar (var, List.map ~f:(Term.subst_sorts_sort map) sorts)
    | (T_num.Value (_, svar) | T_num.NAdd svar | T_num.NSub svar | T_num.NMult svar | T_num.NDiv svar | T_num.NPower svar | T_num.NNeg svar) as sym ->
      T_num.fsym_of_num_fsym sym @@ Term.subst_sorts_sort map @@ Sort.SVar svar
    | T_bool.Formula phi ->
      T_bool.Formula (Formula.subst_sorts map phi)
    | T_tuple.TupleCons sorts ->
      T_tuple.TupleCons (List.map ~f:(Term.subst_sorts_sort map) sorts)
    | T_tuple.TupleSel (sorts, i) ->
      T_tuple.TupleSel (List.map ~f:(Term.subst_sorts_sort map) sorts, i)
    | T_dt.DTCons (name, arg_sorts, dt) ->
      T_dt.DTCons (name, List.map arg_sorts ~f:(Term.subst_sorts_sort map), Datatype.subst_sorts map dt)
    | T_dt.DTSel (name, dt, sort) ->
      T_dt.DTSel (name, Datatype.subst_sorts map dt, Term.subst_sorts_sort map sort)
    | T_array.ASelect (s1, s2) ->
      T_array.ASelect (Term.subst_sorts_sort map s1, Term.subst_sorts_sort map s2)
    | T_array.AStore (s1, s2) ->
      T_array.AStore (Term.subst_sorts_sort map s1, Term.subst_sorts_sort map s2)
    | T_array.AConst (s1, s2) ->
      T_array.AConst (Term.subst_sorts_sort map s1, Term.subst_sorts_sort map s2)
    | sym -> sym(* ToDo *)
  let rec subst_sorts map = function
    | Var (x, sort, info) ->
      Var (x, subst_sorts_sort map sort, info)
    (*| FunApp (T_real_int.ToReal, [Var (tvar, _, info)], _) ->
      Var (tvar, T_real.SReal, info)
      | FunApp (T_real_int.ToInt, [Var (tvar, _, info)], _) ->
      Var (tvar, T_int.SInt, info)
      | FunApp (T_string.StringConst str, _, info) ->
      Var (Ident.Tvar ("\"" ^ str ^ "\""), T_string.SString, info)*)
    | FunApp (sym, args, info) ->
      FunApp (subst_sorts_fun_sym map sym, List.map ~f:(subst_sorts map) args, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, subst_sorts_sort map sort, subst_sorts map def, subst_sorts map body, info)
  and subst_sorts_sort map = function
    | Sort.SVar svar ->
      (match Map.Poly.find map svar with Some s -> s | None -> Sort.SVar svar)
    | Sort.SArrow (s1, (o, s2, e)) ->
      Sort.SArrow (subst_sorts_sort map s1,
                   (subst_sorts_opsig map o,
                    subst_sorts_sort map s2,
                    subst_sorts_cont map e))
    | T_tuple.STuple sorts ->
      T_tuple.STuple (List.map sorts ~f:(subst_sorts_sort map))
    | T_dt.SDT dt ->
      T_dt.SDT (Datatype.subst_sorts map dt)
    | T_dt.SUS (name, args) ->
      T_dt.SUS (name, List.map args ~f:(subst_sorts_sort map))
    | T_array.SArray (s1, s2) ->
      T_array.SArray (subst_sorts_sort map s1, subst_sorts_sort map s2)
    (*| T_string.SString ->
      T_string.SString (*T_dt.SUS ("string", [])*)
      | T_sequence.SFinSequence ->
      T_sequence.SFinSequence(*T_dt.SUS ("fin_sequence", [])*)
      | T_sequence.SInfSequence ->
      T_sequence.SInfSequence(*T_dt.SUS ("inf_sequence", [])*)*)
    | Sort.SPoly (svs, s) ->
      Sort.SPoly (svs, subst_sorts_sort (Map.remove_keys_set map svs) s)
    | sort(*ToDo*) -> sort(*failwith "subst_sorts_sort"*)
  and subst_sorts_cont map = function
    | Sort.EVar x -> Sort.EVar x
    | Sort.Pure -> Sort.Pure
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Sort.Eff (subst_sorts_opsig map o1,
                subst_sorts_sort map s1,
                subst_sorts_cont map e1,
                subst_sorts_opsig map o2,
                subst_sorts_sort map s2,
                subst_sorts_cont map e2)
    | _ -> failwith "subst_sorts_cont"
  and subst_sorts_opsig map = function
    | Sort.OpSig (opmap, r) ->
      Sort.OpSig (ALMap.map opmap ~f:(subst_sorts_sort map), r)
    | _ -> failwith "subst_sorts_opsig"
  let subst_conts_fun_sym map = function
    | FVar (var, sorts) ->
      FVar (var, List.map ~f:(Term.subst_conts_sort map) sorts)
    | (T_num.Value (_, svar) | T_num.NAdd svar | T_num.NSub svar | T_num.NMult svar | T_num.NDiv svar | T_num.NPower svar | T_num.NNeg svar) as sym ->
      T_num.fsym_of_num_fsym sym @@ Term.subst_conts_sort map @@ Sort.SVar svar
    | T_bool.Formula phi ->
      T_bool.Formula (Formula.subst_conts map phi)
    | T_tuple.TupleCons sorts ->
      T_tuple.TupleCons (List.map ~f:(Term.subst_conts_sort map) sorts)
    | T_tuple.TupleSel (sorts, i) ->
      T_tuple.TupleSel (List.map ~f:(Term.subst_conts_sort map) sorts, i)
    | T_dt.DTCons (name, arg_sorts, dt) ->
      T_dt.DTCons (name, List.map arg_sorts ~f:(Term.subst_conts_sort map), Datatype.subst_conts map dt)
    | T_dt.DTSel (name, dt, sort) ->
      T_dt.DTSel (name, Datatype.subst_conts map dt, Term.subst_conts_sort map sort)
    | T_array.ASelect (s1, s2) ->
      T_array.ASelect (Term.subst_conts_sort map s1, Term.subst_conts_sort map s2)
    | T_array.AStore (s1, s2) ->
      T_array.AStore (Term.subst_conts_sort map s1, Term.subst_conts_sort map s2)
    | T_array.AConst (s1, s2) ->
      T_array.AConst (Term.subst_conts_sort map s1, Term.subst_conts_sort map s2)
    | sym -> sym(* ToDo *)
  let rec subst_conts map = function
    | Var (x, sort, info) ->
      Var (x, subst_conts_sort map sort, info)
    (*| FunApp (T_real_int.ToReal, [Var (tvar, _, info)], _) ->
      Var (tvar, T_real.SReal, info)
      | FunApp (T_real_int.ToInt, [Var (tvar, _, info)], _) ->
      Var (tvar, T_int.SInt, info)
      | FunApp (T_string.StringConst str, _, info) ->
      Var (Ident.Tvar ("\"" ^ str ^ "\""), T_string.SString, info)*)
    | FunApp (sym, args, info) ->
      FunApp (subst_conts_fun_sym map sym, List.map ~f:(subst_conts map) args, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, subst_conts_sort map sort, subst_conts map def, subst_conts map body, info)
  and subst_conts_cont map = function
    | Sort.EVar evar ->
      (match Map.Poly.find map evar with Some e -> e | None -> Sort.EVar evar)
    | Sort.Pure -> Sort.Pure
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Sort.Eff (subst_conts_opsig map o1,
                subst_conts_sort map s1,
                subst_conts_cont map e1,
                subst_conts_opsig map o2,
                subst_conts_sort map s2,
                subst_conts_cont map e2)
    | _ -> failwith "subst_conts_cont"
  and subst_conts_sort map = function
    | Sort.SVar svar -> Sort.SVar svar
    | Sort.SArrow (s1, (o, s2, e)) ->
      Sort.SArrow (subst_conts_sort map s1,
                   (subst_conts_opsig map o,
                    subst_conts_sort map s2,
                    subst_conts_cont map e))
    | T_tuple.STuple sorts ->
      T_tuple.STuple (List.map sorts ~f:(subst_conts_sort map))
    | T_dt.SDT dt ->
      T_dt.SDT (Datatype.subst_conts map dt)
    | T_array.SArray (s1, s2) ->
      T_array.SArray (subst_conts_sort map s1, subst_conts_sort map s2)
    | sort -> sort(*failwith "subst_conts_sort"*)
  and subst_conts_opsig map = function
    | Sort.OpSig (opmap, r) ->
      Sort.OpSig (ALMap.map opmap ~f:(subst_conts_sort map), r)
    | _ -> failwith "subst_conts_opsig"
  let subst_opsigs_fun_sym map = function
    | FVar (var, sorts) ->
      FVar (var, List.map ~f:(Term.subst_opsigs_sort map) sorts)
    | (T_num.Value (_, svar) | T_num.NAdd svar | T_num.NSub svar | T_num.NMult svar | T_num.NDiv svar | T_num.NPower svar | T_num.NNeg svar) as sym ->
      T_num.fsym_of_num_fsym sym @@ Term.subst_opsigs_sort map @@ Sort.SVar svar
    | T_bool.Formula phi ->
      T_bool.Formula (Formula.subst_opsigs map phi)
    | T_tuple.TupleCons sorts ->
      T_tuple.TupleCons (List.map ~f:(Term.subst_opsigs_sort map) sorts)
    | T_tuple.TupleSel (sorts, i) ->
      T_tuple.TupleSel (List.map ~f:(Term.subst_opsigs_sort map) sorts, i)
    | T_dt.DTCons (name, arg_sorts, dt) ->
      T_dt.DTCons (name, List.map arg_sorts ~f:(Term.subst_opsigs_sort map), Datatype.subst_opsigs map dt)
    | T_dt.DTSel (name, dt, sort) ->
      T_dt.DTSel (name, Datatype.subst_opsigs map dt, Term.subst_opsigs_sort map sort)
    | T_array.ASelect (s1, s2) ->
      T_array.ASelect (Term.subst_opsigs_sort map s1, Term.subst_opsigs_sort map s2)
    | T_array.AStore (s1, s2) ->
      T_array.AStore (Term.subst_opsigs_sort map s1, Term.subst_opsigs_sort map s2)
    | T_array.AConst (s1, s2) ->
      T_array.AConst (Term.subst_opsigs_sort map s1, Term.subst_opsigs_sort map s2)
    | sym -> sym(* ToDo *)
  let rec subst_opsigs map = function
    | Var (x, sort, info) ->
      Var (x, subst_opsigs_sort map sort, info)
    (*| FunApp (T_real_int.ToReal, [Var (tvar, _, info)], _) ->
      Var (tvar, T_real.SReal, info)
      | FunApp (T_real_int.ToInt, [Var (tvar, _, info)], _) ->
      Var (tvar, T_int.SInt, info)
      | FunApp (T_string.StringConst str, _, info) ->
      Var (Ident.Tvar ("\"" ^ str ^ "\""), T_string.SString, info)*)
    | FunApp (sym, args, info) ->
      FunApp (subst_opsigs_fun_sym map sym, List.map ~f:(subst_opsigs map) args, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, subst_opsigs_sort map sort, subst_opsigs map def, subst_opsigs map body, info)
  and subst_opsigs_sort map = function
    | Sort.SVar svar -> Sort.SVar svar
    | Sort.SArrow (s1, (o, s2, e)) ->
      Sort.SArrow (subst_opsigs_sort map s1,
                   (subst_opsigs_opsig map o,
                    subst_opsigs_sort map s2,
                    subst_opsigs_cont map e))
    | T_tuple.STuple sorts ->
      T_tuple.STuple (List.map sorts ~f:(subst_opsigs_sort map))
    | T_dt.SDT dt ->
      T_dt.SDT (Datatype.subst_opsigs map dt)
    | T_array.SArray (s1, s2) ->
      T_array.SArray (subst_opsigs_sort map s1, subst_opsigs_sort map s2)
    | sort -> sort(*failwith "subst_opsigs_sort"*)
  and subst_opsigs_cont map = function
    | Sort.EVar x -> Sort.EVar x
    | Sort.Pure -> Sort.Pure
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Sort.Eff (subst_opsigs_opsig map o1,
                subst_opsigs_sort map s1,
                subst_opsigs_cont map e1,
                subst_opsigs_opsig map o2,
                subst_opsigs_sort map s2,
                subst_opsigs_cont map e2)
    | _ -> failwith "subst_opsigs_cont"
  and subst_opsigs_opsig map = function
    | Sort.OpSig (opmap, None) ->
      Sort.OpSig (ALMap.map opmap ~f:(subst_opsigs_sort map), None)
    | Sort.OpSig (opmap, Some rvar) -> begin
        match Map.Poly.find map rvar with
        | Some (Sort.OpSig (opmap2, r_opt)) ->
          let opmap' = ALMap.map opmap ~f:(subst_opsigs_sort map) in
          Sort.OpSig (ALMap.force_merge opmap' opmap2, r_opt)
        | None ->
          Sort.OpSig (ALMap.map opmap ~f:(subst_opsigs_sort map), Some rvar)
        | _ -> failwith "subst_opsigs_opsig"
      end
    | _ -> failwith "subst_opsigs_opsig"
  let subst_sort (omap, smap, emap) sort =
    subst_opsigs_sort omap @@ subst_conts_sort emap @@ subst_sorts_sort smap sort
  let subst_cont (omap, smap, emap) eff =
    subst_opsigs_cont omap @@ subst_conts_cont emap @@ subst_sorts_cont smap eff
  let subst_opsig (omap, smap, emap) opsig =
    subst_opsigs_opsig omap @@ subst_conts_opsig emap @@ subst_sorts_opsig smap opsig
  let subst_all (omap, smap, emap) term =
    Term.subst_opsigs omap @@ Term.subst_conts emap @@ Term.subst_sorts smap term

  let alpha_rename_let_fun_sym ?(map=Map.Poly.empty) = function
    | T_bool.Formula phi ->
      T_bool.Formula (Formula.alpha_rename_let ~map phi)
    | FVar (var, sorts) ->
      FVar ((match Map.Poly.find map var with Some v -> v | None -> var), sorts)
    | fsym -> fsym
  let rec alpha_rename_let ?(map=Map.Poly.empty) = function
    | Var (var, sort, info) ->
      Var ((match Map.Poly.find map var with Some v -> v | None -> var), sort, info)
    | FunApp (fsym, ts, info) ->
      FunApp (alpha_rename_let_fun_sym ~map fsym,
              List.map ts ~f:(alpha_rename_let ~map),
              info)
    | LetTerm (var, sort, def, body, info) ->
      let var' = Ident.mk_fresh_tvar () in
      let map' = Map.Poly.set ~key:var ~data:var' map in
      LetTerm (var', sort, alpha_rename_let ~map def, alpha_rename_let ~map:map' body, info)
  (* assume that [phi] is let-normalized *)
  let rec replace_let_formula_body phi new_body =
    match phi with
    | Formula.LetFormula (var, sort, def, body, info) ->
      LetTerm (var, sort, def, replace_let_formula_body body new_body, info)
    | _ -> new_body
  (* assume that [term] is let-normalized *)
  let rec replace_let_body term new_body =
    match term with
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, def, replace_let_body body new_body, info)
    | FunApp (T_bool.Formula phi, [], _) when Formula.is_let_formula phi ->
      replace_let_formula_body phi new_body
    | _ -> new_body
  let rec aconv_tvar = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (sym, args, info) ->
      let sym = match sym with
        | T_bool.Formula phi -> T_bool.Formula (Formula.aconv_tvar phi)
        | sym -> sym
      in
      FunApp (sym, List.map ~f:aconv_tvar args, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, aconv_tvar def, aconv_tvar body, info)
  let aconv_pvar = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (sym, args, info) ->
      let sym = match sym with
        | T_bool.Formula phi -> T_bool.Formula (Formula.aconv_pvar phi)
        | sym -> sym
      in
      FunApp (sym, List.map ~f:Term.aconv_pvar args, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, Term.aconv_pvar def, Term.aconv_pvar body, info)
  let rec fresh_conts_sort = function
    | Sort.SVar svar -> Sort.SVar svar
    | Sort.SArrow (s1, (_o, s2, _e)) ->
      Sort.SArrow (fresh_conts_sort s1,
                   (Sort.mk_fresh_empty_open_opsig (),
                    fresh_conts_sort s2,
                    Sort.mk_fresh_evar ()))
    | Sort.SPoly (svs, s) -> Sort.SPoly (svs, s)
    | (T_bool.SBool | T_int.SInt | T_int.SRefInt | T_real.SReal) as s -> s
    | T_tuple.STuple sorts -> T_tuple.STuple (List.map ~f:fresh_conts_sort sorts)
    | T_dt.SDT dt -> T_dt.SDT (Datatype.fresh_conts_sort dt)
    | T_dt.SUS (name, sorts) -> T_dt.SUS (name, List.map ~f:fresh_conts_sort sorts)
    | T_array.SArray (s1, s2) -> T_array.SArray (fresh_conts_sort s1, fresh_conts_sort s2)
    | (T_string.SString | T_sequence.SFinSequence | T_sequence.SInfSequence) as s ->s
    | _ -> failwith "[fresh_conts_sort] unknown sort"

  let rec fresh_rvs_cont = function
    | Sort.EVar _ | Sort.Pure as e -> e
    | Sort.Eff (o1, s1, e1, o2, s2, e2) ->
      Sort.Eff
        (fresh_rvs_opsig o1, fresh_rvs_sort s1, fresh_rvs_cont e1,
         fresh_rvs_opsig o2, fresh_rvs_sort s2, fresh_rvs_cont e2)
    | _ -> failwith "fresh_rvs_cont"
  and fresh_rvs_sort = function
    | Sort.SVar _ as s -> s
    | Sort.SArrow (s1, (o, s2, e)) ->
      Sort.SArrow (fresh_rvs_sort s1, (fresh_rvs_opsig o, fresh_rvs_sort s2, fresh_rvs_cont e))
    | Sort.SPoly (svs, s) ->
      Sort.SPoly (svs, fresh_rvs_sort s)
    | T_bool.SBool | T_int.SInt | T_int.SRefInt | T_real.SReal as s -> s
    | T_tuple.STuple sorts -> T_tuple.STuple (List.map ~f:fresh_rvs_sort sorts)
    | T_dt.SDT dt -> T_dt.SDT (Datatype.fresh_rvs_sort dt)
    | T_dt.SUS (name, sorts) -> T_dt.SUS (name, (List.map ~f:fresh_rvs_sort sorts))
    | T_array.SArray (s1, s2) -> T_array.SArray (fresh_rvs_sort s1, fresh_rvs_sort s2)
    | T_string.SString | T_sequence.SFinSequence | T_sequence.SInfSequence as s -> s
    | _ -> failwith "[fresh_rvs_sort] unknown sort"
  and fresh_rvs_opsig = function
    | Sort.OpSig (map, _) ->
      Sort.OpSig (Common.Util.ALMap.map map ~f:fresh_rvs_sort, Some (Ident.mk_fresh_rvar ()))
    | _ -> failwith "fresh_rvs_opsig"

  let number_of_pvar_apps is_pos term =
    let rec number_of_pvar_apps_aux ~ex is_pos = function
      | FunApp (T_bool.Formula phi, _, _) ->
        Formula.number_of_pvar_apps is_pos phi
      | LetTerm (var, _, def, body, _) ->
        let def_size = number_of_pvar_apps_aux ~ex is_pos def in
        number_of_pvar_apps_aux ~ex:(Map.Poly.set ~key:var ~data:def_size ex) is_pos body
      | Var (var, _, _) ->
        begin match Map.Poly.find ex var with | Some i -> i | None -> 0 end
      | FunApp (_, ts, _) ->
        List.fold_left ~init:0 ts ~f:(fun ret t -> ret + number_of_pvar_apps_aux ~ex is_pos t)
    in number_of_pvar_apps_aux is_pos term ~ex:(Map.Poly.empty)
  (** Transformation *)
  let rec elim_neq = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (T_bool.Formula phi, [], info) ->
      FunApp (T_bool.Formula (Formula.elim_neq phi), [], info)
    | FunApp (fsym, ts, info) ->
      FunApp (fsym, List.map ts ~f:elim_neq, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, elim_neq def, elim_neq body, info)
  let rec elim_ite = function
    | Var (var, sort, info) -> [Formula.mk_true (), Var (var, sort, info)]
    | FunApp (T_bool.IfThenElse, [t1; t2; t3], _) ->
      let cond = Formula.elim_ite @@ Formula.of_bool_term t1 in
      (List.map ~f:(fun (phi, t) -> Formula.mk_and cond phi, t) @@ elim_ite t2) @
      (List.map ~f:(fun (phi, t) -> Formula.mk_and (Formula.mk_neg cond) phi, t) @@ elim_ite t3)
    | FunApp (T_int.Neg, [t], info) ->
      List.map ~f:(fun (phi, t) -> phi, FunApp (T_int.Neg, [t], info)) @@ elim_ite t
    | FunApp ((T_int.Add | T_int.Sub | T_int.Mult | T_int.Div | T_int.Mod | T_real.RAdd | T_real.RSub | T_real.RMult | T_real.RDiv) as fsym, [t1; t2], info) ->
      List.cartesian_product (elim_ite t1) (elim_ite t2)
      |> List.map ~f:(fun ((phi1, t1), (phi2, t2)) ->
          Formula.and_of [phi1; phi2], FunApp (fsym, [t1; t2], info))
    | FunApp (T_bool.Formula phi, [], info) ->
      [Formula.mk_true (), FunApp (T_bool.Formula (Formula.elim_ite phi), [], info) ]
    | FunApp (fsym, [t1], info) ->
      List.map ~f:(fun (phi, t) -> (phi, FunApp (fsym, [t], info))) @@ elim_ite t1
    (*     | FunApp (fsym, [t1; t2], info) ->
           List.cartesian_product (elim_ite t1) (elim_ite t2)
           |> List.map ~f:(fun ((phi1, t1), (phi2, t2)) ->
           Formula.and_of [phi1; phi2], FunApp (fsym, [t1; t2], info)) *)
    | _ as term->
      (* print_endline ("can't elim ite :" ^ (Term.str_of term)); *)
      [Formula.mk_true (), term]
  let rec elim_pvars unknowns = function
    | Var (_, _, _) as term -> term
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, elim_pvars unknowns def, elim_pvars unknowns body, info)
    | FunApp (T_bool.Formula phi, [], info) ->
      FunApp (T_bool.Formula (Formula.elim_pvars unknowns phi), [], info)
    | FunApp (fsym, ts, info) ->
      FunApp (fsym, List.map ts ~f:(elim_pvars unknowns), info)
  (** eliminate let-binding that contains an unknown to be synthesized
      if the argument is let-normalized, then the return value is let-normalized *)
  let rec elim_let_with_unknowns ?(map=Map.Poly.empty) unknowns = function
    | Var (var, _, _) as term ->
      (match Map.Poly.find map var with Some t -> t | None -> term)
    | LetTerm (var, sort, def, body, info) ->
      let def' = elim_let_with_unknowns ~map unknowns def in
      if Set.Poly.is_empty @@ Set.Poly.inter (Term.fvs_of def') unknowns then
        LetTerm (var, sort, def', elim_let_with_unknowns ~map unknowns body, info)
      else
        elim_let_with_unknowns ~map:(Map.Poly.set map ~key:var ~data:def') unknowns body
    | FunApp (T_bool.Formula phi, [], info) ->
      FunApp (T_bool.Formula (Formula.elim_let_with_unknowns ~map unknowns phi), [], info)
    | FunApp (fsym, ts, info) ->
      FunApp (fsym, List.map ts ~f:(elim_let_with_unknowns ~map unknowns), info)
  let rec elim_let ?(map=Map.Poly.empty) = function
    | Var (var, _, _) as term ->
      (match Map.Poly.find map var with Some t -> t | None -> term)
    | LetTerm (var, _, def, body, _) ->
      let def' = elim_let ~map def in
      elim_let ~map:(Map.Poly.set map ~key:var ~data:def') body
    | FunApp (T_bool.Formula phi, [], info) ->
      FunApp (T_bool.Formula (Formula.elim_let ~map phi), [], info)
    | FunApp (fsym, ts, info) ->
      FunApp (fsym, List.map ts ~f:(elim_let ~map), info)
  let rec has_let ?(map=Map.Poly.empty) = function
    | LetTerm _ -> true
    | FunApp (T_bool.Formula phi, _, _) -> Formula.has_let ~map phi
    | FunApp (_, ts, _) -> List.exists ts ~f:(has_let ~map)
    | Var (var, _, _) -> Map.Poly.mem map var
  (* assume that the argument is alpha-renamed *)
  let rec let_env_of ?(map=Map.Poly.empty) = function
    | LetTerm (var, _, def, body, _) ->
      let_env_of ~map:(Map.Poly.set map ~key:var ~data:(subst map def)) body
    | FunApp (T_bool.Formula phi, [], _) -> Formula.let_env_of ~map phi
    | FunApp (_, ts, _) -> List.fold ts ~init:map ~f:(fun map -> let_env_of ~map)
    | Var _ -> map
  (* assume that the argument is alpha-renamed *)
  let rec let_sort_env_of ?(map=Map.Poly.empty) = function
    | LetTerm (var, sort, _, body, _) ->
      let_sort_env_of ~map:(Map.Poly.set map ~key:var ~data:sort) body
    | FunApp (T_bool.Formula phi, [], _) -> Formula.let_sort_env_of ~map phi
    | FunApp (_, ts, _) -> List.fold ts ~init:map ~f:(fun map -> let_sort_env_of ~map)
    | Var _ -> map

  let rec instantiate_div0_mod0 = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp ((T_int.Div | T_int.Mod), [t1; t2], _) when T_int.is_zero t2 ->
      mk_var (Ident.mk_dontcare (Term.str_of t1)) T_int.SInt
    | FunApp (sym, ts, info) ->
      let sym = match sym with
        | T_bool.Formula phi -> T_bool.Formula (Formula.instantiate_div0_mod0 phi)
        | sym -> sym
      in
      FunApp (sym, List.map ~f:instantiate_div0_mod0 ts, info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, instantiate_div0_mod0 def, instantiate_div0_mod0 body, info)

  let rec extend_pred_params ident extended_params = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (sym, args, info) -> begin
        let sym = match sym with
          | T_bool.Formula phi ->
            T_bool.Formula (Formula.extend_pred_params ident extended_params phi)
          | sym -> sym
        in
        let args = List.map ~f:(extend_pred_params ident extended_params) args in
        FunApp (sym, args, info)
      end
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort,
               extend_pred_params ident extended_params def,
               extend_pred_params ident extended_params body,
               info)

  let rec find_div_mod = function
    | [] -> Set.Poly.empty
    | t :: tl -> Set.Poly.union (find_div_mod_in_term t) (find_div_mod tl)
  and find_div_mod_in_term = function
    | Var (_, _, _) -> Set.Poly.empty
    | FunApp (T_int.Div, [t1; t2], _) | FunApp (T_int.Mod, [t1; t2], _) ->
      Set.Poly.add (Set.Poly.union (find_div_mod_in_term t1) (find_div_mod_in_term t2)) (t1, t2)
    | FunApp (_, args, _) -> find_div_mod args
    | LetTerm (_, _, def, body, _) ->
      Set.Poly.union (find_div_mod_in_term def) (find_div_mod_in_term body)
  let rec replace_div_mod map = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (T_int.Div, [t1; t2], _) ->
      let (divvar, _) = Map.Poly.find_exn map (t1, t2) in
      Var (divvar, T_int.SInt, Dummy)
    | FunApp (T_int.Mod, [t1; t2], _) ->
      let (_, modvar) = Map.Poly.find_exn map (t1, t2) in
      Var (modvar, T_int.SInt, Dummy)
    | FunApp (sym, args, info) ->
      FunApp (sym, List.map args ~f:(replace_div_mod map), info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, replace_div_mod map def, replace_div_mod map body, info)

  let rm_boolean_term = function
    | Var (Ident.Tvar name, sort, _) ->
      Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar name) [sort] []
    | FunApp (T_bool.Formula phi, [], _) ->
      Formula.rm_boolean_term phi
    | LetTerm (var, sort, def, FunApp (T_bool.Formula phi, [], _), info) ->
      Formula.LetFormula (var, sort, def, Formula.rm_boolean_term phi, info)
    | _ -> assert false

  let rec complete_tsort map = function
    | FunApp (T_bool.Formula phi, [], info) ->
      FunApp (T_bool.Formula (Formula.complete_tsort phi), [], info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, complete_tsort map def, complete_tsort map body, info)
    | FunApp (op, ts, info) ->
      FunApp (op, List.map ts ~f:(complete_tsort map), info)
    | t -> t

  let rec complete_psort map = function
    | FunApp (T_bool.Formula phi, [], info) ->
      FunApp (T_bool.Formula (Formula.complete_psort map phi), [], info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, complete_psort map def, complete_psort map body, info)
    | FunApp (op, ts, info) ->
      FunApp (op, List.map ts ~f:(complete_psort map), info)
    | t -> t

  let rec replace_papps map = function
    | FunApp (T_bool.Formula phi, [], info) ->
      FunApp (T_bool.Formula (Formula.replace_papps map phi), [], info)
    | LetTerm (var, sort, def, body, info) ->
      LetTerm (var, sort, replace_papps map def, replace_papps map body, info)
    | FunApp (op, ts, info) ->
      FunApp (op, List.map ts ~f:(replace_papps map), info)
    | t -> t

  let insert_let_term var sort def info term =
    if Set.Poly.mem (tvs_of term) var then
      let var' = Ident.mk_fresh_tvar () in
      LetTerm (var', sort, def, rename (Map.Poly.singleton var var') term, info)
    else term

  (** Observation *)

  let is_bool_sort = Stdlib.(=) T_bool.SBool
  let is_int_sort = Stdlib.(=) T_int.SInt
  let is_int_ref_sort = Stdlib.(=) T_int.SRefInt
  let is_real_sort = Stdlib.(=) T_real.SReal

  let rec sort_of = function
    | Var (_, sort, _) -> sort
    | FunApp (FVar (_, sorts), args, _) ->
      Sort.mk_fun @@ List.drop sorts (List.length args)
    | FunApp (T_int.Int _, _, _) | FunApp (T_int.Mod, _, _) | FunApp (T_int.Rem, _, _) -> T_int.SInt
    | FunApp (T_real.Real _, _, _) | FunApp (T_real.Alge _, _, _) -> T_real.SReal
    | FunApp (T_int.Add, _, _) | FunApp (T_int.Sub, _, _)
    | FunApp (T_int.Mult, _, _) | FunApp (T_int.Div, _, _)
    | FunApp (T_int.Neg, _, _) | FunApp (T_int.Abs, _, _) | FunApp (T_real_int.ToInt, _, _) -> T_int.SInt
    | FunApp (T_real.RAdd, _, _) | FunApp (T_real.RSub, _, _)
    | FunApp (T_real.RMult, _, _) | FunApp (T_real.RDiv, _, _)
    | FunApp (T_real.RNeg, _, _) | FunApp (T_real.RAbs, _, _)| FunApp (T_real_int.ToReal, _, _)-> T_real.SReal
    | FunApp (T_bool.Formula _, _, _) -> T_bool.SBool
    | FunApp (T_bool.IfThenElse, [_; t; _], _) -> sort_of t
    | FunApp (T_num.Value (_, svar), _, _) -> Sort.SVar svar
    | FunApp (T_dt.DTCons (_, _, dt), _, _) -> Datatype.sort_of dt
    | FunApp (T_dt.DTSel (_, _, sort), _, _) -> sort
    | FunApp (T_array.AStore (s1, s2), [_; _ ; _], _) -> T_array.SArray (s1, s2)
    | FunApp (T_array.ASelect (_s1, s2), [_; _], _) -> s2
    | FunApp (T_array.AConst (s1, s2),_, _) -> T_array.SArray (s1, s2)
    | FunApp (T_num.NAdd svar, _, _) | FunApp (T_num.NSub svar, _, _)
    | FunApp (T_num.NMult svar, _, _) | FunApp (T_num.NDiv svar, _, _)
    | FunApp (T_num.NPower svar, _, _) | FunApp (T_num.NNeg svar, _, _) -> Sort.SVar svar
    | FunApp (T_tuple.TupleCons sorts, _, _) -> T_tuple.STuple sorts
    | FunApp (T_tuple.TupleSel (sorts, i), [_], _) -> List.nth_exn sorts i
    | FunApp (T_string.StringConst _, _, _) -> T_string.SString
    | FunApp (T_sequence.Epsilon, [], _) -> T_sequence.SFinSequence
    | FunApp (T_sequence.Symbol _, [], _) -> T_sequence.SFinSequence
    | FunApp (T_sequence.Concat fin, [_; _], _) -> if fin then T_sequence.SFinSequence else T_sequence.SInfSequence
    | FunApp (T_sequence.LeftQuotient fin, [_; _], _) -> if fin then T_sequence.SFinSequence else T_sequence.SInfSequence
    | FunApp (T_sequence.RightQuotient fin, [_; _], _) -> if fin then T_sequence.SFinSequence else T_sequence.SInfSequence
    | LetTerm (_, _, _, body, _) -> sort_of body
    | t -> failwith ("error at sort_of: " ^ str_of t)


  (** Unification and Pattern Matching *)
  let rec unify bvs t1 t2 =
    match t1, t2 with
    | t1, t2 when Stdlib.(t1 = t2) ->
      Option.some @@ Map.Poly.empty
    | FunApp (T_bool.Formula (Formula.Atom (atm1, _)), [], _),
      FunApp (T_bool.Formula (Formula.Atom (atm2, _)), [], _)
      when (Atom.is_true atm1 && Atom.is_true atm2) ||
           (Atom.is_false atm1 && Atom.is_false atm2) (* ToDo: reachable? *) ->
      Option.some @@ Map.Poly.empty
    | Var (x, _, _), t
      when not (Set.Poly.mem bvs x) && not (Set.Poly.mem (tvs_of t) x) ->
      Option.some @@ Map.Poly.singleton x t
    | t, Var (x, _, _)
      when not (Set.Poly.mem bvs x) && not (Set.Poly.mem (tvs_of t) x) ->
      Option.some @@ Map.Poly.singleton x t
    | FunApp (funsym, [Var (x, _, _); t3], _), t2
      when not (Set.Poly.mem bvs x) &&
           (Stdlib.(funsym = T_int.Add) || Stdlib.(funsym = T_real.RAdd) ||
            Stdlib.(funsym = T_int.Sub) || Stdlib.(funsym = T_real.RSub)) &&
           not (Set.Poly.mem (tvs_of t3) x) &&
           not (Set.Poly.mem (tvs_of t2) x) ->
      Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t2; t3])
    | FunApp (funsym, [t3; Var (x, _, _)], _), t2
      when not (Set.Poly.mem bvs x) &&
           (Stdlib.(funsym = T_int.Add) || Stdlib.(funsym = T_real.RAdd) (*|| Stdlib.(funsym = T_int.Mult)*)) &&
           not (Set.Poly.mem (tvs_of t3) x) &&
           not (Set.Poly.mem (tvs_of t2) x) ->
      Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t2; t3])
    | FunApp (funsym, [t3; Var (x, _, _)], _), t2
      when not (Set.Poly.mem bvs x) &&
           (Stdlib.(funsym = T_int.Sub) || Stdlib.(funsym = T_real.RSub) (*|| Stdlib.(funsym = T_int.Div)*)) &&
           not (Set.Poly.mem (tvs_of t3) x) &&
           not (Set.Poly.mem (tvs_of t2) x) ->
      Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app funsym [t3; t2])
    | t1, FunApp (funsym, [Var (x, _, _); t3], _)
      when not (Set.Poly.mem bvs x) &&
           (Stdlib.(funsym = T_int.Add) || Stdlib.(funsym = T_real.RAdd) ||
            Stdlib.(funsym = T_int.Sub) || Stdlib.(funsym = T_real.RSub)) &&
           not (Set.Poly.mem (tvs_of t3) x) &&
           not (Set.Poly.mem (tvs_of t2) x) ->
      Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t1; t3])
    | t1, FunApp (funsym, [t3; Var (x, _, _)], _)
      when not (Set.Poly.mem bvs x) &&
           (Stdlib.(funsym = T_int.Add) || Stdlib.(funsym = T_real.RAdd)
           (*|| Stdlib.(funsym = T_int.Mult)*)) &&
           not (Set.Poly.mem (tvs_of t3) x) &&
           not (Set.Poly.mem (tvs_of t2) x) ->
      Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t1; t3])
    | t1, FunApp (funsym, [t3; Var (x, _, _)], _)
      when not (Set.Poly.mem bvs x) &&
           (Stdlib.(funsym = T_int.Sub) ||
            Stdlib.(funsym = T_real.RSub)
            (*|| Stdlib.(funsym = T_int.Div)*)) &&
           not (Set.Poly.mem (tvs_of t3) x) &&
           not (Set.Poly.mem (tvs_of t2) x) ->
      Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app funsym [t3; t1])
    | FunApp ((T_dt.DTCons (_, _, _) as fsym1), ts1, _),
      FunApp ((T_dt.DTCons (_, _, _) as fsym2), ts2, _) when Stdlib.(fsym1 = fsym2) ->
      List.fold2_exn ts1 ts2 ~init:(Some (Map.Poly.empty)) ~f:(fun opt t1 t2 ->
          match opt with
          | None -> None
          | Some opt ->
            match unify bvs t1 t2 with
            | None -> None
            | Some opt' ->
              try Some (Map.force_merge opt opt'
              (*~catch_dup:(fun (tvar, t1, t2) ->
                  print_endline @@ sprintf "%s : %s != %s"
                    (Ident.name_of_tvar tvar) (Term.str_of t1) (Term.str_of t2))*))
              with _ -> None)
    | _ -> None (* ToDo: remerdy incompleteness. support more general terms *)

  (* variables in t1 and t2 belong to different name spaces *)
  let pattern_match bvs t1 t2 =
    if Set.Poly.is_empty @@ Term.tvs_of t1 && Stdlib.(t1 = t2) then
      Option.some @@ Map.Poly.empty
    else
      match t1, t2 with
      | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) when Z.Compare.(=) n1 n2 -> (* ToDo: reachable? *)
        Option.some @@ Map.Poly.empty
      | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _) when Q.(=) r1 r2 -> (* ToDo: reachable? *)
        Option.some @@ Map.Poly.empty
      | FunApp (T_bool.Formula (Formula.Atom (atm1, _)), [], _), FunApp (T_bool.Formula (Formula.Atom (atm2, _)), [], _)
        when (Atom.is_true atm1 && Atom.is_true atm2) || (Atom.is_false atm1 && Atom.is_false atm2) (* ToDo: reachable? *) ->
        Option.some @@ Map.Poly.empty
      | Var (x, _, _), _ when not @@ Set.Poly.mem bvs x ->
        Option.some @@ Map.Poly.singleton x t2

      | FunApp (funsym, [Var (x, _, _); t3], _), _
        when not (Set.Poly.mem bvs x) &&
             Set.Poly.is_empty @@ Term.tvs_of t3 &&
             (Stdlib.(funsym = T_int.Add) || Stdlib.(funsym = T_int.Sub)) ->
        Option.some @@
        Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t2; t3])
      | FunApp (funsym, [t3; Var (x, _, _)], _), _
        when not (Set.Poly.mem bvs x) &&
             Set.Poly.is_empty @@ Term.tvs_of t3 &&
             (Stdlib.(funsym = T_int.Add) (*|| Stdlib.(funsym = T_int.Mult)*)) ->
        Option.some @@
        Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t2; t3])
      | FunApp (funsym, [t3; Var (x, _, _)], _), _
        when not (Set.Poly.mem bvs x) &&
             Set.Poly.is_empty @@ Term.tvs_of t3 &&
             (Stdlib.(funsym = T_int.Sub) (*|| Stdlib.(funsym = T_int.Div)*)) ->
        Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app funsym [t3; t2])

      | _ -> None (* ToDo: remerdy incompleteness. support more general terms *)
  (* especially, non-linear pattern is not supported *)

  let rec pat_match_sort sort1 sort2 =
    if Stdlib.(sort1 = sort2) then Map.Poly.empty, Map.Poly.empty, Map.Poly.empty
    else
      match sort1, sort2 with
      | Sort.SVar svar, _ ->
        Map.Poly.empty, Map.Poly.singleton svar sort2, Map.Poly.empty
      | Sort.SArrow (s11, (o1, s12, e1)), Sort.SArrow (s21, (o2, s22, e2)) ->
        let omap1, smap1, emap1 = pat_match_cont e1 e2 in
        let omap2, smap2, emap2 = pat_match_opsig o1 o2 in
        let omaps, smaps, emaps =
          List.unzip3 @@ List.map2_exn [s11; s12] [s21; s22] ~f:pat_match_sort
        in
        Map.force_merge_list @@ omap1 :: omap2 :: omaps,
        Map.force_merge_list @@ smap1 :: smap2 :: smaps,
        Map.force_merge_list @@ emap1 :: emap2 :: emaps
      | Sort.SPoly (svs1, s1), Sort.SPoly (svs2, s2) when Set.Poly.equal svs1 svs2 ->
        pat_match_sort s1 s2
      | T_tuple.STuple sorts1, T_tuple.STuple sorts2 ->
        let omaps, smaps, emaps =
          List.unzip3 @@ List.map2_exn sorts1 sorts2 ~f:pat_match_sort
        in
        Map.force_merge_list omaps,
        Map.force_merge_list smaps,
        Map.force_merge_list emaps
      | T_dt.SDT dt1, T_dt.SDT dt2 ->
        Datatype.pat_match_sort dt1 dt2
      | T_dt.SUS (name1, sorts1), T_dt.SUS (name2, sorts2) when String.(name1 = name2) ->
        let omaps, smaps, emaps =
          List.unzip3 @@ List.map2_exn sorts1 sorts2 ~f:pat_match_sort
        in
        Map.force_merge_list omaps,
        Map.force_merge_list smaps,
        Map.force_merge_list emaps
      | T_dt.SDT dt1, T_dt.SUS (name2, sorts2) when String.(dt1.name = name2) ->
        let omaps, smaps, emaps =
          List.unzip3 @@ List.map2_exn (Datatype.args_of dt1) sorts2 ~f:pat_match_sort
        in
        Map.force_merge_list omaps,
        Map.force_merge_list smaps,
        Map.force_merge_list emaps
      | T_dt.SUS (name1, sorts1), T_dt.SDT dt2 when String.(name1 = dt2.name) ->
        let omaps, smaps, emaps =
          List.unzip3 @@ List.map2_exn sorts1 (Datatype.args_of dt2) ~f:pat_match_sort
        in
        Map.force_merge_list omaps,
        Map.force_merge_list smaps,
        Map.force_merge_list emaps
      | T_array.SArray (s11, s12), T_array.SArray (s21, s22) ->
        let omaps, smaps, emaps =
          List.unzip3 @@ List.map2_exn [s11; s12] [s21; s22] ~f:pat_match_sort
        in
        Map.force_merge_list omaps,
        Map.force_merge_list smaps,
        Map.force_merge_list emaps
      | _ -> failwith ("[pat_match_sort] " ^ str_of_sort sort1 ^ " and " ^ str_of_sort sort2 ^ " does not match")
  and pat_match_cont e1 e2 =
    if Stdlib.(e1 = e2) then Map.Poly.empty, Map.Poly.empty, Map.Poly.empty
    else
      match e1, e2 with
      | Sort.EVar evar, _ ->
        Map.Poly.empty, Map.Poly.empty, Map.Poly.singleton evar e2
      | Sort.Eff (o11, s11, e11, o12, s12, e12), Sort.Eff (o21, s21, e21, o22, s22, e22) ->
        let omaps1, smaps1, emaps1 =
          List.unzip3 @@ List.map2_exn [s11; s12] [s21; s22] ~f:pat_match_sort
        in
        let omaps2, smaps2, emaps2 =
          List.unzip3 @@ List.map2_exn [o11; o12] [o21; o22] ~f:pat_match_opsig
        in
        let omaps3, smaps3, emaps3 =
          List.unzip3 @@ List.map2_exn [e11; e12] [e21; e22] ~f:pat_match_cont
        in
        Map.force_merge_list @@ omaps1 @ omaps2 @ omaps3,
        Map.force_merge_list @@ smaps1 @ smaps2 @ smaps3,
        Map.force_merge_list @@ emaps1 @ emaps2 @ emaps3
      | _ -> failwith "pat_match_cont"
  and pat_match_opsig o1 o2 =
    if Stdlib.(o1 = o2) then Map.Poly.empty, Map.Poly.empty, Map.Poly.empty
    else
      match o1, o2 with
      | Sort.OpSig (map1, r1), Sort.OpSig (map2, r2) ->
        let lefts, boths, rights = ALMap.split_lbr map1 map2 in
        if List.is_empty lefts && List.is_empty rights then (*ToDo*)
          let omap =
            match r1, r2 with
            | None, None -> Map.Poly.empty
            | Some r1, Some r2 ->
              if Stdlib.(r1 = r2)(*ToDo*) then Map.Poly.empty
              else Map.Poly.singleton r1 (Sort.mk_empty_open_opsig_from_rvar r2)(*ToDo*)
            (*failwith @@ sprintf "[pat_match_opsig @ 1] %s and %s"
              (Ident.name_of_rvar r1) (Ident.name_of_rvar r2)*)
            | Some r, None ->
              Map.Poly.singleton r Sort.empty_closed_opsig(*ToDo*)
            (*failwith @@ sprintf "[pat_match_opsig @ 2] %s" (Ident.name_of_rvar r)*)
            | None, Some r ->
              failwith @@ sprintf "[pat_match_opsig @ 3] %s" (Ident.name_of_rvar r)
          in
          let omaps, smaps, emaps =
            List.unzip3 @@
            List.map boths ~f:(fun (_op, (sort1, sort2)) -> pat_match_sort sort1 sort2)
          in
          Map.force_merge_list @@ omap :: omaps,
          Map.force_merge_list smaps,
          Map.force_merge_list emaps
        else failwith "[pat_match_opsig @ 4]"
      | _ -> failwith "[pat_match_opsig @ 5]"

  let rec fold t ~f =
    match t with
    | Var (ident, sort, _) -> f#ftvar ident sort
    | FunApp (FVar (ident, sorts), args, _) -> f#fvar ident sorts (List.map args ~f:(fold ~f))
    | FunApp (T_int.Int i, [], _) -> f#fint i
    | FunApp (T_real.Real r, [], _) -> f#freal r
    | FunApp (T_int.Add, [t1; t2], _) -> f#fiadd (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_int.Sub, [t1; t2], _) -> f#fisub (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_int.Mult, [t1; t2], _) -> f#fimult (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_int.Div, [t1; t2], _) -> f#fidiv (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_int.Power, [t1; t2], _) -> f#fipower (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_int.Neg, [t1], _) -> f#fineg (fold t1 ~f)
    | FunApp (T_int.Mod, [t1; t2], _) -> f#fimod (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_real.RAdd, [t1; t2], _) -> f#fradd (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_real.RSub, [t1; t2], _) -> f#frsub (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_real.RMult, [t1; t2], _) -> f#frmult (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_real.RDiv, [t1; t2], _) -> f#frdiv (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_real.RPower, [t1; t2], _) -> f#frpower (fold t1 ~f) (fold t2 ~f)
    | FunApp (T_real.RNeg, [t1], _) -> f#frneg (fold t1 ~f)
    | FunApp (T_bool.Formula phi, [], _) -> f#fformula phi
    | FunApp (T_bool.IfThenElse, [t1; t2; t3], _) -> f#fite (fold t1 ~f) (fold t2 ~f) (fold t3 ~f)
    | FunApp (T_array.AStore _, [t1; t2; t3], _) -> f#fastore (fold t1 ~f) (fold t2 ~f) (fold t3 ~f)
    | FunApp (T_array.ASelect _, [t1; t2], _) -> f#faselect (fold t1 ~f) (fold t2 ~f)
    | _ -> failwith @@ "unsupported fold term case: " ^ str_of t

  let rec map_term ~f = function
    | FunApp (T_bool.Formula phi, [], info) ->
      f @@ FunApp (T_bool.Formula (Formula.map_term phi ~f), [], info)
    | FunApp (fsym, args, info) ->
      f @@ FunApp (fsym, List.map args ~f:(map_term ~f), info)
    | LetTerm (var, sort, def, body, info) ->
      f @@ LetTerm (var, sort, map_term ~f def, map_term ~f body, info)
    | t -> f t

  let iter_term ~f t = let _ = map_term t ~f:(fun t -> f t; t) in ()
end

and Predicate : Type.PredicateType
  with type formula := Formula.t
   and type term := Term.t
= struct
  type fixpoint = Mu | Nu

  type t =
    | Var of pred_bind
    | Psym of pred_sym
    | Fixpoint of fixpoint * Ident.pvar * sort_env_list * Formula.t

  (** Construction *)
  let mk_var pvar sort = Var (pvar, sort)
  let mk_psym psym = Psym psym
  let mk_fix fix pvar args body = Fixpoint (fix, pvar, args, body)

  (** Observation *)
  let is_var = function Var _ -> true | _ -> false
  let is_psym = function Psym _ -> true | _ -> false
  let is_fix = function Fixpoint _ -> true | _ -> false

  let tvs_of = function
    | Var _ -> Set.Poly.empty
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, Ident.Pvar name, bounds, body) ->
      Set.Poly.diff
        (Formula.tvs_of body)
        (Set.Poly.add (Set.Poly.of_list @@ List.map ~f:fst bounds) (Ident.Tvar name))
  let pvs_of = function
    | Var (pvar, _) -> Set.Poly.singleton pvar
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, pvar, bounds, body) ->
      Set.Poly.diff
        (Formula.pvs_of body)
        (Set.Poly.add (Set.Poly.map ~f:(fun (Ident.Tvar name) -> Ident.Pvar name) @@ Set.Poly.of_list @@ List.map ~f:fst bounds) pvar)
  let fvs_of atm =
    Set.Poly.union
      (tvs_of atm)
      (Set.Poly.map ~f:(fun (Ident.Pvar name) -> Ident.Tvar(*ToDo*) name) @@ pvs_of atm)
  let svs_of = function
    | Var (_, sorts) -> Set.Poly.of_list @@ List.filter_map sorts ~f:(function Sort.SVar svar -> Some svar | _ -> None)
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, _, bounds, body) ->
      Set.Poly.union
        (Formula.svs_of body)
        (Set.Poly.of_list @@ List.filter_map ~f:(function Sort.SVar svar -> Some svar | _ -> None) @@ List.map ~f:snd bounds)
  let term_sort_env_of = function
    | Var _ | Psym _ -> Set.Poly.empty
    | Fixpoint (_, _, bounds, body) ->
      Set.Poly.diff (Formula.term_sort_env_of body) (Set.Poly.of_list bounds)
  let pred_sort_env_of ?(bpvs = Set.Poly.empty) = function
    | Var (pvar, sorts) ->
      if Set.Poly.mem bpvs pvar then Set.Poly.empty else Set.Poly.singleton (pvar, sorts)
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, pvar, _, phi) ->
      let bpvs = Set.Poly.add bpvs pvar in
      Formula.pred_sort_env_of ~bpvs phi
  let sort_env_of ?(bpvs = Set.Poly.empty) pred =
    Set.Poly.union
      (term_sort_env_of pred)
      (Set.Poly.map ~f:(fun (Ident.Pvar name, sorts) -> Ident.Tvar(*ToDo*) name, Sort.mk_fun (sorts @ [T_bool.SBool])) @@ pred_sort_env_of ~bpvs pred)
  let terms_of = function
    | Var _ -> Set.Poly.empty
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, _, _, phi) -> Formula.terms_of phi
  let fvar_apps_of = function
    | Var (_, _) -> Set.Poly.empty
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, _, _, phi) -> Formula.fvar_apps_of phi

  let nesting_level = function
    | Fixpoint (_, _, _, phi) ->
      1 + (Formula.nesting_level phi)
    | _ -> 0
  let number_of_quantifiers = function
    | Fixpoint (_, _, _, phi) -> Formula.number_of_quantifiers phi
    | _ -> 0

  (** Destruction *)
  let let_var = function Var (pvar, sort) -> (pvar, sort) | _ -> assert false
  let let_psym = function Psym psym -> psym | _ -> assert false
  let let_fix = function Fixpoint (fix, pvar, args, body) -> (fix, pvar, args, body) | _ -> assert false

  (** Transformation *)
  let flip_fixpoint = function Mu -> Nu | Nu -> Mu

  let negate ?(negate_formula = Formula.mk_neg ~info:Dummy) = function
    | Var _ -> failwith "Predicate.negate"
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      Fixpoint (flip_fixpoint fixpoint, pvar, bounds, negate_formula body)
    | Psym T_bool.Eq -> Psym T_bool.Neq
    | Psym T_bool.Neq -> Psym T_bool.Eq
    | Psym T_int.Leq -> Psym T_int.Gt | Psym T_real.RLeq -> Psym T_real.RGt
    | Psym (T_num.NLeq sort) -> Psym (T_num.NGt sort)
    | Psym T_int.Geq -> Psym T_int.Lt | Psym T_real.RGeq -> Psym T_real.RLt
    | Psym (T_num.NGeq sort) -> Psym (T_num.NLt sort)
    | Psym T_int.Lt -> Psym T_int.Geq | Psym T_real.RLt -> Psym T_real.RGeq
    | Psym (T_num.NLt sort) -> Psym (T_num.NGeq sort)
    | Psym T_int.Gt -> Psym T_int.Leq | Psym T_real.RGt -> Psym T_real.RLeq
    | Psym (T_num.NGt sort) -> Psym (T_num.NLeq sort)
    | Psym T_int.PDiv -> Psym T_int.NPDiv | Psym T_int.NPDiv -> Psym T_int.PDiv
    | Psym T_real_int.IsInt -> failwith "not supported"
    | Psym (T_tuple.IsTuple sorts) -> Psym (T_tuple.NotIsTuple sorts)
    | Psym (T_tuple.NotIsTuple sorts) -> Psym (T_tuple.IsTuple sorts)
    | Psym (T_dt.IsCons (name, dt)) -> Psym (T_dt.NotIsCons (name, dt))
    | Psym (T_dt.NotIsCons (name, dt)) -> Psym (T_dt.IsCons (name, dt))
    | Psym (T_sequence.IsPrefix fin) -> Psym (T_sequence.NotIsPrefix fin)
    | Psym (T_sequence.NotIsPrefix fin) -> Psym (T_sequence.IsPrefix fin)
    | Psym (T_sequence.InRegExp (fin, regexp)) -> Psym (T_sequence.NotInRegExp (fin, regexp))
    | Psym (T_sequence.NotInRegExp (fin, regexp)) -> Psym (T_sequence.InRegExp (fin, regexp))
    | Psym _ -> failwith "not supported"

  let complete_psort map = function
    | Var (pvar, _) ->
      (match Map.Poly.find map pvar with
       | Some sorts -> Var (pvar, sorts)
       | None -> failwith @@ "not found " ^ (Ident.name_of_pvar pvar))
    | pred -> pred

  let extend_pred_params ident extended_params = function
    | Fixpoint (fp, pvar, params, body) ->
      let body = Formula.extend_pred_params ident extended_params body in
      Fixpoint (fp, pvar, params, body)
    | x -> x

  (** Substitution *)
  let rename map = function
    | Var (Ident.Pvar var, sort) ->
      (match Map.Poly.find map (Ident.Tvar var(*ToDo*)) with
       | None -> Var (Ident.Pvar var, sort)
       | Some tvar -> Var (Ident.tvar_to_pvar tvar, sort))
    | Psym sym -> Psym sym
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      let map = Map.remove_keys map (List.map ~f:fst bounds) in
      Fixpoint (fixpoint, pvar, bounds, Formula.rename map body)
  let rename_pvars map = function
    | Var (pvar, sorts) ->
      (match Map.Poly.find map pvar with
       | None -> Var (pvar, sorts)
       | Some pvar' -> Var (pvar', sorts))
    | Psym sym -> Psym sym
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      let map' = Map.Poly.remove map pvar in
      Fixpoint (fixpoint, pvar, bounds, Formula.rename_pvars map' body)
  let rename_sorted_pvars map = function
    | Var (Ident.Pvar name, sorts) ->
      (match Map.Poly.find map (name, sorts) with
       | None -> Var (Ident.Pvar name, sorts)
       | Some pvar' -> Var (pvar', sorts))
    | Psym sym -> Psym sym
    | Fixpoint (fixpoint, Ident.Pvar name, bounds, body) ->
      let map' = Map.Poly.remove map (name, List.map bounds ~f:snd) in
      Fixpoint (fixpoint, Ident.Pvar name, bounds, Formula.rename_sorted_pvars map' body)
  let subst_neg pvar = function
    | Var (pvar', sort) ->
      if Stdlib.(pvar = pvar') then assert false (* it must be handled with Formula.subst_neg *)
      else Var (pvar', sort)
    | Psym psym -> Psym psym
    | Fixpoint (fixpoint, pvar', bounds, body) ->
      if Stdlib.(pvar = pvar') then assert false
      else Fixpoint (fixpoint, pvar', bounds, Formula.subst_neg pvar body)
  let subst_sorts_psym map = function
    | (T_num.NGt svar | T_num.NLt svar | T_num.NGeq svar | T_num.NLeq svar) as psym ->
      T_num.psym_of_num_psym psym @@ Term.subst_sorts_sort map @@ Sort.SVar svar
    | T_tuple.IsTuple sorts ->
      T_tuple.IsTuple (List.map ~f:(Term.subst_sorts_sort map) sorts)
    | T_tuple.NotIsTuple sorts ->
      T_tuple.NotIsTuple (List.map ~f:(Term.subst_sorts_sort map) sorts)
    | T_dt.IsCons (name, dt) ->
      T_dt.IsCons (name, Datatype.subst_sorts map dt)
    | T_dt.NotIsCons (name, dt) ->
      T_dt.NotIsCons (name, Datatype.subst_sorts map dt)
    | psym -> psym(* ToDo *)
  let subst_conts_psym map = function
    | (T_num.NGt svar | T_num.NLt svar | T_num.NGeq svar | T_num.NLeq svar) as psym ->
      T_num.psym_of_num_psym psym @@ Term.subst_conts_sort map @@ Sort.SVar svar
    | T_tuple.IsTuple sorts ->
      T_tuple.IsTuple (List.map ~f:(Term.subst_conts_sort map) sorts)
    | T_tuple.NotIsTuple sorts ->
      T_tuple.NotIsTuple (List.map ~f:(Term.subst_conts_sort map) sorts)
    | T_dt.IsCons (name, dt) ->
      T_dt.IsCons (name, Datatype.subst_conts map dt)
    | T_dt.NotIsCons (name, dt) ->
      T_dt.NotIsCons (name, Datatype.subst_conts map dt)
    | psym -> psym(* ToDo *)
  let subst_opsigs_psym map = function
    | (T_num.NGt svar | T_num.NLt svar | T_num.NGeq svar | T_num.NLeq svar) as psym ->
      T_num.psym_of_num_psym psym @@ Term.subst_opsigs_sort map @@ Sort.SVar svar
    | T_tuple.IsTuple sorts ->
      T_tuple.IsTuple (List.map ~f:(Term.subst_opsigs_sort map) sorts)
    | T_tuple.NotIsTuple sorts ->
      T_tuple.NotIsTuple (List.map ~f:(Term.subst_opsigs_sort map) sorts)
    | T_dt.IsCons (name, dt) ->
      T_dt.IsCons (name, Datatype.subst_opsigs map dt)
    | T_dt.NotIsCons (name, dt) ->
      T_dt.NotIsCons (name, Datatype.subst_opsigs map dt)
    | psym -> psym(* ToDo *)
  let subst_sorts map = function
    | Var (pvar, sorts) ->
      Var (pvar, List.map ~f:(Term.subst_sorts_sort map) sorts)
    | Psym psym -> Psym (subst_sorts_psym map psym)
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      Fixpoint (fixpoint, pvar, Formula.subst_sorts_bounds map bounds, Formula.subst_sorts map body)
  let subst_conts map = function
    | Var (pvar, sorts) ->
      Var (pvar, List.map ~f:(Term.subst_conts_sort map) sorts)
    | Psym psym -> Psym (subst_conts_psym map psym)
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      Fixpoint (fixpoint, pvar, Formula.subst_conts_bounds map bounds, Formula.subst_conts map body)
  let subst_opsigs map = function
    | Var (pvar, sorts) ->
      Var (pvar, List.map ~f:(Term.subst_opsigs_sort map) sorts)
    | Psym psym -> Psym (subst_opsigs_psym map psym)
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      Fixpoint (fixpoint, pvar, Formula.subst_opsigs_bounds map bounds, Formula.subst_opsigs map body)

  let aconv_tvar = function
    | Var (pvar, sorts) -> Var (pvar, sorts)
    | Psym sym -> Psym sym
    | Fixpoint (fp, pvar, params, body) ->
      let params', map = refresh_sort_env_list params in
      Fixpoint (fp, pvar, params', Formula.aconv_tvar @@ Formula.rename map body)
  let aconv_pvar = function
    | Var (pvar, sorts) -> Var (pvar, sorts)
    | Psym sym -> Psym sym
    | Fixpoint (fp, pvar, params, body) ->
      let pvar' = Ident.mk_fresh_pvar () in
      let body = Formula.rename_pvars (Map.Poly.singleton pvar pvar') body in
      let body = Formula.aconv_pvar body in
      Fixpoint (fp, pvar', params, body)

  (** Printing *)
  let str_of_predsym = function
    | T_bool.Eq -> "="
    | T_bool.Neq -> "!="
    | T_int.Leq | T_real.RLeq -> "<="
    | T_int.Geq | T_real.RGeq -> ">="
    | T_int.Lt | T_real.RLt -> "<"
    | T_int.Gt | T_real.RGt -> ">"
    | T_int.PDiv -> "|" | T_int.NPDiv -> "!|"
    | T_num.NLeq svar ->
      sprintf "<=_%s" (Ident.name_of_svar svar)
    (* "'<=" *)
    | T_num.NGeq svar ->
      sprintf ">=_%s" (Ident.name_of_svar svar)
    (* "'>=" *)
    | T_num.NLt svar ->
      sprintf "<_%s" (Ident.name_of_svar svar)
    (* "'<" *)
    | T_num.NGt svar ->
      sprintf ">_%s" (Ident.name_of_svar svar)
    (* "'>" *)
    | T_tuple.IsTuple sorts ->
      sprintf "is_tuple(%s)" (String.concat_map_list ~sep:" * " sorts ~f:Term.str_of_sort)
    | T_tuple.NotIsTuple sorts ->
      sprintf "is_not_tuple(%s)" (String.concat_map_list ~sep:" * " sorts ~f:Term.str_of_sort)
    | T_dt.IsCons (name, _) -> sprintf "is_%s" name
    | T_dt.NotIsCons (name, _) -> sprintf "is_not_%s" name
    | T_sequence.IsPrefix _fin -> "is_prefix" | T_sequence.NotIsPrefix _fin -> "not is_prefix"
    | T_sequence.InRegExp (_fin, regexp) ->
      sprintf "in [%s]" @@ Grammar.RegWordExp.str_of Fn.id regexp
    | T_sequence.NotInRegExp (_fin, regexp) ->
      sprintf "not in [%s]" @@ Grammar.RegWordExp.str_of Fn.id regexp
    | _ -> failwith "unknown pred symbol"
  let str_of_fixpoint = function
    | Mu -> "mu"
    | Nu -> "nu"
  let str_of pred =
    match pred with
    | Var (Ident.Pvar ident, _sorts) -> ident
    (*Printf.sprintf "(%s : [%s])" ident
      (String.concat_map_list ~sep:";" ~f:Term.str_of_sort sorts)*)
    | Psym sym -> str_of_predsym sym
    | Fixpoint (fp, Ident.Pvar pident, params, phi) ->
      Printf.sprintf "(%s%s(%s). %s)"
        (str_of_fixpoint fp)
        pident
        (str_of_sort_env_list Term.str_of_sort params)
        (Formula.str_of ~priority:0 phi)
end

and Atom : Type.AtomType
  with type predicate := Predicate.t
   and type term := Term.t
   and type formula := Formula.t
   and type termSubst := TermSubst.t
   and type predSubst := PredSubst.t
= struct
  type t =
    | True of info
    | False of info
    | App of Predicate.t * Term.t list * info

  (** Construction *)
  let mk_true ?(info=Dummy) () = True info
  let mk_false ?(info=Dummy) () = False info
  let mk_app ?(info=Dummy) pred args = App (pred, args, info)

  let mk_psym_app ?(info=Dummy) psym args = mk_app ~info (Predicate.mk_psym psym) args
  let mk_pvar_app ?(info=Dummy) pvar sorts args = mk_app ~info (Predicate.mk_var pvar sorts) args
  let pvar_app_of_senv (pvar, senv) =
    mk_pvar_app pvar (List.map ~f:snd senv) (Term.of_sort_env senv) 


  let of_bool_var b = T_bool.mk_eq (Term.mk_var b T_bool.SBool) (T_bool.mk_true ())
  let of_neg_bool_var b = T_bool.mk_eq (Term.mk_var b T_bool.SBool) (T_bool.mk_false ())
  let of_bool_term = function
    | Term.Var (_, T_bool.SBool, _) as t ->
      T_bool.mk_eq t (T_bool.mk_true ())
    | t ->(*ToDo: check that [t] is a boolean term*) T_bool.mk_eq t (T_bool.mk_true ())
  let of_neg_bool_term = function
    | Term.Var (_, T_bool.SBool, _) as t ->
      T_bool.mk_eq t (T_bool.mk_false ())
    | t ->(*ToDo: check that [t] is a boolean term*) T_bool.mk_eq t (T_bool.mk_false ())

  (** Observation *)
  let is_true = function True _ -> true | _ -> false
  let is_false = function False _ -> true | _ -> false
  let is_app = function App (_, _, _) -> true | _ -> false
  let is_psym_app = function App (Predicate.Psym _, _, _) -> true | _ -> false
  let is_pvar_app = function App (Predicate.Var _, _, _) -> true | _ -> false
  let is_pvar_app_of pvar = function
    | App (Predicate.Var (pvar', _), _, _) -> Stdlib.(pvar = pvar')
    | _ -> false

  let tvs_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
      Set.Poly.union_list @@ Predicate.tvs_of pred :: List.map args ~f:Term.tvs_of
  let pvs_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
      Set.Poly.union_list @@ Predicate.pvs_of pred :: List.map args ~f:Term.pvs_of
  let fvs_of atm =
    Set.Poly.union (tvs_of atm) @@
    Set.Poly.map ~f:(fun (Ident.Pvar name) -> Ident.Tvar(*ToDo*) name) @@ pvs_of atm
  let svs_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
      Set.Poly.union_list @@ Predicate.svs_of pred :: List.map args ~f:Term.svs_of
  let funsyms_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (_, terms, _) ->
      Set.Poly.union_list @@ List.map ~f:Term.funsyms_of terms
  let term_sort_env_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
      Set.Poly.union_list @@
      Predicate.term_sort_env_of pred :: List.map args ~f:Term.term_sort_env_of
  let pred_sort_env_of ?(bpvs = Set.Poly.empty) = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
      Set.Poly.union_list @@
      Predicate.pred_sort_env_of ~bpvs pred :: List.map args ~f:(Term.pred_sort_env_of ~bpvs)
  let sort_env_of ?(bpvs = Set.Poly.empty) atm =
    Set.Poly.union (term_sort_env_of atm) @@
    Set.Poly.map ~f:(fun (Ident.Pvar name, sorts) -> Ident.Tvar(*ToDo*) name, Sort.mk_fun (sorts @ [T_bool.SBool])) @@
    pred_sort_env_of ~bpvs atm
  let pathexps_of atom =
    match atom with
    | True _ | False _ -> Set.Poly.empty
    | App (Predicate.Fixpoint (_, _, bounds, body), args, _) ->
      Set.Poly.diff (Formula.pathexps_of body) (Set.Poly.of_list @@ List.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))
      |> Set.Poly.union @@ Set.Poly.union_list @@ List.map args ~f:Term.pathexps_of
    | App (_, args, _) ->
      Set.Poly.union_list @@ List.map args ~f:Term.pathexps_of
  let filtered_terms_of atom ~f =
    match atom with
    | True _ | False _ -> Set.Poly.empty
    | App (Predicate.Fixpoint (_, _, _, body), args, _) ->
      Formula.filtered_terms_of body ~f
      |> Set.Poly.union @@ List.fold_left args ~init:Set.Poly.empty ~f:(fun ret t -> Set.Poly.union ret (Term.filtered_terms_of t ~f))
    | App (_, args, _) ->
      List.fold_left args ~init:Set.Poly.empty ~f:(fun ret t -> Set.Poly.union ret (Term.filtered_terms_of t ~f))
  let terms_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, terms, _) ->
      Set.Poly.union (Predicate.terms_of pred) (Set.Poly.of_list terms)
  let fvar_apps_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, terms, _) ->
      Set.Poly.union_list (Predicate.fvar_apps_of pred :: List.map ~f:Term.fvar_apps_of terms)

  let occur pv atom = Set.Poly.mem (pvs_of atom) pv

  let nesting_level = function
    | True _ | False _ -> 0
    | App (pred, _, _) -> Predicate.nesting_level pred
  let number_of_quantifiers = function
    | True _ | False _ -> 0
    | App (pred, _, _) -> Predicate.number_of_quantifiers pred
  let number_of_pvar_apps is_pos = function
    | True _ | False _ -> 0
    | App (Predicate.Var _, [], _) -> 0
    | App (Predicate.Var _, _, _) -> if is_pos then 1 else 0
    | App (Predicate.Psym _, _, _) -> 0
    | App (Predicate.Fixpoint _, _, _) -> assert false (* This function does not support fixpoint fomulas appropriately *)
  let count_pvar_apps = function
    | True _ | False _ -> []
    | App (Predicate.Var (pvar, _), _, _) -> [pvar, (1, 0)]
    | App (Predicate.Psym _, _, _) -> []
    | App (Predicate.Fixpoint _, _, _) -> assert false

  let ast_size = function
    | True _ | False _ -> 1
    | App (Predicate.Var _, terms, _) | App (Predicate.Psym _, terms, _) ->
      (List.fold ~f:(fun acc term -> acc + Term.ast_size term) ~init:1 terms)
    | App (Predicate.Fixpoint (_, _, _, phi), terms, _) ->
      (List.fold ~f:(fun acc term -> acc + Term.ast_size term) ~init:(Formula.ast_size phi) terms)

  let occur_times ?(map=Map.Poly.empty) x = function
    | Atom.True _ | Atom.False _ -> 0
    | Atom.App (_, ts, _) -> List.fold ~init:0 ~f:(fun acc t -> acc + Term.occur_times ~map x t) ts


  (** Destruction *)
  let let_app = function
    | App (pred, args, info) -> pred, args, info
    | _ -> assert false
  let let_psym_app = function
    | App (Predicate.Psym sym, args, info) -> sym, args, info
    | _ -> assert false
  let let_pvar_app = function
    | App (Predicate.Var (pvar, sorts), args, info) -> pvar, sorts, args, info
    | _ -> assert false
  let info_of_true = function
    | True info -> info
    | _ -> assert false
  let info_of_false = function
    | False info -> info
    | _ -> assert false
  let info_of = function
    | True info -> info
    | False info -> info
    | App (_, _, info) -> info
  let pvar_of = function App (Predicate.Var (pvar, _), _, _) -> pvar | _ -> assert false

  (** Substitution *)
  let rename map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.rename map pred, List.map ~f:(Term.rename map) args, info)
  let rename_pvars map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.rename_pvars map pred, List.map args ~f:(Term.rename_pvars map), info)
  let rename_sorted_pvars map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.rename_sorted_pvars map pred, List.map args ~f:(Term.rename_sorted_pvars map), info)
  let alpha_rename_let ?(map=Map.Poly.empty) = function
    | App (pred, [], info) ->
      App (Predicate.rename map pred, [], info)
    | App (pred, ts, info) ->
      App (pred, List.map ts ~f:(Term.alpha_rename_let ~map), info)
    | atom -> atom
  let subst map = function
    | True info -> True info
    | False info -> False info
    | App (Var (pvar, sorts), args, info) ->
      App (Var (pvar, sorts), List.map ~f:(Term.subst map) args, info)
    | App (Psym sym, args, info) ->
      App (Psym sym, List.map ~f:(Term.subst map) args, info)
    | App (Fixpoint (fixpoint, pvar, bounds, body), args, info) ->
      let map' = Map.remove_keys map (List.map ~f:fst bounds) in
      App (Fixpoint (fixpoint, pvar, bounds, Formula.subst map' body),
           List.map ~f:(Term.subst map') args, info)
  let subst_preds map = function
    | True info -> Formula.mk_atom (True info)
    | False info -> Formula.mk_atom (False info)
    | App (Predicate.Var (pvar, sort), args, info) ->
      let args = List.map ~f:(Term.subst_preds map) args in
      (match Map.Poly.find map pvar with
       | Some (params, phi) ->
         let map =
           try (* ToDo : check whether args match sorts *)
             Map.Poly.of_alist_exn @@ List.zip_exn (List.map ~f:fst params) args
           with e ->
             Printf.printf "ident: %s #params: %d #args: %d"
               (Ident.name_of_pvar pvar)
               (List.length params)
               (List.length args);
             raise e
         in
         Formula.subst map phi
       | None -> Formula.mk_atom (App (Predicate.Var (pvar, sort), args, info)))
    | App (Psym sym, args, info) ->
      Formula.mk_atom (App (Psym sym, List.map ~f:(Term.subst_preds map) args, info))
    | App (Predicate.Fixpoint (fp, pvar, params, phi), terms, info) ->
      let terms = List.map ~f:(Term.subst_preds map) terms in
      let map' = Map.Poly.remove map pvar in
      Formula.mk_atom (App (Predicate.Fixpoint (fp, pvar, params, Formula.subst_preds map' phi), terms, info))
  let subst_neg pvar = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) -> App (Predicate.subst_neg pvar pred, args, info)
  let subst_sorts map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.subst_sorts map pred, List.map ~f:(Term.subst_sorts map) args, info)
  let subst_conts map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.subst_conts map pred, List.map ~f:(Term.subst_conts map) args, info)
  let subst_opsigs map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.subst_opsigs map pred, List.map ~f:(Term.subst_opsigs map) args, info)

  let aconv_tvar = function
    | True info -> True info | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.aconv_tvar pred, List.map ~f:Term.aconv_tvar args, info)
  let aconv_pvar = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.aconv_pvar pred, List.map ~f:Term.aconv_pvar args, info)

  (** Transformation *)
  let refresh_tvar (senv, atm) =
    let map = Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar ()) in
    Map.rename_keys_map map senv, rename map atm

  let negate ?(negate_formula = Formula.mk_neg ~info:Dummy) = function
    | True info -> False info
    | False info -> True info
    | App (pred, args, info) -> App (Predicate.negate ~negate_formula pred, args, info)
  let complete_psort map = function
    | True info -> True info
    | False info -> False info
    | App (pred, terms, info) -> App (Predicate.complete_psort map pred, terms, info)
  let elim_neq = function
    | App (Psym T_bool.Neq, [t1; t2], _) ->
      Formula.mk_neg @@ Formula.eq (Term.elim_neq t1) (Term.elim_neq t2)
    | App (pred, terms, info) ->
      Formula.mk_atom @@ App (pred, List.map ~f:Term.elim_neq terms, info)
    | atm -> Formula.mk_atom atm
  let elim_ite = function
    | App (Psym (T_bool.Eq | T_bool.Neq |
                 T_int.Leq | T_int.Geq | T_int.Lt | T_int.Gt |
                 T_real.RLeq | T_real.RGeq | T_real.RLt | T_real.RGt) as pred, [t1; t2], info) ->
      List.cartesian_product (Term.elim_ite t1) (Term.elim_ite t2)
      |> List.map ~f:(fun ((phi1, t1), (phi2, t2)) ->
          Formula.and_of [phi1; phi2; Formula.Atom (App (pred, [t1; t2], info), Dummy)])
      |> Formula.or_of
    | App (pred, [t], info) ->
      Term.elim_ite t
      |> List.map ~f:(fun (phi, t) ->
          Formula.and_of [phi; Formula.mk_atom (App (pred, [t], info))])
      |> Formula.or_of
    | atm -> Formula.mk_atom atm
  let has_let ?(map=Map.Poly.empty) = function
    | App (_, args, _) -> List.exists args ~f:(Term.has_let ~map)
    | _ -> false
  (* assume that the argument is alpha-renamed *)
  let let_env_of ?(map=Map.Poly.empty) = function
    | App (_, args, _) -> List.fold args ~init:map ~f:(fun map -> Term.let_env_of ~map)
    | _ -> map
  (* assume that the argument is alpha-renamed *)
  let let_sort_env_of ?(map=Map.Poly.empty) = function
    | App (_, args, _) -> List.fold args ~init:map ~f:(fun map -> Term.let_sort_env_of ~map)
    | _ -> map

  let instantiate_div0_mod0 = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) -> App (pred, List.map args ~f:Term.instantiate_div0_mod0, info)

  let find_div_mod = function
    | True _ | False _ -> Set.Poly.empty
    | App (_, t, _) -> Term.find_div_mod t
  let replace_div_mod map = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) -> App (pred, List.map args ~f:(Term.replace_div_mod map), info)

  let rm_boolean_term atom =
    match atom with
    | App (Predicate.Psym T_bool.Eq, [t1; t2], _) ->
      if Term.is_bool_sort @@ Term.sort_of t1 then
        let phi1 = Term.rm_boolean_term t1 in
        let phi2 = Term.rm_boolean_term t2 in
        Formula.mk_or (Formula.mk_and phi1 phi2) (Formula.mk_and (Formula.mk_neg phi1) (Formula.mk_neg phi2))
      else Formula.mk_atom atom
    | App (Predicate.Psym T_bool.Neq, [t1; t2], _) ->
      if Term.is_bool_sort @@ Term.sort_of t1 then
        let phi1 = Term.rm_boolean_term t1 in
        let phi2 = Term.rm_boolean_term t2 in
        Formula.mk_or (Formula.mk_and phi1 (Formula.mk_neg phi2)) (Formula.mk_and (Formula.mk_neg phi1) phi2)
      else Formula.mk_atom atom
    | atom -> Formula.mk_atom atom

  let extend_pred_params ident (extended_params: sort_env_list) = function
    | App (Predicate.Var (ident', params), args, info) when Stdlib.(ident = ident') ->
      let extended_sorts: Sort.t list = List.map ~f:snd extended_params in
      let params = params @ extended_sorts in
      let extended_args = Term.of_sort_env extended_params in
      let args = args @ extended_args in
      App (Predicate.Var (ident, params), args, info)
    | App (pred, args, info) ->
      let pred = Predicate.extend_pred_params ident extended_params pred in
      let args = List.map ~f:(fun arg -> Term.extend_pred_params ident extended_params arg) args in
      App (pred, args, info)
    | x -> x

  let insert_let_pvar_app var sort def info atom =
    let x, sorts, ts, _ = Atom.let_pvar_app atom in
    Atom.mk_pvar_app ~info x sorts @@ List.map ts ~f:(Term.insert_let_term var sort def info)

  (** Printing *)
  let str_of ?(priority=0) atom =
    match atom with
    | True _ -> "true"
    | False _ -> "false"
    | App (Predicate.Psym ((T_bool.Eq | T_bool.Neq |
                            T_int.Leq | T_real.RLeq | T_num.NLeq _ |
                            T_int.Geq | T_real.RGeq | T_num.NGeq _ |
                            T_int.Lt | T_real.RLt | T_num.NLt _ |
                            T_int.Gt | T_real.RGt | T_num.NGt _ |
                            T_int.PDiv | T_int.NPDiv) as op), [t1; t2], _) ->
      Priority.add_bracket priority Priority.eq_neq_lt_leq_gt_geq @@
      Printf.sprintf "%s %s %s"
        (Term.str_of ~priority:Priority.eq_neq_lt_leq_gt_geq t1)
        (Predicate.str_of_predsym op)
        (Term.str_of ~priority:Priority.eq_neq_lt_leq_gt_geq t2)
    | App (pred, args, _) ->
      if List.length args = 0 then
        Predicate.str_of pred
      else
        Priority.add_bracket priority Priority.fun_app @@
        Printf.sprintf "(%s %s)"
          (Predicate.str_of pred)
          (String.concat_map_list ~sep:" " args ~f:(Term.str_of ~priority:Priority.fun_app))

  (** Unification *)
  let unify bvs atom1 atom2 =
    match atom1, atom2 with
    | True _ , True _ | False _, False _ -> Some Map.Poly.empty
    | App (pred, terms, _), App (pred', terms', _)
      when Stdlib.(=) pred pred' && List.length terms = List.length terms'->
      List.fold2_exn terms terms' ~init:(Some Map.Poly.empty) ~f:(fun opt t1 t2 ->
          Option.(opt >>= fun map ->
                  match Term.unify bvs (Term.subst map t1) (Term.subst map t2) with
                  | Some theta ->
                    begin
                      try
                        Some (Map.force_merge theta (Map.Poly.map map ~f:(Term.subst theta))
                        (*~catch_dup:(fun (tvar, t1, t2) ->
                          print_endline @@ sprintf "%s : %s != %s"
                            (Ident.name_of_tvar tvar) (Term.str_of t1) (Term.str_of t2))*))
                      with _ -> None
                    end
                  | None -> None))
    | _ -> None

  let pattern_match bvs atom1 atom2 =
    match atom1, atom2 with
    | True _ , True _ | False _, False _ -> Some Map.Poly.empty
    | App (pred, terms, _), App (pred', terms', _)
      when Stdlib.(=) pred pred' && List.length terms = List.length terms'->
      (try
         List.fold2_exn terms terms' ~init:(Some Map.Poly.empty) ~f:(fun opt t1 t2 ->
             Option.(opt >>= fun map ->
                     match Term.pattern_match bvs t1 t2 with
                     | Some theta ->
                       Some (Map.force_merge theta map
                       (*~catch_dup:(fun (tvar, t1, t2) ->
                         print_endline @@ sprintf "%s : %s != %s"
                           (Ident.name_of_tvar tvar) (Term.str_of t1) (Term.str_of t2))*))
                     | None -> None))
       with _ -> (*nonlinear pattern not supported*)None)
    | _ -> None



  let fold ~f = function
    | True _ -> f#ftrue ()
    | False _ -> f#ffalse ()
    | App (Predicate.Psym (T_bool.Eq ), [t1; t2], _) -> f#feq t1 t2
    | App (Predicate.Psym (T_bool.Neq), [t1; t2], _) -> f#fneq t1 t2
    | App (Predicate.Psym (T_int.Leq), [t1; t2], _) -> f#fileq t1 t2
    | App (Predicate.Psym (T_real.RLeq), [t1; t2], _) -> f#frleq t1 t2
    | App (Predicate.Psym (T_int.Geq), [t1; t2], _) -> f#figeq t1 t2
    | App (Predicate.Psym (T_real.RGeq), [t1; t2], _) -> f#frgeq t1 t2
    | App (Predicate.Psym (T_int.Lt), [t1; t2], _) -> f#filt t1 t2
    | App (Predicate.Psym (T_real.RLt), [t1; t2], _) -> f#frlt t1 t2
    | App (Predicate.Psym (T_int.Gt), [t1; t2], _) -> f#figt t1 t2
    | App (Predicate.Psym (T_real.RGt), [t1; t2], _) -> f#frgt t1 t2
    | App (Predicate.Psym (T_int.PDiv), [t1; t2], _) -> f#fipdiv t1 t2
    | App (Predicate.Psym (T_int.NPDiv), [t1; t2], _) -> f#finpdiv t1 t2
    | App (Predicate.Var (ident, sort), args, _) -> f#fpvar ident sort args
    | atom -> failwith @@ "unsupported fold atom case: " ^ str_of atom

  let map_term ~f = function
    | (True _ | False _) as atom -> atom
    | App (pred, ts, info) -> App (pred, List.map ts ~f:(Term.map_term ~f), info)

  let iter_term ~f t = let _ = map_term t ~f:(fun t -> f t; t) in ()

  let fold_map_term ~f ~ft atom = fold ~f @@ map_term ~f:ft atom

  let instantiate atom =
    if is_pvar_app atom then
      map_term atom ~f:(function
          | Term.Var (var, sort, _) as term ->
            if Ident.is_dontcare var then Term.mk_dummy sort
            else begin
              (*print_endline (Term.str_of term);*)
              (* [var] is let-bound variable *)
              term
            end
          | t -> t)
    else atom
end

and Formula : Type.FormulaType
  with type term := Term.t
   and type atom := Atom.t
   and type rand := Rand.t
   and type predicate_fixpoint := Predicate.fixpoint
   and type termSubst := TermSubst.t
   and type predSubst := PredSubst.t
= struct
  type unop = Not
  type binop = And | Or | Imply | Iff | Xor
  type binder = Forall | Exists | Random of Rand.t

  type t =
    | Atom of Atom.t * info
    | UnaryOp of unop * Formula.t * info
    | BinaryOp of binop * Formula.t * Formula.t * info
    | Bind of binder * sort_env_list * Formula.t * info
    | LetRec of (Predicate.fixpoint * Ident.pvar * sort_env_list * Formula.t) list * Formula.t * info
    | LetFormula of Ident.tvar * Sort.t * Term.t * Formula.t * info

  (** Construction *)
  let mk_atom ?(info=Dummy) atom = Atom (atom, info)
  let mk_unop ?(info=Dummy) op phi = UnaryOp (op, phi, info)
  let rec mk_neg ?(info=Dummy) = function LetFormula (var, sort, def, body, info) -> LetFormula (var, sort, def, mk_neg body, info) | phi -> UnaryOp (Not, phi, info)
  let mk_binop ?(info=Dummy) op phi1 phi2 = BinaryOp (op, phi1, phi2, info)
  let mk_and ?(info=Dummy) phi1 phi2 = BinaryOp (And, phi1, phi2, info)
  let mk_or ?(info=Dummy) phi1 phi2 = BinaryOp (Or, phi1, phi2, info)
  let mk_imply ?(info=Dummy) phi1 phi2 = BinaryOp (Imply, phi1, phi2, info)
  let mk_iff ?(info=Dummy) phi1 phi2 = BinaryOp (Iff, phi1, phi2, info)
  let mk_xor ?(info=Dummy) phi1 phi2 = BinaryOp (Xor, phi1, phi2, info)
  let mk_bind ?(info=Dummy) binder bound body = Bind (binder, bound, body, info)

  let mk_forall ?(info=Dummy) bound body = Bind (Forall, bound, body, info)
  let mk_exists ?(info=Dummy) bound body = Bind (Exists, bound, body, info)
  let mk_random ?(info=Dummy) r bound body = Bind (Random r, bound, body, info)
  let mk_bind_if_bounded ?(info=Dummy) binder bound body =
    if List.is_empty bound then body else mk_bind binder bound body ~info
  let mk_forall_if_bounded ?(info=Dummy) = mk_bind_if_bounded Forall ~info
  let mk_exists_if_bounded ?(info=Dummy) = mk_bind_if_bounded Exists ~info
  let rec mk_binds quantifiers f =
    match quantifiers with
    | [] -> f
    | (binder, sortenv)::tl -> mk_bind binder sortenv (mk_binds tl f)
  let rec mk_randoms rands f =
    match rands with
    | [] -> f
    | (var, rand)::tl ->
      mk_random rand [var, Rand.sort_of rand] (mk_randoms tl f)
  let mk_letrec ?(info=Dummy) funcs body = LetRec (funcs, body, info)
  let mk_let_formula ?(info=Dummy) var sort def body = LetFormula (var, sort, def, body, info)
  let mk_false ?(info=Dummy) () = Atom (Atom.mk_false (), info)
  let mk_true ?(info=Dummy) () = Atom (Atom.mk_true (), info)

  let and_of ?(info=Dummy) phis =
    let rec aux acc = function
      | [] -> acc
      | Atom (Atom.True _, _) :: phis -> aux acc phis
      | Atom (Atom.False info', info) :: _ -> Atom (Atom.False info', info)
      | phi :: phis -> aux (mk_and acc phi ~info) phis
    in
    match phis with
    | [] -> Atom (Atom.True info, info)
    | x :: xs -> aux x xs
  let or_of ?(info=Dummy) phis =
    let rec aux acc = function
      | [] -> acc
      | Atom (Atom.True info', info) :: _ -> Atom (Atom.True info', info)
      | Atom (Atom.False _, _) :: phis -> aux acc phis
      | phi :: phis -> aux (mk_or acc phi ~info) phis
    in
    match phis with
    | [] -> Atom (Atom.False info, info)
    | x :: xs -> aux x xs
  let xor_of ?(info=Dummy) phis =
    match phis with
    | Atom (Atom.True info', info) :: Atom (Atom.True _, _) :: []
    | Atom (Atom.False info', info) :: Atom (Atom.False _, _) :: [] ->
      Atom (Atom.False info', info)
    | Atom (Atom.True info', info) :: Atom (Atom.False _, _) :: []
    | Atom (Atom.False info', info) :: Atom (Atom.True _, _) :: [] ->
      Atom (Atom.True info', info)
    | Atom (Atom.True _, _) :: phi :: []
    | phi :: Atom (Atom.True _, _) :: [] -> mk_neg phi ~info
    | Atom (Atom.False _, _) :: phi :: []
    | phi :: Atom (Atom.False _, _) :: [] -> phi
    | phi1 :: phi2 :: [] ->
      mk_or
        (mk_and (mk_neg phi1 ~info) phi2 ~info)
        (mk_and phi1 (mk_neg phi2 ~info) ~info) ~info
    | _ -> assert false
  let rec negate = function
    | Atom (atom, info) as phi ->
      (try Atom (Atom.negate atom, info) with _ -> mk_neg phi)
    | UnaryOp (Not, phi, _) -> phi
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, sort, def, negate body, info)
    | phi -> mk_neg phi

  let of_bool_var b = mk_atom (Atom.of_bool_var b)
  let of_neg_bool_var b = mk_atom (Atom.of_neg_bool_var b)

  let rec of_bool_term = function
    | Term.FunApp (T_bool.Formula phi, _, _) -> phi
    | Term.FunApp (T_bool.IfThenElse, [t1; t2; t3], info) ->
      let p1 = of_bool_term t1 in
      let p2 = of_bool_term t2 in
      let p3 = of_bool_term t3 in
      mk_or (mk_and p1 p2) (mk_and (negate p1) p3) ~info
    | Term.LetTerm (var, sort, def, body, info) ->
      LetFormula (var, sort, def, of_bool_term body, info)
    | t -> mk_atom @@ Atom.of_bool_term t
  let rec of_neg_bool_term = function
    | Term.FunApp (T_bool.Formula phi, _, _) -> negate phi
    | Term.FunApp (T_bool.IfThenElse, [t1; t2; t3], info) ->
      let p1 = of_bool_term t1 in
      let p2 = of_neg_bool_term t2 in
      let p3 = of_neg_bool_term t3 in
      mk_or (mk_and p1 p2) (mk_and (negate p1) p3) ~info
    | Term.LetTerm (var, sort, def, body, info) ->
      LetFormula (var, sort, def, of_neg_bool_term body, info)
    | t -> mk_atom @@ Atom.of_neg_bool_term t

  let geq t1 t2 = mk_atom ((if T_int.is_sint t1 then T_int.mk_geq else T_real.mk_rgeq) t1 t2)
  let gt t1 t2 = mk_atom ((if T_int.is_sint t1 then T_int.mk_gt else T_real.mk_rgt) t1 t2)
  let leq t1 t2 = mk_atom ((if T_int.is_sint t1 then T_int.mk_leq else T_real.mk_rleq) t1 t2)
  let lt t1 t2 = mk_atom ((if T_int.is_sint t1 then T_int.mk_lt else T_real.mk_rlt) t1 t2)
  let eq t1 t2 = mk_atom (T_bool.mk_eq t1 t2)
  let neq t1 t2 = mk_atom (T_bool.mk_neq t1 t2)
  let mk_range v lb ub =
    [ Formula.leq (T_int.mk_int lb) v; Formula.leq v (T_int.mk_int ub) ]
  let mk_range_opt v lb ub =
    match (lb, ub) with
    | None, None -> []
    | None, Some ub -> [ Formula.leq v (T_int.mk_int ub) ]
    | Some lb, None -> [ Formula.leq (T_int.mk_int lb) v ]
    | Some lb, Some ub -> [ Formula.leq (T_int.mk_int lb) v; Formula.leq v (T_int.mk_int ub) ]
  (** Observation *)
  let is_atom = function Atom (_, _) -> true | _ -> false
  let is_true = function Atom (Atom.True _, _) -> true | _ -> false
  let is_false = function Atom (Atom.False _, _) -> true | _ -> false
  let is_eq = function Atom (Atom.App (Predicate.Psym T_bool.Eq, [_t1; _t2], _), _) -> true | _ -> false
  let is_unop = function UnaryOp (_, _, _) -> true | _ -> false
  let is_neg = function UnaryOp (Not, _, _) -> true | _ -> false
  let is_binop = function BinaryOp (_, _, _, _) -> true | _ -> false
  let is_and = function BinaryOp (And, _, _, _) -> true | _ -> false
  let is_or = function BinaryOp (Or, _, _, _) -> true | _ -> false
  let is_imply = function BinaryOp (Imply, _, _, _) -> true | _ -> false
  let is_iff = function BinaryOp (Iff, _, _, _) -> true | _ -> false
  let is_xor = function BinaryOp (Xor, _, _, _) -> true | _ -> false
  let is_bind = function Bind (_, _, _, _) -> true | _ -> false
  let is_forall = function Bind (Forall, _, _, _) -> true | _ -> false
  let is_exists = function Bind (Exists, _, _, _) -> true | _ -> false
  let is_random = function Random _ -> true | _ -> false
  let is_letrec = function LetRec _ -> true | _ -> false
  let is_let_formula = function LetFormula _ -> true | _ -> false

  let rec tvs_of = function
    | Atom (atom, _) -> Atom.tvs_of atom
    | UnaryOp (_, phi, _) -> tvs_of phi
    | BinaryOp (_, phi1, phi2, _) -> Set.Poly.union (tvs_of phi1) (tvs_of phi2)
    | Bind (_, bounds, phi, _) ->
      Set.Poly.diff (tvs_of phi) (Set.Poly.of_list @@ List.map ~f:fst bounds)
    | LetRec (funcs, phi, _) ->
      Set.Poly.diff
        (Set.Poly.union_list @@ tvs_of phi :: List.map funcs ~f:(fun (_, _, bounds, body) ->
             Set.Poly.diff (tvs_of body) (Set.Poly.of_list @@ List.map ~f:fst bounds)))
        (Set.Poly.of_list @@ List.map funcs ~f:(fun (_, Ident.Pvar name, _, _) -> Ident.Tvar name))
    | LetFormula (tvar, sort, def, body, info) ->
      Term.tvs_of (LetTerm (tvar, sort, def, T_bool.of_formula body, info))
  let rec pvs_of = function
    | Atom (atom, _) -> Atom.pvs_of atom
    | UnaryOp (_, phi, _) -> pvs_of phi
    | BinaryOp (_, phi1, phi2, _) -> Set.Poly.union (pvs_of phi1) (pvs_of phi2)
    | Bind (_, _, phi, _) -> pvs_of phi
    | LetRec (funcs, phi, _) ->
      Set.Poly.diff
        (Set.Poly.union_list @@
         pvs_of phi :: List.map funcs ~f:(fun (_, _, bounds, body) ->
             Set.Poly.diff
               (pvs_of body)
               (Set.Poly.map ~f:(fun (Ident.Tvar name) -> Ident.Pvar name) @@
                Set.Poly.of_list @@ List.map ~f:fst bounds)))
        (Set.Poly.of_list @@ List.map funcs ~f:(fun (_, pvar, _, _) -> pvar))
    | LetFormula (tvar, sort, def, body, info) ->
      Term.pvs_of (LetTerm (tvar, sort, def, T_bool.of_formula body, info))
  let fvs_of phi =
    Set.Poly.union
      (tvs_of phi)
      (Set.Poly.map ~f:(fun (Ident.Pvar name) -> Ident.Tvar(*ToDo*) name) @@ pvs_of phi)
  let rec svs_of = function
    | Atom (atom, _) -> Atom.svs_of atom
    | UnaryOp (_uop(* ToDo *), phi, _) -> svs_of phi
    | BinaryOp (_bop(* ToDo *), phi1, phi2, _) -> Set.Poly.union (svs_of phi1) (svs_of phi2)
    | Bind (_, bounds, phi, _) ->
      Set.Poly.union
        (Set.Poly.of_list @@ List.filter_map ~f:(function Sort.SVar svar -> Some svar | _ -> None) @@
         List.map ~f:snd bounds)
        (svs_of phi)
    | LetRec (funcs, phi, _) ->
      Set.Poly.union_list @@ svs_of phi :: List.map funcs ~f:(fun (_, _, bounds, body) ->
          Set.Poly.union
            (Set.Poly.of_list @@ List.filter_map ~f:(function
                 | Sort.SVar svar -> Some svar | _ -> None) @@
             List.map ~f:snd bounds)
            (svs_of body))
    | LetFormula (tvar, sort, def, body, info) ->
      Term.svs_of (LetTerm (tvar, sort, def, T_bool.of_formula body, info))
  let rec funsyms_of = function
    | Atom (atom, _) -> Atom.funsyms_of atom
    | UnaryOp (_, phi, _) -> funsyms_of phi
    | BinaryOp (_, phi1, phi2, _) -> Set.Poly.union (funsyms_of phi1) (funsyms_of phi2)
    | Bind (_, _, phi, _) -> funsyms_of phi
    | LetRec (_, _, _) -> assert false (* not implemented *)
    | LetFormula (var, sort, def, body, info) ->
      Term.funsyms_of (LetTerm (var, sort, def, T_bool.of_formula body, info))
  let rec nesting_level =function
    | UnaryOp (_, phi, _) -> nesting_level phi
    | BinaryOp (_, phi1, phi2, _) ->
      max (nesting_level phi1) (nesting_level phi2)
    | Atom (atom, _) -> Atom.nesting_level atom
    | Bind (_, _, phi, _) -> nesting_level phi
    | LetRec (bounded, body, _) ->
      let levels = List.map ~f:(fun (_, _, _, phi) -> 1 + nesting_level phi) bounded in
      let levels = (nesting_level body) :: levels in
      List.fold ~f:(fun acc level -> if acc < level then level else acc) ~init:0 levels
    | LetFormula _ -> failwith @@ "'LetFormula' is not supported yet" (* TODO *)
  let rec term_sort_env_of = function
    | Atom (atom, _) -> Atom.term_sort_env_of atom
    | UnaryOp (_, phi, _) -> term_sort_env_of phi
    | BinaryOp (_, phi1, phi2, _) -> Set.Poly.union (term_sort_env_of phi1) (term_sort_env_of phi2)
    | Bind (_, bounds, phi, _) -> Set.Poly.diff (term_sort_env_of phi) (Set.Poly.of_list bounds)
    | LetRec (funcs, phi, _) ->
      Set.Poly.union_list @@
      (term_sort_env_of phi :: List.map funcs ~f:(fun (a, b, c, d) -> Predicate.term_sort_env_of (Predicate.Fixpoint (a, b, c, d))))
    | LetFormula (var, sort, def, body, info) ->
      Set.Poly.remove (Term.term_sort_env_of (LetTerm (var, sort, def, T_bool.of_formula body, info))) (var, sort)
  let rec pred_sort_env_of ?(bpvs = Set.Poly.empty) = function
    | Atom (atom, _) -> Atom.pred_sort_env_of ~bpvs atom
    | UnaryOp (_, phi, _) -> pred_sort_env_of ~bpvs phi
    | BinaryOp (_, phi1, phi2, _) ->
      Set.Poly.union (pred_sort_env_of ~bpvs phi1) (pred_sort_env_of ~bpvs phi2)
    | Bind (_, _, phi, _) -> pred_sort_env_of ~bpvs phi
    | LetRec (funcs, phi, _) ->
      let bpvs =
        Set.Poly.union bpvs @@
        Set.Poly.of_list @@ List.map funcs ~f:(fun (_, pvar, _, _) -> pvar)
      in
      Set.Poly.union_list @@
      (pred_sort_env_of ~bpvs phi :: List.map funcs ~f:(fun (a, b, c, d) ->
           Predicate.pred_sort_env_of ~bpvs (Predicate.Fixpoint (a, b, c, d))))
    | LetFormula (var, sort, def, body, info) ->
      Term.pred_sort_env_of ~bpvs (LetTerm (var, sort, def, T_bool.of_formula body, info))
  let sort_env_of ?(bpvs = Set.Poly.empty) phi =
    Set.Poly.union
      (term_sort_env_of phi)
      (Set.Poly.map ~f:(fun (Ident.Pvar name, sorts) -> Ident.Tvar(*ToDo*) name, Sort.mk_fun (sorts @ [T_bool.SBool])) @@ pred_sort_env_of ~bpvs phi)
  let rec pathexps_of phi =
    match phi with
    | Atom (atom, _) -> Atom.pathexps_of atom
    | UnaryOp (_, phi, _) -> pathexps_of phi
    | BinaryOp (_, phi1, phi2, _) -> Set.Poly.union (pathexps_of phi1) (pathexps_of phi2)
    | Bind (_, bounds, phi, _) ->
      Set.Poly.diff (pathexps_of phi) (Set.Poly.of_list @@ List.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))
    | LetRec (funcs, phi, _) ->
      (pathexps_of phi :: List.map funcs ~f:(fun (_, _, bounds, body) ->
           Set.Poly.diff (pathexps_of body) (Set.Poly.of_list @@ List.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))))
      |> Set.Poly.union_list
    | LetFormula (var, sort, def, body, info) ->
      Term.pathexps_of (LetTerm (var, sort, def, T_bool.of_formula body, info))
  let rec filtered_terms_of phi ~f =
    match phi with
    | Atom (atom, _) ->  Atom.filtered_terms_of atom ~f
    | UnaryOp (_, phi, _) -> filtered_terms_of phi ~f
    | BinaryOp (_, phi1, phi2, _) -> Set.Poly.union (filtered_terms_of phi1 ~f) (filtered_terms_of phi2 ~f)
    | Bind (_, bounds, phi, _) ->
      Set.Poly.diff (filtered_terms_of phi ~f) (Set.Poly.of_list @@ List.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))
    | LetRec (funcs, phi, _) ->
      ((filtered_terms_of phi ~f):: List.map funcs ~f:(fun (_, _, bounds, body) ->
           Set.Poly.diff (filtered_terms_of body ~f) (Set.Poly.of_list @@ List.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))))
      |> Set.Poly.union_list
    | LetFormula (var, sort, def, body, info) ->
      Term.filtered_terms_of (LetTerm (var, sort, def, T_bool.of_formula body, info)) ~f

  (* assume that the argument is let-normalized *)
  let rec body_of_let = function
    | LetFormula (_, _, _, body, _) -> body_of_let body
    | phi -> phi
  let rec conjuncts_of = function
    | BinaryOp (And, phi1, phi2, _) ->
      Set.Poly.union (conjuncts_of phi1) (conjuncts_of phi2)
    | phi -> Set.Poly.singleton phi
  let rec disjuncts_of = function
    | BinaryOp (Or, phi1, phi2, _) ->
      Set.Poly.union (disjuncts_of phi1) (disjuncts_of phi2)
    | phi -> Set.Poly.singleton phi

  let rec number_of_quantifiers = function
    | UnaryOp (_, phi, _) -> number_of_quantifiers phi
    | BinaryOp (_, phi1, phi2, _) ->
      (number_of_quantifiers phi1) + (number_of_quantifiers phi2)
    | Atom (atom, _) -> Atom.number_of_quantifiers atom
    | Bind (_, _, phi, _) -> 1 + (number_of_quantifiers phi)
    | LetRec (bounded, body, _) ->
      let nums = List.map ~f:(fun (_, _, _, phi) -> number_of_quantifiers phi) bounded in
      let nums = (number_of_quantifiers body) :: nums in
      List.fold ~f:(fun acc num -> acc + num) ~init:0 nums
    | LetFormula _ -> failwith @@ "'LetFormula' is not supported yet" (* TODO *)

  let rec number_of_pvar_apps is_pos = function
    | Atom (atom, _) -> Atom.number_of_pvar_apps is_pos atom
    | UnaryOp (Not, phi, _) -> number_of_pvar_apps (not is_pos) phi
    | BinaryOp (Imply, phi1, phi2, _) ->
      (number_of_pvar_apps (not is_pos) phi1) + (number_of_pvar_apps is_pos phi2)
    | BinaryOp (Iff, _, _, _) -> assert false
    | BinaryOp (Xor, _, _, _) -> assert false
    | BinaryOp (And, phi1, phi2, _) | BinaryOp (Or, phi1, phi2, _) ->
      (number_of_pvar_apps is_pos phi1) + (number_of_pvar_apps is_pos phi2)
    | Bind (_, _, phi, _) -> number_of_pvar_apps is_pos phi
    | LetRec (_, _, _) -> assert false
    | LetFormula (var, sort, def, body, info) ->
      Term.number_of_pvar_apps is_pos @@
      Term.LetTerm (var, sort, def, T_bool.of_formula body, info)
  (*List.fold (fun acc (_, _, _, phi) -> acc + (number_of_pvar_apps is_pos phi))
    (number_of_pvar_apps is_pos body) bounded*)

  let rec count_pvar_apps = function
    | Atom (atom, _) -> Atom.count_pvar_apps atom
    | UnaryOp (Not, phi, _) -> List.Assoc.map (count_pvar_apps phi) ~f:(fun (pc, nc) -> nc, pc)
    | BinaryOp (Imply, phi1, phi2, _) ->
      let r1 = List.Assoc.map (count_pvar_apps phi1) ~f:(fun (pc, nc) -> nc, pc) in
      let r2 = count_pvar_apps phi2 in
      (r1 @ r2)
      |> List.group ~break:(fun x y -> Stdlib.(fst x <> fst y))
      (* |> Util.List.classify (fun x y -> fst x = fst y) *)
      |> List.map ~f:(function [] -> assert false | (x :: xs) ->
          fst x,
          let pcs, ncs = List.unzip (snd x :: List.map ~f:snd xs) in
          (List.fold pcs ~init:0 ~f:(+), List.fold ncs ~init:0 ~f:(+)))
    | BinaryOp (Iff, _, _, _) -> assert false
    | BinaryOp (Xor, _, _, _) -> assert false
    | BinaryOp (And, phi1, phi2, _) | BinaryOp (Or, phi1, phi2, _) ->
      let r1 = count_pvar_apps phi1 in
      let r2 = count_pvar_apps phi2 in
      (r1 @ r2)
      |> List.group ~break:(fun x y -> Stdlib.(fst x <> fst y))
      (* |> Util.List.classify (fun x y -> fst x = fst y) *)
      |> List.map ~f:(function [] -> assert false | (x :: xs) ->
          fst x,
          let pcs, ncs = List.unzip (snd x :: List.map ~f:snd xs) in
          (List.fold pcs ~init:0 ~f:(+), List.fold ncs ~init:0 ~f:(+)))
    | Bind (_, _, phi, _) -> count_pvar_apps phi
    | LetRec (_, _, _) -> assert false
    | LetFormula _ -> failwith @@ "'LetFormula' is not supported yet" (* TODO *)

  let rec ast_size = function
    | UnaryOp (_, phi, _) -> 1 + ast_size phi
    | BinaryOp (_, phi1, phi2, _) -> 1 + ast_size phi1 + ast_size phi2
    | Atom (atom, _) -> Atom.ast_size atom
    | Bind (_, _, phi, _) -> 1 + ast_size phi
    | LetRec (bounded, phi, _) ->
      List.fold ~init:1 bounded ~f:(fun acc (_, _, _, phi) -> acc + (ast_size phi)) + ast_size phi
    | LetFormula (var, sort, def, body, info) ->
      Term.ast_size (LetTerm (var, sort, def, T_bool.of_formula body, info))

  let rec occur_times ?(map=Map.Poly.empty) x = function
    | Formula.Atom (atom, _) -> Atom.occur_times ~map x atom
    | Formula.BinaryOp (_, phi1, phi2, _) -> occur_times ~map x phi1 + occur_times ~map x phi2
    | Formula.UnaryOp (_, phi1, _) -> occur_times ~map x phi1
    | Formula.Bind (_, _, phi1, _) -> occur_times ~map x phi1
    | Formula.LetRec _ -> failwith "[occur_times_in_formula]unsupported letrec"
    | Formula.LetFormula (var, _, def, body, _) ->
      let map = Map.Poly.add_exn ~key:var ~data:(Term.occur_times ~map x def) map in
      occur_times ~map x body

  let rec terms_of = function
    | Atom (atom, _) -> Atom.terms_of atom
    | UnaryOp (_, phi, _) -> terms_of phi
    | BinaryOp (_, p1, p2, _) -> Set.Poly.union (terms_of p1) (terms_of p2)
    | _ -> failwith "not implemented yet"
  let rec fvar_apps_of = function
    | Atom (atom, _) -> Atom.fvar_apps_of atom
    | UnaryOp (_, phi, _) -> fvar_apps_of phi
    | BinaryOp (_, p1, p2, _) -> Set.Poly.union (fvar_apps_of p1) (fvar_apps_of p2)
    | _ -> failwith "not implemented yet"
  (* assume that [phi] is let-normalized *)
  let rec atoms_of ?(pos=true) = function
    | UnaryOp (Not, phi, _) -> atoms_of ~pos:(not pos) phi
    (*| UnaryOp (_, phi, _) -> aux pos phi*)
    | BinaryOp ((Imply | Iff | Xor), _, _, _) -> assert false
    | BinaryOp (_, phi1, phi2, _) ->
      let pos1, neg1 = atoms_of ~pos phi1 in
      let pos2, neg2 = atoms_of ~pos phi2 in
      Set.Poly.union pos1 pos2, Set.Poly.union neg1 neg2
    | Atom (atom, _) -> (* ToDo *)
      if pos then Set.Poly.singleton atom, Set.Poly.empty
      else Set.Poly.empty, Set.Poly.singleton atom
    | Bind (_, _, phi, _) -> atoms_of ~pos phi
    | LetRec (_bounded, _body, _) -> assert false
    (*Set.Poly.union_list @@
      aux pos body :: List.map bounded ~f:(fun (_, _, _, phi) -> aux pos phi)*)
    | LetFormula (_, _, def, body, _) ->
      let pos1, neg1 = Term.atoms_of ~pos def in
      let pos2, neg2 = atoms_of ~pos body in
      Set.Poly.union pos1 pos2, Set.Poly.union neg1 neg2

  (** Construction *)
  let bind ?(info=Dummy) binder bounds body =
    let ftv = tvs_of body in
    let bounds = List.filter ~f:(fun (tvar, _) -> Set.Poly.mem ftv tvar) bounds in
    mk_bind_if_bounded binder bounds body ~info
  let forall ?(info=Dummy) bounds body = bind ~info Forall bounds body
  let exists ?(info=Dummy) bounds body = bind ~info Exists bounds body
  let bind_fvs binder fml =
    let bounds =
      tvs_of fml |> Set.Poly.to_list
      |> List.map ~f:(fun tvar -> tvar, T_int.SInt(* TODO: infer the sorts *)) in
    mk_bind_if_bounded binder bounds fml ~info:Dummy
  let bind_fvs_with_exists fml = bind_fvs Exists fml
  let bind_fvs_with_forall fml = bind_fvs Forall fml

  (** Destruction *)
  let let_atom = function
    | Atom (atom, info) -> atom, info
    | _ -> assert false
  let let_eq = function
    | Atom (Atom.App (Predicate.Psym T_bool.Eq, [t1; t2], _), info) -> t1, t2, info
    | _ -> assert false
  let let_unop = function
    | UnaryOp (op, phi, info) -> op, phi, info
    | _ -> assert false
  let let_neg = function
    | UnaryOp (Not, phi, info) -> phi, info
    | _ -> assert false
  let let_binop = function
    | BinaryOp (op, phi1, phi2, info) -> op, phi1, phi2, info
    | _ -> assert false
  let let_and = function
    | BinaryOp (And, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_or = function
    | BinaryOp (Or, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_imply = function
    | BinaryOp (Imply, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_iff = function
    | BinaryOp (Iff, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_xor = function
    | BinaryOp (Xor, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_bind = function
    | Bind (binder, params, body, info) -> binder, params, body, info
    | _ -> assert false
  let let_forall = function
    | Bind (Forall, params, body, info) -> params, body, info
    | _ -> assert false
  let let_exists = function
    | Bind (Exists, params, body, info) -> params, body, info
    | _ -> assert false
  let let_forall_or_formula = function
    | Bind (Forall, params, body, info) -> params, body, info
    | fml -> [], fml, Dummy
  let let_exists_or_formula = function
    | Bind (Exists, params, body, info) -> params, body, info
    | fml -> [], fml, Dummy
  let let_letrec = function
    | LetRec (funcs, body, info) -> funcs, body, info
    | _ -> assert false

  (** Substitution *)
  let rec rename map = function
    | Atom (atom, info) -> Atom (Atom.rename map atom, info)
    | UnaryOp (Not, phi, info) -> UnaryOp (Not, rename map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, rename map phi1, rename map phi2, info)
    | Bind (binder, bounds, body, info) ->
      let map = Map.remove_keys map (List.map ~f:fst bounds) in
      (match binder with
       | Random rand -> Bind (Random (Rand.rename map rand), bounds, rename map body, info)
       | _ -> Bind (binder, bounds, rename map body, info))
    | LetRec (funcs, body, info) ->
      let funcs =
        List.map ~f:(fun (fix, pvar, arg_sorts, func_body) ->
            let map' = Map.remove_keys map (List.map ~f:fst arg_sorts) in
            (fix, pvar, arg_sorts, rename map' func_body)) funcs in
      LetRec (funcs, rename map body, info)
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.rename map (LetTerm (var, sort, def, T_bool.of_formula body, info))
  let rec rename_pvars map = function
    | Atom (atom, info) -> Atom (Atom.rename_pvars map atom, info)
    | UnaryOp (Not, phi, info) -> UnaryOp (Not, rename_pvars map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, rename_pvars map phi1, rename_pvars map phi2, info)
    | Bind (binder, bounds, body, info) ->
      Bind (binder, bounds, rename_pvars map body, info)
    | LetRec (funcs, body, info) ->
      let funcs =
        List.map funcs ~f:(fun (fix, pvar, arg_sorts, func_body) ->
            let map' = Map.Poly.remove map pvar in
            (fix, pvar, arg_sorts, rename_pvars map' func_body))
      in LetRec (funcs, rename_pvars map body, info)
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.rename_pvars map (LetTerm (var, sort, def, T_bool.of_formula body, info))
  let rec rename_sorted_pvars map = function
    | Atom (atom, info) -> Atom (Atom.rename_sorted_pvars map atom, info)
    | UnaryOp (Not, phi, info) -> UnaryOp (Not, rename_sorted_pvars map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, rename_sorted_pvars map phi1, rename_sorted_pvars map phi2, info)
    | Bind (binder, bounds, body, info) ->
      Bind (binder, bounds, rename_sorted_pvars map body, info)
    | LetRec (funcs, body, info) ->
      let funcs =
        List.map funcs ~f:(fun (fix, Ident.Pvar name, arg_sorts, func_body) ->
            let map' = Map.Poly.remove map (name, List.map ~f:snd arg_sorts) in
            (fix, Ident.Pvar name, arg_sorts, rename_sorted_pvars map' func_body))
      in LetRec (funcs, rename_sorted_pvars map body, info)
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.rename_sorted_pvars map (LetTerm (var, sort, def, T_bool.of_formula body, info))
  let rec alpha_rename_let ?(map=Map.Poly.empty) = function
    | Atom (atom, info) ->
      Atom (Atom.alpha_rename_let ~map atom, info)
    | UnaryOp (op, phi, info) ->
      UnaryOp (op, alpha_rename_let ~map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, alpha_rename_let ~map phi1, alpha_rename_let ~map phi2, info)
    | Bind (binder, senv, body, info) ->
      let bounds = Set.Poly.of_list @@ List.map ~f:fst senv in
      let map' = Map.Poly.filter_keys map ~f:(Fn.non @@ Set.Poly.mem bounds) in
      Bind (binder, senv, alpha_rename_let ~map:map' body, info)
    | LetFormula (var, sort, def, body, info) ->
      let var' = Ident.mk_fresh_tvar () in
      let map' = Map.Poly.set ~key:var ~data:var' map in
      LetFormula (var', sort, Term.alpha_rename_let ~map def, alpha_rename_let ~map:map' body, info)
    | LetRec _ as phi -> phi

  (* assume that [phi] is let-normalized *)
  let rec replace_let_body phi new_body =
    match phi with
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, sort, def, replace_let_body body new_body, info)
    | _ -> new_body
  (* assume that [term] is let-normalized *)
  let rec replace_let_term_body term new_body =
    match term with
    | Term.LetTerm (var, sort, def, body, info) ->
      LetFormula (var, sort, def, replace_let_term_body body new_body, info)
    | Term.FunApp (T_bool.Formula phi, [], _) when Formula.is_let_formula phi ->
      replace_let_body phi new_body
    | _ -> new_body
  (* substitution for term variable *)
  let rec subst map phi =
    let rec aux ~next map phi =
      match phi with
      | Atom (Atom.App (Var (Ident.Pvar var, []), [], _), _)
        when Map.Poly.mem map (Ident.Tvar var(*ToDo*)) ->
        let tvar = Ident.Tvar var in
        begin match Map.Poly.find map tvar(*ToDo*) with
          | Some t ->
            next @@ of_bool_term @@
            if Term.is_var t then t else Term.subst map t
          | None -> next phi
        end
      | Atom (atom, info) -> next @@ Atom (Atom.subst map atom, info)
      | UnaryOp (Not, phi, info) ->
        aux map phi ~next:(fun phi' -> next @@ UnaryOp (Not, phi', info))
      | BinaryOp (op, phi1, phi2, info) ->
        aux map phi1 ~next:(fun phi1' -> aux map phi2 ~next:(fun phi2' ->
            next @@ BinaryOp (op, phi1', phi2', info)))
      | Bind (binder, bounds, body, info) ->
        let map' = Map.remove_keys map (List.map ~f:fst bounds) in
        aux map' body ~next:(fun body' -> next @@ Bind (binder, bounds, body', info))
      | LetRec (funcs, body, info) ->
        let funcs =
          List.map ~f:(fun (fix, pvar, arg_sorts, func_body) ->
              let map' = Map.remove_keys map (List.map ~f:fst arg_sorts) in
              (fix, pvar, arg_sorts, subst map' func_body)) funcs
        in
        aux map body ~next:(fun body' -> next @@ LetRec (funcs, body', info))
      | LetFormula (var, sort, def, body, info) ->
        aux map body ~next:(fun body' -> next @@
                             LetFormula (var, sort, Term.subst map def, body', info))
    in aux map phi ~next:Fn.id
  let rec subst_preds map = function
    | Atom (atom, _) -> Atom.subst_preds map atom
    | UnaryOp (Not, phi, info) ->
      UnaryOp (Not, subst_preds map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, subst_preds map phi1, subst_preds map phi2, info)
    | Bind (binder, params, phi, info) ->
      let phi = subst_preds map phi in
      Bind (binder, params, phi, info)
    | LetRec (bounded, body, info) ->
      (* ToDo: the following code is wrong if ident is bound by let rec *)
      let bounded = List.map bounded ~f:(fun (fp, pvar, params, phi) ->
          (fp, pvar, params, subst_preds map phi)) in
      let body = subst_preds map body in
      LetRec (bounded, body, info)
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, sort, Term.subst_preds map def, subst_preds map body, info)
  let rec subst_neg pvar = function
    | Atom (Atom.App (Predicate.Var (pvar', sort), args, info), info') ->
      let atom = Atom.App (Predicate.Var (pvar', sort), args, info) in
      if Stdlib.(pvar = pvar') then UnaryOp (Not, Atom (atom, info), Dummy)
      else Atom (Atom.subst_neg pvar atom, info')
    | Atom (atom, info) -> Atom (Atom.subst_neg pvar atom, info)
    | UnaryOp (Not, phi, info) ->
      (match subst_neg pvar phi with
       | UnaryOp (Not, phi', _) -> phi'
       | phi' -> UnaryOp (Not, phi', info))
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, subst_neg pvar phi1, subst_neg pvar phi2, info)
    | Bind (binder, bounds, body, info) ->
      Bind (binder, bounds, subst_neg pvar body, info)
    | LetRec (funcs, body, info) ->
      LetRec
        (List.map ~f:(fun (fix, pvar', bounds, body) ->
             fix, pvar', bounds, subst_neg pvar body) funcs,
         subst_neg pvar body, info)
    | LetFormula (var, sort, dec, body, info) ->
      LetFormula (var, sort, dec, subst_neg pvar body, info)
  let rec subst_pvar maps = function
    | Atom (Atom.App (Predicate.Var (pvar', []), [], _), _) as fml ->
      (match Map.Poly.find maps pvar' with Some phi -> phi | None -> fml)
    | Atom ((Atom.True _ | Atom.False _), _) as fml -> fml
    | UnaryOp (op, phi, info) ->
      UnaryOp (op, subst_pvar maps phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, subst_pvar maps phi1, subst_pvar maps phi2, info)
    | Bind (binder, bounds, body, info) ->
      Bind (binder, bounds, subst_pvar maps body, info)
    | _ -> failwith "[subst_pvar] not implemented"

  let rec replace_papps map = function
    | Atom (atom, info) ->
      begin match Map.Poly.find map atom with
        | None -> Formula.mk_atom atom ~info
        | Some atom' -> Formula.mk_atom atom' ~info
      end
    | UnaryOp (op, phi1, info) -> UnaryOp (op, replace_papps map phi1, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, replace_papps map phi1, replace_papps map phi2, info)
    | Bind (binder, bounds, body, info) ->
      Bind (binder, bounds, replace_papps map body, info)
    | LetRec (funcs, body, info) -> LetRec (funcs, replace_papps map body, info)
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.replace_papps map @@
      Term.LetTerm (var, sort, def, T_bool.of_formula body, info)

  let rec aconv_tvar = function
    | Atom (atom, info) -> mk_atom (Atom.aconv_tvar atom) ~info
    | UnaryOp (Not, phi, info) -> mk_neg (aconv_tvar phi) ~info
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, aconv_tvar phi1, aconv_tvar phi2, info)
    | Bind (binder, bounds, phi, info) ->
      let bounds', map = refresh_sort_env_list bounds in
      Bind (binder, bounds', rename map (aconv_tvar phi), info)
    | LetRec (funcs, body, info) ->
      let funcs' =
        List.map funcs ~f:(fun (fp, pvar, params, body) ->
            Predicate.let_fix @@ Predicate.aconv_tvar @@
            Predicate.Fixpoint (fp, pvar, params, body))
      in
      LetRec (funcs', aconv_tvar body, info)
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.aconv_tvar @@
      Term.LetTerm (var, sort, def, T_bool.of_formula body, info)

  let rec aconv_pvar = function
    | Atom (atom, info) -> Atom (Atom.aconv_pvar atom, info)
    | UnaryOp (Not, phi, info) -> UnaryOp (Not, aconv_pvar phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, aconv_pvar phi1, aconv_pvar phi2, info)
    | Bind (binder, bounds, phi, info) ->
      Bind (binder, bounds, aconv_pvar phi (* ToDo: fix bug *), info)
    | LetRec (funcs, phi, info) ->
      let map =
        Map.Poly.of_alist_exn @@ List.map ~f:(fun (_, pvar, _, _) ->
            pvar, Ident.mk_fresh_pvar ()) funcs
      in
      let funcs =
        List.map funcs ~f:(fun (fp, pvar, params, phi) ->
            fp, Map.Poly.find_exn map pvar, params, rename_pvars map phi)
      in
      LetRec (funcs, rename_pvars map phi, info)
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.aconv_pvar @@
      Term.LetTerm (var, sort, def, T_bool.of_formula body, info)

  (** Transformation *)
  let flip_quantifier = function Forall -> Exists | Exists -> Forall | Random r -> Random r

  let reduce_sort_map (senv, phi) =
    let fvs = fvs_of phi in
    Map.Poly.filter_keys senv ~f:(Set.Poly.mem fvs), phi
  let refresh_tvar (senv, phi) =
    let map = Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar ()) in
    Map.rename_keys_map map senv, rename map phi
  (*let refresh_tvar (phi: Formula.t) =
    let map =
      Map.of_set_exn @@
      Set.Poly.map ~f:(fun (t, s) -> (t, Term.mk_fresh_var s)) @@
      term_sort_env_of phi in
    Formula.subst map phi*)

  let rec complete_psort map = function
    | Atom (atom, info) -> Atom (Atom.complete_psort map atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, complete_psort map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, complete_psort map phi1, complete_psort map phi2, info)
    | Bind (binder, bounds, body, info) ->
      Bind (binder, bounds, complete_psort map body, info)
    | LetRec _ -> failwith "LetRec in this position is not supported."
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.complete_psort map @@
      Term.LetTerm (var, sort, def, T_bool.of_formula body, info)

  let rec complete_tsort env = function
    | Atom (atom, info) -> Atom (Atom.subst env atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, complete_tsort env phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, complete_tsort env phi1, complete_tsort env phi2, info)
    | Bind (binder, args, phi, info) ->
      let env' =
        Set.Poly.fold ~init:env (Set.Poly.of_list args) ~f:(fun env (x, sort) ->
            Map.Poly.update env x ~f:(fun _ -> Term.mk_var x sort))
      in
      Bind (binder, args, complete_tsort env' phi, info)
    | LetRec _ -> failwith "LetRec in this position is not supported."
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.complete_tsort env @@
      Term.LetTerm (var, sort, def, T_bool.of_formula body, info)
  let complete_tsort = complete_tsort Map.Poly.empty

  let rec rm_forall = function
    | Atom (atom, info) -> Set.Poly.empty, Atom (atom, info)
    | UnaryOp (op, phi, info) ->
      let senv', phi' = rm_forall phi in
      senv', UnaryOp (op, phi', info)
    | BinaryOp (op, phi1, phi2, info) ->
      let senv1', phi1' = rm_forall phi1 in
      let senv2', phi2' = rm_forall phi2 in
      Set.Poly.union senv1' senv2', BinaryOp (op, phi1', phi2', info)
    | Bind (Forall, senv, phi, _) ->
      let senv', phi' = rm_forall phi in
      Set.Poly.union (Set.Poly.of_list senv) senv', phi'
    | Bind (_, _, _, _) -> failwith "unimplemented"
    | LetRec (_, _, _) -> failwith "unimplemented"
    | LetFormula (var, sort, def, body, info) -> (*assume there is no forall in def*)
      let senv, body' = rm_forall body in
      senv, LetFormula (var, sort, def, body', info)

  (** ToDo: this seems not capture avoiding *)
  let move_quantifiers_to_front fml =
    let rec rename_in_formula used_names replace_env fml =
      if is_atom fml then
        let atom, info = let_atom fml in
        let atom = rename_in_atom replace_env atom in
        mk_atom atom ~info, used_names, replace_env
      else if is_binop fml then
        let binop, left, right, info = let_binop fml in
        let left, used_names, replace_env = rename_in_formula used_names replace_env left in
        let right, used_names, replace_env = rename_in_formula used_names replace_env right in
        mk_binop binop left right ~info, used_names, replace_env
      else if is_unop fml then
        let unop, body, info = let_unop fml in
        let body, used_names, replace_env = rename_in_formula used_names replace_env body in
        mk_unop unop body ~info, used_names, replace_env
      else if is_bind fml then
        let binder, bounds, body, info = let_bind fml in
        let new_bounds = List.map bounds ~f:(fun (tvar, sort) ->
            let var_name = ref (Ident.name_of_tvar tvar ^ "#q") in
            while Map.Poly.mem used_names !var_name do
              var_name := !var_name ^ "'"
            done;
            Ident.Tvar !var_name, sort)
        in
        let new_bound_tvars, _ = List.unzip new_bounds in
        let bound_tvars = List.map ~f:fst bounds in
        let used_names = Map.update_with used_names (Map.Poly.of_alist_exn @@ List.map bound_tvars ~f:(fun tvar -> Ident.name_of_tvar tvar, ())) in
        let replace_env = Map.update_with replace_env (Map.Poly.of_alist_exn @@ List.zip_exn bound_tvars new_bound_tvars) in
        let body, used_names, replace_env = rename_in_formula used_names replace_env body in
        mk_bind binder new_bounds body ~info, used_names, replace_env
      else
        assert false
    and rename_in_atom replace_env atom =
      if Atom.is_true atom || Atom.is_false atom then
        atom
      else if Atom.is_app atom then
        let pred, args, info = Atom.let_app atom in
        let pred = rename_in_predicate pred in
        let args = List.map ~f:(rename_in_term replace_env) args in
        Atom.mk_app pred args ~info
      else
        assert false
    and rename_in_predicate pred =
      if Predicate.is_fix pred then
        let fix, pvar, args, body = Predicate.let_fix pred in
        let body = rename body in
        Predicate.mk_fix fix pvar args body
      else if Predicate.is_psym pred || Predicate.is_var pred then
        pred
      else
        assert false
    and rename_in_term replace_env term =
      if Term.is_var term then
        let (tvar, sort), info = Term.let_var term in
        Term.mk_var (Map.Poly.find_exn replace_env tvar) sort ~info
      else if Term.is_app term then
        let funsym, args, info = Term.let_app term in
        Term.mk_fsym_app funsym (List.map ~f:(rename_in_term replace_env) args) ~info
      else
        assert false
    and rename fml =
      let fv = Set.Poly.to_list @@ tvs_of fml in
      (* let fv_names = (List.map ~f:(fun tvar -> (Ident.name_of_tvar tvar, ())) fv) in *)
      let fml, _, _ =
        rename_in_formula Map.Poly.empty (Map.Poly.of_alist_exn @@ List.zip_exn fv fv) fml
      in
      fml
    in
    let mk_bind binder bounds fml =
      if List.is_empty bounds then fml else mk_bind binder bounds fml
    in
    let rec move_to_front_in_formula fml =
      if is_atom fml then
        let atom, info = let_atom fml in
        mk_atom (move_to_front_in_atom atom) ~info, [], []
      else if is_neg fml then
        let negop, fml, info = let_unop fml in
        let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
        mk_unop negop fml ~info, exists_bounds, forall_bounds
      else if is_imply fml then
        (* TODO *)
        failwith ((*str_of fml ^*) " not supported\n")
      else if is_iff fml then
        (* TODO *)
        failwith ((*str_of fml ^*) " not supported\n")
      else if is_and fml || is_or fml then
        let binop, left_fml, right_fml, info = let_binop fml in
        let left_fml, left_forall_bounds, left_exists_bounds = move_to_front_in_formula left_fml in
        let right_fml, right_forall_bounds, right_exists_bounds = move_to_front_in_formula right_fml in
        mk_binop binop left_fml right_fml ~info,
        left_forall_bounds @ right_forall_bounds,
        left_exists_bounds @ right_exists_bounds
      else if is_bind fml then
        let binder, bounds, fml, _ = let_bind fml in
        let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
        let binder_bounds, another_bounds =
          match binder with
          | Forall -> forall_bounds, exists_bounds
          | Exists -> exists_bounds, forall_bounds
          | Random _ -> assert false
        in
        let fml = mk_bind (flip_quantifier binder) another_bounds fml in
        let another_bounds = [] in
        let binder_bounds = bounds @ binder_bounds in
        let forall_bounds, exists_bounds =
          match binder with
          | Forall -> binder_bounds, another_bounds
          | Exists -> another_bounds, binder_bounds
          | Random _ -> assert false
        in
        fml, forall_bounds, exists_bounds
      else
        assert false
    and move_to_front_in_atom atom =
      if Atom.is_app atom then
        let pred, args, info = Atom.let_app atom in
        Atom.mk_app (move_to_front_in_predicate pred) args ~info
      else if Atom.is_true atom || Atom.is_false atom then
        atom
      else
        assert false
    and move_to_front_in_predicate pred =
      if Predicate.is_fix pred then
        let fix, pvar, arg_sorts, body = Predicate.let_fix pred in
        Predicate.mk_fix fix pvar arg_sorts (move_to_front body)
      else if Predicate.is_psym pred || Predicate.is_var pred then
        pred
      else
        assert false
    and move_to_front fml =
      let fml, forall_bounds, exists_bounds = move_to_front_in_formula fml in
      mk_bind Forall forall_bounds
      @@ mk_bind Exists exists_bounds fml
    in
    move_to_front @@ rename fml

  let rec elim_neq = function
    | Atom (atom, _) -> Atom.elim_neq atom
    | UnaryOp (op, phi, info) -> UnaryOp (op, elim_neq phi, info)
    | BinaryOp (op, phi1, phi2, info) -> BinaryOp (op, elim_neq phi1, elim_neq phi2, info)
    | Bind (bin, senv, phi, info) -> Bind (bin, senv, elim_neq phi, info)
    | LetRec (_, _, _) -> failwith "'LetRec' is not supported"
    | LetFormula _ -> failwith "'LetFormula' is not supported"

  let rec elim_ite = function
    | Atom (atom, _) -> Atom.elim_ite atom
    | UnaryOp (op, phi, info) -> UnaryOp (op, elim_ite phi, info)
    | BinaryOp (op, phi1, phi2, info) -> BinaryOp (op, elim_ite phi1, elim_ite phi2, info)
    | Bind (bin, senv, phi, info) -> Bind (bin, senv, elim_ite phi, info)
    | LetRec (_, _, _) -> failwith "'LetRec' is not supported"
    | LetFormula _ -> failwith "'LetFormula' is not supported"

  let rec elim_pvars unknowns = function
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, sort, Term.elim_pvars unknowns def, elim_pvars unknowns body, info)
    | UnaryOp (op, phi1, info) ->
      UnaryOp (op, elim_pvars unknowns phi1, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, elim_pvars unknowns phi1, elim_pvars unknowns phi2, info)
    | Bind (bin, senv, phi1, info) ->
      Bind (bin, senv, elim_pvars unknowns phi1, info)
    | Atom (Atom.App (Predicate.Var (Ident.Pvar var, []), [], _), _) as phi ->
      if Set.Poly.mem unknowns (Ident.Tvar var) then phi
      else of_bool_term (Term.mk_var (Ident.Tvar var) T_bool.SBool)
    | Atom (Atom.App (pred, args, info), info') ->
      Atom (Atom.App (pred, List.map args ~f:(Term.elim_pvars unknowns), info), info')
    | Atom ((Atom.True _ | Atom.False _) as atom, info) -> Atom (atom, info)
    | LetRec _ -> failwith "unimplemented"
  (** eliminate let-binding that contains an unknown to be synthesized *)
  let rec elim_let_with_unknowns ?(map=Map.Poly.empty) unknowns = function
    | LetFormula (var, sort, def, body, info) ->
      let def' = Term.elim_let_with_unknowns ~map unknowns def in
      if Set.Poly.is_empty @@ Set.Poly.inter (Term.fvs_of def') unknowns then
        LetFormula (var, sort, def', elim_let_with_unknowns ~map unknowns body, info)
      else
        elim_let_with_unknowns ~map:(Map.Poly.set map ~key:var ~data:def') unknowns body
    | UnaryOp (op, phi1, info) ->
      UnaryOp (op, elim_let_with_unknowns ~map unknowns phi1, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, elim_let_with_unknowns ~map unknowns phi1, elim_let_with_unknowns ~map unknowns phi2, info)
    | Bind (bin, senv, phi1, info) ->
      let bounds = Set.Poly.of_list @@ List.map ~f:fst senv in
      let map' = Map.Poly.filter_keys map ~f:(Fn.non @@ Set.Poly.mem bounds) in
      Bind (bin, senv, elim_let_with_unknowns ~map:map' unknowns phi1, info)
    | Atom (Atom.App (Predicate.Var (Ident.Pvar var, []), [], _), _) as phi -> begin
        match Map.Poly.find map (Ident.Tvar var) with
        | Some t -> of_bool_term t
        | None -> phi
      end
    | Atom (Atom.App (pred, args, info), info') ->
      Atom (Atom.App (pred, List.map args ~f:(Term.elim_let_with_unknowns ~map unknowns), info), info')
    | Atom ((Atom.True _ | Atom.False _) as atom, info) -> Atom (atom, info)
    | LetRec _ -> failwith "unimplemented"
  let rec elim_let ?(map=Map.Poly.empty) = function
    | LetFormula (var, _, def, body, _) ->
      let def' = Term.elim_let ~map def in
      elim_let ~map:(Map.Poly.set map ~key:var ~data:def') body
    | UnaryOp (op, phi1, info) ->
      UnaryOp (op, elim_let ~map phi1, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, elim_let ~map phi1, elim_let ~map phi2, info)
    | Bind (bin, senv, phi1, info) ->
      let bounds = Set.Poly.of_list @@ List.map ~f:fst senv in
      let map' = Map.Poly.filter_keys map ~f:(Fn.non @@ Set.Poly.mem bounds) in
      Bind (bin, senv, elim_let ~map:map' phi1, info)
    | Atom (Atom.App (Predicate.Var (Ident.Pvar var, []), [], _), _) as phi -> begin
        match Map.Poly.find map (Ident.Tvar var) with
        | Some t -> of_bool_term t
        | None -> phi
      end
    | Atom (Atom.App (pred, args, info), info') ->
      Atom (Atom.App (pred, List.map args ~f:(Term.elim_let ~map), info), info')
    | Atom ((Atom.True _ | Atom.False _) as atom, info) -> Atom (atom, info)
    | LetRec _ -> failwith "unimplemented"
  let rec elim_unused_bounds fml =
    if is_atom fml then
      fml (* TODO *)
    else if is_and fml then
      let fml1, fml2, info = let_and fml in
      mk_and (elim_unused_bounds fml1) (elim_unused_bounds fml2) ~info
    else if is_or fml then
      let fml1, fml2, info = let_or fml in
      mk_or (elim_unused_bounds fml1) (elim_unused_bounds fml2) ~info
    else if is_bind fml then
      let binder, bounds, fml, info = let_bind fml in
      let fml = elim_unused_bounds fml in
      let ftv = tvs_of fml in
      let bounds = List.filter ~f:(fun (tvar, _) -> Set.Poly.mem ftv tvar) bounds in
      mk_bind_if_bounded binder bounds fml ~info
    else if is_neg fml then
      let fml, info = let_neg fml in
      mk_neg (elim_unused_bounds fml) ~info
    else
      failwith ((*str_of fml ^ *)" not supported\n")

  let rec has_let ?(map=Map.Poly.empty) = function
    | LetFormula _ -> true
    | UnaryOp (_, phi, _) -> has_let ~map phi
    | BinaryOp (_, phi1, phi2, _) -> has_let ~map phi1 || has_let ~map phi2
    | Bind (_, _, phi, _) -> has_let ~map phi
    | Atom (atom, _) -> Atom.has_let ~map atom
    | LetRec _ -> failwith "unimplemented"
  (* assume that the argument is alpha-renamed *)
  let rec let_env_of ?(map=Map.Poly.empty) = function
    | LetFormula (var, _, def, body, _) ->
      let_env_of ~map:(Map.Poly.set map ~key:var ~data:(Term.subst map def)) body
    | UnaryOp (_, phi, _) -> let_env_of phi ~map
    | BinaryOp (_, phi1, phi2, _) -> let_env_of phi2 ~map:(let_env_of phi1 ~map)
    | Bind (_, _, phi, _) -> let_env_of phi ~map
    | Atom (atom, _) -> Atom.let_env_of atom ~map
    | LetRec _ -> map
  (* assume that the argument is alpha-renamed *)
  let rec let_sort_env_of ?(map=Map.Poly.empty) = function
    | LetFormula (var, sort, _, body, _) ->
      let_sort_env_of ~map:(Map.Poly.set map ~key:var ~data:sort) body
    | UnaryOp (_, phi, _) -> let_sort_env_of phi ~map
    | BinaryOp (_, phi1, phi2, _) -> let_sort_env_of phi2 ~map:(let_sort_env_of phi1 ~map)
    | Bind (_, _, phi, _) -> let_sort_env_of phi ~map
    | Atom (atom, _) -> Atom.let_sort_env_of atom ~map
    | LetRec _ -> map
  (* assume that the argument is normalized and alpha-renamed *)
  let rec equivalent_sat = function
    | LetFormula (var, sort, def, body, _) ->
      mk_and (eq (Term.mk_var var sort) def) @@ equivalent_sat body
    (* | Bind (Forall, bounds, phi, info) -> Bind (Forall, bounds, equivalent_valid phi, info) *)
    (* | Bind (op, bounds, phi, info) -> Bind (op, bounds, equivalent_sat phi, info) *)
    | phi -> phi
  (* assume that the argument is normalized and alpha-renamed *)
  and equivalent_valid = function
    | LetFormula (var, sort, def, body, _) ->
      mk_or (neq (Term.mk_var var sort) def) @@ equivalent_valid body
    (* | Bind (binder, bounds, phi, info) -> Bind (binder, bounds, equivalent_valid phi, info) *)
    | phi -> phi
  (* assume that [phi] is normalized and alpha-renamed *)
  let equivalent_let is_forall phi =
    let lenv = Map.Poly.to_alist @@ let_sort_env_of phi in
    if is_forall then forall lenv @@ equivalent_valid phi
    else exists lenv @@ equivalent_sat phi

  let rec instantiate_div0_mod0 = function
    | Atom (atom, info) -> Atom (Atom.instantiate_div0_mod0 atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, instantiate_div0_mod0 phi, info)
    | BinaryOp (op, phi1, phi2, info) -> BinaryOp (op, instantiate_div0_mod0 phi1, instantiate_div0_mod0 phi2, info)
    | Bind (bin, senv, phi, info) -> Bind (bin, senv, instantiate_div0_mod0 phi, info)
    | LetRec (_, _, _) -> failwith "unimplemented"
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.instantiate_div0_mod0 (LetTerm (var, sort, def, T_bool.of_formula body, info))

  let rec find_div_mod = function
    | Atom (atom, _) -> Atom.find_div_mod atom
    | UnaryOp (_, phi, _) -> find_div_mod phi
    | BinaryOp (_, phi1, phi2, _) -> Set.Poly.union (find_div_mod phi1) (find_div_mod phi2)
    | Bind (_, _, phi, _) -> find_div_mod phi
    | LetRec (_, _, _) -> failwith "unimplemented"
    | LetFormula (var, sort, def, body, info) ->
      Term.find_div_mod [(LetTerm (var, sort, def, T_bool.of_formula body, info))]

  let rec replace_div_mod map = function
    | Atom (atom, info) -> Atom (Atom.replace_div_mod map atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, replace_div_mod map phi, info)
    | BinaryOp (op, phi1, phi2, info) -> BinaryOp (op, replace_div_mod map phi1, replace_div_mod map phi2, info)
    | Bind (bin, senv, phi, info) -> Bind (bin, senv, replace_div_mod map phi, info)
    | LetRec (_, _, _) -> failwith "unimplemented"
    | LetFormula (var, sort, def, body, info) ->
      of_bool_term @@ Term.replace_div_mod map (LetTerm (var, sort, def, T_bool.of_formula body, info))

  (* Prerequisites of rm_div_mod f
     f is normalized and a-converted, and there are no free variables in f
     there are some unimplemented forms
     for example, (exists x. x=0 and z = x mod 0) and (exists y. y=0 and z = y mod 0)
     but if f is prenex normal form then no problem *)
  (* rm_div_mod must be done before simplify*)
  let rm_div_mod f =
    let divmod = find_div_mod f in
    if Set.Poly.is_empty divmod then f else
      let map = Set.Poly.to_map divmod ~f:(fun (_, _) -> (Ident.mk_fresh_tvar (), Ident.mk_fresh_tvar ())) in
      let f = replace_div_mod map f in
      let newmap = Map.rename_keys map ~f:(fun (t1, t2) -> Some (Term.replace_div_mod map t1, Term.replace_div_mod map t2)) in
      let make_check_zero ((e1, n1),(d1, m1)) ((e2, n2),(d2, m2)) =
        let atom1 = Formula.mk_and (Formula.eq e1 e2) (Formula.eq n1 n2) in
        let atom2 = Formula.mk_and
            (Formula.eq (Term.mk_var d1 T_int.SInt) (Term.mk_var d2 T_int.SInt))
            (Formula.eq (Term.mk_var m1 T_int.SInt) (Term.mk_var m2 T_int.SInt)) in
        Formula.mk_imply atom1 atom2 in
      let check_zero outerlist innerlist =
        let (f, newlist) = List.fold innerlist ~init:((Formula.mk_true ()), outerlist) ~f:(fun (acc, outerlist) a ->
            let acc = Formula.mk_and acc (Formula.and_of @@List.map outerlist ~f:(make_check_zero a)) in
            let outerlist = a::outerlist in (acc, outerlist))
        in (f, newlist) in
      let make_restriction mapouter mapinner =
        let outerlist = Map.Poly.to_alist mapouter in
        let innerlist = Map.Poly.to_alist mapinner in
        let f1 = Formula.and_of @@List.map innerlist ~f:(fun ((e, n), (d, m)) ->
            let atom1 = Formula.neq n (T_int.zero ()) in
            let atom2 = Formula.eq e (T_int.mk_add (T_int.mk_mult n (Term.mk_var d T_int.SInt)) (Term.mk_var m T_int.SInt)) in
            let atom3 = Formula.leq (T_int.zero ()) (Term.mk_var m T_int.SInt) in
            let atom4 = Formula.lt (Term.mk_var m T_int.SInt) (T_int.mk_abs n) in
            Formula.mk_imply atom1 (Formula.and_of [atom2; atom3; atom4])) in
        let (f2, newlist) = check_zero outerlist innerlist in
        (Formula.mk_and f1 f2, Map.Poly.of_alist_exn newlist) in
      let rec divide_map map1 map2 vars =
        let (map21, map22) = Map.Poly.partitioni_tf map2 ~f:(fun ~key:(t1, t2) ~data:(_, _) ->
            let varset = Set.Poly.union (Term.tvs_of t1) (Term.tvs_of t2) in
            Set.Poly.is_subset varset ~of_:vars) in
        if Map.Poly.is_empty map21 then (map1, map2, vars)
        else let newvars = Map.Poly.fold map21 ~init:Set.Poly.empty ~f:(fun ~key:_ ~data:(d, m) newvars ->
            Set.Poly.add (Set.Poly.add newvars d) m) in
          divide_map (Map.force_merge map1 map21) map22 (Set.Poly.union vars newvars) in
      let rec add_restriction mapouter mapinner vars = function
        | Atom (atom, info) -> Atom (atom, info)
        | UnaryOp (op, phi, info) -> UnaryOp (op, add_restriction mapouter mapinner vars phi, info)
        | BinaryOp (op, phi1, phi2, info) -> BinaryOp (op, add_restriction mapouter mapinner vars phi1, add_restriction mapouter mapinner vars phi2, info)
        | Bind (binder, bounds, phi, info) ->
          let (newvars, _) = List.unzip bounds in
          let newvars = Set.Poly.union vars (Set.Poly.of_list newvars) in
          let (map1, map2, newvars) = divide_map Map.Poly.empty mapinner newvars in
          let (restriction, newmap) = make_restriction mapouter map1 in
          let sortenv = Map.Poly.fold map1 ~init:[] ~f:(fun ~key:_ ~data:(d, m) l -> (d, T_int.SInt)::(m, T_int.SInt)::l) in
          let f = Formula.mk_exists sortenv (Formula.mk_and restriction (add_restriction newmap map2 newvars phi)) in
          Bind (binder, bounds, f, info)
        | LetFormula (var, sort, def, body, info) ->
          LetFormula (var, sort, def, add_restriction mapouter mapinner vars body, info)
        | LetRec (_, _, _) -> failwith "unimplemented" in
      let (map1, map2, vars) = divide_map Map.Poly.empty newmap Set.Poly.empty in
      let (init, _) = make_restriction Map.Poly.empty map1 in
      let sortenv = Map.Poly.fold map1 ~init:[] ~f:(fun ~key:_ ~data:(d, m) l -> (d, T_int.SInt)::(m, T_int.SInt)::l) in
      Formula.mk_exists sortenv (Formula.mk_and init (add_restriction map1 map2 vars f))

  let rec rm_boolean_term = function
    | Atom (atom, _) -> Atom.rm_boolean_term atom
    | UnaryOp (op, phi, info) -> UnaryOp (op, rm_boolean_term phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, rm_boolean_term phi1, rm_boolean_term phi2, info)
    | Bind (binder, bounded, phi, info) -> Bind (binder, bounded, rm_boolean_term phi, info)
    | LetRec (_, _, _) -> failwith "unimplemented"
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, sort, def, rm_boolean_term body, info)

  let rec extend_pred_params ident extended_params = function
    | Atom (atom, info) -> Atom (Atom.extend_pred_params ident extended_params atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, extend_pred_params ident extended_params phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, extend_pred_params ident extended_params phi1, extend_pred_params ident extended_params phi2, info)
    | Bind (binder, bounded, phi, info) ->
      Bind (binder, bounded, extend_pred_params ident extended_params phi, info)
    | LetRec (fps, body, info) ->
      let fps = List.map ~f:(fun (fp, pvar, params, body) -> fp, pvar, params, extend_pred_params ident extended_params body) fps in
      let body = extend_pred_params ident extended_params body in
      LetRec (fps, body, info)
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, sort, def, extend_pred_params ident extended_params body, info)

  let rec rm_atom ?(polarity=true) ?(is_and=true) ~f = function
    | Atom (atom, info) ->
      let polarity = if is_and then polarity else not polarity in
      if f atom then if polarity then mk_true () else mk_false () else Atom (atom, info)
    | UnaryOp (Not, phi, info) -> UnaryOp (Not, rm_atom ~polarity:(not polarity) ~is_and ~f phi, info)
    | BinaryOp (And, phi1, phi2, info) -> BinaryOp (And, rm_atom ~polarity ~is_and:true ~f phi1, rm_atom ~polarity ~is_and:true ~f phi2, info)
    | BinaryOp (Or, phi1, phi2, info) -> BinaryOp (Or, rm_atom ~polarity ~is_and:false ~f phi1, rm_atom ~polarity ~is_and:false ~f phi2, info)
    | Bind (binder, bounded, phi, info) -> Bind (binder, bounded, rm_atom ~polarity ~is_and ~f phi, info)
    | phi -> phi

  let insert_let_formula var sort def info phi =
    if Set.Poly.mem (Formula.tvs_of phi) var then
      let var' = Ident.mk_fresh_tvar () in
      LetFormula (var', sort, def, rename (Map.Poly.singleton var var') phi, info)
    else phi

  let rec nnf_of = function
    | Atom (_, _) as phi -> phi
    | UnaryOp (Not, Atom (Atom.True _, _), _)  -> mk_false ()
    | UnaryOp (Not, Atom (Atom.False _, _), _) -> mk_true ()
    | UnaryOp (Not, atom, _) when is_atom atom -> mk_neg atom
    | UnaryOp (Not, UnaryOp (Not, phi, _), _) -> nnf_of phi
    | UnaryOp (Not, BinaryOp (And, phi1, phi2, _), _) ->
      mk_or (nnf_of @@ mk_neg phi1) (nnf_of @@ mk_neg phi2)
    | UnaryOp (Not, BinaryOp (Or, phi1, phi2, _), _) ->
      mk_and (nnf_of @@ mk_neg phi1) (nnf_of @@ mk_neg phi2)
    | UnaryOp (Not, BinaryOp (Imply, phi1, phi2, _), _) ->
      mk_and (nnf_of phi1) (nnf_of @@ mk_neg phi2)
    | UnaryOp (Not, BinaryOp (Iff, phi1, phi2, _), _) ->
      mk_xor (nnf_of phi1) (nnf_of phi2)
    | UnaryOp (Not, BinaryOp (Xor, phi1, phi2, _), _) ->
      mk_iff (nnf_of phi1) (nnf_of phi2)
    | UnaryOp (Not, Bind (Forall, params, phi, _), _) ->
      mk_bind Exists params (nnf_of @@ mk_neg phi)
    | UnaryOp (Not, Bind (Exists, params, phi, _), _) ->
      mk_bind Forall params (nnf_of @@ mk_neg phi)
    | UnaryOp (Not, LetFormula (var, sort, def, body, _), _) ->
      mk_let_formula var sort def @@ nnf_of @@ mk_neg body
    | UnaryOp (Not, LetRec ([], phi, _), _) ->
      nnf_of (mk_neg phi)
    | BinaryOp (And, phi1, phi2, _) ->
      mk_and (nnf_of phi1) (nnf_of phi2)
    | BinaryOp (Or, phi1, phi2, _) ->
      mk_or (nnf_of phi1) (nnf_of phi2)
    | BinaryOp (Imply, phi1, phi2, _) ->
      mk_or (nnf_of @@ mk_neg phi1) (nnf_of phi2)
    | BinaryOp (Iff, phi1, phi2, _) ->
      mk_iff (nnf_of phi1) (nnf_of phi2)
    | BinaryOp (Xor, phi1, phi2, _) ->
      mk_xor (nnf_of phi1) (nnf_of phi2)
    | Bind (b, params, phi, _) ->
      mk_bind b params (nnf_of phi)
    | LetRec ([], phi, _) ->
      nnf_of phi
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, sort, def, nnf_of body, info)
    | phi -> failwith ("Unexpected formula in nnf_of: " ^ Formula.str_of phi)

  let rec dnf_of_aux ?(process_pure=false) exi_senv senv = function
    | Atom (Atom.True _, _) ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    | UnaryOp (Not, Atom (Atom.True _, _), _) ->
      Set.Poly.empty
    | Atom (Atom.False _, _) ->
      Set.Poly.empty
    | UnaryOp (Not, Atom (Atom.False _, _), _) ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    | phi when not process_pure && Set.Poly.is_empty @@ Set.Poly.inter (fvs_of phi) (Map.key_set exi_senv) ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi)
    | Atom (Atom.App (Predicate.Var (Ident.Pvar name, _), _, _) as atom, _) ->
      let tvar = Ident.Tvar name in
      begin
        match Map.Poly.find exi_senv tvar, Map.Poly.find senv tvar with
        | Some _, None -> Set.Poly.singleton (Set.Poly.singleton atom, Set.Poly.empty, Set.Poly.empty)
        | None, Some _ -> Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
        | _ -> failwith "dnf_of"
      end
    | UnaryOp (Not, Atom (Atom.App (Predicate.Var (Ident.Pvar name, _), _, _) as atom, _), _) ->
      let tvar = Ident.Tvar name in
      begin
        match Map.Poly.find exi_senv tvar, Map.Poly.find senv tvar with
        | Some _, None -> Set.Poly.singleton (Set.Poly.empty, Set.Poly.singleton atom, Set.Poly.empty)
        | None, Some _ -> Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_neg (mk_atom atom)))
        | _ -> failwith "cnf_of"
      end
    | Atom (Atom.App (Predicate.Psym _, _, _) as atom, _) -> (* not reachable *)
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
    | UnaryOp (Not, Atom (Atom.App (Predicate.Psym _, _, _) as atom, _), _) -> (* not reachable *)
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_neg (mk_atom atom)))
    | UnaryOp (Not, _, _) -> assert false
    | Atom (Atom.App (Predicate.Fixpoint _, _, _), _) -> failwith "not supported"
    | BinaryOp (And, phi1, phi2, _) ->
      let cls1 = dnf_of_aux ~process_pure exi_senv senv phi1 in
      let cls2 = dnf_of_aux ~process_pure exi_senv senv phi2 in
      Set.cartesian_map cls1 cls2 ~f:(fun (ps1, ns1, phis1) (ps2, ns2, phis2) ->
          Set.Poly.union ps1 ps2, Set.Poly.union ns1 ns2, Set.Poly.union phis1 phis2)
    | BinaryOp (Or, phi1, phi2, _) ->
      let cls1 = dnf_of_aux ~process_pure exi_senv senv phi1 in
      let cls2 = dnf_of_aux ~process_pure exi_senv senv phi2 in
      let phis, cls =
        Set.Poly.union cls1 cls2
        |> Set.Poly.partition_tf ~f:(fun (ps, ns, phis) ->
            Set.Poly.is_empty ps && Set.Poly.is_empty ns &&
            Set.Poly.is_empty @@ Set.Poly.inter (Map.key_set exi_senv) (fvs_of @@ and_of @@ Set.Poly.to_list phis))
        |> Pair.map (Set.Poly.map ~f:(fun (_, _, phis) -> and_of @@ Set.Poly.to_list phis)) Fn.id
      in
      if Set.Poly.is_empty phis then cls
      else if process_pure then
        Set.Poly.union cls @@
        Set.Poly.map phis ~f:(fun phi -> Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi)
      else Set.Poly.add cls (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton @@ or_of @@ Set.Poly.to_list phis)
    | BinaryOp (Imply, _, _, _) -> assert false
    | BinaryOp (Iff, phi1, phi2, _) ->
      (* t1 <=> t2 -> (t1 and t2) or (not t1 and not t2) *)
      dnf_of_aux ~process_pure exi_senv senv @@
      mk_or
        (mk_and (nnf_of phi1) (nnf_of phi2))
        (mk_and (nnf_of @@ mk_neg phi1) (nnf_of @@ mk_neg phi2))
    | BinaryOp (Xor, phi1, phi2, _) ->
      (* t1 xor t2 -> (t1 and not t2) or (not t1 and t2) *)
      dnf_of_aux ~process_pure exi_senv senv @@
      mk_or
        (mk_and (nnf_of phi1) (nnf_of @@ mk_neg phi2))
        (mk_and (nnf_of @@ mk_neg phi1) (nnf_of phi2))
    | Bind (_, _, _, _) -> assert false
    | LetRec (_, _, _) -> assert false
    | LetFormula (var, sort, def, body, info) ->
      let senv' = Map.Poly.set senv ~key:var ~data:sort in
      Set.Poly.map (dnf_of_aux ~process_pure exi_senv senv' body) ~f:(fun (ps, ns, phis) ->
          Set.Poly.map ~f:(Atom.insert_let_pvar_app var sort def info) ps,
          Set.Poly.map ~f:(Atom.insert_let_pvar_app var sort def info) ns,
          Set.Poly.singleton @@ insert_let_formula var sort def info @@ and_of @@ Set.Poly.to_list phis)
  (* outputs the DNF formula represented by a list of clauses where a clause is represented by a triple [(ps,ns,phi')] consisting of
     [ps]: predicate variable applications,
     [ns] negated predicate variable applications, and
     [phi']: a pure formula *)
  (* assume that [phi] is in NNF and let-normalized *)
  (* assume that [phi1] and [phi2] in [phi1 = phi2] and [phi1 <> phi2] do not contain a predicate variable application *)
  let dnf_of ?(process_pure=false) exi_senv phi =
    phi
    |> dnf_of_aux ~process_pure exi_senv Map.Poly.empty
    |> Set.Poly.map ~f:(fun (ps, ns, phis) -> ps, ns, and_of @@ Set.Poly.to_list phis)

  let rec cnf_of_aux ?(process_pure=false) exi_senv senv = function
    | Atom (Atom.True _, _) ->
      Set.Poly.empty
    | UnaryOp (Not, Atom (Atom.True _, _), _) ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    | Atom (Atom.False _, _) ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
    | UnaryOp (Not, Atom (Atom.False _, _), _) ->
      Set.Poly.empty
    | phi when not process_pure && Set.Poly.is_empty @@ Set.Poly.inter (fvs_of phi) (Map.key_set exi_senv) ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi)
    | Atom (Atom.App (Predicate.Var (Ident.Pvar name, _), _, _) as atom, _) ->
      let tvar = Ident.Tvar name in
      begin
        match Map.Poly.find exi_senv tvar, Map.Poly.find senv tvar with
        | Some _, None -> Set.Poly.singleton (Set.Poly.singleton atom, Set.Poly.empty, Set.Poly.empty)
        | None, Some _ -> Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
        | _ -> failwith "cnf_of"
      end
    | UnaryOp (Not, Atom (Atom.App (Predicate.Var (Ident.Pvar name, _), _, _) as atom, _), _) ->
      let tvar = Ident.Tvar name in
      begin
        match Map.Poly.find exi_senv tvar, Map.Poly.find senv tvar with
        | Some _, None -> Set.Poly.singleton (Set.Poly.empty, Set.Poly.singleton atom, Set.Poly.empty)
        | None, Some _ -> Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_neg (mk_atom atom)))
        | _ -> failwith "cnf_of"
      end
    | Atom (Atom.App (Predicate.Psym _, _, _) as atom, _) -> (* not reachable *)
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
    | UnaryOp (Not, Atom (Atom.App (Predicate.Psym _, _, _) as atom, _), _) -> (* not reachable *)
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_neg (mk_atom atom)))
    | UnaryOp (Not, _, _) -> assert false
    | Atom (Atom.App (Predicate.Fixpoint _, _, _), _) -> failwith "not supported"
    | BinaryOp (And, phi1, phi2, _) ->
      let cls1 = cnf_of_aux ~process_pure exi_senv senv phi1 in
      let cls2 = cnf_of_aux ~process_pure exi_senv senv phi2 in
      let phis, cls =
        Set.Poly.union cls1 cls2
        |> Set.Poly.partition_tf ~f:(fun (ps, ns, phis) ->
            Set.Poly.is_empty ps && Set.Poly.is_empty ns &&
            Set.Poly.is_empty @@ Set.Poly.inter (Map.key_set exi_senv) (fvs_of @@ or_of @@ Set.Poly.to_list phis))
        |> Pair.map (Set.Poly.map ~f:(fun (_, _, phis) -> or_of @@ Set.Poly.to_list phis)) Fn.id
      in
      if Set.Poly.is_empty phis then cls
      else if process_pure then
        Set.Poly.union cls @@
        Set.Poly.map phis ~f:(fun phi -> Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi)
      else Set.Poly.add cls (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton @@ and_of @@ Set.Poly.to_list phis)
    | BinaryOp (Or, phi1, phi2, _) ->
      let cls1 = cnf_of_aux ~process_pure exi_senv senv phi1 in
      let cls2 = cnf_of_aux ~process_pure exi_senv senv phi2 in
      Set.cartesian_map cls1 cls2 ~f:(fun (ps1, ns1, phis1) (ps2, ns2, phis2) ->
          Set.Poly.union ps1 ps2, Set.Poly.union ns1 ns2, Set.Poly.union phis1 phis2)
    | BinaryOp (Imply, _, _, _) -> assert false
    | BinaryOp (Iff, phi1, phi2, _) ->
      (* t1 <=> t2 -> (not t1 or t2) and (t1 or not t2) *)
      cnf_of_aux ~process_pure exi_senv senv @@
      mk_and
        (mk_or (nnf_of @@ mk_neg phi1) (nnf_of phi2))
        (mk_or (nnf_of phi1) (nnf_of @@ mk_neg phi2))
    | BinaryOp (Xor, phi1, phi2, _) ->
      (* t1 xor t2 -> (t1 or t2) and (not t1 or not t2) *)
      cnf_of_aux ~process_pure exi_senv senv @@
      mk_and
        (mk_or (nnf_of phi1) (nnf_of phi2))
        (mk_or (nnf_of @@ mk_neg phi1) (nnf_of @@ mk_neg phi2))
    | Bind (binder, _, _, _) ->
      failwith @@ Formula.str_of_binder binder ^ " not supported"
    | LetRec (_, _, _) -> assert false
    | LetFormula (var, sort, def, body, info) ->
      let senv' = Map.Poly.set senv ~key:var ~data:sort in
      Set.Poly.map (cnf_of_aux ~process_pure exi_senv senv' body) ~f:(fun (ps, ns, phis) ->
          Set.Poly.map ~f:(Atom.insert_let_pvar_app var sort def info) ps,
          Set.Poly.map ~f:(Atom.insert_let_pvar_app var sort def info) ns,
          Set.Poly.singleton @@ insert_let_formula var sort def info @@ or_of @@ Set.Poly.to_list phis)
  (* outputs the CNF formula represented by a list of clauses where a clause is represented by a triple [(ps,ns,phi')] consisting of
     [ps]: predicate variable applications,
     [ns] negated predicate variable applications, and
     [phi']: a pure formula *)
  (* assume that [phi] is in NNF and let-normalized *)
  (* assume that [phi1] and [phi2] in [phi1 = phi2] and [phi1 <> phi2] do not contain a predicate variable application *)
  let cnf_of ?(process_pure=false) exi_senv phi =
    phi
    |> cnf_of_aux ~process_pure exi_senv Map.Poly.empty
    |> Set.Poly.map ~f:(fun (ps, ns, phis) -> ps, ns, or_of @@ Set.Poly.to_list phis)

  let rec to_atom = function
    | Atom (atom, _) -> atom
    | UnaryOp (Not, Atom (atom, _), _) -> Atom.negate atom
    | UnaryOp (Not, UnaryOp (Not, phi', _), _) -> to_atom phi'
    | phi -> failwith (Formula.str_of phi ^ " is not atomic formula")

  let threshold = 10
  let enable = false
  let drop_let = true
  (* assume that [phi] is let-normalized *)
  let psym_pvar_apps_of ?(simplifier=Fn.id) phi =
    let pos, neg = atoms_of phi in
    let pos = Set.Poly.filter_map pos ~f:(fun atm ->
        let atm = to_atom @@ (if drop_let then body_of_let else elim_let ~map:Map.Poly.empty) @@ simplifier @@ replace_let_body phi @@ mk_atom atm in
        let size = Atom.ast_size atm in
        (*print_endline @@ "size: " ^ string_of_int size;*)
        if enable && size >= threshold then None else Some atm)
    in
    let neg = Set.Poly.filter_map neg ~f:(fun atm ->
        let atm = to_atom @@ (if drop_let then body_of_let else elim_let ~map:Map.Poly.empty) @@ simplifier @@ replace_let_body phi @@ mk_atom atm in
        let size = Atom.ast_size atm in
        (*print_endline @@ "size: " ^ string_of_int size;*)
        if enable && size >= threshold then None else Some atm)
    in
    let psyms, pos_pvars =
      Set.Poly.fold pos ~f:(fun (symapps, papps) atom ->
          if Atom.is_psym_app atom then atom::symapps, papps
          else if Atom.is_pvar_app atom then symapps, atom::papps
          else symapps, papps)
        ~init:([], [])
    in
    let psyms, neg_pvars =
      Set.Poly.fold neg ~f:(fun (symapps, papps) atom ->
          if Atom.is_psym_app atom then Atom.negate atom::symapps, papps
          else if Atom.is_pvar_app atom then symapps, atom::papps
          else symapps, papps)
        ~init:(psyms, [])
    in
    psyms, pos_pvars, neg_pvars

  let univ_clos phi =
    let bounds = Set.Poly.to_list @@ term_sort_env_of phi in
    if List.is_empty bounds then phi else mk_forall bounds phi

  (* assume the input is alpha-converted *)
  let rec split_exists = function
    | Bind (Exists, senv1, phi, _) ->
      let senv2, phi = split_exists phi in
      senv1 @ senv2, phi
    | phi -> [], phi
  (* assume the input is alpha-converted and in NNF *)
  let rec split_quantifiers = function
    | Atom (App (pred, tl, _), _) ->
      let qs, termlist = (* ToDo: the following seems not correct *)
        List.fold tl ~init:([], []) ~f:(fun (qs, terms) -> function
            | FunApp (T_bool.Formula phi, [], _) ->
              let q, phi = split_quantifiers phi in
              qs @ q, terms @ [T_bool.of_formula phi]
            | term -> qs, terms @ [term])
      in
      qs, mk_atom @@ Atom.mk_app pred termlist
    | Atom (_, _) as phi ->
      [], phi
    | UnaryOp (unop, phi, _) -> (* ToDo: correct? *)
      let qs, phi = split_quantifiers phi in
      qs, mk_unop unop phi
    | BinaryOp (binop, phi1, phi2, _) ->
      let qs1, phi1 = split_quantifiers phi1 in
      let qs2, phi2 = split_quantifiers phi2 in
      qs1 @ qs2, mk_binop binop phi1 phi2
    | Bind (binder, sortenv, phi, _) ->
      let qs, phi = split_quantifiers phi in
      (binder, sortenv) :: qs, phi
    | LetRec (_, _, _) -> assert false
    | LetFormula _ -> failwith @@ "'LetFormula' is not supported yet" (* TODO *)
  let pnf_of f =
    let quantifiers, phi = split_quantifiers f in
    mk_binds quantifiers phi
  let skolemize_fun phi =
    let rec aux senv fsenv = function
      | Atom (_, _) as phi ->
        (* we here assume that phi does not contain quantifiers *)senv, fsenv, phi
      | UnaryOp (unop, phi, _) ->
        let senv, fsenv, phi = aux senv fsenv phi in
        senv, fsenv, mk_unop unop phi
      | BinaryOp (binop, phi1, phi2, _) ->
        let senv, fsenv, phi1 = aux senv fsenv phi1 in
        let senv, fsenv, phi2 = aux senv fsenv phi2 in
        senv, fsenv, mk_binop binop phi1 phi2
      | Bind (Forall, uni_senv, phi, _) ->
        let bounded = Map.of_list_exn uni_senv in
        aux (Map.force_merge bounded senv) fsenv phi
      | Bind (Exists, exi_senv, phi, _) ->
        let args = Map.Poly.to_alist senv in
        let subst, bounds_rev =
          List.fold ~init:(Map.Poly.empty, []) exi_senv
            ~f:(fun (subst, bounds_rev) (Ident.Tvar x, sort) ->
                let new_tvar = Ident.mk_fresh_tvar ~prefix:(Some ("#skolem_" ^ x)) () in
                Map.Poly.add_exn subst
                  ~key:(Ident.Tvar x)
                  ~data:(Term.mk_fvar_app new_tvar (List.map ~f:snd args @ [sort])
                           (Term.of_sort_env args)),
                (new_tvar, Sort.mk_fun (List.map ~f:snd args @ [sort])) :: bounds_rev)
        in
        aux senv (fsenv @ List.rev bounds_rev) (Formula.subst subst phi)
      | Bind (Random _, _, _, _) -> assert false (*ToDo*)
      | LetRec (_, _, _) -> assert false
      | LetFormula (var, sort, def, body, info) ->
        let senv = Map.Poly.add_exn ~key:var ~data:sort senv in
        let senv, fsenv, body = aux senv fsenv body in
        senv, fsenv, LetFormula (var, sort, def, body, info)
    in
    aux Map.Poly.empty [] phi
  let skolemize_pred phi =
    let rec aux senv fsenv = function
      | Atom (_, _) as phi ->
        (* we here assume that phi does not contain quantifiers *)senv, fsenv, phi
      | UnaryOp (unop, phi, _) ->
        let senv, fsenv, phi = aux senv fsenv phi in
        senv, fsenv, mk_unop unop phi
      | BinaryOp (binop, phi1, phi2, _) ->
        let senv, fsenv, phi1 = aux senv fsenv phi1 in
        let senv, fsenv, phi2 = aux senv fsenv phi2 in
        senv, fsenv, mk_binop binop phi1 phi2
      | Bind (Forall, uni_senv, phi, _) ->
        let bounded = Map.of_list_exn uni_senv in
        aux (Map.force_merge bounded senv) fsenv phi
      | Bind (Exists, exi_senv, phi, _) ->
        let args = Map.Poly.to_alist senv in
        let bounded, subst, bounds_rev =
          List.fold ~init:(Map.Poly.empty, Map.Poly.empty, []) exi_senv
            ~f:(fun (bounded, subst, bounds_rev) (Ident.Tvar x, sort) ->
                let name_tvar = Ident.mk_fresh_tvar ~prefix:(Some ("#skolem_" ^ x)) () in
                let ret = Term.mk_var name_tvar sort in
                let Ident.Pvar name = Ident.mk_fresh_pvar () in
                let name = "FN" ^ Ident.divide_flag ^ x ^ name in
                let fnpvarapp = Atom.mk_pvar_app (Ident.Pvar name) (List.map ~f:snd args @ [sort])
                    (Term.of_sort_env args @ [ret]) in
                Map.Poly.add_exn bounded ~key:name_tvar ~data:sort,
                Map.Poly.add_exn subst ~key:(Ident.Tvar x) ~data:ret,
                (fnpvarapp, Sort.mk_fun @@ List.map ~f:snd args @ [sort; T_bool.SBool]) :: bounds_rev)
        in
        aux (Map.force_merge bounded senv)
          (fsenv @ List.rev @@ List.map ~f:(fun (a, sort) -> Atom.pvar_of a, sort) bounds_rev)
          (Formula.mk_imply
             (Formula.and_of @@ List.map bounds_rev ~f:(fun (a, _) -> Formula.mk_atom a))
             (Formula.subst subst phi))
      | Bind (Random _, _, _, _) -> assert false (*ToDo*)
      | LetRec (_, _, _) -> assert false
      | LetFormula (var, sort, def, body, info) ->
        let senv = Map.Poly.add_exn ~key:var ~data:sort senv in
        let senv, fsenv, body = aux senv fsenv body in
        senv, fsenv, LetFormula (var, sort, def, body, info)
    in
    aux Map.Poly.empty [] phi

  (** Printing *)
  let str_of_unop = function Not -> "Not"
  let str_of_binop = function
    | And -> "And" | Or -> "Or" | Imply -> "Imply" | Iff -> "Iff" | Xor -> "Xor"
  let str_of_binder = function
    | Forall -> "Forall" | Exists -> "Exists" | Random r -> Rand.str_of r

  let str_of ?(priority=0) phi =
    let rec aux ?(priority=0) phi ~next =
      match phi with
      | Atom (atom, _) -> next @@ Atom.str_of ~priority atom
      | UnaryOp (Not, phi, _) ->
        aux ~priority:(Priority.fun_app+1(*ToDo*)) phi ~next:(fun s ->
            next @@ Priority.add_bracket priority Priority.fun_app @@
            Printf.sprintf "not %s" s)
      | BinaryOp (And, phi1, phi2, _) ->
        aux ~priority:Priority.binary_and phi1 ~next:(fun s1 ->
            aux ~priority:Priority.binary_and phi2 ~next:(fun s2 ->
                next @@ Priority.add_bracket priority Priority.binary_and @@
                Printf.sprintf "%s /\\ %s" s1 s2))
      | BinaryOp (Or, phi1, phi2, _) ->
        aux ~priority:Priority.binary_or phi1 ~next:(fun s1 ->
            aux ~priority:Priority.binary_or phi2 ~next:(fun s2 ->
                next @@ Priority.add_bracket priority Priority.binary_or @@
                Printf.sprintf "%s \\/ %s" s1 s2))
      | BinaryOp (Imply, phi1, phi2, _) ->
        aux phi1 ~priority:Priority.imply_iff_xor ~next:(fun s1 ->
            aux phi2 ~priority:Priority.imply_iff_xor ~next:(fun s2 ->
                next @@ Priority.add_bracket priority Priority.imply_iff_xor @@
                Printf.sprintf "%s => %s" s1 s2))
      | BinaryOp (Iff, phi1, phi2, _) ->
        aux phi1 ~priority:Priority.imply_iff_xor ~next:(fun s1 ->
            aux phi2 ~priority:Priority.imply_iff_xor ~next:(fun s2 ->
                next @@ Priority.add_bracket priority Priority.imply_iff_xor @@
                Printf.sprintf "%s <=> %s" s1 s2))
      | BinaryOp (Xor, phi1, phi2, _) ->
        aux phi1 ~priority:Priority.imply_iff_xor ~next:(fun s1 ->
            aux phi2 ~priority:Priority.imply_iff_xor ~next:(fun s2 ->
                next @@ Priority.add_bracket priority Priority.imply_iff_xor @@
                Printf.sprintf "%s xor %s" s1 s2))
      | Bind (Forall, params, phi, _) ->
        aux phi ~priority:Priority.let_forall_exists ~next:(fun s ->
            next @@ Priority.add_bracket priority Priority.let_forall_exists @@
            Printf.sprintf "forall %s. %s"
              (str_of_sort_env_list Term.str_of_sort params) s)
      | Bind (Exists, params, phi, _) ->
        aux phi ~priority:Priority.let_forall_exists ~next:(fun s ->
            next @@ Priority.add_bracket priority Priority.let_forall_exists @@
            Printf.sprintf "exists %s. %s"
              (str_of_sort_env_list Term.str_of_sort params) s)
      | Bind (Random r, params, phi, _) ->
        aux phi ~priority:Priority.let_forall_exists ~next:(fun s ->
            next @@ Priority.add_bracket priority Priority.let_forall_exists @@
            Printf.sprintf "%s %s. %s"
              (Rand.str_of r) (str_of_sort_env_list Term.str_of_sort params) s)
      | LetRec (funcs, body, _) ->
        aux body ~priority:Priority.let_forall_exists ~next:(fun s ->
            next @@ Priority.add_bracket priority Priority.let_forall_exists @@
            Printf.sprintf "let rec %s in %s"
              (String.concat_map_list ~sep:" and " funcs ~f:(fun (fix, pvar, bounds, body) ->
                   let var_names =
                     if List.is_empty bounds then
                       ["()"]
                     else
                       List.map bounds ~f:(fun (tvar, _) -> Ident.name_of_tvar tvar)
                   in
                   aux body ~priority:0 ~next:(fun s ->
                       Printf.sprintf "%s %s =%s %s"
                         (Ident.name_of_pvar pvar)
                         (String.concat ~sep:" " var_names)
                         (Predicate.str_of_fixpoint fix)
                         s)))
              s)
      | LetFormula (var, sort, def, phi, _) ->
        aux phi ~priority:Priority.let_forall_exists ~next:(fun s ->
            next @@ Priority.add_bracket priority Priority.let_forall_exists @@
            Printf.sprintf "letf %s:%s = %s in %s"
              (Ident.name_of_tvar var)
              (Term.short_name_of_sort sort)
              (Term.str_of def)
              s)
    in aux ~priority ~next:(fun s -> s) phi

  let rec fold phi ~f =
    let rec aux phi ~next =
      match phi with
      | Atom (atom, _) -> next @@ f#fatom atom
      | UnaryOp (Not, phi, _) ->
        aux phi ~next:(fun phi' -> next @@ f#fnot phi')
      | BinaryOp (And, phi1, phi2, _) ->
        aux phi1 ~next:(fun phi1' -> aux phi2 ~next:(fun phi2' -> next @@ f#fand phi1' phi2'))
      | BinaryOp (Or, phi1, phi2, _) ->
        aux phi1 ~next:(fun phi1' -> aux phi2 ~next:(fun phi2' -> next @@ f#for_ phi1' phi2'))
      | BinaryOp (Imply, phi1, phi2, _) ->
        aux phi1 ~next:(fun phi1' -> aux phi2 ~next:(fun phi2' -> next @@ f#fimply phi1' phi2'))
      | BinaryOp (Iff, phi1, phi2, _) ->
        aux phi1 ~next:(fun phi1' -> aux phi2 ~next:(fun phi2' -> next @@ f#fiff phi1' phi2'))
      | Bind (binder, senv, phi, _) -> aux phi ~next:(fun phi' -> next @@ f#fbind binder senv phi')
      | LetRec (funcs, phi, _) ->
        aux phi ~next:(fun phi' ->
            next @@ f#fletrec
              (List.map funcs ~f:(fun (fix, pvar, senv, phi) -> (fix, pvar, senv, fold phi ~f)))
              phi')
      | LetFormula (var, sort, def, body, _) ->
        aux body ~next:(fun body' -> next @@ f#fletformula var sort def body')
      | _ -> failwith "unsupported fold case"
    in aux phi ~next:Fn.id

  let map_atom phi ~f =
    fold phi ~f:(object
      method fatom atom = f atom
      method fand p1 p2 = mk_and p1 p2
      method for_ p1 p2 = mk_or p1 p2
      method fnot p1 = mk_neg p1
      method fbind binder senv p1 = mk_bind binder senv p1
      method fletrec funcs p1 = mk_letrec funcs p1
      method fimply p1 p2 = mk_imply p1 p2
      method fiff p1 p2 = mk_iff p1 p2
      method fletformula var sort def body = mk_let_formula var sort def body
    end)
  let rec map_atom_polarity polarity phi ~f =
    match phi with
    | Atom (atom, _) -> f polarity atom
    | UnaryOp (Not, phi, info) -> UnaryOp (Not, map_atom_polarity (not polarity) phi ~f, info)
    | BinaryOp (op, phi1, phi2, info) -> BinaryOp (op, map_atom_polarity polarity phi1 ~f, map_atom_polarity polarity phi2 ~f, info)
    | Bind (binder, senv, phi, info) -> Bind (binder, senv, map_atom_polarity polarity phi ~f, info)
    | LetRec (funcs, phi, info) ->
      LetRec (List.map funcs ~f:(fun (fix, pvar, senv, phi) ->
          (fix, pvar, senv, map_atom_polarity polarity phi ~f)), map_atom_polarity polarity phi ~f, info)
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, sort, def, map_atom_polarity polarity body ~f, info)
  let rec map_term phi ~f =
    match phi with
    | LetFormula (var, sort, def, body, info) -> LetFormula (var, sort, Term.map_term def ~f, map_term ~f body, info)
    | phi -> Formula.map_atom phi ~f:(fun atom -> Formula.mk_atom @@ Atom.map_term ~f atom)
  let iter_term ~f t = let _ = map_term t ~f:(fun t -> f t; t) in ()
  let rec iter_pred_app ~(f: Ident.pvar -> Term.t list -> unit) formula =
    if Formula.is_atom formula then begin
      let atom, _ = Formula.let_atom formula in
      if Atom.is_app atom then
        let pred, args, _ = Atom.let_app atom in
        if Predicate.is_var pred then
          f (fst @@ Predicate.let_var pred) args
    end else if Formula.is_unop formula then
      let _, fml, _ = Formula.let_unop formula in
      iter_pred_app ~f fml
    else if Formula.is_binop formula then
      let _, fml1, fml2, _ = Formula.let_binop formula in
      iter_pred_app ~f fml1;
      iter_pred_app ~f fml2
    else if Formula.is_bind formula then
      let _, _, fml, _ = Formula.let_bind formula in
      iter_pred_app ~f fml
    else assert false
  (* failwith @@ Printf.sprintf "iter_pred_app: not implemented: %s" @@ Formula.str_of formula *)

  let subst_sorts_bounds map bounds =
    List.map bounds ~f:(fun (x, s) -> x, Term.subst_sorts_sort map s)
  let subst_conts_bounds map bounds =
    List.map bounds ~f:(fun (x, s) -> x, Term.subst_conts_sort map s)
  let subst_opsigs_bounds map bounds =
    List.map bounds ~f:(fun (x, s) -> x, Term.subst_opsigs_sort map s)
  let rec subst_sorts map = function
    | Atom (atom, info) ->
      Atom (Atom.subst_sorts map atom, info)
    | UnaryOp (op, phi, info) ->
      UnaryOp (op, subst_sorts map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, subst_sorts map phi1, subst_sorts map phi2, info)
    | Bind (Random rand, bounds, phi, info) ->
      let bounds' =
        List.map bounds ~f:(fun (x, s) -> x, Term.subst_sorts_sort map s)
      in
      Bind (Random (Rand.subst_sorts map rand), bounds', subst_sorts map phi, info)
    | Bind (binder, bounds, phi, info) ->
      Bind (binder, subst_sorts_bounds map bounds, subst_sorts map phi, info)
    | LetRec (funcs, phi, info) ->
      let funcs' =
        List.map funcs ~f:(fun (fix, pvar, bounds, phi) ->
            (fix, pvar, subst_sorts_bounds map bounds, subst_sorts map phi))
      in
      LetRec (funcs', subst_sorts map phi, info)
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, Term.subst_sorts_sort map sort, Term.subst_sorts map def, subst_sorts map body, info)
  let rec subst_conts map = function
    | Atom (atom, info) ->
      Atom (Atom.subst_conts map atom, info)
    | UnaryOp (op, phi, info) ->
      UnaryOp (op, subst_conts map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, subst_conts map phi1, subst_conts map phi2, info)
    | Bind (Random rand, bounds, phi, info) ->
      let bounds' =
        List.map bounds ~f:(fun (x, s) -> x, Term.subst_conts_sort map s)
      in
      Bind (Random (Rand.subst_conts map rand), bounds', subst_conts map phi, info)
    | Bind (binder, bounds, phi, info) ->
      Bind (binder, subst_conts_bounds map bounds, subst_conts map phi, info)
    | LetRec (funcs, phi, info) ->
      let funcs' =
        List.map funcs ~f:(fun (fix, pvar, bounds, phi) ->
            (fix, pvar, subst_conts_bounds map bounds, subst_conts map phi))
      in
      LetRec (funcs', subst_conts map phi, info)
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, Term.subst_conts_sort map sort, Term.subst_conts map def, subst_conts map body, info)
  let rec subst_opsigs map = function
    | Atom (atom, info) ->
      Atom (Atom.subst_opsigs map atom, info)
    | UnaryOp (op, phi, info) ->
      UnaryOp (op, subst_opsigs map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, subst_opsigs map phi1, subst_opsigs map phi2, info)
    | Bind (Random rand, bounds, phi, info) ->
      let bounds' =
        List.map bounds ~f:(fun (x, s) -> x, Term.subst_opsigs_sort map s)
      in
      Bind (Random (Rand.subst_opsigs map rand), bounds', subst_opsigs map phi, info)
    | Bind (binder, bounds, phi, info) ->
      Bind (binder, subst_opsigs_bounds map bounds, subst_opsigs map phi, info)
    | LetRec (funcs, phi, info) ->
      let funcs' =
        List.map funcs ~f:(fun (fix, pvar, bounds, phi) ->
            (fix, pvar, subst_opsigs_bounds map bounds, subst_opsigs map phi))
      in
      LetRec (funcs', subst_opsigs map phi, info)
    | LetFormula (var, sort, def, body, info) ->
      LetFormula (var, Term.subst_opsigs_sort map sort, Term.subst_opsigs map def, subst_opsigs map body, info)
end

and T_bool : Type.T_boolType
  with type formula := Formula.t
   and type atom := Atom.t
   and type term := Term.t
= struct
  type fun_sym += Formula of Formula.t | IfThenElse
  type pred_sym += Eq | Neq
  type Sort.t += SBool

  (** Construction *)
  let of_atom ?(info=Dummy) atom = Term.mk_fsym_app (Formula (Formula.mk_atom atom)) [] ~info
  let of_formula ?(info=Dummy) phi = Term.mk_fsym_app (Formula phi) [] ~info
  let mk_if_then_else ?(info=Dummy) cond then_ else_ = Term.mk_fsym_app IfThenElse [cond; then_; else_] ~info
  let mk_eq ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym Eq) [t1; t2] ~info
  let mk_neq ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym Neq) [t1; t2] ~info
  let mk_true ?(info=Dummy) () = of_atom (Atom.mk_true ()) ~info
  let mk_false ?(info=Dummy) () = of_atom (Atom.mk_false ()) ~info
  let mk_eqs ts =
    List.concat_mapi ts ~f:(fun i t ->
        List.foldi ts ~init:[] ~f:(fun i1 ret t1 ->
            if i1 <= i || Stdlib.(Term.sort_of t <> Term.sort_of t1) then ret
            else mk_eq t t1 :: ret))
  let ifte phi t1 t2 = mk_if_then_else (of_formula phi) t1 t2
  let rec neg = function
    | Term.Var (x, s, _) ->
      assert (Term.is_bool_sort s); of_atom @@ Atom.of_neg_bool_var x
    | Term.FunApp (Formula phi, _, _) ->
      of_formula @@ Formula.negate phi
    | Term.FunApp (IfThenElse, [t1; t2; t3], _) ->
      mk_if_then_else t1 (neg t2) (neg t3)
    | term ->
      failwith @@ sprintf "[T_bool.neg] %s not supported" @@ Term.str_of term

  (** Observation *)
  let is_atom = function
    | Term.FunApp (Formula (Formula.Atom (_, _)), [], _) -> true
    | _ -> false
  let is_true = function
    | Term.FunApp (Formula (Formula.Atom (Atom.True _, _)), [], _) -> true
    | _ -> false
  let is_false = function
    | Term.FunApp (Formula (Formula.Atom (Atom.False _, _)), [], _) -> true
    | _ -> false

  let is_sbool t = Term.is_bool_sort @@ Term.sort_of t

  (** Destruction *)
  let let_bool = function
    | Term.FunApp (Formula (Formula.Atom (Atom.True _, _)), [], _) -> true
    | Term.FunApp (Formula (Formula.Atom (Atom.False _, _)), [], _) -> false
    | _ -> assert false
end

and T_int : Type.T_intType
  with type term := Term.t
   and type atom := Atom.t
= struct
  type fun_sym +=
    | Int of Z.t
    | Add | Sub | Mult | Div | Mod | Neg | Abs | Power | Rem
  type pred_sym += Leq | Geq | Lt | Gt | PDiv | NPDiv
  type Sort.t += SInt | SRefInt | SUnrefInt

  (** Construction *)
  let mk_int ?(info=Dummy) n = Term.mk_fsym_app (Int n) [] ~info
  let from_int ?(info=Dummy) n = mk_int (Z.of_int n) ~info
  let zero ?(info=Dummy) () = mk_int Z.zero ~info
  let one ?(info=Dummy) () = mk_int Z.one ~info
  let hundred ?(info=Dummy) () = from_int 100 ~info
  let mk_add ?(info=Dummy) t1 t2 = Term.mk_fsym_app Add [t1; t2] ~info
  let mk_sub ?(info=Dummy) t1 t2 = Term.mk_fsym_app Sub [t1; t2] ~info
  let mk_mult ?(info=Dummy) t1 t2 = Term.mk_fsym_app Mult [t1; t2] ~info
  let mk_div ?(info=Dummy) t1 t2 = Term.mk_fsym_app Div [t1; t2] ~info
  let mk_mod ?(info=Dummy) t1 t2 = Term.mk_fsym_app Mod [t1; t2] ~info
  let mk_neg ?(info=Dummy) t = Term.mk_fsym_app Neg [t] ~info
  (*  let mk_neg ?(info=Dummy) t =
      mk_mult (mk_int (Z.neg Z.one) ~info) t ~info*)

  let mk_abs ?(info=Dummy) t = Term.mk_fsym_app Abs [t] ~info
  let mk_power ?(info=Dummy) t1 t2 = Term.mk_fsym_app Power [t1; t2] ~info
  let mk_rem ?(info=Dummy) t1 t2 = Term.mk_fsym_app Rem [t1; t2] ~info

  let mk_sum ?(info=Dummy) t ts =
    List.fold ~init:t ts ~f:(fun t1 t2 -> mk_add t1 t2 ~info)
  let mk_prod ?(info=Dummy) t ts =
    List.fold ~init:t ts ~f:(fun t1 t2 -> mk_mult t1 t2 ~info)

  let mk_leq ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym Leq) [t1; t2] ~info
  let mk_geq ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym Geq) [t1; t2] ~info
  let mk_lt ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym Lt) [t1; t2] ~info
  let mk_gt ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym Gt) [t1; t2] ~info
  let mk_pdiv ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym PDiv) [t1; t2] ~info
  let mk_npdiv ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym NPDiv) [t1; t2] ~info

  let abs t = T_bool.ifte (Formula.geq t (zero ())) t (mk_neg t)
  let l1_norm ts = mk_sum (zero ()) (List.map ~f:abs ts)
  let l2_norm_sq ts = mk_sum (zero ()) (List.map ~f:(fun t -> mk_mult t t) ts)

  (** Observation *)
  let is_int = function Term.FunApp (Int _, [], _) -> true | _ -> false
  let is_sint t = Term.is_int_sort @@ Term.sort_of t
  let is_add = function Term.FunApp (Add, _, _) -> true | _ -> false
  let is_sub = function Term.FunApp (Sub, _, _) -> true | _ -> false
  let is_mult = function Term.FunApp (Mult, _, _) -> true | _ -> false
  let is_div = function Term.FunApp (Div, _, _) -> true | _ -> false
  let is_mod = function Term.FunApp (Mod, _, _) -> true | _ -> false
  let is_neg = function Term.FunApp (Neg, _, _) -> true | _ -> false
  let is_abs = function Term.FunApp (Abs, _, _) -> true | _ -> false
  let is_power = function Term.FunApp (Power, _, _) -> true | _ -> false
  let is_rem = function Term.FunApp (Rem, _, _) -> true | _ -> false
  let is_zero = function Term.FunApp (Int i, _, _) when Z.Compare.(i = Z.zero) -> true | _ -> false
  let is_unit = function Term.FunApp (Int i, _, _) when Z.Compare.(i = Z.one) -> true | _ -> false
  let is_minus_one = function Term.FunApp (Int i, _, _) when Z.Compare.(i = Z.minus_one) -> true | _ -> false

  let psym_of_atom = function
    | Atom.App (Predicate.Psym sym, _, _) -> sym
    | _ -> assert false
  let is_leq atom = Stdlib.(Leq = psym_of_atom atom)
  let is_geq atom = Stdlib.(Geq = psym_of_atom atom)
  let is_lt atom = Stdlib.(Lt = psym_of_atom atom)
  let is_gt atom = Stdlib.(Gt = psym_of_atom atom)
  let is_pdiv atom = Stdlib.(PDiv = psym_of_atom atom)
  let is_npdiv atom = Stdlib.(NPDiv = psym_of_atom atom)

  (** Destruction *)
  let let_int = function
    | Term.FunApp (Int n, [], _) -> n
    | _ -> assert false
  let let_add = function
    | Term.FunApp (Add, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_sub = function
    | Term.FunApp (Sub, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_mult = function
    | Term.FunApp (Mult, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_div = function
    | Term.FunApp (Div, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_mod = function
    | Term.FunApp (Mod, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_neg = function
    | Term.FunApp (Neg, [t], info) -> t, info
    | _ -> assert false
  let let_abs = function
    | Term.FunApp (Abs, [t], info) -> t, info
    | _ -> assert false
  let let_power = function
    | Term.FunApp (Power, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rem = function
    | Term.FunApp (Rem, [t1;t2], info) -> t1, t2, info
    | _ -> assert false

  let let_leq = function
    | Atom.App (Predicate.Psym Leq, [t1; t2], info) -> t1, t2 , info
    | _ -> assert false
  let let_geq = function
    | Atom.App (Predicate.Psym Geq, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_lt = function
    | Atom.App (Predicate.Psym Lt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_gt = function
    | Atom.App (Predicate.Psym Gt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_pdiv = function
    | Atom.App (Predicate.Psym PDiv, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_npdiv = function
    | Atom.App (Predicate.Psym NPDiv, [t1; t2], info) -> t1, t2, info
    | _ -> assert false

  let neg_fsym = function
    | Add -> Sub | Sub -> Add | Mult -> Div | Div -> Mult
    | _ -> failwith "undefined "
end

and T_real : Type.T_realType
  with type rterm := Term.t
   and type ratom := Atom.t
= struct
  type fun_sym +=
    | Real of Q.t | Alge of Term.t * int
    | RAdd | RSub | RMult | RDiv | RNeg | RAbs | RPower
  type pred_sym += RLeq | RGeq | RLt | RGt
  type Sort.t += SReal

  (** Construction *)
  let mk_real ?(info=Dummy) f = Term.mk_fsym_app (Real f) [] ~info
  let mk_alge ?(info=Dummy) t n = Term.mk_fsym_app (Alge (t, n)) [] ~info
  let rzero ?(info=Dummy) () = mk_real Q.zero ~info
  let rone ?(info=Dummy) () = mk_real Q.one ~info
  let mk_radd ?(info=Dummy) t1 t2 = Term.mk_fsym_app RAdd [t1; t2] ~info
  let mk_rsub ?(info=Dummy) t1 t2 = Term.mk_fsym_app RSub [t1; t2] ~info
  let mk_rmult ?(info=Dummy) t1 t2 = Term.mk_fsym_app RMult [t1; t2] ~info
  let mk_rdiv ?(info=Dummy) t1 t2 = Term.mk_fsym_app RDiv [t1; t2] ~info
  let mk_rneg ?(info=Dummy) t = Term.mk_fsym_app RNeg [t] ~info
  (*  let mk_neg ?(info=Dummy) t =
      mk_mult (mk_int (Z.neg Z.one) ~info) t ~info*)

  let mk_rabs ?(info=Dummy) t = Term.mk_fsym_app RAbs [t] ~info
  let mk_rpower ?(info=Dummy) t1 t2 = Term.mk_fsym_app RPower [t1; t2] ~info

  let mk_rsum ?(info=Dummy) t ts =
    List.fold ~init:t ts ~f:(fun t1 t2 -> mk_radd t1 t2 ~info)
  let mk_rprod ?(info=Dummy) t ts =
    List.fold ~init:t ts ~f:(fun t1 t2 -> mk_rmult t1 t2 ~info)

  let mk_rleq ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym RLeq) [t1; t2] ~info
  let mk_rgeq ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym RGeq) [t1; t2] ~info
  let mk_rlt ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym RLt) [t1; t2] ~info
  let mk_rgt ?(info=Dummy) t1 t2 = Atom.mk_app (Predicate.Psym RGt) [t1; t2] ~info

  let l1_norm ts = mk_rsum (rzero ()) (List.map ~f:mk_rabs ts)
  let l2_norm_sq ts = mk_rsum (rzero ()) (List.map ~f:(fun t -> mk_rmult t t) ts)

  (** Observation *)
  let is_real = function Term.FunApp (Real _, [], _) -> true | _ -> false
  let is_sreal t = Term.is_real_sort @@ Term.sort_of t
  let is_alge = function Term.FunApp (Alge _, [], _) -> true | _ -> false
  let is_radd = function Term.FunApp (RAdd, _, _) -> true | _ -> false
  let is_rsub = function Term.FunApp (RSub, _, _) -> true | _ -> false
  let is_rmult = function Term.FunApp (RMult, _, _) -> true | _ -> false
  let is_rdiv = function Term.FunApp (RDiv, _, _) -> true | _ -> false
  let is_rneg = function Term.FunApp (RNeg, _, _) -> true | _ -> false
  let is_rabs = function Term.FunApp (RAbs, _, _) -> true | _ -> false
  let is_rpower = function Term.FunApp (RPower, _, _) -> true | _ -> false
  let is_rzero = function Term.FunApp ((Real r), _, _) when Q.(r = zero) -> true | _ -> false
  let is_runit = function Term.FunApp (Real r, _, _) when Q.(r = one) -> true | _ -> false
  let is_rminus_one = function Term.FunApp (Real r, _, _) when Q.(r = minus_one) -> true | _ -> false

  let psym_of_atom = function
    | Atom.App (Predicate.Psym sym, _, _) -> sym
    | _ -> assert false
  let is_rleq atom = Stdlib.(RLeq = psym_of_atom atom)
  let is_rgeq atom = Stdlib.(RGeq = psym_of_atom atom)
  let is_rlt atom = Stdlib.(RLt = psym_of_atom atom)
  let is_rgt atom = Stdlib.(RGt = psym_of_atom atom)

  (** Destruction *)
  let let_real = function
    | Term.FunApp (Real f, [], _) -> f
    | t -> failwith @@ Printf.sprintf "%s is not real" @@ Term.str_of t
  let let_alge = function
    | Term.FunApp (Alge (t, n), [], _) -> t, n
    | _ -> assert false
  let let_radd = function
    | Term.FunApp (RAdd, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rsub = function
    | Term.FunApp (RSub, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rmult = function
    | Term.FunApp (RMult, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rdiv = function
    | Term.FunApp (RDiv, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rneg = function
    | Term.FunApp (RNeg, [t], info) -> t, info
    | _ -> assert false
  let let_rabs = function
    | Term.FunApp (RAbs, [t], info) -> t, info
    | _ -> assert false
  let let_rpower = function
    | Term.FunApp (RPower, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false

  let let_rleq = function
    | Atom.App (Predicate.Psym RLeq, [t1; t2], info) -> t1, t2 , info
    | _ -> assert false
  let let_rgeq = function
    | Atom.App (Predicate.Psym RGeq, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_rlt = function
    | Atom.App (Predicate.Psym RLt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_rgt = function
    | Atom.App (Predicate.Psym RGt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
end

and T_real_int : Type.T_real_intType
  with type term := Term.t
   and type rterm := Term.t
   and type atom := Atom.t
   and type ratom := Atom.t
= struct
  include T_int
  include T_real

  type fun_sym += ToReal | ToInt
  type pred_sym += IsInt

  let mk_to_real ?(info=Dummy) t = Term.mk_fsym_app ToReal [t] ~info
  let mk_to_int ?(info=Dummy) t = Term.mk_fsym_app ToInt [t] ~info

  let mk_is_int ?(info=Dummy) t = Atom.mk_app (Predicate.Psym IsInt) [t] ~info

  let is_to_real = function Term.FunApp (ToReal, _, _) -> true | _ -> false
  let is_to_int = function Term.FunApp (ToInt, _, _) -> true | _ -> false

  let psym_of_atom = function
    | Atom.App (Predicate.Psym sym, _, _) -> sym
    | _ -> assert false
  let is_is_int atom = Stdlib.(IsInt = psym_of_atom atom)

  let let_to_real = function
    | Term.FunApp (ToReal, [t], info) -> t, info
    | _ -> assert false
  let let_to_int = function
    | Term.FunApp (ToInt, [t], info) -> t, info
    | _ -> assert false
  let let_is_int = function
    | Atom.App (Predicate.Psym IsInt, [t], info) -> t, info
    | _ -> assert false

  let origin_of sorts = List.map sorts ~f:(function
      | T_int.SInt -> T_int.zero ()
      | T_real.SReal -> T_real.rzero ()
      | T_bool.SBool -> T_bool.mk_false ()
      | _ -> failwith "not supported")
end
and T_num : Type.T_numType
  with type term := Term.t
   and type rterm := Term.t
   and type atom := Atom.t
   and type ratom := Atom.t
= struct
  include T_real_int
  type fun_sym +=
    | Value of string * Ident.svar
    | NAdd of Ident.svar
    | NSub of Ident.svar
    | NMult of Ident.svar
    | NDiv of Ident.svar
    | NPower of Ident.svar
    | NNeg of Ident.svar

  type pred_sym +=
    | NLeq of Ident.svar
    | NGeq of Ident.svar
    | NLt of Ident.svar
    | NGt of Ident.svar

  exception NotValue

  let mk_value ?(info=Dummy) ident =
    if String.is_prefix ident ~prefix:"e" || String.is_prefix ident ~prefix:"E" then
      raise NotValue
    else
      try let _ = Z.of_string ident in Term.mk_fsym_app (Value (ident, Ident.mk_fresh_svar ())) [] ~info with _ ->
      try let _ = Q.of_string ident in Term.mk_fsym_app (Value (ident, Ident.mk_fresh_svar ())) [] ~info with _ ->
      try let _ = Q.of_float @@ float_of_string ident in Term.mk_fsym_app (Value (ident, Ident.mk_fresh_svar ())) [] ~info with _ ->
        raise NotValue
  let mk_nadd ?(info=Dummy) t1 t2 = Term.mk_fsym_app (NAdd (Ident.mk_fresh_svar ())) [t1;t2] ~info
  let mk_nsub ?(info=Dummy) t1 t2 = Term.mk_fsym_app (NSub (Ident.mk_fresh_svar ())) [t1;t2] ~info
  let mk_nmult ?(info=Dummy) t1 t2 = Term.mk_fsym_app (NMult (Ident.mk_fresh_svar ())) [t1;t2] ~info
  let mk_ndiv ?(info=Dummy) t1 t2 = Term.mk_fsym_app (NDiv (Ident.mk_fresh_svar ())) [t1;t2] ~info
  let mk_npower ?(info=Dummy) t1 t2 = Term.mk_fsym_app (NPower (Ident.mk_fresh_svar ())) [t1;t2] ~info
  let mk_nneg ? (info=Dummy) t1 = Term.mk_fsym_app (NNeg (Ident.mk_fresh_svar ())) [t1] ~info
  let mk_ngeq ?(info=Dummy) t1 t2 = Atom.mk_psym_app (NGeq (Ident.mk_fresh_svar ())) [t1;t2] ~info
  let mk_nleq ?(info=Dummy) t1 t2 = Atom.mk_psym_app (NLeq (Ident.mk_fresh_svar ())) [t1;t2] ~info
  let mk_ngt ?(info=Dummy) t1 t2 = Atom.mk_psym_app (NGt (Ident.mk_fresh_svar ())) [t1;t2] ~info
  let mk_nlt ?(info=Dummy) t1 t2 = Atom.mk_psym_app (NLt (Ident.mk_fresh_svar ())) [t1;t2] ~info

  let is_nadd = function Term.FunApp (NAdd _, _, _) -> true | _ -> false
  let is_nsub = function Term.FunApp (NSub _, _, _) -> true | _ -> false
  let is_nmult = function Term.FunApp (NMult _, _, _) -> true | _ -> false
  let is_ndiv = function Term.FunApp (NDiv _, _, _) -> true | _ -> false
  let is_npower = function Term.FunApp (NPower _, _, _) -> true | _ -> false
  let is_nneg = function Term.FunApp (NNeg _, _, _) -> true | _ -> false
  let is_ngeq = function Atom.App (Predicate.Psym NGeq _, _, _) -> true | _ -> false
  let is_nleq = function Atom.App (Predicate.Psym NLeq _, _, _) -> true | _ -> false
  let is_ngt = function Atom.App (Predicate.Psym NGt _, _, _) -> true | _ -> false
  let is_nlt = function Atom.App (Predicate.Psym NLt _, _, _) -> true | _ -> false

  let let_nadd = function Term.FunApp (NAdd _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nsub = function Term.FunApp (NSub _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nmult = function Term.FunApp (NMult _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_ndiv = function Term.FunApp (NDiv _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_npower = function Term.FunApp (NPower _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nneg = function Term.FunApp (NNeg _, [t1], info) -> t1, info | _ -> assert false
  let let_ngeq = function Atom.App (Predicate.Psym NGeq _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nleq = function Atom.App (Predicate.Psym NLeq _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_ngt = function Atom.App (Predicate.Psym NGt _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nlt = function Atom.App (Predicate.Psym NLt _, [t1; t2], info) -> t1, t2, info | _ -> assert false

  let is_value = function Term.FunApp (Value _, _, _) -> true | _ -> false

  let fsym_of_num_fsym fsym = function
    | T_int.SInt -> begin
        match fsym with
        | Value (value, _) -> begin
            try T_int.Int (Z.of_string value) with _ ->
            try T_int.Int (Z.of_int (Q.to_int @@ Q.of_string value)) with _ ->
            try T_int.Int (Z.of_int @@ Q.to_int @@ Q.of_float @@ float_of_string value) with _ ->
              raise NotValue
          end
        | NAdd _ -> T_int.Add
        | NSub _ -> T_int.Sub
        | NMult _ -> T_int.Mult
        | NDiv _ -> T_int.Div
        | NPower _ -> T_int.Power
        | NNeg _ -> T_int.Neg
        | _ -> fsym
      end
    | T_real.SReal -> begin
        match fsym with
        | Value (value, _) -> begin
            try T_real.Real (Q.of_string value) with _ ->
            try T_real.Real (Q.of_float @@ float_of_string value) with _ ->
              raise NotValue
          end
        | NAdd _ -> T_real.RAdd
        | NSub _ -> T_real.RSub
        | NMult _ -> T_real.RMult
        | NDiv _ -> T_real.RDiv
        | NPower _ -> T_real.RPower
        | NNeg _ -> T_real.RNeg
        | _ -> fsym
      end
    | Sort.SVar _ -> fsym
    | sort -> failwith @@ sprintf "sort %s is not num" (Term.str_of_sort sort)
  let psym_of_num_psym psym = function
    | T_int.SInt -> begin
        match psym with
        | NGeq _ -> T_int.Geq
        | NLeq _ -> T_int.Leq
        | NGt _ -> T_int.Gt
        | NLt _ -> T_int.Lt
        | _ -> psym
      end
    | T_real.SReal -> begin
        match psym with
        | NGeq _ -> T_real.RGeq
        | NLeq _ -> T_real.RLeq
        | NGt _ -> T_real.RGt
        | NLt _ -> T_real.RLt
        | _ -> psym
      end
    | Sort.SVar _ -> psym
    | sort -> failwith @@ sprintf "sort %s is not num" (Term.str_of_sort sort)
end
and T_array : Type.T_arrayType with
  type term := Term.t and
type atom := Atom.t = struct
  type fun_sym +=
    | AStore of Sort.t * Sort.t
    | ASelect of Sort.t * Sort.t
    | AConst of Sort.t * Sort.t
  type Sort.t += SArray of Sort.t * Sort.t

  let mk_array_sort s1 s2 = SArray (s1, s2)
  let mk_select s1 s2 a i = Term.mk_fsym_app (ASelect (s1, s2)) [a; i]
  let mk_store s1 s2 a i e = Term.mk_fsym_app (AStore (s1, s2)) [a; i; e]

  let mk_const_array s1 s2 v = Term.mk_fsym_app (AConst (s1, s2)) [v]

  let index_sort_of = function SArray (si, _) -> si | _ -> failwith "not array sort"
  let elem_sort_of = function SArray (_, se) -> se | _ -> failwith "not array sort"

  let is_select = function Term.FunApp (ASelect _, _, _) -> true | _ -> false
  let is_store = function Term.FunApp (AStore _, _, _) -> true | _ -> false
  let let_select = function Term.FunApp (ASelect (s1, s2), [a; i], info) -> s1, s2, a, i, info | _ -> assert false
  let let_store = function Term.FunApp (AStore (s1, s2), [a; i; e], info) -> s1, s2, a, i, e, info | _ -> assert false

  let eval_select arr i =
    let rec aux t =
      match t with
      | Term.FunApp (AStore _, [arr1; i1; e1], _) ->
        if Stdlib.(i = i1) then begin
          (* print_endline @@ sprintf "eval select : %s [%s]->%s" (Term.str_of arr) (Term.str_of i) (Term.str_of e1); *)
          Some e1
        end else aux arr1
      | Term.FunApp (AConst _, [e1], _) ->
        (* print_endline @@ sprintf "eval select : %s [%s]->%s" (Term.str_of arr) (Term.str_of i) (Term.str_of e1);  *)
        Some e1
      (* | Term.FunApp (T_bool.Formula (Formula.Atom (atm, _)), _, _) when is_select_bool atm->
         let arr', i', _ = let_select_bool atm in
         aux @@ mk_select arr' i'
         | Term.FunApp (T_bool.Formula (Formula.Atom (atm, _)), _, _) when is_select_bool_neg atm->
         let arr', i', _ = let_select_bool_neg atm in
         aux @@ mk_select arr' i' *)
      | _ -> None
    in
    aux arr

  let rec of_arrow = function
    | Sort.SArrow (s1, (o, s2, Sort.Pure)) when Sort.is_empty_opsig o -> mk_array_sort (of_arrow s1) (of_arrow s2)
    | s -> s

  let of_fvar_app = function
    | Term.FunApp (FVar (tvar, sorts), ts, _) ->
      let arr_sort = of_arrow @@ Sort.mk_fun sorts in
      List.fold_left ts ~init:(Term.mk_var tvar arr_sort)
        ~f:(fun arr t ->
            match Term.sort_of arr with
            | SArray (s1, s2) -> mk_select s1 s2 arr t
            | _ -> failwith "of_fvar_app")
    | t -> t
end

and FunEnv : Type.FunEnvType
  with type term := Term.t
   and type formula := Formula.t
= struct
  type t = (Ident.tvar, (sort_env_list * Sort.t * Term.t * bool * Formula.t)) Map.Poly.t

  let mk_empty () = Map.Poly.empty
  let property_of (fenv:t) phi =
    if Map.Poly.is_empty fenv then Formula.mk_true ()
    else
      let recterms =
        Formula.filtered_terms_of phi ~f:(function
            | Term.FunApp (FVar (v, _), _, _) -> Map.Poly.mem fenv v
            | _ -> false)
      in
      Formula.and_of @@ Set.Poly.to_list @@
      Set.Poly.filter_map recterms ~f:(function
          | Term.FunApp (FVar (v, _), args, _) -> begin
              match Map.Poly.find fenv v with
              | Some (_, _, _, _, property) when Formula.is_bind property->
                let (_, env, phi, _) = Formula.let_bind property in
                let sub = Map.of_list_exn @@ List.map2_exn env args ~f:(fun (tvar, _) t -> (tvar, t)) in
                Some (Formula.subst sub phi)
              | _ -> None
            end
          | _ -> None)

  let defined_atom_formula_of polarity (fenv:t) phi =
    (assert (Formula.is_atom phi));
    if Map.Poly.is_empty fenv then phi
    else
      let property = property_of fenv phi in
      if Formula.is_true property then if polarity then phi else Formula.mk_neg phi
      else if polarity then Formula.mk_and property phi else Formula.mk_neg @@ Formula.mk_imply property phi

  (*assume phi is nnf*)
  let rec defined_formula_of_aux (fenv:t) phi =
    let open Formula in
    match phi with
    | Atom _ -> defined_atom_formula_of true fenv phi
    | UnaryOp (Not, phi, _) -> defined_atom_formula_of false fenv phi
    | BinaryOp (op, phi1, phi2, info) -> BinaryOp (op, defined_formula_of_aux fenv phi1, defined_formula_of_aux fenv phi2, info)
    | Bind (binder, env, phi, info) -> Bind (binder, env, defined_formula_of_aux fenv phi, info)
    | _ -> failwith "unsupported"

  let defined_formula_of (fenv:t) phi =
    if Map.Poly.is_empty fenv then phi
    else defined_formula_of_aux fenv @@ Formula.nnf_of phi

  let str_of t =
    Map.Poly.to_alist t
    |> String.concat_map_list ~sep:"\n" ~f:(fun (v, (params, _, def, is_rec, prop)) ->
        sprintf
          "let %sfun %s %s = %s\n  * property: %s"
          (if is_rec then "rec " else "")
          (Ident.name_of_tvar v)
          (String.concat_map_list ~sep:" " params ~f:(fun (x, s) ->
               sprintf "(%s:%s)" (Ident.name_of_tvar x) (Term.str_of_sort s)))
          (Term.str_of def)
          (Formula.str_of prop))
    |> sprintf "fun env:\n%s"
end
and T_dt: Type.T_dtType
  with type term := Term.t
   and type atom := Atom.t
   and type formula := Formula.t
   and type dtenv := DTEnv.t
   and type dt := Datatype.t
   and type dtcons := Datatype.cons
   and type dtsel := Datatype.sel
   and type flag := Datatype.flag
= struct
  type fun_sym +=
    | DTSel of string * Datatype.t * Sort.t
    | DTCons of string * Sort.t list * Datatype.t
  type pred_sym +=
    | IsCons of string * Datatype.t
    | NotIsCons of string * Datatype.t
  type Sort.t +=
    | SDT of Datatype.t
    | SUS of string * (Sort.t list)

  let pars_of = function SDT dt -> Datatype.args_of dt | _ -> assert false

  let mk_cons ?(info=Dummy) dt name terms =
    match Datatype.look_up_cons dt name with
    | Some cons ->
      let fsym = Datatype.fsym_of_cons dt cons in
      Term.mk_fsym_app fsym terms ~info
    | _ -> failwith @@ "unknown cons :" ^ name

  let mk_sel ?(info=Dummy) dt name term =
    match Datatype.look_up_sel dt name with
    | Some sel ->
      let fsym = Datatype.fsym_of_sel dt sel in
      Term.mk_fsym_app fsym [term] ~info
    | _ -> failwith @@ "unknown sel :" ^ name
  let mk_sel_by_cons ?(info=Dummy) dt cons_name i term =
    match Datatype.look_up_cons dt cons_name with
    | Some cons ->
      let sel = List.nth_exn (Datatype.sels_of_cons cons) i in
      let fsym = Datatype.fsym_of_sel dt sel in
      Term.mk_fsym_app fsym [term] ~info
    | _ -> failwith @@ "unknown cons :" ^ cons_name

  let mk_is_cons ?(info=Dummy) dt name term =
    Atom.mk_psym_app (IsCons (name, dt)) [term] ~info

  let mk_is_not_cons ?(info=Dummy) dt name term =
    Atom.mk_psym_app (NotIsCons (name, dt)) [term] ~info

  let sels_of_cons = function
    | DTCons (name, _, dt) ->
      (match Datatype.look_up_cons dt name with
       | Some cons -> Datatype.sels_of_cons cons
       | _ -> assert false)
    | _ -> assert false
  let is_sdt = function SDT _ -> true | _ -> false
  let is_sus = function SUS _ -> true | _ -> false
  let is_dt = function SDT dt -> Datatype.is_dt dt | _ -> false
  let is_codt = function SDT dt -> Datatype.is_dt dt | _ -> false
  let is_undef = function SUS (_, _) -> true | _ -> false

  let rec is_finite_dt ?(his=[]) sort =
    if (List.exists his ~f:(Stdlib.(=) sort)) then false
    else
      match sort with
      | SDT dt ->
        let conses = Datatype.conses_of dt in
        List.for_all conses ~f:(fun cons ->
            let args = Datatype.sorts_of_cons dt cons in
            List.for_all args ~f:(fun arg -> is_finite_dt ~his:(sort::his) arg))
      (* | T_bool.SBool -> true *)
      | _ -> false

  let is_cons = function Term.FunApp (DTCons _, _, _) -> true | _ -> false
  let is_sel = function Term.FunApp (DTSel _, _, _) -> true | _ -> false
  let is_is_cons = function Atom.App (Predicate.Psym (IsCons _), _, _) -> true | _ -> false
  let is_is_not_cons = function Atom.App (Predicate.Psym (NotIsCons _), _, _) -> true | _ -> false

  let rec mk_dummy = function
    | SDT dt when Datatype.is_dt dt -> begin
        match Datatype.look_up_base_cons dt with
        | Some cons ->
          let sorts = Datatype.sorts_of_cons dt cons in
          mk_cons dt (Datatype.name_of_cons cons) (List.map sorts ~f:mk_dummy)
        | None -> assert false
      end
    | SUS (name, _) as sort -> Term.mk_var (Ident.Tvar ("dummy_" ^ name)) sort
    | sort -> Term.mk_dummy sort

  let base_terms_of dt =
    let conses = Datatype.base_conses_of dt in
    List.map conses ~f:(fun cons -> mk_cons dt cons.name [])

  let size_of_cons t =
    let size = ref 0 in
    ignore @@ Term.map_term t ~f:(function
        | Term.FunApp (DTCons _, _, _) as t -> incr size; t | t -> t);
    !size
  let inst_unknown_sel_term simplify_term phi =
    Formula.map_term phi ~f:(fun t -> match simplify_term t with
        | Term.FunApp (DTSel (_, _, sort), _, _) -> Term.mk_dummy sort
        | t -> t)
end
and Datatype : Type.DatatypeType
  with type term := Term.t
   and type formula := Formula.t
= struct
  type sel =
    | Sel of string * Sort.t
    | InSel of string * string * Sort.t list
  type cons = {
    name : string;
    sels : sel list
  }
  type func = FCons of cons | FSel of sel
  type flag = FDt | FCodt | Undef | Alias of Sort.t
  type dt = {
    name : string;
    args : Sort.t list;
    conses : cons list
  }
  type t = {
    name : string;
    dts : dt list; (* mutually defined datatypes including name *)
    flag : flag
  }
  (*let verbose = false
    let print_endline str = if verbose then print_endline str else ()*)
  let mk_dt name args = {name = name; args = args; conses = []}
  let create name dts flag = {name = name; dts = dts; flag = flag}
  let mk_uninterpreted_datatype ?(numeral=0) name =
    let rec aux numeral =
      if numeral = 0 then []
      else Sort.mk_fresh_svar () :: aux (numeral - 1)
    in
    create name [mk_dt name @@ aux numeral] Undef
  let mk_alias name sort = create name [] (Alias sort)

  let update_name t name = { t with name = name }

  let mk_cons ?(sels=[]) name = { name = name; sels = sels }
  let mk_sel name ret_sort = Sel (name, ret_sort)
  let mk_insel name ret_name args = InSel (name, ret_name, args)
  (* let mk_poly_sel name = PolySel (name, Sort.mk_fresh_svar) *)

  let dts_of t = t.dts
  let name_of t = t.name
  let flag_of t = t.flag
  let name_of_dt (dt:dt) = dt.name
  let args_of_dt (dt:dt) = dt.args
  let conses_of_dt (dt:dt) = dt.conses
  let sels_of_cons (cons:cons) = cons.sels
  let name_of_cons (cons:cons) = cons.name
  let name_of_sel = function
    (* | PolySel (name, _, _) *)
    | Sel (name, _)
    | InSel (name, _, _) -> name

  let look_up_dt t name =
    List.find (dts_of t) ~f:(fun dt -> Stdlib.(name = name_of_dt dt))

  let dt_of t =
    match look_up_dt t @@ name_of t with
    | Some dt -> dt
    | _ -> failwith @@ sprintf "unknown dt: %s" (name_of t)

  let conses_of t = conses_of_dt @@ dt_of t
  let sels_of t =
    List.fold_left (conses_of t) ~init:[] ~f:(fun ret cons -> ret @ sels_of_cons cons)
  let args_of t = args_of_dt @@ dt_of t
  let full_name_of t =
    let name = name_of t in
    let args = args_of t in
    if List.is_empty args then name
    else
      sprintf "(%s) %s" (String.concat_map_list ~sep:", " args ~f:Term.str_of_sort) name

  let full_name_of_dt dt =
    let name = name_of_dt dt in
    let args = args_of_dt dt in
    if List.is_empty args then name
    else
      sprintf "(%s) %s" (String.concat_map_list ~sep:", " args ~f:Term.str_of_sort) name

  let short_name_of t =
    let name = String.prefix (name_of t) 1 in
    let args = args_of t in
    if List.is_empty args then name
    else
      sprintf "%s!%s" (String.concat_map_list ~sep:"" args ~f:Term.short_name_of_sort) name

  let is_dt t = match flag_of t with FDt -> true | _ -> false
  let is_codt t = match flag_of t with FCodt -> true | _ -> false
  let is_undef t = match flag_of t with Undef -> true | _ -> false
  let is_alias t = match flag_of t with Alias _ -> true | _ -> false
  let is_sel = function Sel _ -> true | _ -> false
  let is_insel = function InSel _ -> true | _ -> false
  let is_fcons = function FCons _ -> true | _ -> false
  let is_fsel = function FSel _ -> true | _ -> false

  let rec is_poly t =
    List.exists (dt_of t).args ~f:(function
        | Sort.SVar _ -> true
        | T_dt.SDT t1 -> is_poly t1
        | _ -> false)

  let update_dts t dts = { t with dts = dts }

  let rec update_dts_with_dt dts dt =
    match dts with
    | [] -> []
    | dt1 :: tl ->
      if Stdlib.(name_of_dt dt1 = name_of_dt dt) then dt :: tl
      else dt1 :: update_dts_with_dt tl dt

  let update_dt t dt = { t with dts = update_dts_with_dt (dts_of t) dt }

  let str_of_sel = function
    (* | PolySel (name, ret_sort, _) *)
    | Sel (name, ret_sort) ->
      sprintf "%s : %s" name (Term.str_of_sort ret_sort)
    | InSel (name, ret_name, args) ->
      sprintf "%s : %s" name @@ full_name_of_dt @@ mk_dt ret_name args
  let str_of_cons cons =
    let name = name_of_cons cons in
    let sels = List.map ~f:str_of_sel @@ sels_of_cons cons in
    sprintf "%s (%s)" name @@ String.concat ~sep:", " sels
  let full_str_of_sel t = function
    | Sel (name, ret_sort) ->
      sprintf "%s : %s" name (Term.str_of_sort ret_sort)
    | InSel (name, ret_name, _) ->
      sprintf "%s : %s" name @@ full_name_of @@ update_name t ret_name
  let full_str_of_cons t cons =
    let name = name_of_cons cons in
    let sels = List.map ~f:(full_str_of_sel t) @@ sels_of_cons cons in
    sprintf "%s (%s)" name @@ String.concat ~sep:", " sels
  let str_of_flag = function
    | FCodt -> "codata"
    | FDt -> "data"
    | Undef -> "undef"
    | Alias s -> sprintf "alias(%s)" (Term.str_of_sort s)
  let str_of t =
    match t.flag with
    | Undef -> "u'" ^ t.name
    | Alias s -> sprintf "%s(%s)" t.name (Term.str_of_sort s)
    | _ ->
      sprintf "%s where [%s]" (full_name_of t) @@
      String.concat_map_list ~sep:" and " (dts_of t) ~f:(fun dt ->
          sprintf "%s %s = %s"
            (str_of_flag @@ flag_of t)
            (full_name_of_dt dt)
          (*String.concat_map_list ~sep:" " ~f:Term.str_of_sort @@ args_of_dt dt)*) @@
          String.concat_map_list ~sep:" | " ~f:str_of_cons @@ conses_of_dt dt)

  (*let str_of_sorts sorts = String.concat_map_list ~sep:" " sorts ~f:Term.str_of_sort*)
  let rec update_dt_args t dt args his =
    (*(match his with
      | [_] ->
       print_endline @@ sprintf ">>>>>update dt args:%s with {%s}" (full_name_of_dt dt) (str_of_sorts args)
      | _ ->
       print_endline @@ sprintf ">>>>>>>>>>>update dt args:%s with {%s}" (full_name_of_dt dt) (str_of_sorts args));*)
    let conses' =
      List.fold2_exn (args_of_dt dt) args ~init:(conses_of_dt dt) ~f:(fun conses arg1 arg ->
          List.map conses ~f:(fun cons ->
              let sels' =
                List.map (sels_of_cons cons) ~f:(function
                    | Sel (name, (Sort.SVar _ as svar)) when Stdlib.(svar = arg1) -> begin
                        match arg with
                        | T_dt.SDT t1 -> begin
                            match look_up_dt t (name_of t1) with
                            | Some _ -> InSel (name, name_of t1, args_of t1)
                            | _ -> Sel (name, arg)
                          end
                        | _ -> Sel (name, arg)
                      end
                    | InSel (name, ret_name, args1) ->
                      InSel (name, ret_name, if Stdlib.(ret_name = name_of_dt dt) then args else args1)
                    | sel -> sel)
              in
              { cons with sels = sels' }))
    in
    List.fold_left conses' ~init:t ~f:(fun t cons ->
        List.fold_left (sels_of_cons cons) ~init:t ~f:(fun t -> function
            | Sel _ -> t
            | InSel (_, ret_sort, args) ->
              if not @@ List.exists his ~f:(Stdlib.(=) ret_sort) then
                let t', dt' = update_dt_args (update_name t ret_sort) (dt_of @@ update_name t ret_sort) args (ret_sort :: his) in
                update_name (update_dt t' dt') (name_of t)
              else t)),
    { dt with args = args; conses = conses' }
  and update_args t args =
    let dt = dt_of t in
    (*print_endline @@ sprintf "update dt args: %s with {%s}"
      (full_name_of_dt dt) (str_of_sorts args);*)
    let omap, smap, emap =
      let omaps, smaps, emaps =
        List.unzip3 @@ List.map2_exn (args_of_dt dt) args ~f:Term.pat_match_sort
      in
      Map.force_merge_list omaps,
      Map.force_merge_list smaps,
      Map.force_merge_list emaps
    in
    let ret = update_dt t @@ subst_dt (omap, smap, emap) dt in
    (*print_endline @@ sprintf "after update: %s" @@ str_of ret;*)
    ret
  and subst_sorts_dt smap dt =
    { dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            { cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                    | InSel (name, ret_name, args) ->
                      InSel (name, ret_name, List.map args ~f:(Term.subst_sorts_sort smap))
                    | Sel (name, ret_sort) ->
                      Sel (name, Term.subst_sorts_sort smap ret_sort)) });
      args = List.map (args_of_dt dt) ~f:(Term.subst_sorts_sort smap) }
  and subst_conts_dt emap dt =
    { dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            { cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                    | InSel (name, ret_name, args) ->
                      InSel (name, ret_name, List.map args ~f:(Term.subst_conts_sort emap))
                    | Sel (name, ret_sort) ->
                      Sel (name, Term.subst_conts_sort emap ret_sort)) });
      args = List.map (args_of_dt dt) ~f:(Term.subst_conts_sort emap) }
  and subst_opsigs_dt omap dt =
    { dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            { cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                    | InSel (name, ret_name, args) ->
                      InSel (name, ret_name, List.map args ~f:(Term.subst_opsigs_sort omap))
                    | Sel (name, ret_sort) ->
                      Sel (name, Term.subst_opsigs_sort omap ret_sort)) });
      args = List.map (args_of_dt dt) ~f:(Term.subst_opsigs_sort omap) }
  and subst_dt maps dt =
    { dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            { cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                    | InSel (name, ret_name, args) ->
                      let args = List.map args ~f:(Term.subst_sort maps) in
                      InSel (name, ret_name, args)
                    | Sel (name, ret_sort) ->
                      Sel (name, Term.subst_sort maps ret_sort)) });
      args = List.map (args_of_dt dt) ~f:(Term.subst_sort maps) }
  let subst_sorts smap dt =
    update_args dt @@ List.map ~f:(Term.subst_sorts_sort smap) @@ args_of dt
  let subst_conts emap dt =
    update_args dt @@ List.map ~f:(Term.subst_conts_sort emap) @@ args_of dt
  let subst_opsigs omap dt =
    update_args dt @@ List.map ~f:(Term.subst_opsigs_sort omap) @@ args_of dt
  let subst maps dt =
    update_args dt @@ List.map ~f:(Term.subst_sort maps) @@ args_of dt

  let full_dts_of t =
    let name = name_of t in
    dts_of @@
    List.fold_left (conses_of t) ~init:t ~f:(fun ret cons ->
        List.fold_left (sels_of_cons cons) ~init:ret ~f:(fun ret -> function
            | InSel (_, ret_name, args) ->
              if Stdlib.(name <> ret_name) then update_args (update_name ret ret_name) args else ret
            | Sel _ -> ret))

  let update_conses t conses = update_dt t { (dt_of t) with conses = conses }

  let add_cons t cons =
    let dt = dt_of t in
    let conses = conses_of_dt dt in
    update_dt t {dt with conses = cons :: conses}

  let add_sel cons sel =
    let sels = sels_of_cons cons in
    { cons with sels = sel::sels }

  let look_up_cons t name =
    conses_of t |> List.find ~f:(fun cons -> Stdlib.(name = name_of_cons cons))

  let look_up_sel_of_cons cons name =
    sels_of_cons cons |> List.find ~f:(fun sel -> Stdlib.(name = name_of_sel sel))

  let look_up_sel t name =
    List.fold_left (conses_of t) ~init:None ~f:(fun ret cons ->
        match ret with
        | None -> List.find (sels_of_cons cons) ~f:(fun sel -> Stdlib.(name = name_of_sel sel))
        | _ -> ret)

  let look_up_cons_of_sel t name =
    List.find (conses_of t) ~f:(fun cons ->
        List.exists (sels_of_cons cons) ~f:(fun sel -> Stdlib.(name = name_of_sel sel)))

  let look_up_func t name =
    match look_up_cons t name with
    | Some cons -> Some (FCons cons)
    | None ->
      match look_up_sel t name with
      | Some sel -> Some (FSel sel)
      | None -> None

  let sort_of t =
    match flag_of t with
    | Undef -> T_dt.SUS (name_of t, args_of t)
    | Alias s -> s
    | _ -> T_dt.SDT t
  let sort_of_sel t = function
    | Sel (_, sort) -> sort
    | InSel (_, ret_name, args) ->
      match look_up_dt t ret_name with
      | Some _ -> sort_of @@ update_args (update_name t ret_name) args
      | None -> failwith @@ sprintf "unknown sort: %s" ret_name
  let sorts_of_cons t cons =
    List.map (sels_of_cons cons) ~f:(sort_of_sel t)
  let sorts_of_cons_name t cons_name =
    match look_up_cons t cons_name with
    | Some cons -> sorts_of_cons t cons
    | _ -> failwith @@ sprintf "%s not found" cons_name

  let svs_of t = Set.Poly.union_list @@ List.map ((*ToDo*)dt_of t).args ~f:Term.svs_of_sort
  let evs_of t = Set.Poly.union_list @@ List.map ((*ToDo*)dt_of t).args ~f:Term.evs_of_sort
  let rvs_of t = Set.Poly.union_list @@ List.map ((*ToDo*)dt_of t).args ~f:Term.rvs_of_sort
  let fresh_conts_sort_dt dt =
    { dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            { cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                    | InSel (name, ret_name, args) ->
                      InSel (name, ret_name, List.map args ~f:Term.fresh_conts_sort)
                    | Sel (name, ret_sort) ->
                      Sel (name, Term.fresh_conts_sort ret_sort)) });
      args = List.map (args_of_dt dt) ~f:Term.fresh_conts_sort }
  let fresh_conts_sort t = { t with dts = List.map ~f:fresh_conts_sort_dt t.dts }
  let fresh_rvs_sort_dt dt =
    { dt with
      conses =
        List.map (conses_of_dt dt) ~f:(fun cons ->
            { cons with
              sels =
                List.map (sels_of_cons cons) ~f:(function
                    | InSel (name, ret_name, args) ->
                      InSel (name, ret_name, List.map args ~f:Term.fresh_rvs_sort)
                    | Sel (name, ret_sort) ->
                      Sel (name, Term.fresh_rvs_sort ret_sort)) });
      args = List.map (args_of_dt dt) ~f:Term.fresh_rvs_sort }
  let fresh_rvs_sort t = { t with dts = List.map ~f:fresh_rvs_sort_dt t.dts }

  let is_finite t =
    let conses = conses_of t in
    not @@ List.exists conses ~f:(fun cons ->
        let args = sorts_of_cons t cons in
        List.for_all args ~f:(fun arg -> Stdlib.(arg = T_dt.SDT t) && T_dt.is_finite_dt arg))

  let rec is_singleton = function
    | T_dt.SDT t as sort ->
      (match conses_of t with
       | [cons] ->
         List.for_all (sorts_of_cons t cons) ~f:(fun arg ->
             Stdlib.(arg = sort) || is_singleton arg)
       | _ -> false)
    | _ -> false

  let fresh_of t =
    let dts' =
      List.map (dts_of t) ~f:(fun dt ->
          let args' =
            List.map (args_of_dt dt) ~f:(function Sort.SVar _ -> Sort.mk_fresh_svar () | arg -> arg)
          in
          snd @@ update_dt_args t dt args' [])
    in
    { t with dts = dts' }

  let fsym_of_cons t cons =
    (* let t = fresh_of t in *)
    match look_up_cons t @@ name_of_cons cons with
    | Some cons -> T_dt.DTCons (name_of_cons cons, sorts_of_cons t cons, t)
    | None -> assert false

  let fsym_of_sel t sel =
    (* let t = fresh_of t in *)
    match look_up_sel t @@ name_of_sel sel with
    | None -> assert false
    | Some sel ->
      match sel with
      | Sel (name, ret_sort) -> T_dt.DTSel (name, t, ret_sort)
      | InSel (name, ret_name, args) ->
        match look_up_dt t ret_name with
        | Some _ -> T_dt.DTSel (name, t, sort_of @@ update_args (update_name t ret_name) args)
        | None -> failwith @@ sprintf "unknown dt sort:%s" ret_name

  let fsym_of_func t func =
    match func with
    | FCons cons -> fsym_of_cons t cons
    | FSel sel -> fsym_of_sel t sel

  let look_up_base_cons t =
    let has_direct_base t =
      let conses = conses_of t in
      List.exists conses ~f:(fun cons ->
          let sels = sels_of_cons cons in
          List.for_all sels ~f:(function Sel _ -> true | InSel _ -> false))
    in
    let rec look_up_other_base t his=
      if List.exists his ~f:(fun t1 -> Stdlib.(name_of t = name_of t1)) then None
      else
        conses_of t
        |> List.sort ~compare:(fun cons1 cons2 ->
            let sels1, sels2 = sels_of_cons cons1, sels_of_cons cons2 in
            if List.length sels1 < List.length sels2 then - 1
            else if List.length sels1 > List.length sels2 then 1
            else 0)
        |> List.find ~f:(fun cons ->
            let sels = sels_of_cons cons in
            List.for_all sels ~f:(function
                | Sel _ -> true
                | InSel (_, ret_name, _) ->
                  let ret_dt = update_name t ret_name in
                  if has_direct_base ret_dt then true
                  else Option.is_some @@ look_up_other_base ret_dt (t :: his)))
    in
    let conses = conses_of t in
    List.find conses ~f:(fun cons ->
        let sels = sels_of_cons cons in
        List.for_all sels ~f:(function
            | Sel _ -> true
            | InSel (_, ret_name, _) -> Option.is_some @@ look_up_other_base (update_name t ret_name) [t]))
  let size_fun_var_of dt = Ident.Tvar (sprintf "SizeOf_%s" (name_of dt))

  let size_of_cons dt cons =
    1 + (List.length @@
         List.filter ~f:(fun sel -> T_dt.is_sdt @@ sort_of_sel dt sel) @@
         sels_of_cons cons)
  let min_size_of sort =
    match sort with
    | T_dt.SDT dt ->
      let conses = conses_of dt in
      let sizes = List.map conses ~f:(size_of_cons dt) in
      List.hd_exn @@ List.sort sizes ~compare:(Int.compare)
    | _ -> 0
  let base_conses_of t =
    let conses = conses_of t in
    List.filter conses ~f:(fun cons -> List.is_empty @@ sels_of_cons cons)
  let used_dt_and_sorts_of dt =
    let rec inner visited dt ret =
      if Set.Poly.mem visited dt then (visited, ret)
      else
        let visited = Set.Poly.add visited dt in
        let conses = conses_of dt in
        let sorts = Set.Poly.of_list @@ List.concat_map conses ~f:(sorts_of_cons dt) in
        let ret = Set.Poly.union ret sorts in
        let dts = Set.Poly.filter_map sorts ~f:(function T_dt.SDT dt -> Some dt | _ -> None) in
        Set.Poly.fold dts ~init:(visited, ret) ~f:(fun (visited, ret) dt -> inner visited dt ret)
    in
    inner Set.Poly.empty dt Set.Poly.empty

  (** TODO: Now assume [dt] is a monotype datatype, support polytype in future *)
  (**
      let rec SizeOf_dt (x:dt) =
        if is_cons_0 x then 1 + SizeOf_(typeof(sel_01))(sel_01(x)) + ... + SizeOf_(typeof(sel_0n))(sel_0n(x))
        ...
        else if is_cons_m x then 1 + SizeOf(typeof(sel_m1))(sel_m1(x)) + ... + SizeOf(typeof(sel_mp))(sel_mp(x))
        else 1

      property:
        forall x:dt. (is_cons_0 x => SizeOf_dt(x) >= 1 + |sels_0|) /\ ... /\ (is_cons_m x => SizeOf_dt(x) >= 1 + |sels_m|)*)
  let size_fun_of dt =
    let term_of_sel x sel =
      match sort_of_sel dt sel with
      | T_dt.SDT dt1 ->
        let t = T_dt.mk_sel dt (name_of_sel sel) x in
        Term.mk_fvar_app (size_fun_var_of dt1) [T_dt.SDT dt1; T_int.SInt] [t]
      | _ -> T_int.zero ()
    in
    let conses = conses_of dt in
    let fun_var = size_fun_var_of dt in
    let x = Term.mk_var (Ident.Tvar "x") (T_dt.SDT dt) in
    let params = [Ident.Tvar "x", T_dt.SDT dt] in
    let def =
      List.fold_right conses ~init:(T_int.zero ()) ~f:(fun cons acc ->
          let sels = sels_of_cons cons in
          T_bool.ifte (Formula.mk_atom @@ T_dt.mk_is_cons dt cons.name x)
            (List.fold sels ~init:(T_int.one ()) ~f:(fun acc sel -> T_int.mk_add acc (term_of_sel x sel)))
            acc)
    in
    let prop =
      Formula.mk_forall params @@
      Formula.and_of @@
      List.map conses ~f:(fun cons ->
          let min_size =
            List.map (sels_of_cons cons) ~f:(fun sel ->
                min_size_of @@ sort_of_sel dt sel)
            |> List.fold ~init:1 ~f:(+)
          in
          Formula.mk_imply (Formula.mk_atom @@ T_dt.mk_is_cons dt cons.name x) @@
          Formula.mk_atom @@
          T_int.mk_geq
            (Term.mk_fvar_app fun_var (List.map ~f:snd params @ [T_int.SInt]) [x])
            (T_int.mk_int @@ Z.of_int min_size))
    in
    (fun_var, (params, T_int.SInt, def, true, prop))

  let app_size_fun dt x =
    let fun_var = size_fun_var_of dt in
    Term.mk_fvar_app fun_var [T_dt.SDT dt; T_int.SInt] [x]

  let pat_match_sort dt1 dt2 =
    if String.(dt1.name = dt2.name) then
      let omaps, smaps, emaps =
        List.unzip3 @@ List.map2_exn (args_of dt1) (args_of dt2) ~f:Term.pat_match_sort
      in
      Map.force_merge_list omaps,
      Map.force_merge_list smaps,
      Map.force_merge_list emaps
    else Map.Poly.empty, Map.Poly.empty, Map.Poly.empty
end
and DTEnv : Type.DTEnvType
  with type flag := Datatype.flag
   and type datatype := Datatype.t
   and type dtfunc := Datatype.func
   and type formula := Formula.t
= struct
  type t = (string, Datatype.t) Map.Poly.t

  let look_up_dt t name = Map.Poly.find t name
  let look_up_func t name =
    (* print_endline @@ "find func: " ^ name; *)
    Map.Poly.fold t ~init:None ~f:(fun ~key:_ ~data:dt ret ->
        (* print_endline @@ Datatype.str_of dt; *)
        match ret with
        | Some _ -> ret
        | None ->
          match Datatype.look_up_func dt name with
          | Some func ->
            (* print_endline ("found:" ^ (Datatype.str_of_func func)); *)
            Some (dt, func)
          | None ->
            (* print_endline "not found!"; *)
            ret)
  let look_up_dt_by_cons_name t name =
    match look_up_func t name with
    | Some (dt, _) -> Some dt
    | None -> None
  let mk_empty () = Map.Poly.empty

  let update_dt t dt =
    let name = Datatype.name_of dt in
    match look_up_dt t name with
    | Some _ -> Map.Poly.set t ~key:name ~data:dt
    | None -> Map.Poly.add_exn t ~key:name ~data:dt

  let update_dts t dt =
    List.fold_left (Datatype.dts_of dt) ~init:t ~f:(fun env dt1 ->
        update_dt env @@ Datatype.update_name dt @@ Datatype.name_of_dt dt1)

  let str_of t =
    "datatype env:\n  " ^
    String.concat ~sep:"\n  " @@
    Map.Poly.data @@ Map.Poly.mapi t ~f:(fun ~key ~data -> key ^ ": " ^ Datatype.str_of data)

  let name_is_cons t name =
    match look_up_func t name with
    | Some (_, func) -> Datatype.is_fcons func | _ -> false

  let name_is_sel t name =
    match look_up_func t name with
    | Some (_, func) -> Datatype.is_fsel func | _ -> false

  let name_is_func t name =
    match look_up_func t name with
    | Some _ -> true | _ -> false

  let force_merge env1 env2 = Map.force_merge env1 env2

  let rec of_sort = function
    | T_dt.SDT dt ->
      let args = Datatype.args_of dt in
      let full_name = Datatype.full_name_of(*adding instantiated datatypes?*) dt in
      force_merge (of_sorts args) @@ Map.Poly.singleton full_name dt
    | _ -> Map.Poly.empty
  and of_sorts =
    List.fold ~init:Map.Poly.empty ~f:(fun ret sort -> force_merge ret @@ of_sort sort)

  let rec of_term = function
    | Term.FunApp (T_dt.DTSel (_, dt, ret_sort), ts, _) ->
      of_sort (T_dt.SDT dt)
      |> force_merge (of_sort ret_sort)
      |> force_merge @@ of_terms ts
    | Term.FunApp (T_dt.DTCons (_, args, dt), ts, _) ->
      of_sort (T_dt.SDT dt)
      |> force_merge (of_sorts args)
      |> force_merge @@ of_terms ts
    | Term.FunApp (T_bool.Formula phi, _, _) -> of_formula phi
    | Term.FunApp (FVar (_, sorts), ts, _) -> force_merge (of_sorts sorts) (of_terms ts)
    | Term.Var (_, T_dt.SDT dt, _) -> of_sort (T_dt.SDT dt)
    | Term.FunApp (_, ts, _) as term -> force_merge (of_terms ts) @@ of_sort (Term.sort_of term)
    | _ -> Map.Poly.empty
  and of_terms =
    List.fold_left ~init:Map.Poly.empty ~f:(fun ret term -> force_merge ret @@ of_term term)
  and of_atom = function
    | Atom.App (Predicate.Psym (T_dt.IsCons (_, dt)), [t], _) ->
      force_merge (of_term t) @@ of_sort (T_dt.SDT dt)
    | Atom.App (_, ts, _) -> of_terms ts
    | _ -> Map.Poly.empty
  and of_formula = function
    | Formula.Atom (atom, _) -> of_atom atom
    | Formula.UnaryOp (_, phi, _) -> of_formula phi
    | Formula.BinaryOp (_, phi1, phi2, _) -> force_merge (of_formula phi1) (of_formula phi2)
    | Formula.Bind (_, _, phi, _) -> of_formula phi
    | Formula.LetFormula (_, _, def, body, _) -> force_merge (of_formula body) (of_term def)
    | _ -> Map.Poly.empty

end

and T_tuple : Type.T_tupleType
  with type term := Term.t
   and type atom := Atom.t
= struct
  type Sort.t += STuple of Sort.t list
  type fun_sym += TupleCons of Sort.t list | TupleSel of Sort.t list * int
  type pred_sym += IsTuple of Sort.t list | NotIsTuple of Sort.t list

  let mk_tuple_cons sorts ts = Term.mk_fsym_app (TupleCons sorts) ts
  let mk_tuple_sel sorts t i = Term.mk_fsym_app (TupleSel (sorts, i)) [t]
  let mk_is_tuple sorts t = Atom.mk_psym_app (IsTuple sorts) [t]
  let mk_is_not_tuple sorts t = Atom.mk_psym_app (NotIsTuple sorts) [t]

  let let_tuple_cons = function Term.FunApp (TupleCons sorts, ts, info) -> sorts, ts, info | _ -> assert false
  let let_tuple_sel = function Term.FunApp (TupleSel (sorts, i), [t], info) -> sorts, i, t, info | _ -> assert false

  let is_tuple_cons = function Term.FunApp (TupleCons _, _, _) -> true | _ -> false
  let is_tuple_sel = function Term.FunApp (TupleSel _, _, _) -> true | _ -> false

  let rec eval_sel = function
    | Term.FunApp (TupleSel (_, i), [Term.FunApp (TupleCons _, ts, _)], _) ->
      eval_sel @@ List.nth_exn ts i
    | t -> t

  let sorts_of = function STuple sorts -> sorts | _ -> assert false
end

and T_string : Type.T_stringType
  with type term := Term.t
= struct
  type Sort.t += SString
  type fun_sym += StringConst of string

  let mk_string_const str = Term.mk_fsym_app (StringConst str) []
  let let_string_const = function
    | Term.FunApp (StringConst str, _, info) -> str, info
    | _ -> assert false
end

and T_sequence : Type.T_sequenceType
  with type term := Term.t
   and type atom := Atom.t
= struct
  type Sort.t += SFinSequence | SInfSequence
  type fun_sym +=
    | Epsilon
    | Symbol of string
    | Concat of bool(* the first argument must be finite *)
    | LeftQuotient of bool(* the first argument must be finite *)
    | RightQuotient of bool(* the first argument must be finite *)
  type pred_sym +=
    | IsPrefix of bool
    | NotIsPrefix of bool
    | InRegExp of bool * string Grammar.RegWordExp.t
    | NotInRegExp of bool * string Grammar.RegWordExp.t

  let mk_eps () = Term.mk_fsym_app Epsilon []
  let mk_symbol symbol = Term.mk_fsym_app (Symbol symbol) []
  let concat ~fin t1 t2 = Term.mk_fsym_app (Concat fin) [t1; t2]

  let mk_is_prefix fin t1 t2 =
    Atom.mk_psym_app (IsPrefix fin) [t1; t2]
  let mk_is_not_prefix fin t1 t2 =
    Atom.mk_psym_app (NotIsPrefix fin) [t1; t2]
  let mk_is_in_regexp fin regexp t =
    Atom.mk_psym_app (InRegExp (fin, regexp)) [t]
  let mk_is_not_in_regexp fin regexp t =
    Atom.mk_psym_app (NotInRegExp (fin, regexp)) [t]
end

and TermSubst : Type.TermSubstType
  with type term := Term.t
= struct
  type t = (Ident.tvar, Term.t) Map.Poly.t

  let str_of subst =
    String.concat_map_list ~sep:", " (Map.Poly.to_alist subst) ~f:(fun (x, term) ->
        Printf.sprintf "%s |-> %s" (Ident.str_of_tvar x) (Term.str_of term))
end

and PredSubst : Type.PredSubstType
  with type formula := Formula.t
= struct
  type t = (Ident.pvar, (sort_env_list * Formula.t)) Map.Poly.t
end

and Rand : Type.RandType
  with type formula := Formula.t
   and type term := Term.t
   and type termSubst := TermSubst.t
= struct
  type t =
    | Uniform of Term.t * Term.t
    | Gauss of Term.t * Term.t
    | IntUniform of Term.t * Term.t

  let mk_uniform t1 t2 = Uniform (t1, t2)
  let mk_gauss t1 t2 = Gauss (t1, t2)
  let mk_int_uniform t1 t2 = IntUniform (t1, t2)

  let let_uniform = function
    | Uniform (t1, t2) -> t1, t2
    | _ -> assert false
  let let_gauss = function
    | Gauss (t1, t2) -> t1, t2
    | _ -> assert false
  let let_int_uniform = function
    | IntUniform (t1, t2) -> t1, t2
    | _ -> assert false

  let subst map = function
    | Uniform (t1, t2) -> mk_uniform (Term.subst map t1) (Term.subst map t2)
    | Gauss (t1, t2) -> mk_gauss (Term.subst map t1) (Term.subst map t2)
    | IntUniform (t1, t2) -> mk_int_uniform (Term.subst map t1) (Term.subst map t2)
  let subst_sorts map = function
    | Uniform (t1, t2) ->
      Uniform (Term.subst_sorts map t1, Term.subst_sorts map t2)
    | Gauss (t1, t2) ->
      Gauss (Term.subst_sorts map t1, Term.subst_sorts map t2)
    | IntUniform (t1, t2) ->
      IntUniform (Term.subst_sorts map t1, Term.subst_sorts map t2)
  let subst_conts map = function
    | Uniform (t1, t2) ->
      Uniform (Term.subst_conts map t1, Term.subst_conts map t2)
    | Gauss (t1, t2) ->
      Gauss (Term.subst_conts map t1, Term.subst_conts map t2)
    | IntUniform (t1, t2) ->
      IntUniform (Term.subst_conts map t1, Term.subst_conts map t2)
  let subst_opsigs map = function
    | Uniform (t1, t2) ->
      Uniform (Term.subst_opsigs map t1, Term.subst_opsigs map t2)
    | Gauss (t1, t2) ->
      Gauss (Term.subst_opsigs map t1, Term.subst_opsigs map t2)
    | IntUniform (t1, t2) ->
      IntUniform (Term.subst_opsigs map t1, Term.subst_opsigs map t2)

  let sort_of = function
    | Uniform (_, _) -> T_real.SReal
    | Gauss (_, _) -> T_real.SReal
    | IntUniform (_, _) -> T_int.SInt

  let str_of = function
    | Uniform (t1, t2) ->
      Printf.sprintf "Uniform(%s, %s)" (Term.str_of t1) (Term.str_of t2)
    | Gauss (t1, t2) ->
      Printf.sprintf "Gauss(%s, %s)" (Term.str_of t1) (Term.str_of t2)
    | IntUniform (t1, t2) ->
      Printf.sprintf "IntUniform(%s, %s)" (Term.str_of t1) (Term.str_of t2)

  let rename map = function
    | Uniform (t1, t2) -> Uniform (Term.rename map t1, Term.rename map t2)
    | Gauss (t1, t2) -> Gauss (Term.rename map t1, Term.rename map t2)
    | IntUniform (t1, t2) -> IntUniform (Term.rename map t1, Term.rename map t2)

  (*Invariant: t1 <= t2*)
  let mk_uniform_bounds vars = function
    | Uniform (t1, t2) ->
      Formula.and_of @@
      List.concat @@List.map vars ~f:(fun var ->
          let t = Term.mk_var var T_real.SReal in
          let a1 = Formula.mk_atom @@ T_real.mk_rleq t1 t in
          let a2 = Formula.mk_atom @@ T_real.mk_rleq t t2 in [a1; a2])
    | IntUniform (t1, t2) ->
      Formula.and_of @@
      List.concat @@List.map vars ~f:(fun var ->
          let t = Term.mk_var var T_int.SInt in
          let a1 = Formula.mk_atom @@ T_int.mk_leq t1 t in
          let a2 = Formula.mk_atom @@ T_int.mk_leq t t2 in [a1; a2])
    | _ -> assert false
end

type model = (sort_bind * Term.t option) list
(*val str_of_model:  -> string*)
let str_of_model model =
  String.concat_map_list ~sep:", " model ~f:(function
      | (Ident.Tvar ident, _), None ->
        Printf.sprintf "%s |-> *" ident
      | (Ident.Tvar ident, _), Some value ->
        Printf.sprintf "%s |-> %s" ident (Term.str_of value))

module UTermEnv = struct
  type t = {
    term_to_tvar: (Term.t, Ident.tvar * Formula.t Set.Poly.t) Hashtbl.Poly.t;
    tvar_to_term : (Ident.tvar, Term.t * Formula.t Set.Poly.t) Hashtbl.Poly.t
  }

  let create () : t = {
    term_to_tvar = Hashtbl.Poly.create ();
    tvar_to_term = Hashtbl.Poly.create ()
  }
  let clone t = {
    term_to_tvar = Hashtbl.Poly.copy t.term_to_tvar;
    tvar_to_term = Hashtbl.Poly.copy t.tvar_to_term
  }

  let is_empty t = Hashtbl.Poly.is_empty t.term_to_tvar

  let set t term tvar constrs =
    Hashtbl.Poly.set t.term_to_tvar ~key:term ~data:(tvar, constrs);
    Hashtbl.Poly.set t.tvar_to_term ~key:tvar ~data:(term, constrs)

  let of_term t term =
    match Hashtbl.Poly.find t.term_to_tvar term with
    | Some (tvar, constrs) -> tvar, constrs
    | None ->
      let tvar, constrs = Ident.Tvar (sprintf "|%s|" (Term.str_of term)), Set.Poly.empty in
      set t term tvar constrs;
      tvar, constrs

  let of_tvar t = Hashtbl.Poly.find_exn t.tvar_to_term

  let add_constr_by_term t term phi =
    let tvar, constrs =
      match Hashtbl.Poly.find t.term_to_tvar term with
      | Some (tvar, constrs) -> tvar, constrs
      | None -> Ident.Tvar (sprintf "|%s|" (Term.str_of term)), Set.Poly.empty
    in
    let constrs' = Set.Poly.add constrs phi in
    set t term tvar constrs'

  let add_constr_by_tvar t tvar phi =
    let term, constrs = Hashtbl.Poly.find_exn t.tvar_to_term tvar in
    let constrs' = Set.Poly.add constrs phi in
    set t term tvar constrs'

  let update_by_model t (model:model) =
    List.iter model ~f:(function
        | (tvar, _), Some term -> begin
            try
              let t1, _ = of_tvar t tvar in
              add_constr_by_tvar t tvar @@ Formula.eq t1 term
            with _ -> ()
          end
        | (_, _), _ -> ())
  let to_sub t =
    Map.Poly.of_alist_exn @@ Hashtbl.Poly.to_alist @@
    Hashtbl.Poly.map t.tvar_to_term ~f:fst

  (* assumed phi is simplifyed*)
  let subst_formula t phi =
    if is_empty t then phi else
      Formula.map_term phi ~f:(fun term ->
          if Term.is_uninterpreted_term term then
            let tvar, _ = of_term t term in
            Term.mk_var tvar (Term.sort_of term)
          else term)

  let to_formula t =
    if is_empty t then Formula.mk_true () else
      Formula.and_of @@ Set.Poly.to_list @@
      Hashtbl.Poly.fold t.tvar_to_term ~init:Set.Poly.empty
        ~f:(fun ~key:_ ~data:(_, constrs) ret -> Set.Poly.union constrs ret)

  let to_neg_formula t =
    Formula.and_of @@ List.map ~f:Formula.mk_neg @@ Set.Poly.to_list @@
    Hashtbl.Poly.fold t.tvar_to_term ~init:Set.Poly.empty
      ~f:(fun ~key:_ ~data:(_, constrs) ret -> Set.Poly.union constrs ret)

  let str_of t =
    Hashtbl.Poly.fold t.tvar_to_term ~init:""
      ~f:(fun ~key:tvar ~data:(term, constrs) ret ->
          sprintf "%s\n %s <=> %s :\n  %s" ret
            (Term.str_of term)
            (Ident.name_of_tvar tvar)
            (String.concat_map_set ~sep:"\n  " ~f:Formula.str_of constrs))
end

let remove_dontcare_elem ?(freshvar=false) ((x, s), v) =
  match v with
  | None -> x, if freshvar then Term.mk_var (Ident.mk_fresh_dontcare (Ident.name_of_tvar x)) s else Term.mk_dummy s
  | Some t -> x, t
let remove_dontcare ?(freshvar=false) m =
  List.filter m ~f:(function
      | ((Ident.Tvar "div0", Sort.SArrow (_, _)), None) -> false (* bug of model generation of z3 4.8.8? *)
      | ((Ident.Tvar "mod0", Sort.SArrow (_, _)), None) -> false (* bug of model generation of z3 4.8.8? *)
      | ((Ident.Tvar "array-ext", Sort.SArrow (_, _)), None) -> false
      | _ -> true)
  |> List.map ~f:(remove_dontcare_elem ~freshvar)

let ref_dtenv = Atomic.make @@ DTEnv.mk_empty ()
let update_ref_dtenv (dtenv:DTEnv.t) =
  Atomic.set ref_dtenv @@
  Map.force_merge ~catch_dup:(fun (name, t1, t2) ->
      failwith @@ sprintf "duplicate definition of %s as %s and %s"
        name (Datatype.str_of t1) (Datatype.str_of t2))
    dtenv @@ Atomic.get ref_dtenv

let ref_fenv = Atomic.make @@ FunEnv.mk_empty ()
let update_ref_fenv fenv =
  Map.Poly.iteri fenv ~f:(fun ~key ~data:_ -> Hash_set.add defined_fvars key);
  Atomic.set ref_fenv @@ Map.force_merge fenv @@ Atomic.get ref_fenv

let dummy_term_senv = Atomic.make []
let is_dummy_term tvar sort =
  List.exists (Atomic.get dummy_term_senv) ~f:(fun (tvar1, sort1) ->
      Stdlib.(tvar = tvar1) &&
      match sort with Some sort -> Stdlib.(sort = sort1) | _ -> true)
let add_dummy_term tvar sort =
  if not (is_dummy_term tvar (Some sort)) &&
     (T_dt.is_sus sort || Sort.is_arrow sort) then begin
    Atomic.set dummy_term_senv @@
    Atomic.get dummy_term_senv @ [tvar, sort];
  end
let mk_fresh_dummy_term = function
  | T_dt.SUS (name, _) as sort ->
    let tvar = Ident.mk_fresh_dummy_tvar name in
    let term = Term.mk_var tvar sort in
    add_dummy_term tvar sort;
    term
  | _ -> assert false

type term_subst_elem = Ident.tvar * Term.t
type term_subst_set = term_subst_elem Set.Poly.t
type term_subst_list = term_subst_elem list
type term_subst_map = (Ident.tvar, Term.t) Map.Poly.t

type pred_subst_elem = Ident.pvar * (sort_env_list * Formula.t)
type pred_subst_set = pred_subst_elem Set.Poly.t
type pred_subst_list = pred_subst_elem list
type pred_subst_map = (Ident.pvar, (sort_env_list * Formula.t)) Map.Poly.t

let sort_env_map_of_pred_sort_env_map map =
  Map.rename_keys_and_drop_unused ~f:(fun p -> Some (Ident.pvar_to_tvar p)) @@
  Map.Poly.map map ~f:(fun sorts -> Sort.mk_fun @@ sorts @ [T_bool.SBool])
