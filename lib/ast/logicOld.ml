open Core
open Common
open Util

(** First-Order Fixpoint Logic with Theories *)
type fun_sym = ..
type pred_sym = ..

module Priority = struct
  type t = int
  let comma = 2
  let letrec_forall_exists = comma + 2
  let imply_iff = letrec_forall_exists + 2
  let binary_or = imply_iff + 2
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
    else
      inner_str
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
    | Int i1, Int i2   -> Int (opi i1 i2)
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

  let ite cond_ then_ else_ = match cond_ with | Bool true -> then_ | Bool false -> else_ | _ -> failwith "type error @ Value.ite"

  let str_of = function
    | Bool b -> string_of_bool b
    | Int n -> Z.to_string n
    | Real r -> Q.to_string r
end

module Sort = struct
  type t = ..
  type t += SVar of Ident.svar | SArrow of t * t 

  let mk_fresh_svar () = SVar(Ident.mk_fresh_svar ())

  let mk_arrow s1 s2 = SArrow(s1, s2)
  let rec arity_of = function
    | SArrow (_s1, s2) -> 1 + arity_of s2
    | _ -> 0 (* assert false*)

  let is_arrow = function
    | SArrow _ -> true
    | _ -> false

  let rec mk_fun = function
    | [s] -> s
    | s :: ss -> mk_arrow s (mk_fun ss)
    | _ -> assert false
  let rec ret_of = function
    | SArrow (_s1, s2) -> ret_of s2
    | sort -> sort
  let rec args_of = function
    | SArrow (s1, s2) ->
      let args = args_of s2 in
      s1 :: args
    | _ -> []
  let rec args_ret_of = function
    | SArrow (s1, s2) ->
      let args, ret = args_ret_of s2 in
      s1 :: args, ret
    | s -> [], s
end

module SortMap = struct
  type t = (Ident.tvar, Sort.t) Map.Poly.t

  let empty = Map.Poly.empty
  let merge = Map.force_merge
  let merge_list = function
    | [] -> Map.Poly.empty
    | senv :: senvs' -> List.fold ~init:senv senvs' ~f:merge

  let str_of str_of_sort senv =
    String.concat ~sep:" " @@
    List.map (Map.Poly.to_alist senv) ~f:(fun (tvar, sort) ->
        Printf.sprintf "(%s: %s)" (Ident.name_of_tvar tvar) (str_of_sort sort))

  let of_set = Map.of_set
  let of_list m = of_set @@ Set.Poly.of_list m
  let to_list = Map.Poly.to_alist
  let key_set = Map.Poly.key_set
end

module type SortEnvType = sig
  type t

  val empty: t
  val singleton: Ident.tvar -> Sort.t -> t
  val of_list: (Ident.tvar * Sort.t) list -> t
  val of_sorts: Sort.t list -> t
  val of_set: (Ident.tvar * Sort.t) Set.Poly.t -> t
  val of_map: (Ident.tvar, Sort.t) Map.Poly.t -> t
  val from_to: t -> t -> (Ident.tvar, Ident.tvar) Map.Poly.t
  val args_of: t -> Ident.tvar list
  val args_set_of: t -> Ident.tvar Set.Poly.t
  val sorts_of: t -> Sort.t list
  val is_empty: t -> bool
  val mem: t -> Ident.tvar -> bool
  val length: t -> int
  val str_of: (Sort.t -> string) -> t -> string
  val list_of: t -> (Ident.tvar * Sort.t) list
  val set_of: t -> (Ident.tvar * Sort.t) Set.Poly.t
  val map_of: t -> (Ident.tvar, Sort.t) Map.Poly.t
  val refresh: t -> t * (Ident.tvar, Ident.tvar) Map.Poly.t
  val normalize: t -> t * (Ident.tvar, Ident.tvar) Map.Poly.t
  val exists: f:(Ident.tvar * Sort.t -> bool) -> t -> bool
  val filter: f:(Ident.tvar * Sort.t -> bool) -> t -> t
  val partition_tf: f:(Ident.tvar * Sort.t -> bool) -> t -> t * t
  val map: f:(Ident.tvar * Sort.t -> 'a) -> t -> 'a list
  val map2_exn: f:((Ident.tvar * Sort.t) -> (Ident.tvar * Sort.t) -> 'a) -> t -> t -> 'a list
  val iter : f:(Ident.tvar * Sort.t -> unit) -> t -> unit
  val find : f:(Ident.tvar * Sort.t -> bool) -> t -> (Ident.tvar * Sort.t) option
  val append: t -> t -> t
end
module SortEnv : SortEnvType = struct
  type t = (Ident.tvar * Sort.t) list

  let empty = []
  let singleton x s = [x, s]
  let of_list senv = senv
  let of_sorts sorts =
    let param_ident_count = ref 0 in
    let mk_param_ident () =
      incr param_ident_count;
      Ident.Tvar ("x" ^ string_of_int !param_ident_count)
    in
    List.map sorts ~f:(fun sort -> mk_param_ident (), sort)
  let of_set = Set.Poly.to_list
  let of_map m = Map.Poly.to_alist m
  let from_to senv1 senv2 = Map.Poly.of_alist_exn @@ List.map2_exn senv1 senv2 ~f:(fun (x1, _) (x2, _) -> x1, x2)
  let args_of = List.map ~f:fst
  let args_set_of senv = Set.Poly.of_list @@ args_of senv
  let sorts_of = List.map ~f:snd
  let is_empty = List.is_empty
  let mem senv x = List.Assoc.mem senv x ~equal:Stdlib.(=)
  let length = List.length
  let str_of str_of_sort senv =
    String.concat ~sep:", " @@
    List.map senv ~f:(fun (tvar, sort) ->
        Printf.sprintf "%s: %s" (Ident.name_of_tvar tvar) (str_of_sort sort))
  let list_of senv = senv
  let set_of = Set.Poly.of_list
  let map_of = Map.Poly.of_alist_exn
  let refresh senv =
    let senv' = List.map ~f:(fun (_, s) -> Ident.mk_fresh_tvar(), s) senv in
    let rename = List.zip_exn senv senv'
                 |> List.map ~f:(fun ((x, _), (x', _)) -> x, x')
                 |> Map.Poly.of_alist_exn in
    senv', rename
  let normalize senv =
    let senv' = of_sorts @@ sorts_of senv in
    let rename = List.zip_exn senv senv'
                 |> List.map ~f:(fun ((x, _), (x', _)) -> x, x')
                 |> Map.Poly.of_alist_exn in
    senv', rename
  let exists ~f = List.exists ~f
  let filter ~f = List.filter ~f
  let partition_tf ~f = List.partition_tf ~f
  let map ~f = List.map ~f
  let map2_exn ~f = List.map2_exn ~f
  let iter ~f = List.iter ~f
  let find ~f = List.find ~f
  let append = (@)
end

type info = ..
type info += Dummy
type info += ApproxConstraint of bool (* is parameter? *)

type parsed
type fixpoint_free

type fun_sym += | FVar of Ident.tvar * Sort.t list 


module Type = struct
  module type TermType = sig

    type formula
    type atom

    type t =
      | Var of Ident.tvar * Sort.t * info
      | FunApp of fun_sym * t list * info


    (** Construction *)
    val mk_var: ?info:info -> Ident.tvar -> Sort.t -> t
    val mk_fsym_app: ?info:info -> fun_sym -> t list -> t
    val mk_fvar_app: ?info:info -> Ident.tvar -> Sort.t list -> t list -> t
    val mk_dummy: Sort.t -> t
    val of_value: Value.t -> t
    val of_sort_env: SortEnv.t -> t list

    (** Observation *)
    val is_fvar_sym: fun_sym -> bool

    val is_var: t -> bool
    val is_app: t -> bool
    val is_fvar_app: t -> bool
    val is_numerical_compound: t -> bool
    val is_pathexp : t -> bool

    val tvs_of: t -> Ident.tvar Set.Poly.t
    val pvs_of: t -> Ident.pvar Set.Poly.t
    val funsyms_of: t -> fun_sym Set.Poly.t
    val term_sort_env_of: t -> (Ident.tvar * Sort.t) Set.Poly.t
    val pred_sort_env_of: t -> (Ident.pvar * Sort.t list) Set.Poly.t
    val sort_env_of: t -> (Ident.tvar * Sort.t) Set.Poly.t
    val fvar_apps_of : t -> t Set.Poly.t
    val pathexps_of : t -> t Set.Poly.t
    val filtered_terms_of : t -> f:(t -> bool) -> t Core.Set.Poly.t

    val ast_size: t -> int

    val sort_of : t -> Sort.t

    (** Destruction *)
    val let_var: t -> Ident.tvar * Sort.t * info
    val let_app: t -> fun_sym * t list * info
    val let_fvar_app: t -> Ident.tvar * Sort.t list * t list * info

    val value_of: t -> Value.t

    (** Substitution *)
    val rename: (Ident.tvar, Ident.tvar) Map.Poly.t -> t -> t
    val rename_pvars: (Ident.pvar, Ident.pvar) Map.Poly.t -> t -> t
    val rename_fun_sym: (Ident.tvar, Ident.tvar) Map.Poly.t -> fun_sym -> fun_sym
    val subst: (Ident.tvar, t) Map.Poly.t -> t -> t
    val subst_preds: (Ident.pvar, (SortEnv.t * formula)) Map.Poly.t -> t -> t
    val subst_fun_sym: (Ident.tvar, t) Map.Poly.t -> fun_sym -> fun_sym
    val aconv_pvar : t -> t

    (** Transformation *)
    val elim_ite : t -> (formula * t) list
    val instantiate_div0_mod0 : t -> t
    val extend_pred_params : Ident.pvar -> SortEnv.t -> t -> t
    val find_div_mod : t list -> (t * t) Set.Poly.t
    val replace_div_mod : ((t * t), (Ident.tvar * Ident.tvar)) Map.Poly.t -> t -> t
    val rm_boolean_term: t -> formula

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

    (** Printing *)
    val str_of_funsym: fun_sym -> string
    val str_of_sort: Sort.t -> string
    val str_of: ?priority:Priority.t -> t -> string

    (** Unification and Pattern Matching *)
    val unify: Ident.tvar Set.Poly.t -> t -> t -> (Ident.tvar, t) Map.Poly.t option
    val pattern_match: Ident.tvar Set.Poly.t -> t -> t -> (Ident.tvar, t) Map.Poly.t option
  end

  module type PredicateType = sig
    type fixpoint = Mu | Nu

    type formula
    type term

    type t =
      | Var of Ident.pvar * Sort.t list
      | Psym of pred_sym
      | Fixpoint of fixpoint * Ident.pvar * SortEnv.t * formula

    (** Construction *)
    val mk_var: Ident.pvar -> Sort.t list -> t
    val mk_psym: pred_sym -> t
    val mk_fix: fixpoint -> Ident.pvar -> SortEnv.t -> formula -> t

    (** Observation *)
    val is_var: t -> bool
    val is_psym: t -> bool
    val is_fix: t -> bool

    val tvs_of: t -> Ident.tvar Set.Poly.t
    val pvs_of: t -> Ident.pvar Set.Poly.t
    val term_sort_env_of: t -> (Ident.tvar * Sort.t) Set.Poly.t
    val pred_sort_env_of: t -> (Ident.pvar * Sort.t list) Set.Poly.t
    val sort_env_of: t -> (Ident.tvar * Sort.t) Set.Poly.t
    val terms_of: t -> term Set.Poly.t
    val fvar_apps_of: t -> term Set.Poly.t

    val nesting_level: t -> int
    val number_of_quantifiers: t -> int

    (** Destruction *)
    val let_var: t -> Ident.pvar * Sort.t list
    val let_psym: t -> pred_sym
    val let_fix: t -> fixpoint * Ident.pvar * SortEnv.t * formula

    (** Substitution *)
    val rename: (Ident.tvar, Ident.tvar) Map.Poly.t -> t -> t
    val rename_pvars: (Ident.pvar, Ident.pvar) Map.Poly.t -> t -> t
    val subst_neg: Ident.pvar -> t -> t
    val aconv_tvar: t -> t
    val aconv_pvar: t -> t

    (** Transformation *)
    val negate: ?negate_formula:(formula -> formula) -> t -> t
    val complete_psort: (Ident.pvar, Sort.t list) Map.Poly.t -> t -> t
    val flip_fixpoint: fixpoint -> fixpoint
    val extend_pred_params: Ident.pvar -> SortEnv.t -> t -> t

    (** Printing *)
    val str_of_predsym: pred_sym -> string
    val str_of: t -> string
    val str_of_fixpoint: fixpoint -> string
  end 

  module type AtomType = sig

    type predicate
    type term
    type termSubst
    type formula

    type t =
      | True of info
      | False of info
      | App of predicate * term list * info

    (** Construction *)
    val mk_true: ?info:info -> unit -> t
    val mk_false: ?info:info -> unit -> t
    val mk_app: ?info:info -> predicate -> term list -> t
    val mk_psym_app: ?info:info -> pred_sym -> term list -> t
    val mk_pvar_app: ?info:info -> Ident.pvar -> Sort.t list -> term list -> t
    val of_bool_var : Ident.tvar -> t
    val of_neg_bool_var : Ident.tvar -> t
    val of_bool_term : term -> t
    val of_neg_bool_term : term -> t

    (** Observation *)
    val is_true: t -> bool
    val is_false: t -> bool
    val is_app: t -> bool
    val is_psym_app: t -> bool
    val is_pvar_app: t -> bool
    val occur: Ident.pvar -> t -> bool

    val tvs_of : t -> Ident.tvar Set.Poly.t
    val pvs_of : t -> Ident.pvar Set.Poly.t
    val fvs_of : t -> Ident.tvar Set.Poly.t
    val funsyms_of : t -> fun_sym Set.Poly.t
    val term_sort_env_of : t -> (Ident.tvar * Sort.t) Set.Poly.t
    val pred_sort_env_of : t -> (Ident.pvar * Sort.t list) Set.Poly.t
    val sort_env_of : t -> (Ident.tvar * Sort.t) Set.Poly.t
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
    val let_app: t -> predicate * term list * info
    val let_psym_app: t -> pred_sym * term list * info
    val let_pvar_app: t -> Ident.pvar * Sort.t list * term list * info
    val info_of_true: t -> info
    val info_of_false: t -> info
    val info_of: t -> info
    val pvar_of: t -> Ident.pvar

    (** Substitution *)
    val rename: (Ident.tvar, Ident.tvar) Map.Poly.t -> t -> t
    val rename_pvars: (Ident.pvar, Ident.pvar) Map.Poly.t -> t -> t
    val subst: termSubst -> t -> t
    val subst_preds: (Ident.pvar, (SortEnv.t * formula)) Map.Poly.t -> t -> formula
    val subst_neg: Ident.pvar -> t -> t
    val aconv_tvar : t -> t
    val aconv_pvar : t -> t
    (** Transformation *)
    val refresh_tvar: SortMap.t * t -> SortMap.t * t
    val negate: ?negate_formula:(formula -> formula) -> t -> t
    val complete_psort: (Ident.pvar, Sort.t list) Map.Poly.t -> t -> t
    val elim_neq: t -> formula
    val elim_ite: t -> formula
    val instantiate_div0_mod0 : t -> t
    val find_div_mod: t -> (term * term) Set.Poly.t
    val replace_div_mod: ((term * term), (Ident.tvar * Ident.tvar)) Map.Poly.t -> t -> t
    val rm_boolean_term: t -> formula
    val extend_pred_params : Ident.pvar -> SortEnv.t -> t -> t

    val instantiate : t -> t
    val map_term : t -> f:(term -> term) -> t
    val fold : t ->
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
      > -> 'a
    val fold_map_term : t ->
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
      > -> ft : (term -> term)
      -> 'a

    (* Printing *)
    val str_of: ?priority:Priority.t -> t -> string

    (* Unification and Pattern Matching *)
    val unify: Ident.tvar Set.Poly.t -> t -> t -> termSubst option
    val pattern_match: Ident.tvar Set.Poly.t -> t -> t -> termSubst option
  end 

  module type FormulaType = sig
    type atom
    type termSubst
    type predicate_fixpoint
    type term
    type rand

    type unop = Not
    type binop = And | Or | Imply | Iff
    type binder = Forall | Exists | Random of rand

    type t =
      | Atom of atom * info
      | UnaryOp of unop * t * info
      | BinaryOp of binop * t * t * info
      | Bind of binder * SortEnv.t * t * info
      | LetRec of (predicate_fixpoint * Ident.pvar * SortEnv.t * t) list * t * info

    (** Construction *)
    val mk_atom: ?info:info -> atom -> t
    val mk_unop: ?info:info -> unop -> t -> t

    val mk_neg:?info:info ->  t -> t
    val mk_binop: ?info:info -> binop -> t -> t -> t
    val mk_and: ?info:info -> t -> t -> t
    val mk_or: ?info:info -> t -> t -> t
    val mk_iff: ?info:info -> t -> t -> t
    val mk_imply: ?info:info -> t -> t -> t

    val mk_bind: ?info:info -> binder -> SortEnv.t -> t -> t
    val mk_forall : ?info:info -> SortEnv.t -> t -> t
    val mk_bind_if_bounded : ?info:info -> binder -> SortEnv.t -> t -> t
    val mk_exists : ?info:info -> SortEnv.t -> t -> t
    val mk_random : ?info:info -> rand -> SortEnv.t -> t -> t
    val mk_forall_if_bounded : ?info:info -> SortEnv.t -> t -> t
    val mk_exists_if_bounded : ?info:info -> SortEnv.t -> t -> t
    val mk_binds: (binder * SortEnv.t) list -> t -> t
    val mk_randoms : (Ident.tvar * rand) list -> t -> t

    val mk_letrec : ?info:info -> (predicate_fixpoint * Ident.pvar * SortEnv.t * t) list -> t -> t
    val mk_false: ?info:info -> unit -> t
    val mk_true: ?info:info -> unit -> t

    val bind: ?info:info -> binder -> SortEnv.t -> t -> t
    val forall: ?info:info -> SortEnv.t -> t -> t
    val exists: ?info:info -> SortEnv.t -> t -> t
    val or_of: ?info:info -> t list -> t
    val and_of: ?info:info -> t list -> t
    val xor_of: ?info:info -> t list -> t
    val of_bool_var : Ident.tvar -> t
    val of_neg_bool_var : Ident.tvar -> t
    val of_bool_term: term -> t

    val geq: term -> term -> t
    val gt: term -> term -> t
    val leq: term -> term -> t
    val lt: term -> term -> t
    val eq: term -> term -> t
    val neq: term -> term -> t
    val mk_range: term -> Z.t -> Z.t -> t list
    val mk_range_opt: term -> Z.t option -> Z.t option -> t list

    (** Observation *)
    val is_atom: t -> bool
    val is_unop: t -> bool
    val is_neg: t -> bool
    val is_binop: t -> bool
    val is_true: t -> bool
    val is_false: t -> bool
    val is_and: t -> bool
    val is_or: t -> bool
    val is_imply: t -> bool
    val is_iff: t -> bool
    val is_bind: t -> bool
    val is_forall: t -> bool
    val is_exists: t -> bool
    val is_random: binder -> bool
    val is_letrec: t -> bool

    val tvs_of: t -> Ident.tvar Set.Poly.t
    val pvs_of: t -> Ident.pvar Set.Poly.t
    val fvs_of: t -> Ident.tvar Set.Poly.t
    val funsyms_of: t -> fun_sym Set.Poly.t
    val term_sort_env_of: t -> (Ident.tvar * Sort.t) Set.Poly.t
    val pred_sort_env_of: t -> (Ident.pvar * Sort.t list) Set.Poly.t
    val sort_env_of: t -> (Ident.tvar * Sort.t) Set.Poly.t
    val pathexps_of : t -> term Set.Poly.t

    val conjuncts_of: t -> t Set.Poly.t
    val disjuncts_of : t -> t Set.Poly.t

    val nesting_level: t -> int
    val number_of_quantifiers: t -> int
    val number_of_pvar_apps: bool -> t -> int
    val count_pvar_apps: t -> (Ident.pvar * (int * int)) list
    val ast_size: t -> int

    (** Destruction *)
    val let_atom: t -> atom * info
    val let_unop: t -> unop * t * info
    val let_neg: t -> t * info
    val let_binop: t -> binop * t * t * info
    val let_and: t -> t * t * info
    val let_or: t -> t * t * info
    val let_imply: t -> t * t * info
    val let_iff: t -> t * t * info
    val let_bind: t -> binder * SortEnv.t * t * info
    val let_forall: t -> SortEnv.t * t * info
    val let_exists: t -> SortEnv.t * t * info
    val let_forall_or_formula: t -> SortEnv.t * t * info
    val let_exists_or_formula: t -> SortEnv.t * t * info
    val let_letrec: t -> (predicate_fixpoint * Ident.pvar * SortEnv.t * t) list * t * info

    (** Substitution *)
    val rename: (Ident.tvar, Ident.tvar) Map.Poly.t -> t -> t
    val rename_pvars: (Ident.pvar, Ident.pvar) Map.Poly.t -> t -> t
    val subst: termSubst -> t -> t
    val subst_preds: (Ident.pvar, (SortEnv.t * t)) Map.Poly.t -> t -> t
    val subst_neg: Ident.pvar -> t -> t
    val replace_papps: (atom, atom) Map.Poly.t -> t -> t
    val aconv_tvar : t -> t
    val aconv_pvar : t -> t

    (** Transformation *)
    val flip_quantifier: binder -> binder
    val reduce_sort_map: SortMap.t * t -> SortMap.t * t
    val refresh_tvar: SortMap.t * t -> SortMap.t * t
    val complete_psort: (Ident.pvar, Sort.t list) Map.Poly.t -> t -> t
    val complete_tsort: t -> t
    val elim_neq: t -> t
    val elim_ite: t -> t
    val instantiate_div0_mod0 : t -> t
    val rm_forall: t -> (Ident.tvar * Sort.t) Set.Poly.t * t
    val find_div_mod: t -> (term * term) Set.Poly.t
    val replace_div_mod: ((term * term), (Ident.tvar * Ident.tvar)) Map.Poly.t -> t -> t
    val rm_div_mod: t -> t
    val rm_boolean_term: t -> t

    val extend_pred_params : Ident.pvar -> SortEnv.t -> t -> t

    val terms_of: t -> term Set.Poly.t
    val fvar_apps_of: t -> term Set.Poly.t
    val atoms_of: t -> atom Set.Poly.t * atom Set.Poly.t
    val psym_pvar_apps_of: t -> atom list * atom list * atom list
    val filtered_terms_of: t -> f:(term -> bool) -> term Set.Poly.t

    val cnf_of: Ident.tvar Set.Poly.t -> t -> (atom Set.Poly.t * atom Set.Poly.t * t) Set.Poly.t
    val dnf_of: t -> (atom Set.Poly.t * atom Set.Poly.t * t) Set.Poly.t
    val nnf_of: t -> t
    val neg_of: t -> t

    val univ_clos: t -> t

    val split_quantifiers: t -> ((binder * SortEnv.t) list * t)
    val pnf_of: t -> t
    val skolemize_fun: t -> SortMap.t * (Ident.tvar * Sort.t) list * t
    val skolemize_pred: t -> SortMap.t * (Ident.pvar * Sort.t) list * t

    val fold :
      t -> 
      f:< fand : 'a -> 'a -> 'a; 
          fatom : atom -> 'a;
          fbind : binder -> SortEnv.t -> 'a -> 'a;
          fletrec : (predicate_fixpoint * Ident.pvar * SortEnv.t * 'a) list -> 'a -> 'a;
          fnot : 'a -> 'a; 
          for_ : 'a -> 'a -> 'a;
          fbind : binder -> SortEnv.t -> 'a -> 'a;
          fletrec : (predicate_fixpoint * Ident.pvar * SortEnv.t * 'a) list -> 'a -> 'a 
        > -> 'a
    val map_atom : t -> f:(atom -> t) -> t
    val map_term : t -> f:(term -> term) -> t
    val map_atom_polarity : bool -> t -> f:(bool -> atom -> t) -> t


    (** Printing *)
    val str_of_binder: binder -> string
    val str_of_binop: binop -> string
    val str_of_unop: unop -> string
    val str_of: ?priority:Priority.t -> t -> string
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
    type Sort.t += SInt

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

    (* Substitution *)
    val subst_eqterm: term -> term -> Ident.tvar -> atom -> 
      (Value.t -> term -> 'monomial) * (term -> 'monomial -> (Value.t * 'monomial) option) * ('monomial -> term) -> atom
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

    type fun_sym +=
      | AStore
      | ASelect
      | AConst of Sort.t

    type Sort.t += SArray of Sort.t * Sort.t

    val mk_array_sort : Sort.t -> Sort.t -> Sort.t
    val mk_select : term -> term -> term
    val mk_store : term -> term -> term -> term
    val mk_const_array : Sort.t -> term -> term

    val index_sort_of : Sort.t -> Sort.t
    val elem_sort_of : Sort.t -> Sort.t

    val is_select : term -> bool
    val is_store : term -> bool

    val let_select : term -> term * term * info
    val let_store : term -> term * term * term * info

    val eval_select : term -> term -> term option

  end
  module type T_recfvarType = sig

    type term
    type formula

    type fun_sym += RecFVar of Ident.tvar * (Ident.tvar * Sort.t) list * Sort.t * term

    val mk_recfvar_app : ?info:info -> Ident.tvar -> (Ident.tvar * Sort.t) list -> Sort.t -> term -> term list -> term

    val is_recfvar_sym : fun_sym -> bool
    val is_recfvar_app : term -> bool

    val defined_formula_of : (Ident.tvar * 'a * 'b * 'c * (formula Core.Set.Poly.t)) Core.Set.Poly.t -> formula -> formula

  end
  module type T_dtType = sig

    type term
    type atom
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
      | IsNotCons of string * dt
    type Sort.t += 
      | SDT of dt 
      | SUS of string * (Sort.t list)

    val pars_of : Sort.t -> Sort.t list

    val mk_sel : ?info:info -> dt -> string -> term -> term
    val mk_cons : ?info:info -> dt -> string -> term list -> term
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
    val mk_is_cons : ?info:info -> dt -> dtcons -> term -> atom
  end
  module type DatatypeType = sig
    type sel = 
      | Sel  of string * Sort.t
      | InSel of string * string * Sort.t list
    type cons =  {
      name :string ;
      sels : sel list
    }
    type func = | FCons of cons | FSel of sel
    type flag = | FDt | FCodt | Undef
    type dt = {
      name : string ;
      args : Sort.t list ;
      conses : cons list
    }
    type t =  {
      name : string ;
      dts  :  dt list;
      flag : flag
    }
    val mk_dt : string -> Sort.t list -> dt
    val create : string -> dt list -> flag -> t
    val mk_uninterpreted_datatype : ?numeral:int -> string -> t
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

    val dt_of : t -> dt
    val conses_of : t -> cons list
    val sels_of : t -> sel list
    val args_of : t -> Sort.t list
    val full_name_of : t -> string
    val full_name_of_dt : dt -> string

    val is_dt : t -> bool
    val is_codt : t -> bool
    val is_undef : t -> bool

    val is_sel : sel -> bool
    val is_insel : sel -> bool

    val is_fcons : func -> bool
    val is_fsel : func -> bool

    val update_dts : t ->  dt list -> t
    val update_dt : t -> dt -> t
    val update_args : t -> Sort.t list -> t
    val update_conses : t -> cons list -> t

    val add_cons : t -> cons -> t
    val add_sel : cons -> sel -> cons

    val str_of_sel : sel -> string
    val str_of_cons : cons -> string
    val str_of_flag : flag -> string
    val str_of : t -> string
    val full_str_of_sel : t -> sel -> string
    val full_str_of_cons : t -> cons -> string

    val sort_of: t -> Sort.t
    val sort_of_sel : t -> sel -> Sort.t
    val sorts_of_cons_args : t -> cons -> Sort.t list

    val is_finite : t -> bool
    val is_singleton : Sort.t -> bool
    val fsym_of_cons : t -> cons -> fun_sym
    val fsym_of_sel : t -> sel -> fun_sym
    val fsym_of_func : t -> func -> fun_sym
    val fresh_of : t -> t
  end 
  module type DTEnvType = sig

    type flag
    type datatype
    type dtfunc
    type formula


    type t = (string, datatype) Map.Poly.t

    val look_up_dt : t -> string -> datatype option
    val look_up_func : t -> string -> (datatype * dtfunc) option
    val update_dt : t -> datatype -> t
    val update_dts : t -> datatype -> t
    val str_of : t -> string
    val sort_of_name : t -> string -> Sort.t
    val name_is_cons : t -> string -> bool
    val name_is_sel : t -> string -> bool 
    val name_is_func : t -> string -> bool
    val of_formula : formula -> t
    val merge : t -> t -> t
  end
  module type SortEnvType = sig

    type term

    type t = (Ident.tvar * Sort.t) list
    val sorts_of : t -> Sort.t list
    val args_of : t -> term list
    val str_of: t -> string
  end

  module type TermSubstType = sig

    type term

    type t = (Ident.tvar, term) Map.Poly.t
    val empty: t
    val merge: t -> t -> t
    val str_of_model: ((Ident.tvar * Sort.t) * term option) list -> string
    val str_of: t -> string
  end

  module type RandType = sig
    type term
    type termSubst
    type t = Uniform of term * term | Gauss of term * term

    val mk_uniform: term -> term -> t
    val mk_gauss: term -> term -> t
    val subst: termSubst -> t -> t
    val sort_of: t -> Sort.t
    val str_of: t -> string
  end
end

module rec Term : Type.TermType 
  with type formula := Formula.t and
  type atom := Atom.t = struct

  type t =
    | Var of Ident.tvar * Sort.t * info
    | FunApp of fun_sym * t list * info

  (** Printer *)
  let rec str_of_sort = function
    | Sort.SArrow (s1, s2) -> str_of_sort s1 ^ " -> " ^ str_of_sort s2
    | T_bool.SBool -> "bool"
    | T_int.SInt -> "int"
    | T_real.SReal -> "real"
    | T_array.SArray (e, i) -> sprintf "(array %s %s)" (str_of_sort e) (str_of_sort i)
    | T_dt.SDT(dt) -> Datatype.full_name_of dt 
    | T_dt.SUS(name, _) -> name
    | Sort.SVar(svar) -> Ident.name_of_svar svar
    | _ -> failwith "unknown sort"

  (** Construction *)
  let mk_var ?(info=Dummy) var sort = Var(var, sort, info)
  let mk_fsym_app ?(info=Dummy) sym ts = FunApp(sym, ts, info)
  let mk_fvar_app ?(info=Dummy) tvar sorts ts = FunApp(FVar (tvar, sorts), ts, info)

  let rec mk_dummy sort= 
    match sort with
    | T_int.SInt -> T_int.zero () | T_real.SReal -> T_real.rzero ()
    | T_bool.SBool -> T_bool.mk_false () 
    | T_dt.SDT (_) | T_dt.SUS (_, _) -> T_dt.mk_dummy sort
    | T_array.SArray (_, se) as sa -> T_array.mk_const_array sa @@ mk_dummy se
    | s -> failwith ("mk dummy error:" ^ str_of_sort s)
  let of_value = function
    | Value.Int i    -> T_int.mk_int i
    | Value.Real r   -> T_real.mk_real r
    | Value.Bool b   -> T_bool.of_atom (if b then Atom.True Dummy else Atom.False Dummy)
  let of_sort_env = SortEnv.map ~f:(uncurry mk_var)

  (** Observation *)
  let is_fvar_sym = function FVar(_, _) -> true | _ -> false
  let is_var = function Var(_, _, _) -> true | _ -> false
  let is_app = function FunApp(_, _, _) -> true | _ -> false
  let is_fvar_app = function FunApp(FVar(_, _), _, _) -> true | _ -> false
  let is_numerical_compound term =
    Stdlib.(<>) (Term.sort_of term) T_bool.SBool &&
    match term with
    | Term.Var _ -> false
    | Term.FunApp ((T_int.Int _| T_real.Real _ | T_real.Alge _ | FVar (_, _)), _, _) -> false
    | Term.FunApp (_, _, _) -> true
  let rec is_pathexp t =
    match t with
    | Var (_, _, _)  -> true
    | FunApp (T_recfvar.RecFVar(_, _, _, _), ts, _) 
    | FunApp (FVar (_, _), ts, _) -> List.exists ts ~f:is_pathexp
    | FunApp (T_int.Neg, [t], _) | FunApp (T_real.RNeg, [t], _) | FunApp(T_num.NNeg _, [t], _) 
    | FunApp (T_real_int.ToReal, [t], _) 
    | FunApp (T_real_int.ToInt, [t], _) -> is_pathexp t
    | FunApp (T_dt.DTSel (sel_name, dt, _) , [FunApp(T_dt.DTCons (cons_name, _, _), _, _)], _) -> 
      begin match Datatype.look_up_cons dt cons_name with
        | Some (cons) -> 
          let sels = Datatype.sels_of_cons cons in
          not @@ List.exists sels ~f:(
            fun sel  -> Stdlib.(=) (Datatype.name_of_sel sel) sel_name 
          ) 
        | None -> assert false end
    | FunApp (T_dt.DTSel (_, _, _) , [t1], _) -> is_pathexp t1 
    | FunApp (T_array.ASelect , [t1; _], _) -> is_pathexp t1
    | _ -> false

  let rec tvs_of = function
    | Var(tvar, _, _) -> Set.Poly.singleton tvar
    | FunApp(sym, args, _) ->
      Set.Poly.union_list @@
      (match sym with
       | FVar (tvar, _) -> Set.Poly.singleton tvar
       | T_bool.Formula phi -> Formula.tvs_of phi
       | _ -> Set.Poly.empty) :: List.map args ~f:tvs_of
  let rec pvs_of = function
    | Var(_, _, _) -> Set.Poly.empty
    | FunApp(sym, args, _) ->
      Set.Poly.union_list @@
      (match sym with
       | T_bool.Formula phi -> Formula.pvs_of phi
       | _ -> Set.Poly.empty) :: List.map args ~f:pvs_of
  let rec funsyms_of = function
    | Var _ -> Set.Poly.empty
    | FunApp(sym, args, _) ->
      Set.Poly.add (Set.Poly.union_list @@ List.map args ~f:funsyms_of) sym
  let rec term_sort_env_of = function
    | Var(var, sort, _) -> Set.Poly.singleton (var, sort)
    | FunApp(sym, args, _) ->
      Set.Poly.union_list @@
      (match sym with
       | FVar (tvar, sorts) -> Set.Poly.singleton (tvar, Sort.mk_fun sorts)
       | T_bool.Formula phi -> Formula.term_sort_env_of phi
       | _ -> Set.Poly.empty) :: List.map args ~f:term_sort_env_of
  let rec pred_sort_env_of = function
    | Var _ -> Set.Poly.empty
    | FunApp (sym, args, _) ->
      Set.Poly.union_list @@
      (match sym with
       | T_bool.Formula phi -> Formula.pred_sort_env_of phi
       | _ -> Set.Poly.empty) :: List.map args ~f:pred_sort_env_of
  let sort_env_of t =
    Set.Poly.union
      (term_sort_env_of t)
      (Set.Poly.map ~f:(fun (Ident.Pvar name, sorts) -> Ident.Tvar(*ToDo*) name, Sort.mk_fun (sorts @ [T_bool.SBool])) @@ pred_sort_env_of t)
  let rec fvar_apps_of = function
    | Var _ -> Set.Poly.empty
    | FunApp (sym, args, _) as t ->
      Set.Poly.union_list @@
      (match sym with
       | FVar(_, _) -> Set.Poly.singleton t
       | T_bool.Formula phi -> Formula.fvar_apps_of phi
       | _ -> Set.Poly.empty) :: List.map args ~f:fvar_apps_of
  let rec pathexps_of t =
    if is_pathexp t then Set.Poly.singleton t
    else match t with
      | Var (_, _, _)  -> Set.Poly.singleton t
      | FunApp(sym, args, _) ->
        Set.Poly.union_list @@
        (match sym with
         | FVar (_, _) -> Set.Poly.singleton t
         | T_bool.Formula phi -> Formula.pathexps_of phi
         | _ -> Set.Poly.empty) :: List.map args ~f:pathexps_of
  let rec filtered_terms_of t ~f =
    Set.Poly.union (if f t then Set.Poly.singleton t else Set.Poly.empty) 
      (match t with
       | FunApp(T_bool.Formula phi, _, _) -> Formula.filtered_terms_of ~f phi
       | FunApp(_, args, _) -> List.map args ~f:(filtered_terms_of ~f) |> Set.Poly.union_list
       | _ -> Set.Poly.empty)
  let ast_size = function
    | Var(_, _, _) -> 1
    | FunApp(sym, args, _) ->
      let size_of_args = List.fold ~f:(fun acc term -> acc + Term.ast_size term) ~init:1 args in
      match sym with
      | T_bool.Formula phi -> size_of_args + (Formula.ast_size phi)
      | _ -> size_of_args

  (** Destruction *)
  let let_var = function
    | Var(var, sort, info) -> (var, sort, info)
    | _ -> assert false
  let let_app = function
    | FunApp(sym, ts, info) -> (sym, ts, info)
    | _ -> assert false
  let let_fvar_app = function
    | FunApp(FVar(var, sorts), ts, info) -> (var, sorts, ts, info)
    | _ -> assert false

  let value_of = function
    | FunApp (T_int.Int n, _, _) -> Value.Int n
    | FunApp (T_real.Real r, _, _) -> Value.Real r
    | FunApp (T_bool.Formula (Formula.Atom (Atom.True _, _)), _, _) -> Value.Bool true
    | FunApp (T_bool.Formula (Formula.Atom (Atom.False _, _)), _, _) -> Value.Bool false
    | _ -> assert false

  (** Substitution *)
  let rec rename map = function
    | Var(var', sort, info) as t -> begin
        match Map.Poly.find map var' with
        | None -> t
        | Some var -> Var(var, sort, info)
      end
    | FunApp (sym, ts, info) ->
      FunApp (rename_fun_sym map sym, List.map ~f:(rename map) ts, info)
  and rename_fun_sym map = function
    | FVar(var', sorts) as fsym -> begin
        match Map.Poly.find map var' with
        | None -> fsym
        | Some var -> FVar(var, sorts)
      end
    | T_bool.Formula phi -> T_bool.Formula(Formula.rename map phi)
    | fsym -> fsym
  let rec rename_pvars map = function
    | FunApp (sym, args, info) ->
      FunApp (rename_pvars_fun_sym map sym, List.map ~f:(rename_pvars map) args, info)
    | t -> t
  and rename_pvars_fun_sym map = function
    | T_bool.Formula phi -> T_bool.Formula(Formula.rename_pvars map phi)
    | fsym -> fsym

  let rec subst map = function
    | Var(var', sort, info) -> begin
        match Map.Poly.find map var' with
        | None -> Var(var', sort, info)
        | Some t -> t
      end
    | FunApp (sym, ts, info) ->
      FunApp (subst_fun_sym map sym, List.map ~f:(subst map) ts, info)
  and subst_fun_sym map = function
    | FVar(var', sorts) -> begin
        match Map.Poly.find map var' with
        | None -> FVar(var', sorts)
        | Some _ -> assert false
      end
    | T_bool.Formula phi -> T_bool.Formula(Formula.subst map phi)
    | sym -> sym
  let subst_preds map = function
    | FunApp (T_bool.Formula phi, args, info) ->
      FunApp (T_bool.Formula (Formula.subst_preds map phi), args, info)
    | sym -> sym
  let aconv_pvar = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (sym, args, info) ->
      let sym = match sym with
        | T_bool.Formula phi -> T_bool.Formula (Formula.aconv_pvar phi)
        | sym -> sym
      in
      FunApp (sym, List.map ~f:Term.aconv_pvar args, info)

  (** Transformation *)
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
          Formula.and_of [phi1; phi2], FunApp(fsym, [t1; t2], info))
    | FunApp (T_bool.Formula phi, [], info) ->
      [Formula.mk_true (), FunApp (T_bool.Formula (Formula.elim_ite phi), [], info) ]
    | FunApp(fsym, [t1], info) ->
      List.map ~f:(fun (phi, t) -> (phi, FunApp(fsym, [t], info))) @@ elim_ite t1
    (*     | FunApp(fsym, [t1; t2], info) ->
           List.cartesian_product (elim_ite t1) (elim_ite t2)
           |> List.map ~f:(fun ((phi1, t1), (phi2, t2)) ->
           Formula.and_of [phi1; phi2], FunApp(fsym, [t1; t2], info)) *)
    | _ as term->
      (* print_endline ("can't elim ite :" ^ (Term.str_of term)); *)
      [Formula.mk_true (), term]
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

  let rec extend_pred_params ident extended_params = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (sym, args, info) -> begin
        let sym = match sym with
          | T_bool.Formula phi -> T_bool.Formula (Formula.extend_pred_params ident extended_params phi)
          | sym -> sym
        in
        let args = List.map ~f:(extend_pred_params ident extended_params) args in
        FunApp (sym, args, info)
      end

  let rec find_div_mod = function
    | [] -> Set.Poly.empty
    | t :: tl -> Set.Poly.union (find_div_mod_in_term t) (find_div_mod tl)
  and find_div_mod_in_term = function
    | Var (_, _, _) -> Set.Poly.empty
    | FunApp (T_int.Div, [t1; t2], _) | FunApp (T_int.Mod, [t1; t2], _) ->
      Set.Poly.add (Set.Poly.union (find_div_mod_in_term t1) (find_div_mod_in_term t2)) (t1, t2)
    | FunApp (_, args, _) -> find_div_mod args
  let rec replace_div_mod map = function
    | Var (var, sort, info) -> Var (var, sort, info)
    | FunApp (T_int.Div, [t1; t2], _) ->
      let (divvar, _) = Map.Poly.find_exn map (t1, t2) in
      Var (divvar, T_int.SInt, Dummy)
    | FunApp (T_int.Mod, [t1; t2], _) ->
      let (_, modvar) = Map.Poly.find_exn map (t1, t2) in
      Var (modvar, T_int.SInt, Dummy)
    | FunApp (sym, args, info) -> FunApp (sym, List.map args ~f:(replace_div_mod map), info)

  let rm_boolean_term = function
    | Var (Ident.Tvar name, sort, _) -> Formula.mk_atom @@Atom.mk_pvar_app (Ident.Pvar name) [sort] []
    | FunApp (T_bool.Formula phi, [], _) -> Formula.rm_boolean_term phi
    | _ -> assert false

  (** Printing *)
  (*let str_of_fun_sym = function
    | T_int.Add -> "T_int.Add" | T_int.Div -> "T_int.Div" | T_int.Mod -> "T_int.Mod" | T_int.Mult -> "T_int.Mult"
    | T_int.Real r -> Printf.sprintf "T_int.Real %s" (Q.to_string r)
    | T_int.Int i -> Printf.sprintf "T_int.Int %s" (Z.to_string i)
    | T_int.Sub -> "T_int.Sub" | T_int.Neg -> "T_int.Neg"
    | T_bool.Formula phi -> Printf.sprintf "T_bool.Formula (%s)" (Formula.str_of phi)
    | T_bool.IfThenElse -> "IfThenElse"
    | _ -> failwith "unimplemented function symbols"*)
  let str_of_funsym = function
    | FVar (x, _sorts) -> Ident.name_of_tvar x
    | T_recfvar.RecFVar(x, _, _, _) -> Ident.name_of_tvar x
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
    | T_num.NNeg svar -> sprintf "-_%s" (Ident.name_of_svar svar)
    | T_num.NAdd svar -> sprintf "+_%s" (Ident.name_of_svar svar)
    | T_num.NSub svar -> sprintf "-_%s" (Ident.name_of_svar svar)
    | T_num.NMult svar -> sprintf "*_%s" (Ident.name_of_svar svar)
    | T_num.NDiv svar -> sprintf "/_%s" (Ident.name_of_svar svar)
    | T_num.NPower svar -> sprintf "^_%s" (Ident.name_of_svar svar)
    | T_num.Value (ident, svar) -> sprintf "value(%s:%s)" ident (Ident.name_of_svar svar)
    | T_bool.Formula phi -> Printf.sprintf "Formula(%s)" @@ Formula.str_of ~priority:0 phi
    | T_bool.IfThenElse -> "IfThenElse"
    (* | T_dt.DTCons (name, args, dt) -> 
       sprintf "[%s:%s]" name (List.fold_left args ~init:(Datatype.full_name_of dt) ~f:(
          fun ret arg -> (str_of_sort arg) ^ "->" ^ ret
        )) *)
    | T_dt.DTCons (name, _, _) -> name
    (* | T_dt.DTSel (name, dt, ret_sort) -> 
       sprintf "[%s : %s -> %s]" name (Datatype.full_name_of dt) (str_of_sort ret_sort) *)
    | T_dt.DTSel (name, _, _) -> name
    | T_array.ASelect -> "select"
    | T_array.AStore -> "store"
    | T_array.AConst (sa) -> sprintf "const_array[%s]" @@ str_of_sort sa
    | _ ->  failwith "unknown function symbol"

  (*let rec str_of = function
    | Var (Ident.Tvar id, _, _) -> Printf.sprintf "Var (%s)" id
    | FunApp (fun_sym, terms, _) -> Printf.sprintf "FunApp (%s, %s)" (str_of_fun_sym fun_sym)
                                      (List.fold ~f:(fun acc term -> acc ^ ", " ^ (str_of term)) ~init:"" terms)*)

  let rec str_of ?(priority=20) = function
    | Var (x, _, _) -> sprintf "%s" (Ident.str_of_tvar x)
    | FunApp(T_recfvar.RecFVar(x, _, _, _), ts, _) 
    | FunApp(FVar (x, _), ts, _) ->
      if List.length ts = 0 then
        Ident.name_of_tvar x
      else
        Priority.add_bracket priority Priority.fun_app
        @@ Printf.sprintf "%s %s"
          (Ident.name_of_tvar x)
          (String.concat ~sep:" " @@ List.map ts ~f:(fun arg -> Term.str_of ~priority:(Priority.fun_app+1(*ToDo*)) arg))

    | FunApp (T_bool.Formula phi, [], _) ->
      Formula.str_of ~priority:20 phi
    | FunApp (T_bool.IfThenElse, [cond; then_; else_], _) ->
      Printf.sprintf "(if %s then %s else %s)"
        (str_of ~priority:0 cond)
        (str_of ~priority:0 then_)
        (str_of ~priority:0 else_)
    | FunApp (T_int.Int n, [], info) ->
      if Z.Compare.(n < Z.zero) then
        str_of ~priority (T_int.mk_neg (FunApp (T_int.Int (Z.neg n), [], info)))
      else Z.to_string n
    | FunApp (T_real.Real r, [], _) -> "r(" ^ (Q.to_string r ^ ")")
    | FunApp (T_real.Alge (t, n), [], _) -> "root-obj(" ^ str_of t ^ " " ^ string_of_int n ^ ")"
    | FunApp (T_int.Neg, [t], _) | FunApp (T_real.RNeg, [t], _) | FunApp(T_num.NNeg _, [t], _) ->
      Priority.add_bracket priority Priority.neg_abs
      @@ Printf.sprintf "-%s" (str_of ~priority:(Priority.neg_abs+1(*ToDo*)) t)
    | FunApp (T_real_int.ToReal, [t], _) ->
      Priority.add_bracket priority Priority.neg_abs
      @@ Printf.sprintf "to_real %s" (str_of ~priority:(Priority.neg_abs+1(*ToDo*)) t)
    | FunApp(T_real_int.ToInt, [t], _)->
      Priority.add_bracket priority Priority.neg_abs
      @@ Printf.sprintf "to_int %s" (str_of ~priority:(Priority.neg_abs+1(*ToDo*)) t)
    | FunApp (T_int.Abs, [t], _) | FunApp (T_real.RAbs, [t], _) ->
      Priority.add_bracket priority Priority.neg_abs
      @@ Printf.sprintf "abs %s" (str_of ~priority:(Priority.neg_abs+1(*ToDo*)) t)
    | FunApp (T_int.Add as op, [t1; t2], _) | FunApp (T_real.RAdd as op, [t1; t2], _) | FunApp(T_num.NAdd _ as op, [t1; t2], _)
    | FunApp (T_int.Sub as op, [t1; t2], _) | FunApp (T_real.RSub as op, [t1; t2], _) | FunApp(T_num.NSub _ as op, [t1; t2], _) ->
      Priority.add_bracket priority Priority.add_sub
      @@ Printf.sprintf "%s %s %s"
        (str_of ~priority:Priority.add_sub t1)
        (Term.str_of_funsym op)
        (str_of ~priority:Priority.add_sub t2)
    | FunApp (T_int.Mult as op, [t1; t2], _) | FunApp (T_real.RMult as op, [t1; t2], _) | FunApp(T_num.NMult _ as op, [t1; t2], _)
    | FunApp (T_int.Div as op, [t1; t2], _) | FunApp (T_real.RDiv as op, [t1; t2], _) | FunApp(T_num.NDiv _ as op, [t1; t2], _)
    | FunApp (T_int.Mod as op, [t1; t2], _) | FunApp(T_int.Rem as op, [t1; t2], _) ->
      Priority.add_bracket priority Priority.mult_div_mod
      @@ Printf.sprintf "%s %s %s"
        (str_of ~priority:Priority.mult_div_mod t1)
        (Term.str_of_funsym op)
        (str_of ~priority:Priority.mult_div_mod t2)
    | FunApp (T_int.Power as op, [t1; t2], _) | FunApp (T_real.RPower as op, [t1; t2], _) | FunApp(T_num.NPower _ as op, [t1; t2], _) ->
      Priority.add_bracket priority Priority.power
      @@ Printf.sprintf "%s%s%s"
        (str_of ~priority:Priority.power t1)
        (Term.str_of_funsym op)
        (str_of ~priority:Priority.power t2)
    | FunApp (T_int.Add, _, _) | FunApp (T_real.RAdd, _, _)
    | FunApp (T_int.Mult, _, _) | FunApp (T_real.RMult, _, _) -> failwith "add and mult are binary"
    | FunApp (T_num.Value _ as op, _, _)  -> str_of_funsym op
    | FunApp(T_dt.DTCons (_, _, _) as fsym, ts, _) ->
      if List.length ts = 0 then
        sprintf "%s" (str_of_funsym fsym)
      else
        sprintf "(%s%s)" (sprintf "%s" (str_of_funsym fsym)) (List.fold_left ts ~init:("") ~f:(
            fun ret term ->
              sprintf "%s %s" ret (str_of term)))
    | FunApp(T_dt.DTSel (_, _, _) as fsym, [t1], _) ->
      sprintf "(%s %s)" (str_of_funsym fsym)  (str_of t1)
    | FunApp(T_array.ASelect , [t1; t2], _) -> sprintf "(select %s %s)" (str_of t1) (str_of t2)
    | FunApp(T_array.AStore , [t1; t2; t3], _) -> sprintf "(store %s %s %s)" (str_of t1) (str_of t2) (str_of t3)
    | FunApp(T_array.AConst _ , [t1], _) -> sprintf "ARR{%s}" (str_of t1)
    | FunApp (f, ts, _) ->
      failwith ("unknown function application: " ^ String.concat ~sep:" " @@ str_of_funsym f :: List.map ts ~f:Term.str_of)

  (** Observation *)

  let rec sort_of = function
    | Var(_, sort, _) -> sort
    | FunApp (FVar (_, sorts), args, _) ->
      Sort.mk_fun @@ List.drop sorts (List.length args)
    | FunApp (T_recfvar.RecFVar (_, _, ret_sort, _), _, _) -> ret_sort
    | FunApp (T_int.Int _, _, _) | FunApp (T_int.Mod, _, _) | FunApp (T_int.Rem, _, _) -> T_int.SInt
    | FunApp (T_real.Real _, _, _) | FunApp (T_real.Alge _, _, _) -> T_real.SReal
    | FunApp (T_int.Add, _, _) | FunApp (T_int.Sub, _, _)
    | FunApp (T_int.Mult, _, _) | FunApp (T_int.Div, _, _)
    | FunApp (T_int.Neg, _, _) | FunApp (T_int.Abs, _, _) | FunApp(T_real_int.ToInt, _, _) -> T_int.SInt
    | FunApp (T_real.RAdd, _, _) | FunApp (T_real.RSub, _, _)
    | FunApp (T_real.RMult, _, _) | FunApp (T_real.RDiv, _, _)
    | FunApp (T_real.RNeg, _, _) | FunApp (T_real.RAbs, _, _)| FunApp(T_real_int.ToReal, _, _)-> T_real.SReal
    | FunApp (T_bool.Formula _, _, _) -> T_bool.SBool
    | FunApp (T_bool.IfThenElse, [_; t; _], _) -> sort_of t
    | FunApp (T_num.Value (_, svar), _, _) -> Sort.SVar(svar)
    | FunApp (T_dt.DTCons (_, _, dt), _, _) -> Datatype.sort_of dt
    | FunApp (T_dt.DTSel (_, _, sort), _, _) -> sort
    | FunApp (T_array.AStore, [a;_;_], _) -> sort_of a
    | FunApp (T_array.ASelect, [a;_], _) -> T_array.elem_sort_of @@ sort_of a
    | FunApp (T_array.AConst (sa),_, _) -> sa
    | FunApp (T_num.NAdd svar, _, _) | FunApp (T_num.NSub svar, _, _)
    | FunApp (T_num.NMult svar, _, _) | FunApp (T_num.NDiv svar, _, _)
    | FunApp (T_num.NPower svar, _, _) | FunApp (T_num.NNeg svar, _, _) -> Sort.SVar(svar)
    | t -> failwith ("error at sort_of: " ^ str_of t)


  (** Unification and Pattern Matching *)
  let unify bvs t1 t2 =
    if Stdlib.(=) t1 t2 then
      Option.some @@ Map.Poly.empty
    else
      match t1, t2 with
      | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) when Z.Compare.(=) n1 n2 -> (* ToDo: reachable? *)
        Option.some @@ Map.Poly.empty
      | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _) when Q.(=) r1 r2 -> (* ToDo *)
        Option.some @@ Map.Poly.empty
      | FunApp (T_bool.Formula (Formula.Atom (atm1, _)), [], _), FunApp (T_bool.Formula (Formula.Atom (atm2, _)), [], _)
        when (Atom.is_true atm1 && Atom.is_true atm2) || (Atom.is_false atm1 && Atom.is_false atm2) (* ToDo: reachable? *) ->
        Option.some @@ Map.Poly.empty

      | Var (x, _, _), _ when not @@ Set.Poly.mem bvs x ->
        if Set.Poly.mem (tvs_of t2) x then None
        else Option.some @@ Map.Poly.singleton x t2
      | _, Var (x, _, _) when not @@ Set.Poly.mem bvs x ->
        if Set.Poly.mem (tvs_of t1) x then None
        else Option.some @@ Map.Poly.singleton x t1

      | FunApp(funsym, [Var (x, _, _); t3], _), _ when not @@ Set.Poly.mem bvs x && (Stdlib.(=) funsym T_int.Add || Stdlib.(=) funsym T_int.Sub) ->
        if Set.Poly.mem (tvs_of t3) x || Set.Poly.mem (tvs_of t2) x then None
        else Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t2; t3])
      | FunApp(funsym, [t3; Var (x, _, _)], _), _ when not @@ Set.Poly.mem bvs x && (Stdlib.(=) funsym T_int.Add (*|| Stdlib.(=) funsym T_int.Mult*)) ->
        if Set.Poly.mem (tvs_of t3) x || Set.Poly.mem (tvs_of t2) x then None
        else Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t2; t3])
      | FunApp(funsym, [t3; Var (x, _, _)], _), _ when not @@ Set.Poly.mem bvs x && (Stdlib.(=) funsym T_int.Sub (*|| Stdlib.(=) funsym T_int.Div*)) ->
        if Set.Poly.mem (tvs_of t3) x || Set.Poly.mem (tvs_of t2) x then None
        else Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app funsym [t3; t2])
      | _, FunApp(funsym, [Var (x, _, _); t3], _) when not @@ Set.Poly.mem bvs x && (Stdlib.(=) funsym T_int.Add || Stdlib.(=) funsym T_real.RAdd || Stdlib.(=) funsym T_int.Sub || Stdlib.(=) funsym T_real.RSub) ->
        if Set.Poly.mem (tvs_of t3) x || Set.Poly.mem (tvs_of t2) x then None
        else Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t1; t3])
      | _, FunApp(funsym, [t3; Var (x, _, _)], _) when not @@ Set.Poly.mem bvs x && (Stdlib.(=) funsym T_int.Add (*|| Stdlib.(=) funsym T_int.Mult*)) ->
        if Set.Poly.mem (tvs_of t3) x || Set.Poly.mem (tvs_of t2) x then None
        else Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t1; t3])
      | _, FunApp(funsym, [t3; Var (x, _, _)], _) when not @@ Set.Poly.mem bvs x && (Stdlib.(=) funsym T_int.Sub (*|| Stdlib.(=) funsym T_int.Div*)) ->
        if Set.Poly.mem (tvs_of t3) x || Set.Poly.mem (tvs_of t2) x then None
        else Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app funsym [t3; t1])

      | _ -> None (* ToDo: remerdy incompleteness. support more general terms *)

  (* variables in t1 and t2 belong to different name spaces*)
  let pattern_match bvs t1 t2 =
    if Set.Poly.is_empty @@ Term.tvs_of t1 && Stdlib.(=) t1 t2 then
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

      | Var (x, _, _), _ when not @@ Set.Poly.mem bvs x -> Option.some @@ Map.Poly.singleton x t2

      | FunApp(funsym, [Var (x, _, _); t3], _), _
        when not @@ Set.Poly.mem bvs x && Set.Poly.is_empty @@ Term.tvs_of t3 && (Stdlib.(=) funsym T_int.Add || Stdlib.(=) funsym T_int.Sub) ->
        Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t2; t3])
      | FunApp(funsym, [t3; Var (x, _, _)], _), _
        when not @@ Set.Poly.mem bvs x && Set.Poly.is_empty @@ Term.tvs_of t3 && (Stdlib.(=) funsym T_int.Add (*|| Stdlib.(=) funsym T_int.Mult*)) ->
        Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app (T_int.neg_fsym funsym) [t2; t3])
      | FunApp(funsym, [t3; Var (x, _, _)], _), _
        when not @@ Set.Poly.mem bvs x && Set.Poly.is_empty @@ Term.tvs_of t3 && (Stdlib.(=) funsym T_int.Sub (*|| Stdlib.(=) funsym T_int.Div*)) ->
        Option.some @@ Map.Poly.singleton x (Term.mk_fsym_app funsym [t3; t2])

      | _ -> None (* ToDo: remerdy incompleteness. support more general terms *)
  (* especially, non-linear pattern is not supported *)


  let rec fold t ~f =
    match t with
    | Var(ident, sort, _) -> f#ftvar ident sort
    | FunApp(FVar(ident, sorts), args, _) -> f#fvar ident sorts (List.map args ~f:(fold ~f))
    | FunApp(T_int.Int i, [], _) -> f#fint i
    | FunApp(T_real.Real r, [], _) -> f#freal r
    | FunApp(T_int.Add, [t1; t2], _) -> f#fiadd (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_int.Sub, [t1; t2], _) -> f#fisub (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_int.Mult, [t1; t2], _) -> f#fimult (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_int.Div, [t1; t2], _) -> f#fidiv (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_int.Power, [t1; t2], _) -> f#fipower (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_int.Neg, [t1], _) -> f#fineg (fold t1 ~f)
    | FunApp(T_int.Mod, [t1; t2], _) -> f#fimod (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_real.RAdd, [t1; t2], _) -> f#fradd (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_real.RSub, [t1; t2], _) -> f#frsub (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_real.RMult, [t1; t2], _) -> f#frmult (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_real.RDiv, [t1; t2], _) -> f#frdiv (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_real.RPower, [t1; t2], _) -> f#frpower (fold t1 ~f) (fold t2 ~f)
    | FunApp(T_real.RNeg, [t1], _) -> f#frneg (fold t1 ~f)
    | FunApp(T_bool.Formula phi, [], _) -> f#fformula phi
    | FunApp(T_bool.IfThenElse, [t1; t2; t3], _) -> f#fite (fold t1 ~f) (fold t2 ~f) (fold t3 ~f)
    | FunApp(T_array.AStore, [t1; t2; t3], _) -> f#fastore (fold t1 ~f) (fold t2 ~f) (fold t3 ~f)
    | FunApp(T_array.ASelect, [t1; t2], _) -> f#faselect (fold t1 ~f) (fold t2 ~f)
    | _ -> failwith "unsupported fold case"

  let rec map_term ~f = function
    | FunApp(T_bool.Formula phi, [], info) -> f @@ FunApp(T_bool.Formula (Formula.map_term phi ~f), [], info)
    | FunApp(fsym, args, info) -> f @@ FunApp(fsym, List.map args ~f:(map_term ~f), info)
    | t -> f t
end

and Predicate : Type.PredicateType
  with type formula := Formula.t and
  type term := Term.t = struct

  type fixpoint = Mu | Nu

  type t =
    | Var of Ident.pvar * Sort.t list
    | Psym of pred_sym
    | Fixpoint of fixpoint * Ident.pvar * SortEnv.t * Formula.t

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
    | Fixpoint (_, _, bounds, body) ->
      Set.Poly.diff (Formula.tvs_of body) (SortEnv.args_set_of bounds)
  let pvs_of = function
    | Var (pvar, _) -> Set.Poly.singleton pvar
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, pvar, _, body) ->
      Set.Poly.remove (Formula.pvs_of body) pvar
  let term_sort_env_of = function
    | Var _ | Psym _ -> Set.Poly.empty
    | Fixpoint (_, _, bounds, body) ->
      Set.Poly.diff (Formula.term_sort_env_of body) (SortEnv.set_of bounds)
  let pred_sort_env_of = function
    | Var (pvar, sorts) -> Set.Poly.singleton (pvar, sorts)
    | Psym _ -> Set.Poly.empty
    | Fixpoint (_, pvar, params, phi) ->
      let sorts = SortEnv.sorts_of params in
      Set.Poly.diff (Formula.pred_sort_env_of phi) (Set.Poly.singleton (pvar, sorts))
  let sort_env_of pred =
    Set.Poly.union
      (term_sort_env_of pred)
      (Set.Poly.map ~f:(fun (Ident.Pvar name, sorts) -> Ident.Tvar(*ToDo*) name, Sort.mk_fun (sorts @ [T_bool.SBool])) @@ pred_sort_env_of pred)
  let terms_of = function
    | Var (_, _) -> Set.Poly.empty
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
      Fixpoint(flip_fixpoint fixpoint, pvar, bounds, negate_formula body)
    | Psym T_int.Leq -> Psym T_int.Gt | Psym T_real.RLeq -> Psym T_real.RGt
    | Psym T_int.Geq -> Psym T_int.Lt | Psym T_real.RGeq -> Psym T_real.RLt
    | Psym T_int.Lt -> Psym T_int.Geq | Psym T_real.RLt -> Psym T_real.RGeq
    | Psym T_int.Gt -> Psym T_int.Leq | Psym T_real.RGt -> Psym T_real.RLeq
    | Psym T_int.PDiv -> Psym T_int.NPDiv | Psym T_int.NPDiv -> Psym T_int.PDiv
    | Psym T_bool.Eq -> Psym T_bool.Neq
    | Psym T_bool.Neq -> Psym T_bool.Eq
    | Psym (T_dt.IsCons (name, dt)) -> Psym (T_dt.IsNotCons (name, dt))
    | Psym (T_dt.IsNotCons (name, dt)) -> Psym (T_dt.IsCons (name, dt))
    (*TODO:support "T_int_real.IsInt" *)
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
       | Some tvar -> Var (Ident.Pvar (Ident.name_of_tvar tvar), sort))
    | Psym sym -> Psym sym
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      let map = List.fold ~init:map ~f:Map.Poly.remove (SortEnv.args_of bounds) in
      Fixpoint(fixpoint, pvar, bounds, Formula.rename map body)
  let rename_pvars map = function
    | Var (pvar, sort) ->
      (match Map.Poly.find map pvar with
       | None -> Var (pvar, sort)
       | Some pvar' -> Var (pvar', sort))
    | Psym sym -> Psym sym
    | Fixpoint (fixpoint, pvar, bounds, body) ->
      let map' = Map.Poly.remove map pvar in
      Fixpoint(fixpoint, pvar, bounds, Formula.rename_pvars map' body)
  let subst_neg pvar = function
    | Var (pvar', sort) ->
      if Stdlib.(=) pvar' pvar then assert false (* it must be handled with Formula.subst_neg *)
      else Var (pvar', sort)
    | Psym psym -> Psym psym
    | Fixpoint (fixpoint, pvar', bounds, body) ->
      if Stdlib.(=) pvar' pvar then assert false
      else Fixpoint (fixpoint, pvar', bounds, Formula.subst_neg pvar body)
  let aconv_tvar = function
    | Var (pvar, sorts) -> Var (pvar, sorts)
    | Psym sym -> Psym sym
    | Fixpoint (fp, pvar, params, body) ->
      let params', map = SortEnv.refresh params in
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
  (*let str_of_predsym = function
    | T_bool.Eq -> "T_bool.Eq" | T_bool.Neq -> "T_bool.Neq"
    | T_int.Leq -> "T_int.Leq" | T_int.Lt -> "T_int.Lt" | T_int.Geq -> "T_int.Geq" | T_int.Gt -> "T_int.Gt"
    | _ -> failwith "undefineded predsymbol"*)
  let str_of_predsym = function
    | T_bool.Eq -> "="
    | T_bool.Neq -> "!="
    | T_int.Leq | T_real.RLeq -> "<="
    | T_int.Geq | T_real.RGeq -> ">="
    | T_int.Lt | T_real.RLt -> "<"
    | T_int.Gt | T_real.RGt -> ">"
    | T_int.PDiv -> "|" | T_int.NPDiv -> "!|"
    | T_num.NLeq svar -> sprintf "<=_%s" (Ident.name_of_svar svar)
    | T_num.NGeq svar -> sprintf ">=_%s" (Ident.name_of_svar svar)
    | T_num.NLt svar -> sprintf "<_%s" (Ident.name_of_svar svar)
    | T_num.NGt svar -> sprintf ">_%s" (Ident.name_of_svar svar)
    | T_dt.IsCons (name, _) -> sprintf "[is_%s]" (name) 
    | T_dt.IsNotCons (name, _) -> sprintf "[is_not_%s]" (name) 
    | _ -> failwith "unknown pred symbol"
  let str_of_fixpoint = function
    | Mu -> "mu"
    | Nu -> "nu"
  (*let str_of = function
    | Var (Ident.Pvar id, _) -> Printf.sprintf "Var (%s)" id
    | Psym symbol -> Printf.sprintf "Psym %s" @@ str_of_predsym symbol
    | Fixpoint (_, _, _, _) -> "Fixpoint" (* TODO: implement *)*)
  let str_of pred =
    match pred with
    | Var (Ident.Pvar ident, _sorts) -> ident
    (*Printf.sprintf "(%s : [%s])" ident
      (List.map ~f:(fun sort -> Term.str_of_sort sort) sorts |> String.concat ~sep:";")*)
    | Psym sym -> str_of_predsym sym
    | Fixpoint (fp, Ident.Pvar pident, params, phi) ->
      Printf.sprintf "(%s%s(%s). %s)"
        (str_of_fixpoint fp)
        pident
        (SortEnv.str_of Term.str_of_sort params)
        (Formula.str_of ~priority:0 phi)
end

and Atom : Type.AtomType 
  with type predicate := Predicate.t and
  type term := Term.t and
  type termSubst := TermSubst.t and
  type formula := Formula.t = struct

  type t =
    | True of info
    | False of info
    | App of Predicate.t * Term.t list * info

  (** Construction *)
  let mk_true ?(info=Dummy) () = True info
  let mk_false ?(info=Dummy) () = False info
  let mk_app ?(info=Dummy) pred args = App(pred, args, info)

  let mk_psym_app ?(info=Dummy) psym args = mk_app ~info (Predicate.mk_psym psym) args
  let mk_pvar_app ?(info=Dummy) pvar sorts args = mk_app ~info (Predicate.mk_var pvar sorts) args

  let of_bool_var b = T_bool.mk_eq (Term.mk_var b T_bool.SBool) (T_bool.mk_true ())
  let of_neg_bool_var b = T_bool.mk_eq (Term.mk_var b T_bool.SBool) (T_bool.mk_false ())
  let of_bool_term t = T_bool.mk_eq t (T_bool.mk_true ())
  let of_neg_bool_term t = T_bool.mk_eq t (T_bool.mk_false ())

  (** Observation *)
  let is_true = function True _ -> true | _ -> false
  let is_false = function False _ -> true | _ -> false
  let is_app = function App (_, _, _) -> true | _ -> false
  let is_psym_app = function App(Predicate.Psym _, _, _) -> true | _ -> false
  let is_pvar_app = function App(Predicate.Var _, _, _)  -> true | _   -> false

  let tvs_of = function
    | True _ | False _ -> Set.Poly.empty
    | App(pred, args, _) ->
      Set.Poly.union_list @@ Predicate.tvs_of pred :: List.map args ~f:Term.tvs_of
  let pvs_of = function
    | True _ | False _ -> Set.Poly.empty
    | App(pred, args, _) ->
      Set.Poly.union_list @@ Predicate.pvs_of pred :: List.map args ~f:Term.pvs_of
  let fvs_of atm =
    Set.Poly.union
      (tvs_of atm)
      (Set.Poly.map ~f:(fun (Ident.Pvar name) -> Ident.Tvar(*ToDo*) name) @@ pvs_of atm)
  let funsyms_of = function
    | True _ | False _ -> Set.Poly.empty
    | App(_, terms, _) ->
      Set.Poly.union_list @@ List.map ~f:Term.funsyms_of terms
  let term_sort_env_of = function
    | True _ | False _ -> Set.Poly.empty
    | App(pred, args, _) ->
      Set.Poly.union_list @@
      (Predicate.term_sort_env_of pred :: List.map args ~f:Term.term_sort_env_of)
  let pred_sort_env_of = function
    | True _ | False _ -> Set.Poly.empty
    | App (pred, args, _) ->
      Set.Poly.union_list @@
      (Predicate.pred_sort_env_of pred :: List.map args ~f:Term.pred_sort_env_of)
  let sort_env_of atm =
    Set.Poly.union
      (term_sort_env_of atm)
      (Set.Poly.map ~f:(fun (Ident.Pvar name, sorts) -> Ident.Tvar(*ToDo*) name, Sort.mk_fun (sorts @ [T_bool.SBool])) @@ pred_sort_env_of atm)
  let pathexps_of atom =
    match atom with
    | True _ | False _ -> Set.Poly.empty
    | App(Predicate.Fixpoint (_, _, bounds, body), args, _) -> 
      Set.Poly.diff (Formula.pathexps_of body) (Set.Poly.of_list @@ SortEnv.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))
      |> Set.Poly.union @@ Set.Poly.union_list @@ List.map args ~f:Term.pathexps_of
    | App(_, args, _) ->
      Set.Poly.union_list @@ List.map args ~f:Term.pathexps_of
  let filtered_terms_of atom ~f =
    match atom with
    | True _ | False _ -> Set.Poly.empty
    | App(Predicate.Fixpoint (_, _, _, body), args, _) ->
      Formula.filtered_terms_of body ~f 
      |> Set.Poly.union @@ List.fold_left args ~init:Set.Poly.empty ~f:(fun ret t -> Set.Poly.union ret (Term.filtered_terms_of t ~f))
    | App(_, args, _) ->
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
    | App(pred, _, _) -> Predicate.nesting_level pred
  let number_of_quantifiers = function
    | True _ | False _ -> 0
    | App(pred, _, _) -> Predicate.number_of_quantifiers pred
  let number_of_pvar_apps is_pos = function
    | True _ | False _ -> 0
    | App(Predicate.Var _, _, _) -> if is_pos then 1 else 0
    | App(Predicate.Psym _, _, _) -> 0
    | App(Predicate.Fixpoint _, _, _) -> assert false (* This function does not support fixpoint fomulas appropriately *)
  let count_pvar_apps = function
    | True _ | False _ -> []
    | App(Predicate.Var (pvar, _), _, _) -> [pvar, (1, 0)]
    | App(Predicate.Psym _, _, _) -> []
    | App(Predicate.Fixpoint _, _, _) -> assert false

  let ast_size = function
    | True _ | False _ -> 1
    | App(Predicate.Var _, terms, _) | App(Predicate.Psym _, terms, _) ->
      (List.fold ~f:(fun acc term -> acc + Term.ast_size term) ~init:1 terms)
    | App(Predicate.Fixpoint (_, _, _, phi), terms, _) ->
      (List.fold ~f:(fun acc term -> acc + Term.ast_size term) ~init:(Formula.ast_size phi) terms)

  (** Destruction *)
  let let_app = function
    | App(pred, args, info) -> pred, args, info
    | _ -> assert false
  let let_psym_app = function
    | App(Predicate.Psym sym, args, info) -> sym, args, info
    | _ -> assert false
  let let_pvar_app = function
    | App(Predicate.Var (pvar, sorts), args, info) -> pvar, sorts, args, info
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
    | App(_, _, info) -> info
  let pvar_of = function App (Predicate.Var (pvar, _), _, _) -> pvar | _ -> assert false

  (** Substitution *)
  let rename map = function
    | True info -> True info
    | False info -> False info
    | App(pred, args, info) ->
      App(Predicate.rename map pred, List.map ~f:(Term.rename map) args, info)
  let rename_pvars map = function
    | True info -> True info
    | False info -> False info
    | App(pred, args, info) ->
      App(Predicate.rename_pvars map pred, List.map args ~f:(Term.rename_pvars map), info)
  let subst map = function
    | True info -> True info
    | False info -> False info
    | App(Var (pvar, sorts), [], info) ->
      let tvar = Ident.Tvar (Ident.name_of_pvar pvar) in
      (match Map.Poly.find map tvar with
       | Some (Term.FunApp (T_bool.Formula (Atom (True _, _)), [], _)) -> True info
       | Some (Term.FunApp (T_bool.Formula (Atom (False _, _)), [], _)) -> False info
       | Some t -> of_bool_term t
       | None -> App(Var (pvar, sorts), [], info))
    | App(Var (pvar, sorts), args, info) ->
      App(Var (pvar, sorts), List.map ~f:(Term.subst map) args, info)
    | App(Psym sym, args, info) ->
      App(Psym sym, List.map ~f:(Term.subst map) args, info)
    | App(Fixpoint (fixpoint, pvar, bounds, body), args, info) ->
      let map' = List.fold ~init:map ~f:Map.Poly.remove (SortEnv.args_of bounds) in
      App(Fixpoint(fixpoint, pvar, bounds, Formula.subst map' body), List.map ~f:(Term.subst map') args, info)
  let subst_preds map = function
    | True info -> Formula.mk_atom (True info)
    | False info -> Formula.mk_atom (False info)
    | App(Predicate.Var (pvar, sort), args, info) ->
      let args = List.map ~f:(Term.subst_preds map) args in
      (match Map.Poly.find map pvar with
       | Some (params, phi) ->
         let map =
           try (* ToDo : check whether args match sorts *)
             Map.Poly.of_alist_exn @@ List.zip_exn (SortEnv.args_of params) args
           with e -> Printf.printf "ident: %s #params: %d #args: %d"
                       (Ident.name_of_pvar pvar)
                       (SortEnv.length params)
                       (List.length args);
             raise e
         in
         Formula.subst map phi
       | None -> Formula.mk_atom (App(Predicate.Var (pvar, sort), args, info)))
    | App(Psym sym, args, info) ->
      Formula.mk_atom (App(Psym sym, List.map ~f:(Term.subst_preds map) args, info))
    | App(Predicate.Fixpoint (fp, pvar, params, phi), terms, info) ->
      let terms = List.map ~f:(Term.subst_preds map) terms in
      let map' = Map.Poly.remove map pvar in
      Formula.mk_atom (App(Predicate.Fixpoint (fp, pvar, params, Formula.subst_preds map' phi), terms, info))
  let subst_neg pvar = function
    | True info -> True info
    | False info -> False info
    | App(pred, args, info) -> App(Predicate.subst_neg pvar pred, args, info)
  let aconv_tvar = function
    | True info -> True info | False info -> False info
    | App (pred, args, info) ->
      App (Predicate.aconv_tvar pred, args, info)
  let aconv_pvar = function
    | True info -> True info
    | False info -> False info
    | App (pred, args, info) ->
      let pred = Predicate.aconv_pvar pred in
      let args = List.map ~f:(fun arg -> Term.aconv_pvar arg) args in
      App (pred, args, info)

  (** Transformation *)
  let refresh_tvar (senv, atm) =
    let map = Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar()) in
    Map.rename_keys_map map senv, rename map atm

  let negate ?(negate_formula = Formula.mk_neg ~info:Dummy) = function
    | True info -> False info
    | False info -> True info
    | App (pred, args, info) -> App(Predicate.negate ~negate_formula pred, args, info)
  let complete_psort map = function
    | True info' -> True info'
    | False info' -> False info'
    | App (pred, terms, info') -> App (Predicate.complete_psort map pred, terms, info') 
  let elim_neq = function
    | App (Psym T_bool.Neq, [t1; t2], _) ->
      Formula.mk_neg @@ Formula.eq t1 t2
    | atm -> Formula.mk_atom atm
  let elim_ite = function
    | App (Psym (T_bool.Eq | T_bool.Neq | T_int.Leq | T_int.Geq | T_int.Lt | T_int.Gt) as pred, [t1; t2], info) ->
      List.cartesian_product (Term.elim_ite t1) (Term.elim_ite t2)
      |> List.map ~f:(fun ((phi1, t1), (phi2, t2)) ->
          Formula.and_of [phi1; phi2; Formula.Atom (App (pred, [t1; t2], info), Dummy)])
      |> Formula.or_of
    | App(pred, [t], info) -> 
      List.map ~f:(fun (phi, t) -> Formula.and_of [phi; Formula.mk_atom (App(pred, [t], info))]) @@ Term.elim_ite t
      |> Formula.or_of
    | atm -> Formula.mk_atom atm
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
      if Stdlib.(=) (Term.sort_of t1) T_bool.SBool then
        let phi1 = Term.rm_boolean_term t1 in
        let phi2 = Term.rm_boolean_term t2 in
        Formula.mk_or (Formula.mk_and phi1 phi2) (Formula.mk_and (Formula.mk_neg phi1) (Formula.mk_neg phi2))
      else Formula.mk_atom atom
    | App (Predicate.Psym T_bool.Neq, [t1; t2], _) ->
      if Stdlib.(=) (Term.sort_of t1) T_bool.SBool then
        let phi1 = Term.rm_boolean_term t1 in
        let phi2 = Term.rm_boolean_term t2 in
        Formula.mk_or (Formula.mk_and phi1 (Formula.mk_neg phi2)) (Formula.mk_and (Formula.mk_neg phi1) phi2)
      else Formula.mk_atom atom
    | atom -> Formula.mk_atom atom

  let extend_pred_params ident (extended_params: SortEnv.t) = function
    | App (Predicate.Var (ident', params), args, info) when Stdlib.(=) ident ident' ->
      let extended_sorts: Sort.t list = SortEnv.sorts_of extended_params in
      let params = params @ extended_sorts in
      let extended_args = Term.of_sort_env extended_params in
      let args = args @ extended_args in
      App (Predicate.Var (ident, params), args, info)
    | App (pred, args, info) ->
      let pred = Predicate.extend_pred_params ident extended_params pred in
      let args = List.map ~f:(fun arg -> Term.extend_pred_params ident extended_params arg) args in
      App (pred, args, info)
    | x -> x

  (** Printing *)
  (*let str_of = function
    | True _ -> "True" | False _ -> "False"
    | App(pred, terms, _) ->
      Printf.sprintf "App(%s, %s)"
        (Predicate.str_of pred)
        (List.fold ~f:(fun acc term -> acc ^ ", " ^ (Term.str_of term)) ~init:"" terms)*)
  let str_of ?(priority=0) atom =
    match atom with
    | True _ -> "true"
    | False _ -> "false"
    | App (Predicate.Psym (T_bool.Eq as op), [t1; t2], _)
    | App (Predicate.Psym (T_bool.Neq as op), [t1; t2], _)
    | App (Predicate.Psym (T_int.Leq as op), [t1; t2], _) | App (Predicate.Psym (T_real.RLeq as op), [t1; t2], _)
    | App (Predicate.Psym (T_int.Geq as op), [t1; t2], _) | App (Predicate.Psym (T_real.RGeq as op), [t1; t2], _)
    | App (Predicate.Psym (T_int.Lt as op), [t1; t2], _) | App (Predicate.Psym (T_real.RLt as op), [t1; t2], _)
    | App (Predicate.Psym (T_int.Gt as op), [t1; t2], _) | App (Predicate.Psym (T_real.RGt as op), [t1; t2], _)
    | App (Predicate.Psym (T_int.PDiv as op), [t1; t2], _) | App (Predicate.Psym (T_int.NPDiv as op), [t1; t2], _) ->
      Priority.add_bracket priority Priority.eq_neq_lt_leq_gt_geq
      @@ Printf.sprintf "%s %s %s"
        (Term.str_of ~priority:Priority.eq_neq_lt_leq_gt_geq t1)
        (Predicate.str_of_predsym op)
        (Term.str_of ~priority:Priority.eq_neq_lt_leq_gt_geq t2)
    | App (pred, args, _) ->
      if List.length args = 0 then
        Predicate.str_of pred
      else
        Priority.add_bracket priority Priority.fun_app
        @@ Printf.sprintf "(%s %s)"
          (Predicate.str_of pred)
          (String.concat ~sep:" " @@ List.map args ~f:(Term.str_of ~priority:Priority.fun_app))

  (** Unification *)
  let unify bvs atom1 atom2 =
    match atom1, atom2 with
    | True _ , True _ | False _, False _ -> Some Map.Poly.empty
    | App(pred, terms, _), App(pred', terms', _)
      when Stdlib.(=) pred pred' && List.length terms = List.length terms'->
      List.fold2_exn terms terms' ~init:(Some Map.Poly.empty) ~f:(fun opt t1 t2 ->
          Option.(opt >>= fun map ->
                  match Term.unify bvs (Term.subst map t1) (Term.subst map t2) with
                  | Some theta -> Some (TermSubst.merge theta (Map.Poly.map map ~f:(Term.subst theta)))
                  | None -> None))
    | _ -> None

  let pattern_match bvs atom1 atom2 =
    match atom1, atom2 with
    | True _ , True _ | False _, False _ -> Some Map.Poly.empty
    | App(pred, terms, _), App(pred', terms', _)
      when Stdlib.(=) pred pred' && List.length terms = List.length terms'->
      (try
         List.fold2_exn terms terms' ~init:(Some Map.Poly.empty) ~f:(fun opt t1 t2 ->
             Option.(opt >>= fun map ->
                     match Term.pattern_match bvs t1 t2 with
                     | Some theta -> Some (TermSubst.merge theta map)
                     | None -> None))
       with _ -> (*nonlinear pattern not supported*)None)
    | _ -> None



  let fold atom ~f =
    match atom with
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
    | App(Predicate.Var (ident, sort), args, _) -> f#fpvar ident sort args
    | _ -> failwith "unsupported fold case"

  let map_term atom ~f =
    match atom with
    | True _ | False _ -> atom
    | App(pred, ts, info) -> App(pred, List.map ts ~f:(Term.map_term ~f), info)

  let fold_map_term atom ~f ~ft =
    fold ~f @@ map_term atom ~f:ft

  let instantiate atom =
    if is_pvar_app atom then
      map_term atom ~f:(function |Term.Var(ident, sort, _) -> if Ident.is_dontcare ident then Term.mk_dummy sort else assert false | t -> t)
    else atom
end

and Formula : Type.FormulaType 
  with type atom := Atom.t and
  type termSubst := TermSubst.t and
  type predicate_fixpoint := Predicate.fixpoint and
  type term := Term.t and
  type rand := Rand.t = struct

  type unop = Not
  type binop = And | Or | Imply | Iff
  type binder = Forall | Exists | Random of Rand.t

  type t =
    | Atom of Atom.t * info
    | UnaryOp of unop * Formula.t * info
    | BinaryOp of binop * Formula.t * Formula.t * info
    | Bind of binder * SortEnv.t * Formula.t * info
    | LetRec of (Predicate.fixpoint * Ident.pvar * SortEnv.t * Formula.t) list * Formula.t * info

  (** Construction *)
  let mk_atom ?(info=Dummy) atom = Atom(atom, info)
  let mk_unop ?(info=Dummy) op phi = UnaryOp(op, phi, info)
  let mk_neg ?(info=Dummy) phi = UnaryOp(Not, phi, info)
  let mk_binop ?(info=Dummy) op phi1 phi2 = BinaryOp(op, phi1, phi2, info)
  let mk_and ?(info=Dummy) phi1 phi2 = BinaryOp(And, phi1, phi2, info)
  let mk_or ?(info=Dummy) phi1 phi2 = BinaryOp(Or, phi1, phi2, info)
  let mk_imply ?(info=Dummy) phi1 phi2 = BinaryOp(Imply, phi1, phi2, info)
  let mk_iff ?(info=Dummy) phi1 phi2 = BinaryOp(Iff, phi1, phi2, info)
  let mk_bind ?(info=Dummy) binder bound body = Bind(binder, bound, body, info)

  let mk_forall ?(info=Dummy) bound body = Bind(Forall, bound, body, info)
  let mk_exists ?(info=Dummy) bound body = Bind(Exists, bound, body, info)
  let mk_random ?(info=Dummy) r bound body = Bind(Random r, bound, body, info)
  let mk_bind_if_bounded ?(info=Dummy) binder bound body =
    if SortEnv.is_empty bound then body else mk_bind binder bound body ~info
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
      mk_random rand (SortEnv.singleton var (Rand.sort_of rand)) (mk_randoms tl f)
  let mk_letrec ?(info=Dummy) funcs body = LetRec(funcs, body, info)
  let mk_false ?(info=Dummy) () = Atom(Atom.mk_false (), info)
  let mk_true ?(info=Dummy) () = Atom(Atom.mk_true (), info)

  let and_of ?(info=Dummy) phis =
    let rec aux acc = function
      | [] -> acc
      | Atom(Atom.True _, _) :: phis -> aux acc phis
      | Atom(Atom.False info', info) :: _ -> Atom(Atom.False info', info)
      | phi :: phis -> aux (mk_and acc phi ~info) phis
    in
    match phis with
    | [] -> Atom (Atom.True info, info)
    | x :: xs -> aux x xs
  let or_of ?(info=Dummy) phis =
    let rec aux acc = function
      | [] -> acc
      | Atom(Atom.True info', info) :: _ -> Atom(Atom.True info', info)
      | Atom(Atom.False _, _) :: phis -> aux acc phis
      | phi :: phis -> aux (mk_or acc phi ~info) phis
    in
    match phis with
    | [] -> Atom (Atom.False info, info)
    | x :: xs -> aux x xs
  let xor_of ?(info=Dummy) phis =
    match phis with
    | Atom(Atom.True info', info) :: Atom(Atom.True _, _) :: []
    | Atom(Atom.False info', info) :: Atom(Atom.False _, _) :: [] -> Atom(Atom.False info', info)
    | Atom(Atom.True info', info) :: Atom(Atom.False _, _) :: []
    | Atom(Atom.False info', info) :: Atom(Atom.True _, _) :: [] -> Atom(Atom.True info', info)
    | Atom(Atom.True _, _) :: phi :: []
    | phi :: Atom(Atom.True _, _) :: [] -> mk_neg phi ~info
    | Atom(Atom.False _, _) :: phi :: []
    | phi :: Atom(Atom.False _, _) :: [] -> phi
    | phi1 :: phi2 :: [] ->
      mk_or (mk_and (mk_neg phi1 ~info) phi2 ~info) (mk_and phi1 (mk_neg phi2 ~info) ~info) ~info
    | _ -> assert false
  let of_bool_var b = mk_atom (Atom.of_bool_var b)
  let of_neg_bool_var b = mk_atom (Atom.of_neg_bool_var b)
  let rec of_bool_term = function
    | Term.Var (b, T_bool.SBool, _) -> of_bool_var b
    | Term.FunApp (T_bool.Formula phi, _, _) -> phi
    | Term.FunApp (T_bool.IfThenElse, [t1; t2; t3], info) (*as t*) ->
      (*mk_atom (T_bool.mk_eq t (T_bool.mk_true ()))*)
      let p1 = of_bool_term t1 in
      let p2 = of_bool_term t2 in
      let p3 = of_bool_term t3 in
      mk_or (mk_and p1 p2) (mk_and (mk_neg p1) p3) ~info
    | term -> failwith (Term.str_of term)

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
  let is_atom = function Atom(_, _) -> true | _ -> false
  let is_unop = function UnaryOp(_, _, _) -> true | _ -> false
  let is_neg = function UnaryOp(Not, _, _) -> true | _ -> false
  let is_binop = function BinaryOp(_, _, _, _) -> true | _ -> false
  let is_true = function Atom(Atom.True _, _) -> true | _ -> false
  let is_false = function Atom(Atom.False _, _) -> true | _ -> false
  let is_and = function BinaryOp(And, _, _, _) -> true | _ -> false
  let is_or = function BinaryOp(Or, _, _, _) -> true | _ -> false
  let is_imply = function BinaryOp(Imply, _, _, _) -> true | _ -> false
  let is_iff = function BinaryOp(Iff, _, _, _) -> true | _ -> false
  let is_bind = function Bind(_, _, _, _) -> true | _ -> false
  let is_forall = function Bind(Forall, _, _, _) -> true | _ -> false
  let is_exists = function Bind(Exists, _, _, _) -> true | _ -> false
  let is_random = function Random _ -> true | _ -> false
  let is_letrec = function LetRec _ -> true | _ -> false

  let rec tvs_of = function
    | Atom(atom, _) ->  Atom.tvs_of atom
    | UnaryOp(_, phi, _) -> tvs_of phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (tvs_of phi1) (tvs_of phi2)
    | Bind(_, bounds, phi, _) ->
      Set.Poly.diff (tvs_of phi) (SortEnv.args_set_of bounds)
    | LetRec(funcs, phi, _) ->
      (tvs_of phi :: List.map funcs ~f:(fun (_, _, bounds, body) ->
           Set.Poly.diff (tvs_of body) (SortEnv.args_set_of bounds)))
      |> Set.Poly.union_list
  let rec pvs_of = function
    | Atom(atom, _) -> Atom.pvs_of atom
    | UnaryOp(_, phi, _) -> pvs_of phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (pvs_of phi1) (pvs_of phi2)
    | Bind(_, _, phi, _) -> pvs_of phi
    | LetRec(funcs, phi, _) ->
      Set.Poly.diff
        ((pvs_of phi :: List.map ~f:(fun (_, _, _, body) -> pvs_of body) funcs)
         |> Set.Poly.union_list)
        (funcs |> List.map ~f:(fun (_, pvar, _, _) -> pvar) |> Set.Poly.of_list)
  let fvs_of phi =
    Set.Poly.union
      (tvs_of phi)
      (Set.Poly.map ~f:(fun (Ident.Pvar name) -> Ident.Tvar(*ToDo*) name) @@ pvs_of phi)

  let rec funsyms_of = function
    | Atom(atom, _) -> Atom.funsyms_of atom
    | UnaryOp(_, phi, _) -> funsyms_of phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (funsyms_of phi1) (funsyms_of phi2)
    | Bind(_, _, phi, _) -> funsyms_of phi
    | LetRec(_, _, _) -> assert false (* not implemented *)
  let rec nesting_level =function
    | UnaryOp(_, phi, _) -> nesting_level phi
    | BinaryOp(_, phi1, phi2, _) ->
      max (nesting_level phi1) (nesting_level phi2)
    | Atom(atom, _) -> Atom.nesting_level atom
    | Bind(_, _, phi, _) -> nesting_level phi
    | LetRec (bounded, body, _) ->
      let levels = List.map ~f:(fun (_, _, _, phi) -> 1 + nesting_level phi) bounded in
      let levels = (nesting_level body) :: levels in
      List.fold ~f:(fun acc level -> if acc < level then level else acc) ~init:0 levels
  let rec term_sort_env_of = function
    | Atom(atom, _) -> Atom.term_sort_env_of atom
    | UnaryOp(_, phi, _) -> term_sort_env_of phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (term_sort_env_of phi1) (term_sort_env_of phi2)
    | Bind(_, bounds, phi, _) -> Set.Poly.diff (term_sort_env_of phi) (SortEnv.set_of bounds)
    | LetRec(funcs, phi, _) ->
      Set.Poly.union_list @@
      (term_sort_env_of phi :: List.map funcs ~f:(fun (a, b, c, d) -> Predicate.term_sort_env_of (Predicate.Fixpoint (a, b, c, d))))
  let rec pred_sort_env_of = function
    | Atom (atom, _) -> Atom.pred_sort_env_of atom
    | UnaryOp (_, phi, _) -> pred_sort_env_of phi
    | BinaryOp (_, phi1, phi2, _) -> Set.Poly.union (pred_sort_env_of phi1) (pred_sort_env_of phi2)
    | Bind (_, _, phi, _) -> pred_sort_env_of phi
    | LetRec (funcs, phi, _) ->
      let pvs =
        Set.Poly.union_list @@
        (pred_sort_env_of phi :: List.map funcs ~f:(fun (a, b, c, d) -> Predicate.pred_sort_env_of (Predicate.Fixpoint (a, b, c, d))))
      in
      let bounded = Set.Poly.of_list @@ List.map funcs ~f:(fun (_, pvar, args, _) -> (pvar, SortEnv.sorts_of args)) in
      Set.Poly.diff pvs bounded
  let sort_env_of phi =
    Set.Poly.union
      (term_sort_env_of phi)
      (Set.Poly.map ~f:(fun (Ident.Pvar name, sorts) -> Ident.Tvar(*ToDo*) name, Sort.mk_fun (sorts @ [T_bool.SBool])) @@ pred_sort_env_of phi)
  let rec pathexps_of phi =
    match phi with
    | Atom(atom, _) ->  Atom.pathexps_of atom
    | UnaryOp(_, phi, _) -> pathexps_of phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (pathexps_of phi1) (pathexps_of phi2)
    | Bind(_, bounds, phi, _) ->
      Set.Poly.diff (pathexps_of phi) (Set.Poly.of_list @@ SortEnv.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))
    | LetRec(funcs, phi, _) ->
      (pathexps_of phi :: List.map funcs ~f:(fun (_, _, bounds, body) ->
           Set.Poly.diff (pathexps_of body) (Set.Poly.of_list @@ SortEnv.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))))
      |> Set.Poly.union_list
  let rec filtered_terms_of phi ~f =
    match phi with
    | Atom(atom, _) ->  Atom.filtered_terms_of atom ~f
    | UnaryOp(_, phi, _) -> filtered_terms_of phi ~f
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (filtered_terms_of phi1 ~f) (filtered_terms_of phi2 ~f)
    | Bind(_, bounds, phi, _) ->
      Set.Poly.diff (filtered_terms_of phi ~f) (Set.Poly.of_list @@ SortEnv.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))
    | LetRec(funcs, phi, _) ->
      ((filtered_terms_of phi ~f):: List.map funcs ~f:(fun (_, _, bounds, body) ->
           Set.Poly.diff (filtered_terms_of body ~f) (Set.Poly.of_list @@ SortEnv.map bounds ~f:(fun (tvar, sort) -> Term.mk_var tvar sort))))
      |> Set.Poly.union_list
  let rec conjuncts_of = function
    | BinaryOp (And, phi1, phi2, _) -> Set.Poly.union (conjuncts_of phi1) (conjuncts_of phi2)
    | phi -> Set.Poly.singleton phi

  let rec disjuncts_of = function
    |BinaryOp (Or, phi1, phi2, _) -> Set.Poly.union (disjuncts_of phi1) (disjuncts_of phi2)
    |phi -> Set.Poly.singleton phi

  let rec number_of_quantifiers = function
    | UnaryOp(_, phi, _) -> number_of_quantifiers phi
    | BinaryOp(_, phi1, phi2, _) ->
      (number_of_quantifiers phi1) + (number_of_quantifiers phi2)
    | Atom(atom, _) -> Atom.number_of_quantifiers atom
    | Bind(_, _, phi, _) -> 1 + (number_of_quantifiers phi)
    | LetRec (bounded, body, _) ->
      let nums = List.map ~f:(fun (_, _, _, phi) -> number_of_quantifiers phi) bounded in
      let nums = (number_of_quantifiers body) :: nums in
      List.fold ~f:(fun acc num -> acc + num) ~init:0 nums

  let rec number_of_pvar_apps is_pos = function
    | Atom(atom, _) -> Atom.number_of_pvar_apps is_pos atom
    | UnaryOp(Not, phi, _) -> number_of_pvar_apps (not is_pos) phi
    | BinaryOp(Imply, phi1, phi2, _) ->
      (number_of_pvar_apps (not is_pos) phi1) + (number_of_pvar_apps is_pos phi2)
    | BinaryOp(Iff, _, _, _) -> assert false
    | BinaryOp(And, phi1, phi2, _) | BinaryOp(Or, phi1, phi2, _) ->
      (number_of_pvar_apps is_pos phi1) + (number_of_pvar_apps is_pos phi2)
    | Bind(_, _, phi, _) -> number_of_pvar_apps is_pos phi
    | LetRec(_, _, _) -> assert false
  (*List.fold (fun acc (_, _, _, phi) -> acc + (number_of_pvar_apps is_pos phi))
    (number_of_pvar_apps is_pos body) bounded*)

  let rec count_pvar_apps = function
    | Atom(atom, _) -> Atom.count_pvar_apps atom
    | UnaryOp(Not, phi, _) -> List.Assoc.map (count_pvar_apps phi) ~f:(fun (pc, nc) -> nc, pc)
    | BinaryOp(Imply, phi1, phi2, _) ->
      let r1 = List.Assoc.map (count_pvar_apps phi1) ~f:(fun (pc, nc) -> nc, pc) in
      let r2 = count_pvar_apps phi2 in
      (r1 @ r2)
      |> List.group ~break:(fun x y -> Stdlib.(<>) (fst x) (fst y))
      (* |> Util.List.classify (fun x y -> fst x = fst y) *)
      |> List.map ~f:(function [] -> assert false | (x :: xs) ->
          fst x,
          let pcs, ncs = List.unzip (snd x :: List.map ~f:snd xs) in
          (List.fold pcs ~init:0 ~f:(+), List.fold ncs ~init:0 ~f:(+))
        )
    | BinaryOp(Iff, _, _, _) -> assert false
    | BinaryOp(And, phi1, phi2, _) | BinaryOp(Or, phi1, phi2, _) ->
      let r1 = count_pvar_apps phi1 in
      let r2 = count_pvar_apps phi2 in
      (r1 @ r2)
      |> List.group ~break:(fun x y -> Stdlib.(<>) (fst x) (fst y))
      (* |> Util.List.classify (fun x y -> fst x = fst y) *)
      |> List.map ~f:(function [] -> assert false | (x :: xs) ->
          fst x,
          let pcs, ncs = List.unzip (snd x :: List.map ~f:snd xs) in
          (List.fold pcs ~init:0 ~f:(+), List.fold ncs ~init:0 ~f:(+))
        )
    | Bind(_, _, phi, _) -> count_pvar_apps phi
    | LetRec(_, _, _) -> assert false

  let rec ast_size = function
    | UnaryOp(_, phi, _) -> 1 + ast_size phi
    | BinaryOp(_, phi1, phi2, _) -> 1 + ast_size phi1 + ast_size phi2
    | Atom(atom, _) -> 1 + Atom.ast_size atom
    | Bind(_, _, phi, _) -> 1 + ast_size phi
    | LetRec (bounded, phi, _) ->
      List.fold ~init:1 bounded ~f:(fun acc (_, _, _, phi) -> acc + (ast_size phi)) + ast_size phi

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
  let atoms_of phi =
    let rec aux pos = function
      | UnaryOp(Not, phi, _) -> aux (not pos) phi
      (*| UnaryOp(_, phi, _) -> aux pos phi*)
      | BinaryOp(Imply, _, _, _) | BinaryOp(Iff, _, _, _) -> assert false
      | BinaryOp(_, phi1, phi2, _) ->
        let pos1, neg1 = aux pos phi1 in
        let pos2, neg2 = aux pos phi2 in
        Set.Poly.union pos1 pos2, Set.Poly.union neg1 neg2
      | Atom(atom, _) ->
        if pos then Set.Poly.singleton atom, Set.Poly.empty
        else Set.Poly.empty, Set.Poly.singleton atom
      | Bind(_, _, phi, _) -> aux pos phi
      | LetRec (_bounded, _body, _) -> assert false
      (*Set.Poly.union_list @@
        aux pos body :: List.map bounded ~f:(fun (_, _, _, phi) -> aux pos phi)*)
    in aux true phi
  let psym_pvar_apps_of phi =
    let pos, neg = atoms_of phi in
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

  (** Construction *)
  let bind ?(info=Dummy) binder bounds body =
    let ftv = tvs_of body in
    let bounds = SortEnv.filter ~f:(fun (tvar, _) -> Set.Poly.mem ftv tvar) bounds in
    mk_bind_if_bounded binder bounds body ~info
  let forall ?(info=Dummy) bounds body = bind ~info Forall bounds body
  let exists ?(info=Dummy) bounds body = bind ~info Exists bounds body

  (** Destruction *)
  let let_atom = function
    | Atom(atom, info) -> atom, info
    | _ -> assert false
  let let_unop = function
    | UnaryOp(op, phi, info) -> op, phi, info
    | _ -> assert false
  let let_neg = function
    | UnaryOp(Not, phi, info) -> phi, info
    | _ -> assert false
  let let_binop = function
    | BinaryOp(op, phi1, phi2, info) -> op, phi1, phi2, info
    | _ -> assert false
  let let_and = function
    | BinaryOp(And, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_or = function
    | BinaryOp(Or, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_imply = function
    | BinaryOp(Imply, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_iff = function
    | BinaryOp(Iff, phi1, phi2, info) -> phi1, phi2, info
    | _ -> assert false
  let let_bind = function
    | Bind(binder, params, body, info) -> binder, params, body, info
    | _ -> assert false
  let let_forall = function
    | Bind(Forall, params, body, info) -> params, body, info
    | _ -> assert false
  let let_exists = function
    | Bind(Exists, params, body, info) -> params, body, info
    | _ -> assert false
  let let_forall_or_formula = function
    | Bind(Forall, params, body, info) -> params, body, info
    | fml -> SortEnv.empty, fml, Dummy
  let let_exists_or_formula = function
    | Bind(Exists, params, body, info) -> params, body, info
    | fml -> SortEnv.empty, fml, Dummy
  let let_letrec = function
    | LetRec(funcs, body, info) -> funcs, body, info
    | _ -> assert false

  (** Substitution *)
  let rec rename map = function
    | Atom (atom, info) -> Atom (Atom.rename map atom, info)
    | UnaryOp(Not, phi, info) -> UnaryOp(Not, rename map phi, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, rename map phi1, rename map phi2, info)
    | Bind(binder, bounds, body, info) ->
      let map = List.fold ~init:map ~f:Map.Poly.remove (SortEnv.args_of bounds) in
      Bind(binder, bounds, rename map body, info)
    | LetRec(funcs, body, info) ->
      let funcs =
        List.map ~f:(fun (fix, pvar, arg_sorts, func_body) ->
            let map' = List.fold ~init:map ~f:Map.Poly.remove (SortEnv.args_of arg_sorts) in
            (fix, pvar, arg_sorts, rename map' func_body)) funcs in
      LetRec(funcs, rename map body, info)
  let rec rename_pvars map = function
    | Atom (atom, info) -> Atom (Atom.rename_pvars map atom, info)
    | UnaryOp(Not, phi, info) -> UnaryOp(Not, rename_pvars map phi, info)
    | BinaryOp(op, phi1, phi2, info) ->
      BinaryOp(op, rename_pvars map phi1, rename_pvars map phi2, info)
    | Bind(binder, bounds, body, info) ->
      Bind(binder, bounds, rename_pvars map body, info)
    | LetRec(funcs, body, info) ->
      let funcs =
        List.map funcs ~f:(fun (fix, pvar, arg_sorts, func_body) ->
            let map' = Map.Poly.remove map pvar in
            (fix, pvar, arg_sorts, rename_pvars map' func_body))
      in LetRec(funcs, rename_pvars map body, info)
  (* substitution for term variable *)
  let rec subst map phi = 
    let rec aux ~next map = function
      | Atom (Atom.App(Var (Ident.Pvar var, []), [], _), _)
        when Map.Poly.mem map (Ident.Tvar var(*ToDo*)) ->
        next @@ of_bool_term @@ Map.Poly.find_exn map (Ident.Tvar var(*ToDo*))
      | Atom (atom, info) -> next @@ Atom(Atom.subst map atom, info)
      | UnaryOp(Not, phi, info) -> aux map phi ~next:(fun phi' -> next @@ UnaryOp(Not, phi', info))
      | BinaryOp(op, phi1, phi2, info) -> 
        aux map phi1 ~next:(fun phi1' -> aux map phi2 ~next:(fun phi2' -> next @@ BinaryOp(op, phi1', phi2', info)))
      | Bind(binder, bounds, body, info) ->
        let map' = List.fold ~init:map ~f:Map.Poly.remove (SortEnv.args_of bounds) in
        aux map' body ~next:(fun body' -> next @@ Bind(binder, bounds, body', info))
      | LetRec(funcs, body, info) ->
        let funcs =
          List.map ~f:(fun (fix, pvar, arg_sorts, func_body) ->
              let map' = List.fold ~init:map ~f:Map.Poly.remove (SortEnv.args_of arg_sorts) in
              (fix, pvar, arg_sorts, subst map' func_body)) funcs in
        aux map body ~next:(fun body' -> next @@ LetRec(funcs, body', info))
    in aux map phi ~next:(fun phi -> phi)
  let rec subst_preds map = function
    | Atom (atom, _) -> Atom.subst_preds map atom
    | UnaryOp(Not, phi, info) ->
      UnaryOp (Not, subst_preds map phi, info)
    | BinaryOp(op, phi1, phi2, info) ->
      BinaryOp(op, subst_preds map phi1, subst_preds map phi2, info)
    | Bind(binder, params, phi, info) ->
      let phi = subst_preds map phi in
      Bind (binder, params, phi, info)
    | LetRec(bounded, body, info) ->
      (* ToDo: the following code is wrong if ident is bound by let rec *)
      let bounded = List.map bounded ~f:(fun (fp, pvar, params, phi) ->
          (fp, pvar, params, subst_preds map phi)) in
      let body = subst_preds map body in
      LetRec (bounded, body, info)
  let rec subst_neg pvar = function
    | Atom (Atom.App(Predicate.Var (pvar', sort), args, info), info') ->
      let atom = Atom.App(Predicate.Var (pvar', sort), args, info) in
      if Stdlib.(=) pvar pvar' then UnaryOp(Not, Atom(atom, info), Dummy)
      else Atom(Atom.subst_neg pvar atom, info')
    | Atom (atom, info) -> Atom (Atom.subst_neg pvar atom, info)
    | UnaryOp(Not, phi, info) ->
      (match subst_neg pvar phi with
       | UnaryOp(Not, phi', _) -> phi'
       | phi' -> UnaryOp(Not, phi', info))
    | BinaryOp(op, phi1, phi2, info) ->
      BinaryOp(op, subst_neg pvar phi1, subst_neg pvar phi2, info)
    | Bind(binder, bounds, body, info) ->
      Bind(binder, bounds, subst_neg pvar body, info)
    | LetRec(funcs, body, info) ->
      LetRec(List.map ~f:(fun (fix, pvar', bounds, body) -> fix, pvar', bounds, subst_neg pvar body) funcs,
             subst_neg pvar body, info)

  let rec replace_papps map = function
    | Atom (atom, info) ->
      begin
        match Map.Poly.find map atom with
        | None -> Formula.mk_atom atom ~info
        | Some atom' -> Formula.mk_atom atom' ~info
      end
    | UnaryOp(op, phi1, info) -> UnaryOp(op, replace_papps map phi1, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, replace_papps map phi1, replace_papps map phi2, info)
    | Bind(binder, bounds, body, info) -> Bind(binder, bounds, replace_papps map body, info)
    | LetRec(funcs, body, info) -> LetRec (funcs, replace_papps map body, info)

  let rec aconv_tvar =
    function
    | Atom (atom, info) -> mk_atom (Atom.aconv_tvar atom) ~info
    | UnaryOp(Not, phi, info) -> mk_neg (aconv_tvar phi) ~info
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, aconv_tvar phi1, aconv_tvar phi2, info)
    | Bind (binder, bounds, phi, info) ->
      let bounds', map = SortEnv.refresh bounds in
      Bind (binder, bounds', rename map (aconv_tvar phi), info)
    | LetRec(funcs, body, info) ->
      let funcs' =
        List.map funcs ~f:(fun (fp, pvar, params, body) ->
            Predicate.let_fix @@ Predicate.aconv_tvar @@ Predicate.Fixpoint (fp, pvar, params, body))
      in
      LetRec (funcs', aconv_tvar body, info)
  let rec aconv_pvar = function
    | Atom (atom, info) -> Atom (Atom.aconv_pvar atom, info)
    | UnaryOp(Not, phi, info) -> UnaryOp (Not, aconv_pvar phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, aconv_pvar phi1, aconv_pvar phi2, info)
    | Bind (binder, bounds, phi, info) ->
      Bind (binder, bounds, aconv_pvar phi (* ToDo: fix bug *), info)
    | LetRec(funcs, phi, info) ->
      let map = Map.Poly.of_alist_exn @@ List.map ~f:(fun (_, pvar, _, _) -> pvar, Ident.mk_fresh_pvar ()) funcs in
      let funcs = List.map funcs ~f:(fun (fp, pvar, params, phi) ->
          fp, Map.Poly.find_exn map pvar, params, rename_pvars map phi)
      in
      LetRec (funcs, rename_pvars map phi, info)

  (** Transformation *)
  let flip_quantifier = function Forall -> Exists | Exists -> Forall | Random r -> Random r

  let reduce_sort_map (senv, phi) =
    let fvs = fvs_of phi in
    Map.Poly.filter_keys senv ~f:(Set.Poly.mem fvs), phi
  let refresh_tvar (senv, phi) =
    let map = Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar()) in
    Map.rename_keys_map map senv, rename map phi
  (*let refresh_tvar (phi: Formula.t) =
    let map =
      Map.of_set @@
      Set.Poly.map ~f:(fun (t, s) -> (t, Term.mk_var (Ident.mk_fresh_tvar ()) s)) @@
      term_sort_env_of phi in
    Formula.subst map phi*)

  let rec complete_psort map = function
    | Atom (atom, info) -> Atom (Atom.complete_psort map atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, complete_psort map phi, info)
    | BinaryOp (op, phi1, phi2, info) -> BinaryOp (op, complete_psort map phi1, complete_psort map phi2, info)
    | Bind (binder, bounds, body, info) -> Bind (binder, bounds, complete_psort map body, info)
    | LetRec _ -> failwith "LetRec in this position is not supported."
  let rec complete_tsort env = function
    | Atom (atom, info) -> Atom (Atom.subst env atom, info)
    | UnaryOp(op, phi, info) -> UnaryOp(op, complete_tsort env phi, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp (op, complete_tsort env phi1, complete_tsort env phi2, info)
    | Bind (binder, args, phi, info) ->
      let env' =
        Set.Poly.fold ~init:env (SortEnv.set_of args) ~f:(fun env (x, sort) ->
            Map.Poly.update env x ~f:(fun _ -> Term.mk_var x sort)) in
      Bind (binder, args, complete_tsort env' phi, info)
    | LetRec _ -> failwith "LetRec in this position is not supported."
  let complete_tsort = complete_tsort Map.Poly.empty

  let rec rm_forall = function
    | Atom (atom, info) -> Set.Poly.empty, Atom (atom, info)
    | UnaryOp(op, phi, info) ->
      let senv', phi' = rm_forall phi in
      senv', UnaryOp(op, phi', info)
    | BinaryOp(op, phi1, phi2, info) ->
      let senv1', phi1' = rm_forall phi1 in
      let senv2', phi2' = rm_forall phi2 in
      Set.Poly.union senv1' senv2', BinaryOp(op,  phi1', phi2', info)
    | Bind(Forall, senv, phi, _) ->
      let senv', phi' = rm_forall phi in
      Set.Poly.union (SortEnv.set_of senv) senv', phi'
    | Bind(_, _, _, _) -> failwith "unimplemented"
    | LetRec(_, _, _) -> failwith "unimplemented"

  let rec elim_neq = function
    | Atom (atom, _) -> Atom.elim_neq atom
    | UnaryOp(op, phi, info) -> UnaryOp(op, elim_neq phi, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op,  elim_neq phi1, elim_neq phi2, info)
    | Bind(bin, senv, phi, info) -> Bind(bin, senv, elim_neq phi, info)
    | LetRec(_, _, _) -> failwith "unimplemented"
  let rec elim_ite = function
    | Atom (atom, _) -> Atom.elim_ite atom
    | UnaryOp(op, phi, info) -> UnaryOp(op, elim_ite phi, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op,  elim_ite phi1, elim_ite phi2, info)
    | Bind(bin, senv, phi, info) -> Bind(bin, senv, elim_ite phi, info)
    | LetRec(_, _, _) -> failwith "unimplemented"
  let rec instantiate_div0_mod0 = function
    | Atom (atom, info) -> Atom (Atom.instantiate_div0_mod0 atom, info)
    | UnaryOp(op, phi, info) -> UnaryOp(op, instantiate_div0_mod0 phi, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op,  instantiate_div0_mod0 phi1, instantiate_div0_mod0 phi2, info)
    | Bind(bin, senv, phi, info) -> Bind(bin, senv, instantiate_div0_mod0 phi, info)
    | LetRec(_, _, _) -> failwith "unimplemented"

  let rec find_div_mod = function
    | Atom(atom, _) -> Atom.find_div_mod atom
    | UnaryOp(_, phi, _) -> find_div_mod phi
    | BinaryOp(_, phi1, phi2, _) -> Set.Poly.union (find_div_mod phi1) (find_div_mod phi2)
    | Bind(_, _, phi, _) -> find_div_mod phi
    | LetRec(_, _, _) -> failwith "unimplemented"
  let rec replace_div_mod map = function
    | Atom (atom, info) -> Atom (Atom.replace_div_mod map atom, info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, replace_div_mod map phi, info)
    | BinaryOp (op, phi1, phi2, info) -> BinaryOp (op, replace_div_mod map phi1, replace_div_mod map phi2, info)
    | Bind (bin, senv, phi, info) -> Bind (bin, senv, replace_div_mod map phi, info)
    | LetRec(_, _, _) -> failwith "unimplemented"

  (* Prerequisites of rm_div_mod f
     f is normalized and a-converted, and there are no free variables in f
     there are some unimplemented forms
     for example, (exists x. x=0 and z = x mod 0) and (exists y. y=0 and z = y mod 0)
     but if f is prenex normal form then no problem *)
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
          let (newvars, _) = List.unzip @@SortEnv.list_of bounds in
          let newvars = Set.Poly.union vars (Set.Poly.of_list newvars) in
          let (map1, map2, newvars) = divide_map Map.Poly.empty mapinner newvars in
          let (restriction, newmap) = make_restriction mapouter map1 in
          let sortenv = Map.Poly.fold map1 ~init:[] ~f:(fun ~key:_ ~data:(d, m) l -> (d, T_int.SInt)::(m, T_int.SInt)::l) in
          let f = Formula.mk_exists (SortEnv.of_list sortenv) (Formula.mk_and restriction (add_restriction newmap map2 newvars phi)) in
          Bind (binder, bounds, f, info)
        | LetRec(_, _, _) -> failwith "unimplemented" in
      let (map1, map2, vars) = divide_map Map.Poly.empty newmap Set.Poly.empty in
      let (init, _) = make_restriction Map.Poly.empty map1 in
      let sortenv = Map.Poly.fold map1 ~init:[] ~f:(fun ~key:_ ~data:(d, m) l -> (d, T_int.SInt)::(m, T_int.SInt)::l) in
      Formula.mk_exists (SortEnv.of_list sortenv) (Formula.mk_and init (add_restriction map1 map2 vars f))

  let rec rm_boolean_term = function
    | Atom (atom, _) -> Atom.rm_boolean_term atom
    | UnaryOp (op, phi, info) -> UnaryOp (op, rm_boolean_term phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
      BinaryOp (op, rm_boolean_term phi1, rm_boolean_term phi2, info)
    | Bind (binder, bounded, phi, info) -> Bind (binder, bounded, rm_boolean_term phi, info)
    | LetRec (_, _, _) -> failwith "unimplemented"

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

  (* assume that phi is in nnf *)
  let rec cnf_of_aux fnvs = function
    | UnaryOp(Not, phi, _) ->
      (match phi with
       | Atom(atom, _) ->
         if Atom.is_true atom then
           Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
         else if Atom.is_false atom then
           Set.Poly.empty
         else if Atom.is_pvar_app atom then
           Set.Poly.singleton (Set.Poly.empty, Set.Poly.singleton atom, Set.Poly.empty)
         else if Atom.is_psym_app atom then
           Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_neg (mk_atom atom)))
         else assert false
       | _ -> (* ToDo: check *)
         Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_neg phi)))
    | Atom(atom, _) ->
      if Atom.is_true atom then
        Set.Poly.empty
      else if Atom.is_false atom then
        Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      else if Atom.is_pvar_app atom then
        Set.Poly.singleton (Set.Poly.singleton atom, Set.Poly.empty, Set.Poly.empty)
      else if Atom.is_psym_app atom then
        Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
      else assert false
    | BinaryOp(And, phi1, phi2, _) ->
      let cls1 = cnf_of_aux fnvs phi1 in
      let cls2 = cnf_of_aux fnvs phi2 in
      let phis, cls =
        Set.Poly.partition_tf
          (Set.Poly.union cls1 cls2)
          ~f:(fun (ps, ns, phis) -> Set.Poly.is_empty ps && Set.Poly.is_empty ns && Set.Poly.is_empty @@ Set.Poly.inter fnvs (tvs_of (or_of (Set.Poly.to_list phis))))
        |> Pair.map (Set.Poly.map ~f:(fun (_, _, phis) -> or_of (Set.Poly.to_list phis))) ident
      in
      if Set.Poly.is_empty phis then cls
      else Set.Poly.add cls (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (and_of (Set.Poly.to_list phis)))
    | BinaryOp(Or, phi1, phi2, _) ->
      let cls1 = cnf_of_aux fnvs phi1 in
      let cls2 = cnf_of_aux fnvs phi2 in
      Set.cartesian_map cls1 cls2
        ~f:(fun (ps1, ns1, phis1) (ps2, ns2, phis2) ->
            Set.Poly.union ps1 ps2, Set.Poly.union ns1 ns2, Set.Poly.union phis1 phis2)
    | BinaryOp(Imply, _, _, _) | BinaryOp(Iff, _, _, _) -> assert false
    | Bind(_, _, _, _) as phi ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi)
    | LetRec (_, _, _) -> assert false
  (* cnf_of phi
      input  : Formula of NNF
      output : a list of clauses where a clause is represented by a triple (ps,ns,phi') consisting of predicate variable applications ps, negated predicate variable applications ns, and a pure formula *)
  let cnf_of fnvs phi =
    phi
    |> cnf_of_aux fnvs
    |> Set.Poly.map ~f:(fun (ps, ns, phis) -> ps, ns, or_of (Set.Poly.to_list phis))

  let rec dnf_of_aux = function
    | UnaryOp(Not, phi, _) ->
      (match phi with
       | Atom(atom, _) ->
         if Atom.is_true atom then
           Set.Poly.empty
         else if Atom.is_false atom then
           Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
         else if Atom.is_pvar_app atom then
           Set.Poly.singleton (Set.Poly.empty, Set.Poly.singleton atom, Set.Poly.empty)
         else if Atom.is_psym_app atom then
           Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_neg (mk_atom atom)))
         else assert false
       | _ -> assert false)
    | Atom(atom, _) ->
      if Atom.is_true atom then
        Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      else if Atom.is_false atom then
        Set.Poly.empty
      else if Atom.is_pvar_app atom then
        Set.Poly.singleton (Set.Poly.singleton atom, Set.Poly.empty, Set.Poly.empty)
      else if Atom.is_psym_app atom then
        Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (mk_atom atom))
      else assert false
    | BinaryOp(Or, phi1, phi2, _) ->
      let cls1 = dnf_of_aux phi1 in
      let cls2 = dnf_of_aux phi2 in
      let phis, cls =
        Set.Poly.partition_tf
          (Set.Poly.union cls1 cls2)
          ~f:(fun (ps, ns, _) -> Set.Poly.is_empty ps && Set.Poly.is_empty ns)
        |> Pair.map (Set.Poly.map ~f:(fun (_, _, phis) -> and_of (Set.Poly.to_list phis))) ident
      in
      if Set.Poly.is_empty phis then cls
      else Set.Poly.add cls (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton (or_of (Set.Poly.to_list phis)))
    | BinaryOp(And, phi1, phi2, _) ->
      let cls1 = dnf_of_aux phi1 in
      let cls2 = dnf_of_aux phi2 in
      Set.cartesian_map cls1 cls2
        ~f:(fun (ps1, ns1, phis1) (ps2, ns2, phis2) ->
            Set.Poly.union ps1 ps2, Set.Poly.union ns1 ns2, Set.Poly.union phis1 phis2)
    | BinaryOp(Imply, _, _, _) | BinaryOp(Iff, _, _, _) -> assert false
    | Bind(_, _, _, _) as phi ->
      Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty, Set.Poly.singleton phi)
    | LetRec (_, _, _) -> assert false
  let dnf_of phi =
    phi
    |> dnf_of_aux
    |> Set.Poly.map ~f:(fun (ps, ns, phis) -> ps, ns, and_of (Set.Poly.to_list phis))

  (* Note: does not transform pure formulas into nnf *)
  let rec nnf_of phi = 
    match phi with
    | Atom(_, _) -> phi
    | UnaryOp(Not, Atom(Atom.True _, _), _)  -> mk_false ()
    | UnaryOp(Not, Atom(Atom.False _, _), _) -> mk_true ()
    | UnaryOp(Not, atom, _) when is_atom atom -> mk_neg atom
    | UnaryOp(Not, UnaryOp(Not, phi, _), _) -> nnf_of phi
    | UnaryOp(Not, BinaryOp(And, phi1, phi2, _), _) ->
      mk_or (nnf_of @@ mk_neg phi1) (nnf_of @@ mk_neg phi2)
    | UnaryOp(Not, BinaryOp(Or, phi1, phi2, _), _) ->
      mk_and (nnf_of @@ mk_neg phi1) (nnf_of @@ mk_neg phi2)
    | UnaryOp(Not, BinaryOp(Imply, phi1, phi2, _), _) ->
      mk_and (nnf_of phi1) (nnf_of @@ mk_neg phi2)
    | UnaryOp(Not, BinaryOp(Iff, phi1, phi2, _), _) ->
      mk_or
        (mk_and (nnf_of phi1) (nnf_of @@ mk_neg phi2))
        (mk_and (nnf_of @@ mk_neg phi1) (nnf_of phi2))
    | BinaryOp(And, phi1, phi2, _) ->
      mk_and (nnf_of phi1) (nnf_of phi2)
    | BinaryOp(Or, phi1, phi2, _) ->
      mk_or (nnf_of phi1) (nnf_of phi2)
    | BinaryOp(Imply, phi1, phi2, _) ->
      mk_or (nnf_of @@ mk_neg phi1) (nnf_of phi2)
    | BinaryOp(Iff, phi1, phi2, _) ->
      mk_and
        (mk_or (nnf_of @@ mk_neg phi1) (nnf_of phi2))
        (mk_or (nnf_of phi1) (nnf_of @@ mk_neg phi2))
    | UnaryOp(Not, Bind (Forall, params, phi, _), _) ->
      mk_bind Exists params (nnf_of @@ mk_neg phi)
    | UnaryOp(Not, Bind (Exists, params, phi, _), _) ->
      mk_bind Forall params (nnf_of @@ mk_neg phi)
    | Bind (b, params, phi, _) -> mk_bind b params (nnf_of phi)
    | UnaryOp (Not, LetRec([], phi, _), _) -> nnf_of (mk_neg phi)
    | LetRec([], phi, _) -> nnf_of phi
    | _ -> failwith ("Unexpected formula in nnf_of: " ^ (Formula.str_of phi))
  let neg_of = function
    | UnaryOp(Not, phi, _) -> phi
    | phi -> mk_neg phi

  let univ_clos phi =
    let bounds = SortEnv.of_set @@ term_sort_env_of phi in
    if SortEnv.is_empty bounds then phi else mk_forall bounds phi

  (* f is a-converted*)
  let rec split_quantifiers f =
    match f with
    | Atom (App (pred, tl, _), _) ->
      let (qs, termlist) = List.fold tl ~init:([], []) ~f:(fun (qs, terms) term ->
          match term with
          | FunApp (T_bool.Formula phi, [], _) ->
            let (q, phi) = split_quantifiers phi in
            (qs @ q, terms @ [(T_bool.of_formula phi)])
          | _ -> (qs, terms @ [term])) in
      (qs, (mk_atom @@Atom.mk_app pred termlist))
    | Atom (_, _) -> ([], f)
    | UnaryOp (unop, phi, _) ->
      let (qs, phi) = split_quantifiers phi in (qs, (mk_unop unop phi))
    | BinaryOp (binop, phi1, phi2, _) ->
      let (qs1, phi1) = split_quantifiers phi1 in
      let (qs2, phi2) = split_quantifiers phi2 in
      (qs1 @ qs2, (mk_binop binop phi1 phi2))
    | Bind (binder, sortenv, phi, _) ->
      let (qs, phi) = split_quantifiers phi in ((binder, sortenv)::qs, phi)
    | LetRec (_, _, _) -> assert false
  let pnf_of f =
    let (quantifiers, phi) = split_quantifiers f in
    mk_binds quantifiers phi
  let skolemize_fun phi =
    let rec aux senv fsenv = function
      | Atom(_, _) as phi ->
        (* we here assume that phi does not contain quantifiers *)senv, fsenv, phi
      | UnaryOp (unop, phi, _) ->
        let senv, fsenv, phi = aux senv fsenv phi in
        senv, fsenv, mk_unop unop phi
      | BinaryOp (binop, phi1, phi2, _) ->
        let senv, fsenv, phi1 = aux senv fsenv phi1 in
        let senv, fsenv, phi2 = aux senv fsenv phi2 in
        senv, fsenv, mk_binop binop phi1 phi2
      | Bind (Forall, uni_senv, phi, _) ->
        let bounded = SortMap.of_set @@ SortEnv.set_of uni_senv in
        aux (SortMap.merge bounded senv) fsenv phi
      | Bind (Exists, exi_senv, phi, _) ->
        let args = SortEnv.of_list @@ SortMap.to_list senv in
        let subst, bounds_rev =
          List.fold ~init:(Map.Poly.empty, []) (SortEnv.list_of exi_senv)
            ~f:(fun (subst, bounds_rev) (Ident.Tvar x, sort) ->
                let new_tvar = Ident.mk_fresh_tvar ~prefix:(Some ("#skolem_" ^ x)) () in
                Map.Poly.add_exn subst
                  ~key:(Ident.Tvar x)
                  ~data:(Term.mk_fvar_app new_tvar (SortEnv.sorts_of args @ [sort])
                           (Term.of_sort_env args)),
                (new_tvar, Sort.mk_fun (SortEnv.sorts_of args @ [sort])) :: bounds_rev)
        in
        aux senv (fsenv @ List.rev bounds_rev) (Formula.subst subst phi)
      | Bind (Random _, _, _, _) -> assert false (*ToDo*)
      | LetRec (_, _, _) -> assert false
    in
    aux SortMap.empty [] phi
  let skolemize_pred phi =
    let rec aux senv fsenv = function
      | Atom(_, _) as phi ->
        (* we here assume that phi does not contain quantifiers *)senv, fsenv, phi
      | UnaryOp (unop, phi, _) ->
        let senv, fsenv, phi = aux senv fsenv phi in
        senv, fsenv, mk_unop unop phi
      | BinaryOp (binop, phi1, phi2, _) ->
        let senv, fsenv, phi1 = aux senv fsenv phi1 in
        let senv, fsenv, phi2 = aux senv fsenv phi2 in
        senv, fsenv, mk_binop binop phi1 phi2
      | Bind (Forall, uni_senv, phi, _) ->
        let bounded = SortMap.of_set @@ SortEnv.set_of uni_senv in
        aux (SortMap.merge bounded senv) fsenv phi
      | Bind (Exists, exi_senv, phi, _) ->
        let args = SortEnv.of_list @@ SortMap.to_list senv in
        let bounded, subst, bounds_rev =
          List.fold ~init:(Map.Poly.empty, Map.Poly.empty, []) (SortEnv.list_of exi_senv)
            ~f:(fun (bounded, subst, bounds_rev) (Ident.Tvar x, sort) ->
                let name_tvar = Ident.mk_fresh_tvar ~prefix:(Some ("#skolem_" ^ x)) () in
                let ret = Term.mk_var name_tvar sort in
                let Ident.Pvar name = Ident.mk_fresh_pvar () in
                let name = "FN_" ^ x ^ name in
                let fnpvarapp = Atom.mk_pvar_app (Ident.Pvar name) (SortEnv.sorts_of args @ [sort])
                    (Term.of_sort_env args @ [ret]) in
                Map.Poly.add_exn bounded ~key:name_tvar ~data:sort,
                Map.Poly.add_exn subst ~key:(Ident.Tvar x) ~data:ret,
                (fnpvarapp, Sort.mk_fun @@ SortEnv.sorts_of args @ [sort; T_bool.SBool]) :: bounds_rev)
        in
        aux (SortMap.merge bounded senv)
          (fsenv @ List.rev @@ List.map ~f:(fun (a, sort) -> Atom.pvar_of a, sort) bounds_rev)
          (Formula.mk_imply
             (Formula.and_of @@ List.map bounds_rev ~f:(fun (a, _) -> Formula.mk_atom a))
             (Formula.subst subst phi))
      | Bind (Random _, _, _, _) -> assert false (*ToDo*)
      | LetRec (_, _, _) -> assert false
    in
    aux SortMap.empty [] phi

  (** Printing *)
  let str_of_unop = function | Not -> "Not"
  let str_of_binop = function | And -> "And" | Or -> "Or" | Imply -> "Imply" | Iff -> "Iff"
  let str_of_binder = function | Forall -> "Forall" | Exists -> "Exists" | Random r -> Rand.str_of r

  (*let rec str_of = function
    | Atom (atom, _) -> Printf.sprintf "Atom (%s)" @@ Atom.str_of atom
    | UnaryOp (op, phi, _) -> Printf.sprintf "UnaryOp (%s, %s)" (str_of_unop op) (str_of phi)
    | BinaryOp (op, phi1, phi2, _) ->
      Printf.sprintf "BinaryOp(%s, %s, %s)" (str_of_binop op) (str_of phi1) (str_of phi2)
    | Bind (binder, terms, phi, _) ->
      Printf.sprintf "Bind (%s, %s, %s)" (str_of_binder binder)
        (List.fold ~f:(fun acc (Ident.Tvar id, _) -> acc ^ ", " ^ id) ~init:"" terms) (str_of phi)
    | LetRec (_, phi, _) ->
      (* TODO: implements *)
      Printf.sprintf "LetRec (fixpoints, %s)" @@ str_of phi*)

  let rec str_of ?(priority=0) phi =
    let rec aux ?(priority=0) phi ~next =
      match phi with
      | Atom (atom, _) -> next @@ Atom.str_of ~priority atom
      | UnaryOp (Not, phi, _) ->
        aux ~priority:(Priority.fun_app+1(*ToDo*)) phi ~next:(fun s -> 
            next @@ Priority.add_bracket priority Priority.fun_app
            @@ Printf.sprintf "not %s" s)
      | BinaryOp (And, phi1, phi2, _) ->
        aux ~priority:Priority.binary_and phi1 ~next:(
          fun s1 -> aux ~priority:Priority.binary_and phi2 ~next:(
              fun s2 -> next @@ Priority.add_bracket priority Priority.binary_and
                @@ Printf.sprintf "%s /\\ %s" s1 s2))
      | BinaryOp (Or, phi1, phi2, _) ->
        aux ~priority:Priority.binary_or phi1 ~next:(
          fun s1 -> aux ~priority:Priority.binary_or phi2 ~next:(
              fun s2 -> next @@ Priority.add_bracket priority Priority.binary_or
                @@ Printf.sprintf "%s \\/ %s" s1 s2))
      | BinaryOp (Imply, phi1, phi2, _) ->
        aux phi1 ~priority:Priority.imply_iff ~next:(
          fun s1 -> aux phi2 ~priority:Priority.imply_iff ~next:(
              fun s2 -> next @@ Priority.add_bracket priority Priority.imply_iff
                @@ Printf.sprintf "%s => %s" s1 s2))
      | BinaryOp (Iff, phi1, phi2, _) ->
        aux phi1 ~priority:Priority.imply_iff ~next:(
          fun s1 -> aux phi2 ~priority:Priority.imply_iff ~next:(
              fun s2 -> next @@ Priority.add_bracket priority Priority.imply_iff
                @@ Printf.sprintf "%s <=> %s" s1 s2))
      | Bind (Forall, params, phi, _) ->
        aux phi ~priority:Priority.letrec_forall_exists ~next:(
          fun s -> 
            next @@ Priority.add_bracket priority Priority.letrec_forall_exists
            @@ Printf.sprintf "forall %s. %s"
              (SortEnv.str_of Term.str_of_sort params) s)
      | Bind (Exists, params, phi, _) ->
        aux phi ~priority:Priority.letrec_forall_exists ~next:(
          fun s -> 
            next @@ Priority.add_bracket priority Priority.letrec_forall_exists
            @@ Printf.sprintf "exists %s. %s"
              (SortEnv.str_of Term.str_of_sort params) s)
      | Bind (Random r, params, phi, _) ->
        aux phi ~priority:Priority.letrec_forall_exists ~next:(
          fun s -> 
            next @@ Priority.add_bracket priority Priority.letrec_forall_exists
            @@ Printf.sprintf "%s %s. %s"
              (Rand.str_of r) (SortEnv.str_of Term.str_of_sort params) s)
      | LetRec (funcs, body, _) ->
        aux body ~priority:0 ~next:(fun s ->
            next @@ Priority.add_bracket priority Priority.letrec_forall_exists
            @@ Printf.sprintf "let rec %s in %s"
              (String.concat ~sep:" and "
                 (List.map ~f:(fun (fix, pvar, bounds, body) ->
                      let var_names =
                        if SortEnv.is_empty bounds then
                          ["()"]
                        else
                          SortEnv.map ~f:(fun (tvar, _) -> Ident.name_of_tvar tvar) bounds
                      in
                      Printf.sprintf "%s %s =%s %s"
                        (Ident.name_of_pvar pvar)
                        (String.concat ~sep:" " var_names)
                        (Predicate.str_of_fixpoint fix)
                        (str_of ~priority:0 body)
                    ) funcs)
              ) s)
    in aux ~priority ~next:(fun s -> s) phi

  let rec fold phi ~f =
    let rec aux phi ~next = 
      match phi with
      | Atom (atom, _) -> next @@ f#fatom atom
      | UnaryOp(Not, phi, _) -> 
        aux phi ~next:(fun phi' -> next @@ f#fnot phi')
      | BinaryOp(And, phi1, phi2, _) -> 
        aux phi1 ~next:(fun phi1' -> aux phi2 ~next:(fun phi2' -> next @@ f#fand phi1' phi2'))
      | BinaryOp(Or, phi1, phi2, _) -> 
        aux phi1 ~next:(fun phi1' -> aux phi2 ~next:(fun phi2' -> next @@ f#for_ phi1' phi2'))
      | Bind(binder, senv, phi, _) -> aux phi ~next:(fun phi' -> f#fbind binder senv phi')
      | LetRec(funcs, phi, _) -> 
        aux phi ~next:(fun phi' ->
            next @@ f#fletrec
              (List.map funcs ~f:(fun (fix, pvar, senv, phi) -> (fix, pvar, senv, fold phi ~f)))  
              phi')
      |_ -> failwith "unsupported fold case"
    in aux phi ~next:(fun phi -> phi)

  let map_atom phi ~f =
    fold phi ~f:(
      object
        method fatom atom = f atom
        method fand p1 p2 = mk_and p1 p2
        method for_ p1 p2 = mk_or p1 p2
        method fnot p1 = mk_neg p1
        method fbind binder senv p1 = mk_bind binder senv p1
        method fletrec funcs p1 = mk_letrec funcs p1
      end
    )
  let map_term phi ~f = Formula.map_atom phi ~f:(fun atom -> Formula.mk_atom @@ Atom.map_term ~f atom)

  let rec map_atom_polarity polarity phi ~f =
    match phi with
    | Atom(atom, _) -> f polarity atom
    | UnaryOp(Not, phi, info) -> UnaryOp(Not, map_atom_polarity (not polarity) phi ~f, info)
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, map_atom_polarity polarity phi1 ~f, map_atom_polarity polarity phi2 ~f, info)
    | Bind(binder, senv, phi, info) -> Bind(binder, senv, map_atom_polarity polarity phi ~f, info)
    | LetRec(funcs, phi, info) -> 
      LetRec(List.map funcs ~f:(fun (fix, pvar, senv, phi) ->
          (fix, pvar, senv, map_atom_polarity polarity phi ~f)), map_atom_polarity polarity phi ~f, info)   
end

and T_bool : Type.T_boolType
  with type formula := Formula.t and
  type atom := Atom.t and
  type term := Term.t = struct

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
    List.concat @@ List.mapi ts ~f:(
      fun i t -> 
        List.foldi ts ~init:[] ~f:(
          fun i1 ret t1 -> 
            if i1 <= i || Stdlib.(<>) (Term.sort_of t) (Term.sort_of t1) then ret
            else (mk_eq t t1)::ret
        )
    )
  let ifte phi t1 t2 = mk_if_then_else (of_formula phi) t1 t2
  let rec neg = function
    | Term.Var (x, s, _) -> assert Stdlib.(s = SBool); of_atom @@ Atom.of_neg_bool_var x
    | Term.FunApp (Formula phi, _, _) -> of_formula @@ Formula.mk_neg phi
    | Term.FunApp (IfThenElse, [t1; t2; t3], _) -> mk_if_then_else t1 (neg t2) (neg t3)
    | term -> failwith (Term.str_of term)

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

  (** Destruction *)
  let let_bool = function
    | Term.FunApp (Formula (Formula.Atom (Atom.True _, _)), [], _) -> true
    | Term.FunApp (Formula (Formula.Atom (Atom.False _, _)), [], _) -> false
    | _ -> assert false
end

and T_int : Type.T_intType 
  with type term := Term.t and
  type atom := Atom.t = struct
  type fun_sym +=
    | Int of Z.t
    | Add | Sub | Mult | Div | Mod | Neg | Abs | Power | Rem
  type pred_sym += Leq | Geq | Lt | Gt | PDiv | NPDiv
  type Sort.t += SInt

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
      mk_mult (mk_int (Z.neg(Z.one)) ~info) t ~info*)

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
  let is_int = function Term.FunApp(Int _, [], _) -> true | _ -> false
  let is_sint t = Stdlib.(=) (Term.sort_of t) SInt
  let is_add = function Term.FunApp(Add, _, _) -> true | _ -> false
  let is_sub = function Term.FunApp(Sub, _, _) -> true | _ -> false
  let is_mult = function Term.FunApp(Mult, _, _) -> true | _ -> false
  let is_div = function Term.FunApp(Div, _, _) -> true | _ -> false
  let is_mod = function Term.FunApp(Mod, _, _) -> true | _ -> false
  let is_neg = function Term.FunApp(Neg, _, _) -> true | _ -> false
  let is_abs = function Term.FunApp(Abs, _, _) -> true | _ -> false
  let is_power = function Term.FunApp(Power, _, _) -> true | _ -> false
  let is_rem = function Term.FunApp(Rem, _, _) -> true | _ -> false
  let is_zero = function Term.FunApp(Int i, _, _) when Z.Compare.(i = Z.zero) -> true | _ -> false
  let is_unit = function Term.FunApp(Int i, _, _) when Z.Compare.(i = Z.one) -> true | _ -> false
  let is_minus_one = function Term.FunApp(Int i, _, _) when Z.Compare.(i = Z.minus_one) -> true | _ -> false

  let psym_of_atom = function
    | Atom.App(Predicate.Psym sym, _, _) -> sym
    | _ -> assert false
  let is_leq atom = Stdlib.(=) Leq (psym_of_atom atom)
  let is_geq atom = Stdlib.(=) Geq (psym_of_atom atom)
  let is_lt atom = Stdlib.(=) Lt (psym_of_atom atom)
  let is_gt atom = Stdlib.(=) Gt (psym_of_atom atom)
  let is_pdiv atom = Stdlib.(=) PDiv (psym_of_atom atom)
  let is_npdiv atom = Stdlib.(=) NPDiv (psym_of_atom atom)

  (** Destruction *)
  let let_int = function
    | Term.FunApp(Int n, [], _) -> n
    | _ -> assert false
  let let_add = function
    | Term.FunApp(Add, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_sub = function
    | Term.FunApp(Sub, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_mult = function
    | Term.FunApp(Mult, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_div = function
    | Term.FunApp(Div, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_mod = function
    | Term.FunApp(Mod, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_neg = function
    | Term.FunApp(Neg, [t], info) -> t, info
    | _ -> assert false
  let let_abs = function
    | Term.FunApp(Abs, [t], info) -> t, info
    | _ -> assert false
  let let_power = function
    | Term.FunApp(Power, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rem = function
    | Term.FunApp(Rem, [t1;t2], info) -> t1, t2, info
    | _ -> assert false

  let let_leq = function
    | Atom.App(Predicate.Psym Leq, [t1; t2], info) -> t1, t2 , info
    | _ -> assert false
  let let_geq = function
    | Atom.App(Predicate.Psym Geq, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_lt = function
    | Atom.App(Predicate.Psym Lt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_gt = function
    | Atom.App(Predicate.Psym Gt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_pdiv = function
    | Atom.App(Predicate.Psym PDiv, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_npdiv = function
    | Atom.App(Predicate.Psym NPDiv, [t1; t2], info) -> t1, t2, info
    | _ -> assert false

  let neg_fsym = function
    | Add -> Sub | Sub -> Add | Mult -> Div | Div -> Mult
    | _ -> failwith "undefined "
  (* subst_eqterm is substitution of int term.
     atom is already normalized.
     example for cx = t, ax + u = 0 -> at + cu = 0 *)
  let subst_eqterm cterm eqterm tvar atom (monomials_of, find_var, mk_term) =
    match atom with
    | Atom.App (Predicate.Psym sym, [t; t0], _) 
      when (match sym with | T_bool.Eq | T_bool.Neq -> true | _ -> false) ->
      let monomial = monomials_of (Value.Int Z.one) t in
      let varterm = Term.mk_var tvar SInt in
      (match find_var varterm monomial with
       | Some (a, rest) ->
         let term = mk_add (mk_mult (Term.of_value a) eqterm) (mk_mult cterm (mk_term rest)) in
         Atom.mk_psym_app sym [term; t0]
       | None -> atom)
    | Atom.App (Predicate.Psym Geq, [t; t0], _) ->
      let monomial = monomials_of (Value.Int Z.one) t in
      let varterm = Term.mk_var tvar SInt in
      (match find_var varterm monomial with
       | Some (a, rest) ->
         let term = mk_add (mk_mult (Term.of_value a) eqterm) (mk_mult cterm (mk_term rest)) in
         if Value.compare Z.Compare.(>=) Q.(>=) (Term.value_of cterm) (Value.Int Z.zero)
         then mk_geq term t0
         else mk_leq term t0
       | None -> atom)
    | Atom.App (Predicate.Psym sym, [d; t], _) 
      when (match sym with | PDiv | NPDiv -> true | _ -> false) ->
      let monomial = monomials_of (Value.Int Z.one) t in
      let varterm = Term.mk_var tvar SInt in
      (match find_var varterm monomial with
       | Some (a, rest) ->
         let term = mk_add (mk_mult (Term.of_value a) eqterm) (mk_mult cterm (mk_term rest)) in
         Atom.mk_psym_app sym [(mk_mult cterm d); term]
       | None -> atom)
    | _ -> assert false
end

and T_real : Type.T_realType 
  with type rterm := Term.t and
  type ratom := Atom.t = struct
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
      mk_mult (mk_int (Z.neg(Z.one)) ~info) t ~info*)

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
  let is_real = function Term.FunApp(Real _, [], _) -> true | _ -> false
  let is_sreal t = Stdlib.(=) (Term.sort_of t) SReal
  let is_alge = function Term.FunApp(Alge _, [], _) -> true | _ -> false
  let is_radd = function Term.FunApp(RAdd, _, _) -> true | _ -> false
  let is_rsub = function Term.FunApp(RSub, _, _) -> true | _ -> false
  let is_rmult = function Term.FunApp(RMult, _, _) -> true | _ -> false
  let is_rdiv = function Term.FunApp(RDiv, _, _) -> true | _ -> false
  let is_rneg = function Term.FunApp(RNeg, _, _) -> true | _ -> false
  let is_rabs = function Term.FunApp(RAbs, _, _) -> true | _ -> false
  let is_rpower = function Term.FunApp(RPower, _, _) -> true | _ -> false
  let is_rzero = function Term.FunApp((Real r), _, _) when Q.(r = zero) -> true | _ -> false
  let is_runit = function Term.FunApp(Real r, _, _) when Q.(r = one) -> true | _ -> false
  let is_rminus_one = function Term.FunApp(Real r, _, _) when Q.(r = minus_one) -> true | _ -> false

  let psym_of_atom = function
    | Atom.App(Predicate.Psym sym, _, _) -> sym
    | _ -> assert false
  let is_rleq atom = Stdlib.(=) RLeq (psym_of_atom atom)
  let is_rgeq atom = Stdlib.(=) RGeq (psym_of_atom atom)
  let is_rlt atom = Stdlib.(=) RLt (psym_of_atom atom)
  let is_rgt atom = Stdlib.(=) RGt (psym_of_atom atom)

  (** Destruction *)
  let let_real = function
    | Term.FunApp (Real f, [], _) -> f
    | t -> failwith @@ Printf.sprintf "%s is not real" @@ Term.str_of t
  let let_alge = function
    | Term.FunApp (Alge (t, n), [], _) -> t, n
    | _ -> assert false
  let let_radd = function
    | Term.FunApp(RAdd, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rsub = function
    | Term.FunApp(RSub, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rmult = function
    | Term.FunApp(RMult, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rdiv = function
    | Term.FunApp(RDiv, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false
  let let_rneg = function
    | Term.FunApp(RNeg, [t], info) -> t, info
    | _ -> assert false
  let let_rabs = function
    | Term.FunApp(RAbs, [t], info) -> t, info
    | _ -> assert false
  let let_rpower = function
    | Term.FunApp(RPower, [phi1; phi2], info) -> phi1, phi2, info
    | _ -> assert false

  let let_rleq = function
    | Atom.App(Predicate.Psym RLeq, [t1; t2], info) -> t1, t2 , info
    | _ -> assert false
  let let_rgeq = function
    | Atom.App(Predicate.Psym RGeq, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_rlt = function
    | Atom.App(Predicate.Psym RLt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
  let let_rgt = function
    | Atom.App(Predicate.Psym RGt, [t1; t2], info) -> t1, t2, info
    | _ -> assert false
end

and T_real_int : Type.T_real_intType 
  with type term := Term.t and
  type rterm := Term.t and
  type atom := Atom.t and
  type ratom := Atom.t = struct
  include T_int
  include T_real

  type fun_sym +=
    | ToReal | ToInt
  type pred_sym +=
    | IsInt

  let mk_to_real ?(info=Dummy) t = Term.mk_fsym_app ToReal [t] ~info
  let mk_to_int ?(info=Dummy) t = Term.mk_fsym_app ToInt [t] ~info

  let mk_is_int ?(info=Dummy) t = Atom.mk_app (Predicate.Psym IsInt) [t] ~info

  let is_to_real = function Term.FunApp(ToReal, _, _) -> true | _ -> false
  let is_to_int = function Term.FunApp(ToInt, _, _) -> true | _ -> false

  let psym_of_atom = function
    | Atom.App(Predicate.Psym sym, _, _) -> sym
    | _ -> assert false
  let is_is_int atom = Stdlib.(=) IsInt (psym_of_atom atom)

  let let_to_real = function
    | Term.FunApp(ToReal, [t], info) -> t, info
    | _ -> assert false
  let let_to_int = function
    | Term.FunApp(ToInt, [t], info) -> t, info
    | _ -> assert false
  let let_is_int = function
    | Atom.App(Predicate.Psym IsInt, [t], info) -> t, info
    | _ -> assert false

  let origin_of sorts = List.map sorts ~f:(function
      | T_int.SInt -> T_int.zero ()
      | T_real.SReal -> T_real.rzero ()
      | T_bool.SBool -> T_bool.mk_false ()
      | _ -> failwith "not supported")
end
and T_num : Type.T_numType
  with type term := Term.t and
  type rterm := Term.t and
  type atom := Atom.t and
  type ratom := Atom.t
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
      try let _ = Z.of_string ident in Term.mk_fsym_app (Value (ident, Ident.mk_fresh_svar ()))  [] ~info
      with _ -> begin try
            let _ = Q.of_string ident in Term.mk_fsym_app (Value (ident, Ident.mk_fresh_svar ()))  [] ~info
          with _ -> begin try
                let _ = Q.of_float @@ float_of_string ident in Term.mk_fsym_app (Value (ident, Ident.mk_fresh_svar ()))  [] ~info
              with _ -> raise NotValue
            end 
        end
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

  let is_nadd = function Term.FunApp(NAdd _, _, _) -> true | _ -> false 
  let is_nsub = function Term.FunApp(NSub _, _, _) -> true | _ -> false 
  let is_nmult = function Term.FunApp(NMult _, _, _) -> true | _ -> false 
  let is_ndiv = function Term.FunApp(NDiv _, _, _) -> true | _ -> false 
  let is_npower = function Term.FunApp(NPower _, _, _) -> true | _ -> false 
  let is_nneg = function Term.FunApp(NNeg _, _, _) -> true | _ -> false
  let is_ngeq = function Atom.App(Predicate.Psym NGeq _, _, _) -> true | _ -> false
  let is_nleq = function Atom.App(Predicate.Psym NLeq _, _, _) -> true | _ -> false
  let is_ngt = function Atom.App(Predicate.Psym NGt _, _, _) -> true | _ -> false
  let is_nlt = function Atom.App(Predicate.Psym NLt _, _, _) -> true | _ -> false

  let let_nadd = function Term.FunApp(NAdd _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nsub = function Term.FunApp(NSub _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nmult = function Term.FunApp(NMult _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_ndiv = function Term.FunApp(NDiv _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_npower = function Term.FunApp(NPower _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nneg = function Term.FunApp(NNeg _, [t1], info) -> t1, info | _ -> assert false
  let let_ngeq = function Atom.App(Predicate.Psym NGeq _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nleq = function Atom.App(Predicate.Psym NLeq _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_ngt = function Atom.App(Predicate.Psym NGt _, [t1; t2], info) -> t1, t2, info | _ -> assert false
  let let_nlt = function Atom.App(Predicate.Psym NLt _, [t1; t2], info) -> t1, t2, info | _ -> assert false

  let is_value = function | Term.FunApp(Value _, _, _) -> true | _ -> false

  let fsym_of_num_fsym fsym sort=
    match sort with
    |T_int.SInt -> begin
        match fsym with
        | Value (value, _) ->        
          begin try T_int.Int (Z.of_string value) 
            with _ -> begin try T_int.Int (Z.of_int (Q.to_int @@ Q.of_string value)) 
                with _ -> begin try T_int.Int (Z.of_int @@ Q.to_int @@ Q.of_float @@ float_of_string value) 
                    with _ -> raise NotValue end end end
        | NAdd _ -> T_int.Add
        | NSub _ -> T_int.Sub
        | NMult _ -> T_int.Mult
        | NDiv _ -> T_int.Div
        | NPower _ -> T_int.Power
        | NNeg _ -> T_int.Neg
        | _ -> fsym
      end
    |T_real.SReal -> begin
        match fsym with
        | Value (value, _) ->        
          begin try T_real.Real (Q.of_string value) 
            with _ -> begin try T_real.Real(Q.of_float @@ float_of_string value) 
                with _ -> raise NotValue end end
        | NAdd _ -> T_real.RAdd
        | NSub _ -> T_real.RSub
        | NMult _ -> T_real.RMult
        | NDiv _ -> T_real.RDiv
        | NPower _ -> T_real.RPower
        | NNeg _ -> T_real.RNeg
        | _ -> fsym
      end
    |_ -> assert false
  let psym_of_num_psym psym sort =
    match sort with
    |T_int.SInt -> begin
        match psym with
        | NGeq _ -> T_int.Geq
        | NLeq _ -> T_int.Leq
        | NGt _ -> T_int.Gt
        | NLt _ -> T_int.Lt
        | _ -> psym
      end
    |T_real.SReal -> begin
        match psym with
        | NGeq _ -> T_real.RGeq
        | NLeq _ -> T_real.RLeq
        | NGt _ -> T_real.RGt
        | NLt _ -> T_real.RLt
        | _ -> psym
      end
    |_ -> assert false
end
and T_array : Type.T_arrayType 
  with type term := Term.t = struct
  type fun_sym +=
    | AStore
    | ASelect
    | AConst of Sort.t
  type Sort.t += SArray of Sort.t * Sort.t

  let mk_array_sort s1 s2 = SArray (s1, s2)
  let mk_select a i = Term.mk_fsym_app ASelect [a;i]
  let mk_store a i e = Term.mk_fsym_app AStore [a;i;e]

  let mk_const_array sa v = Term.mk_fsym_app (AConst (sa)) [v]

  let index_sort_of sa =
    match sa with
    | SArray (si, _) -> si
    | _ -> failwith "not array sort"

  let elem_sort_of sa =
    match sa with
    | SArray (_, se) -> se
    | _ -> failwith "not array sort"

  let is_select = function | Term.FunApp(ASelect, _, _) -> true | _ -> false
  let is_store = function | Term.FunApp(AStore, _, _) -> true | _ -> false

  let let_select = function | Term.FunApp(ASelect, [a; i], info) -> a, i, info | _ -> assert false

  let let_store = function | Term.FunApp(AStore, [a; i; e], info) -> a, i, e, info | _ -> assert false

  let eval_select arr i =
    let rec aux t = 
      match t with
      | Term.FunApp(AStore, [arr1; i1; e1], _) ->
        if Stdlib.(=) i i1 then begin
          (* print_endline @@ sprintf "eval select : %s [%s]->%s" (Term.str_of arr) (Term.str_of i) (Term.str_of e1); *)
          Some e1
        end else aux arr1 
      | Term.FunApp(AConst _, [e1], _) ->
        (* print_endline @@ sprintf "eval select : %s [%s]->%s" (Term.str_of arr) (Term.str_of i) (Term.str_of e1);  *)
        Some e1
      | _ -> None
    in
    aux arr
end

and T_recfvar : Type.T_recfvarType
  with type term := Term.t and
  type formula := Formula.t 
= struct
  type fun_sym += RecFVar of Ident.tvar * (Ident.tvar * Sort.t) list * Sort.t * Term.t

  let mk_recfvar_app ?(info=Dummy) tvar env sort body ts = Term.FunApp(RecFVar (tvar, env, sort, body), ts, info)

  let is_recfvar_sym = function RecFVar _ -> true | _ -> false
  let is_recfvar_app = function |Term.FunApp(RecFVar(_, _, _, _), _, _) -> true | _ -> false


  let property_of fenv phi =
    if Set.Poly.is_empty fenv then Formula.mk_true ()
    else
      let recterms = Formula.filtered_terms_of phi ~f:(is_recfvar_app) in
      Set.Poly.filter_map recterms ~f:( function
          | Term.FunApp(RecFVar(name, _, _, _), args, _) ->
            begin match Set.Poly.find fenv ~f:(fun (name1, _, _, _, _) -> Stdlib.(=) name name1) with
              | Some (_, _, _, _, property) ->
                Some (Set.Poly.map property ~f:(fun phi ->
                    let (_, env, phi', _) = Formula.let_bind phi in
                    let sub = SortMap.of_list @@ List.map2_exn (SortEnv.list_of env) args ~f:(fun (tvar, _) t -> (tvar, t)) in
                    Formula.subst sub phi') |> Set.Poly.to_list |> Formula.and_of) 
              |_ -> None
            end
          | _ -> None) |> Set.Poly.to_list |> Formula.and_of

  let defined_atom_formula_of polarity fenv phi =
    (assert (Formula.is_atom phi));
    if Set.Poly.is_empty fenv then phi
    else
      let property = property_of fenv phi in
      if Formula.is_true property then if polarity then phi else Formula.mk_neg phi 
      else if polarity then Formula.mk_and property phi else Formula.mk_neg @@ Formula.mk_imply property phi

  (*assume phi is nnf*)
  let rec defined_formula_of_aux fenv phi =
    let open Formula in
    match phi with
    | Atom _ -> defined_atom_formula_of true fenv phi
    | UnaryOp(Not, phi, _) -> defined_atom_formula_of false fenv phi
    | BinaryOp(op, phi1, phi2, info) -> BinaryOp(op, defined_formula_of_aux fenv phi1, defined_formula_of_aux fenv phi2, info)
    | Bind(binder, env, phi, info) -> Bind(binder, env, defined_formula_of_aux fenv phi, info)
    | _ -> failwith "unsupported"

  let defined_formula_of fenv phi =
    if Set.Poly.is_empty fenv then phi
    else defined_formula_of_aux fenv @@ Formula.nnf_of phi

end
and T_dt: Type.T_dtType
  with type term := Term.t and
  type atom := Atom.t and
  type dtenv := DTEnv.t and
  type dt := Datatype.t and
  type dtcons := Datatype.cons and
  type dtsel := Datatype.sel and
  type flag := Datatype.flag 
= struct
  type fun_sym += 
    | DTSel of string * Datatype.t * Sort.t
    | DTCons of string * Sort.t list * Datatype.t 
  type pred_sym += 
    | IsCons of string * Datatype.t
    | IsNotCons of string * Datatype.t
  type Sort.t += 
    | SDT of Datatype.t
    | SUS of string * (Sort.t list) 



  let pars_of = function | SDT(dt) -> Datatype.args_of dt | _ -> assert false


  let mk_cons ?(info=Dummy) dt name terms =
    match Datatype.look_up_cons dt name with
    | Some(cons) ->
      let fsym = Datatype.fsym_of_cons dt cons in
      Term.mk_fsym_app fsym terms ~info
    |_ -> failwith @@ "unkonwn cons :" ^ name

  let mk_sel ?(info=Dummy) dt name term =
    match Datatype.look_up_sel dt name with
    | Some(sel) ->
      let fsym = Datatype.fsym_of_sel dt sel in
      Term.mk_fsym_app fsym [term] ~info
    | _ -> failwith @@ "unkonwn sel :" ^ name

  let mk_is_cons ?(info=Dummy) dt cons term =
    Atom.mk_psym_app (IsCons (Datatype.name_of_cons cons, Datatype.fresh_of dt)) [term] ~info


  let sels_of_cons fsym =
    match fsym with
    | DTCons(name, _, dt) -> 
      (match Datatype.look_up_cons dt name with
       | Some cons -> Datatype.sels_of_cons cons
       | _ -> assert false
      )
    | _ -> assert false
  let is_sdt = function | SDT(_) -> true | _ -> false
  let is_sus = function | SUS(_) -> true | _ -> false
  let is_dt = function | SDT(dt) -> Datatype.is_dt dt | _ -> false
  let is_codt = function | SDT(dt) -> Datatype.is_dt dt | _ -> false
  let is_undef = function | SUS(_, _) -> true | _ -> false

  let rec is_finite_dt ?(his=[]) sort = 
    if (List.exists his ~f:(Stdlib.(=) sort)) then false
    else 
      match sort with
      | SDT(dt) -> 
        let conses = Datatype.conses_of dt in
        List.for_all conses ~f:(
          fun cons -> 
            let args = Datatype.sorts_of_cons_args dt cons in
            List.for_all args ~f:(fun arg -> is_finite_dt ~his:(sort::his) arg)
        )
      (* | T_bool.SBool -> true *)
      | _ -> false

  let is_cons = function Term.FunApp(DTCons _, _, _) -> true | _ -> false
  let is_sel = function Term.FunApp(DTSel _, _, _) -> true | _ -> false
  let is_is_cons = function Atom.App(Predicate.Psym(IsCons _), _, _) -> true | _ -> false
  let is_is_not_cons = function Atom.App(Predicate.Psym (IsNotCons _), _, _) -> true | _ -> false

  let rec mk_dummy sort =
    match sort with
    | SDT(dt) when Datatype.is_dt dt-> 
      begin match Datatype.look_up_base_cons dt with
        | Some cons -> 
          let sorts = Datatype.sorts_of_cons_args dt cons in
          mk_cons dt (Datatype.name_of_cons cons)  (List.map sorts ~f:mk_dummy)
        | None -> assert false
      end

    | SUS(name, _) as sort -> Term.mk_var (Ident.Tvar("dummy_" ^ name)) sort
    | _ -> Term.mk_dummy sort
end
and Datatype : Type.DatatypeType = struct
  type sel = 
    | Sel  of string * Sort.t
    | InSel of string * string * Sort.t list
  type cons =  {
    name :string ;
    sels : sel list
  }
  type func = | FCons of cons | FSel of sel
  type flag = | FDt | FCodt | Undef
  type dt = {
    name : string ;
    args : Sort.t list ;
    conses : cons list
  }
  type t =  {
    name : string ;
    dts  :  dt list;
    flag : flag
  }

  let verbose = false

  let print_endline str = if verbose then print_endline str else ()

  let mk_dt name args = {name = name; args = args; conses = []}
  let create name dts flag = {name = name; dts = dts; flag = flag}
  let mk_uninterpreted_datatype ?(numeral=0) name = 
    let rec aux numeral =
      if numeral = 0 then []
      else Sort.mk_fresh_svar () :: (aux (numeral - 1))
    in
    create name [mk_dt name @@ aux numeral] Undef

  let update_name t name = {t with name = name}

  let mk_cons ?(sels=[]) name  = {name = name; sels = sels}
  let mk_sel name ret_sort = Sel(name, ret_sort)
  let mk_insel name ret_name args= InSel(name, ret_name, args)
  (* let mk_poly_sel name = PolySel(name, Sort.mk_fresh_svar) *)

  let dts_of t = t.dts
  let name_of t = t.name
  let flag_of t = t.flag
  let name_of_dt (dt:dt) = dt.name
  let args_of_dt (dt:dt) = dt.args
  let conses_of_dt (dt:dt) = dt.conses
  let sels_of_cons (cons:cons) = cons.sels
  let name_of_cons (cons:cons) = cons.name  
  let name_of_sel = 
    function 
    (* | PolySel (name, _, _)  *)
    | Sel(name, _) 
    | InSel(name, _, _) -> name

  let look_up_dt t name = 
    List.find ~f:(fun dt -> Stdlib.(=) name @@ name_of_dt dt) @@ dts_of t

  let dt_of t =
    match look_up_dt t @@ name_of t with
    | Some dt -> dt
    | _ -> assert false

  let conses_of t = dt_of t |> conses_of_dt
  let sels_of t = 
    let conses = conses_of t in
    List.fold_left conses ~init:[] ~f:(
      fun ret cons -> ret @ sels_of_cons cons 
    )
  let args_of t = dt_of t |> args_of_dt
  let full_name_of t =
    let name = name_of t in
    let args = args_of t in
    List.fold_left args ~init:(name) ~f:(
      fun ret arg -> ret ^ " " ^ Term.str_of_sort arg
    )
  let full_name_of_dt dt =
    let name = name_of_dt dt in
    let args = args_of_dt dt in
    List.fold_left args ~init:(name) ~f:(
      fun ret arg -> ret ^ " " ^ Term.str_of_sort arg
    )

  let is_dt t = match flag_of t with|FDt  -> true | _ -> false
  let is_codt t = match flag_of t with|FCodt  -> true | _ -> false
  let is_undef t = match flag_of t with|Undef   -> true | _ -> false
  let is_sel = function | Sel _ -> true | _ -> false
  let is_insel = function |InSel _ -> true | _ -> false
  let is_fcons = function | FCons _ -> true | _ -> false
  let is_fsel = function | FSel _ -> true | _ -> false

  let update_dts t dts = {t with dts = dts}

  let rec update_dts_with_dt dts dt =
    match dts with
    | [] -> []
    | dt1::tl -> 
      if Stdlib.(=) (name_of_dt dt1) @@ name_of_dt dt then
        dt::tl
      else
        dt1::(update_dts_with_dt tl dt)

  let update_dt t dt = {t with dts = update_dts_with_dt (dts_of t) dt}

  let str_of_sel = function
    (* | PolySel(name, ret_sort, _) *)
    | Sel(name, ret_sort) ->
      sprintf "%s:%s" name (Term.str_of_sort ret_sort)
    | InSel(name, ret_name, args) -> 
      List.fold_left args ~init:(sprintf "%s:%s" name ret_name) ~f:(
        fun ret arg -> ret ^ "_" ^ Term.str_of_sort arg
      )

  let str_of_cons cons = 
    let name = name_of_cons cons in
    let sels = sels_of_cons cons in
    List.fold_left sels ~init:(name) ~f:(
      fun ret sel -> ret ^ " " ^ (str_of_sel sel)
    )

  let full_str_of_sel dt sel =
    match sel with   
    | Sel(name, ret_sort) ->
      sprintf "%s:%s" name (Term.str_of_sort ret_sort)
    | InSel(name, ret_name, _) -> sprintf "%s:%s" name (full_name_of @@ update_name dt ret_name)


  let full_str_of_cons dt cons =
    let name = name_of_cons cons in
    let sels = sels_of_cons cons in
    List.fold_left sels ~init:(name) ~f:(
      fun ret sel -> ret ^ " " ^ (full_str_of_sel dt sel)
    )
  let str_of_flag = function | FCodt -> "codt" | FDt -> "dt" | Undef -> "undef"
  let str_of t =
    let dts = dts_of t in
    List.foldi dts ~init:(full_name_of t ^ ":\n") ~f:(
      fun i ret dt ->
        let ret = if i = 0 then ret else ret ^ "\n and " in
        ret ^ sprintf "(%s:%s) %s" 
          (str_of_flag @@ flag_of t) 
          (full_name_of_dt dt) 
          (* (List.fold_left (args_of_dt dt) ~init:"" ~f:(
              fun ret arg -> ret ^ " " ^ Term.str_of_sort arg)) *)
          (List.fold_left (conses_of_dt dt) ~init:"" ~f:(
              fun ret cons -> ret ^ "\n| " ^ str_of_cons cons))
    ) 

  let str_of_sorts sorts = 
    List.fold_left sorts ~init:"" ~f:(fun ret sort -> ret ^ " " ^ Term.str_of_sort sort)
  let rec update_dt_args t dt args his =
    (match his with
     |[_] -> 
       print_endline @@ sprintf ">>>>>update dt args:%s with {%s}" (full_name_of_dt dt) (str_of_sorts args)
     | _ -> 
       print_endline @@ sprintf ">>>>>>>>>>>update dt args:%s with {%s}" (full_name_of_dt dt) (str_of_sorts args));
    let conses = conses_of_dt dt in
    let args1 = args_of_dt dt in
    let conses' =  List.fold2_exn args1 args ~init:(conses)~f:(
        fun (conses) arg1 arg ->
          List.map conses ~f:(
            fun cons -> 
              let sels = sels_of_cons cons in
              let sels' = List.map sels ~f:(
                  fun sel -> match sel with
                    | Sel(name, (Sort.SVar _ as svar)) when Stdlib.(=) svar arg1 ->
                      begin match arg with
                        |T_dt.SDT(t1) -> 
                          begin match look_up_dt t (name_of t1) with
                            | Some _ -> InSel(name, (name_of t1), (args_of t1))
                            | _ -> Sel(name, arg)
                          end
                        |_ -> Sel(name, arg)
                      end
                    | InSel(name, ret_name, args) ->
                      let args' = List.map args ~f:(fun svar -> if(Stdlib.(=) svar arg1) then arg else svar) in
                      InSel(name, ret_name, args')
                    | _ -> sel
                ) in {cons with sels = sels'}
          )
      ) in
    let t' = List.fold_left conses' ~init:t ~f:(
        fun t cons -> List.fold_left (sels_of_cons cons) ~init:t ~f:(
            fun t sel -> match sel with
              | Sel _ -> t
              | InSel (_, ret_sort, args) -> 
                if (not @@ List.exists his ~f:(Stdlib.(=) ret_sort)) then (
                  let t', dt' = update_dt_args (update_name t ret_sort) (dt_of @@ update_name t ret_sort) args (ret_sort::his) in
                  update_name (update_dt t' dt') (name_of t)
                )
                else t
          )
      ) in
    t', {dt with args = args ; conses = conses'}
  and update_args t args = 
    let dt = dt_of t in
    print_endline @@ sprintf "update dt args:%s with {%s}" (full_name_of_dt dt) (str_of_sorts args);
    let t', dt' = update_dt_args t dt args [name_of t] in
    let ret = update_dt t' dt' in
    print_endline @@ sprintf "after update:%s" (str_of ret);
    ret

  let full_dts_of t =
    let name = name_of t in
    List.fold_left (conses_of t) ~init:t ~f:(
      fun ret cons ->
        List.fold_left (sels_of_cons cons) ~init:ret ~f:(
          fun ret sel ->
            match sel with
            | InSel(_, ret_name, args) ->
              if Stdlib.(<>) name ret_name then update_args (update_name ret ret_name) args 
              else ret
            | _ -> ret
        )
    ) |> dts_of

  let update_conses t conses = update_dt t {(dt_of t) with conses = conses}

  let add_cons t cons = 
    let dt = dt_of t in
    let conses = conses_of_dt dt in
    update_dt t {dt with conses = cons :: conses}

  let add_sel cons sel =
    let sels = sels_of_cons cons in
    {cons with sels = sel::sels}

  let look_up_cons t name =
    conses_of t |>
    List.find ~f:(fun cons -> Stdlib.(=) name (name_of_cons cons))

  let look_up_sel_of_cons cons name =
    sels_of_cons cons |>
    List.find ~f:(fun sel -> Stdlib.(=) name (name_of_sel sel)) 

  let look_up_sel t name =
    conses_of t |>
    List.fold_left ~init:None ~f:(fun ret cons -> 
        match ret with
        | None -> sels_of_cons cons |>
                  List.find  ~f:(fun sel -> Stdlib.(=) name (name_of_sel sel))
        | _ -> ret)

  let look_up_func t name =
    match look_up_cons t name with
    | Some cons -> Some (FCons cons)
    | None -> 
      match look_up_sel t name with
      | Some sel -> Some (FSel sel)
      | None -> None

  let sort_of t =   
    match flag_of t with
    | Undef -> T_dt.SUS(name_of t, args_of t)
    | _ -> T_dt.SDT(t)
  let sort_of_sel t = function 
    | Sel(_, sort) -> sort 
    | InSel(_, ret_name, args) -> 
      match look_up_dt t ret_name with
      | Some _ -> sort_of @@ update_args (update_name t ret_name) args
      | None -> failwith @@ sprintf "unkonwn sort:%s" ret_name

  let sorts_of_cons_args t cons= 
    sels_of_cons cons |>
    List.map ~f:(fun sel -> sort_of_sel t sel)

  let is_finite t = 
    let conses = conses_of t in
    not @@ List.exists conses ~f:(
      fun cons -> 
        let args = sorts_of_cons_args t cons in
        List.for_all args ~f:(
          fun arg -> Stdlib.(=) arg (T_dt.SDT(t)) && T_dt.is_finite_dt arg))

  let rec is_singleton sort =
    match sort with
    | T_dt.SDT(t) ->
      let conses = conses_of t in
      begin match conses with
        | [cons] -> 
          let args =  sorts_of_cons_args t cons in
          List.for_all args ~f:(
            fun arg -> Stdlib.(=) arg sort || is_singleton arg
          )
        | _ -> false 
      end
    | _ -> false

  let fresh_of t =
    let dts = dts_of t in
    let dts' = List.map dts ~f:(
        fun dt ->
          let args = args_of_dt dt in
          let args' = List.map args ~f:(function |Sort.SVar _ -> Sort.mk_fresh_svar () | arg -> arg) in
          snd @@ update_dt_args t dt args' []
      ) in
    {t with dts = dts'}

  let fsym_of_cons t cons =
    let t = fresh_of t in
    match look_up_cons t @@ name_of_cons cons with
    | Some cons -> T_dt.DTCons(name_of_cons cons, sorts_of_cons_args t cons, t)
    | None -> assert false

  let fsym_of_sel t sel =
    let t = fresh_of t in
    match look_up_sel t @@ name_of_sel sel with
    | None -> assert false
    | Some sel ->
      match sel with
      | Sel (name, ret_sort) -> T_dt.DTSel(name, t, ret_sort)
      | InSel (name, ret_name, args) -> 
        match look_up_dt t ret_name with
        | Some _ -> T_dt.DTSel(name, t, sort_of @@ update_args (update_name t ret_name) args)
        | None -> failwith @@ sprintf "unkonwn dt sort:%s" ret_name

  let fsym_of_func t func =
    match func with
    | FCons cons -> fsym_of_cons t cons
    | FSel sel -> fsym_of_sel t sel

  let look_up_base_cons t =
    let has_direct_base t =
      let conses = conses_of t in
      List.exists conses ~f:(
        fun cons -> 
          let sels = sels_of_cons cons in
          List.for_all sels ~f:(
            fun sel -> match sel with | Sel _ -> true | InSel _ -> false
          )
      )
    in
    let rec look_up_other_base t his=
      if List.exists his ~f:(fun t1 -> Stdlib.(=) (name_of t) (name_of t1)) then None
      else
        conses_of t
        |> List.sort ~compare:(
          fun cons1 cons2 -> 
            let sels1, sels2 = (sels_of_cons cons1), (sels_of_cons cons2) in
            if List.length sels1 < List.length sels2 then - 1
            else if List.length sels1 > List.length sels2  then 1
            else 0
        )
        |> List.find ~f:(
          fun cons -> 
            let sels = sels_of_cons cons in
            List.for_all sels ~f:(
              fun sel -> match sel with 
                | Sel _ -> true 
                | InSel(_, ret_name, _) -> 
                  let ret_dt = update_name t ret_name in
                  if has_direct_base ret_dt then true
                  else Option.is_some @@ look_up_other_base ret_dt (t::his)
            )
        )
    in
    let conses = conses_of t in
    List.find conses ~f:(
      fun cons -> 
        let sels = sels_of_cons cons in
        List.for_all sels ~f:(
          fun sel -> match sel with 
            | Sel _ -> true 
            | InSel(_, ret_name, _) -> Option.is_some @@ look_up_other_base (update_name t ret_name) [t]
        ) 
    )

end
and DTEnv : Type.DTEnvType 
  with type flag := Datatype.flag 
   and type datatype := Datatype.t
   and type dtfunc := Datatype.func
   and type formula := Formula.t 
=struct

  type t = (string, Datatype.t) Map.Poly.t

  let look_up_dt t name = Map.Poly.find t name 
  let look_up_func t name =
    (* print_endline @@ "find func: " ^ name;  *)
    Map.Poly.fold t ~init:None ~f:(
      fun ~key:_ ~data:dt ret  ->
        (* print_endline @@ Datatype.str_of dt; *)
        match ret with
        | Some _ -> ret
        | None -> 
          match Datatype.look_up_func dt name with
          | Some (func) -> 
            (* print_endline ("finded:" ^ (Datatype.str_of_func func));  *)
            Some (dt, func)
          | None -> 
            (* print_endline "not finded!";  *)
            ret
    )

  let update_dt t dt = 
    let name = Datatype.name_of dt in
    match look_up_dt t name with
    | Some _ -> Map.Poly.set t ~key:name ~data:dt
    | None   -> Map.Poly.add_exn t ~key:name ~data:dt

  let update_dts t dt =
    let dts = Datatype.dts_of dt in
    List.fold_left dts ~init:t ~f:(
      fun env dt1 ->
        update_dt env @@ Datatype.update_name dt (Datatype.name_of_dt dt1))

  let str_of t =
    Map.Poly.fold t ~init:"datatype env:" ~f:(
      fun ~key:_  ~data:dt ret-> ret ^ "\n" ^ Datatype.str_of dt
    )

  let sort_of_name t name =
    match name with
    | "Int" -> T_int.SInt
    | "Real" -> T_real.SReal
    | "Bool" -> T_bool.SBool
    | _ ->
      match look_up_dt t name with
      | Some dt -> Datatype.sort_of dt
      | _ -> failwith ("unkonwn sort : " ^ name )

  let name_is_cons t name =
    match look_up_func t name with
    | Some (_, func) -> Datatype.is_fcons func | _ -> false

  let name_is_sel t name =
    match look_up_func t name with
    | Some (_, func) -> Datatype.is_fsel func | _ -> false

  let name_is_func t name =
    match look_up_func t name with
    | Some _ -> true | _ -> false

  let merge env1 env2 =
    Map.Poly.fold env2 ~init:env1 ~f:(
      fun ~key ~data ret -> Map.Poly.set ret ~key ~data
    )

  let rec of_sort = function 
    | T_dt.SDT (dt) -> 
      let args = Datatype.args_of dt in
      let full_name = Datatype.full_name_of dt in
      Map.Poly.singleton full_name dt 
      |> merge @@ of_sorts args
    | _ -> Map.Poly.empty
  and of_sorts sorts =
    List.fold sorts ~init:(Map.Poly.empty) ~f:(
      fun ret sort -> merge ret @@ of_sort sort
    )

  let rec of_term term =
    match term with
    | Term.FunApp(T_dt.DTSel (_, dt, ret_sort), ts, _)  ->
      of_sort (T_dt.SDT(dt))
      |> merge (of_sort ret_sort) 
      |> merge @@ of_terms ts
    | Term.FunApp(T_dt.DTCons (_, args, dt), ts, _) ->
      of_sort (T_dt.SDT(dt))
      |> merge (of_sorts args)
      |> merge @@ of_terms ts
    | Term.FunApp (T_bool.Formula phi, _, _) -> of_formula phi
    | Term.FunApp (FVar (_, sorts), ts, _) -> merge (of_sorts sorts) (of_terms ts)
    | Term.Var (_, T_dt.SDT(dt), _) -> of_sort (T_dt.SDT(dt))
    | Term.FunApp(_, ts, _)  ->  merge (of_terms ts) @@ of_sort (Term.sort_of term )
    | _ -> Map.Poly.empty
  and of_terms terms =
    List.fold_left terms ~init:Map.Poly.empty ~f:(fun ret term -> merge ret (of_term term))
  and of_atom atom = 
    match atom with
    | Atom.App(Predicate.Psym (T_dt.IsCons (_, dt)), [t], _) ->
      of_sort (T_dt.SDT(dt))
      |> merge @@ of_term t
    | Atom.App(_, ts, _) -> of_terms ts
    | _ -> Map.Poly.empty
  and of_formula phi =
    match phi with
    | Formula.Atom (atom, _) -> of_atom atom
    | Formula.UnaryOp(_, phi, _) -> of_formula phi
    | Formula.BinaryOp(_, phi1, phi2, _) -> merge (of_formula phi1) (of_formula phi2)
    | Formula.Bind(_, _, phi, _) -> of_formula phi
    | _ -> failwith "unsupported"

end

and TermSubst : Type.TermSubstType
  with type term := Term.t = struct
  type t = (Ident.tvar, Term.t) Map.Poly.t

  let empty = Map.Poly.empty
  let merge sub1 sub2 = Map.Poly.merge sub1 sub2
      ~f:(fun ~key:_ -> function `Left t | `Right t -> Some t
                               | `Both (t1, t2) -> if Stdlib.(=) t1 t2 then Some t1 else assert false)

  let str_of_model model =
    String.concat ~sep:", " @@
    List.map model ~f:(function
        | (Ident.Tvar ident, _), None ->
          Printf.sprintf "%s |-> *" ident
        | (Ident.Tvar ident, _), Some value ->
          Printf.sprintf "%s |-> %s" ident (Term.str_of value))

  let str_of subst =
    String.concat ~sep:", " @@
    List.map (Map.Poly.to_alist subst) ~f:(fun (x, term) ->
        Printf.sprintf "%s |-> %s" (Ident.str_of_tvar x) (Term.str_of term))
end

and Rand : Type.RandType
  with type term := Term.t and
  type termSubst := TermSubst.t = struct

  type t = Uniform of Term.t * Term.t | Gauss of Term.t * Term.t

  let mk_uniform t1 t2 =
    let t1 = match t1 with
      | Term.FunApp(fsym, ts, _) -> Term.mk_fsym_app (T_num.fsym_of_num_fsym fsym T_real.SReal) ts
      | _ -> t1 in
    let t2 = match t2 with
      | Term.FunApp(fsym, ts, _) -> Term.mk_fsym_app (T_num.fsym_of_num_fsym fsym T_real.SReal) ts
      | _ -> t2 in
    Uniform (t1, t2)
  let mk_gauss t1 t2 =
    let t1 = match t1 with
      | Term.FunApp(fsym, ts, _) -> Term.mk_fsym_app (T_num.fsym_of_num_fsym fsym T_real.SReal) ts
      | _ -> t1 in
    let t2 = match t2 with
      | Term.FunApp(fsym, ts, _) -> Term.mk_fsym_app (T_num.fsym_of_num_fsym fsym T_real.SReal) ts
      | _ -> t2 in
    Gauss (t1, t2)

  let subst map = function
    | Uniform (t1, t2) -> mk_uniform (Term.subst map t1) (Term.subst map t2)
    | Gauss (t1, t2) -> mk_gauss (Term.subst map t1) (Term.subst map t2)

  let sort_of = function
    | Uniform (_, _) -> T_real.SReal
    | Gauss (_, _) -> T_real.SReal

  let str_of = function
    | Uniform (t1, t2) ->
      Printf.sprintf "Uniform(%s, %s)" (Term.str_of t1) (Term.str_of t2)
    | Gauss (t1, t2) ->
      Printf.sprintf "Gauss(%s, %s)" (Term.str_of t1) (Term.str_of t2)
end

let remove_dontcare_elem ?(freshvar=false) ((x, s), v) =
  match v with
  | None -> x, if freshvar then Term.mk_var (Ident.mk_fresh_dontcare (Ident.name_of_tvar x)) s else Term.mk_dummy s
  | Some t -> x, t
let remove_dontcare ?(freshvar=false) m =
  List.filter m ~f:(function
      | ((Ident.Tvar "div0", Sort.SArrow (_, _)), None) -> false (* bug of model generation of z3 4.8.8? *)
      | ((Ident.Tvar "mod0", Sort.SArrow (_, _)), None) -> false (* bug of model generation of z3 4.8.8? *)
      | ((Ident.Tvar "array-ext", Sort.SArrow(_, _)), None) -> false
      | _ -> true)
  |> List.map ~f:(remove_dontcare_elem ~freshvar)


let dummy_term_senv = ref SortEnv.empty
let is_dummy_term tvar sort =
  SortEnv.exists !dummy_term_senv ~f:(
    fun (tvar1, sort1) -> Stdlib.(=) tvar tvar1 && (match sort with | Some sort -> Stdlib.(=) sort sort1 | _ -> true)
  )
let add_dummy_term tvar sort =
  if (not @@ is_dummy_term tvar (Some sort)) && T_dt.is_sus sort then begin
    dummy_term_senv := SortEnv.append (!dummy_term_senv) @@ SortEnv.of_list [tvar, sort]
  end
let mk_fresh_dummy_term sort =
  match sort with
  | T_dt.SUS (name, _) -> 
    let tvar = Ident.mk_fresh_dummy_tvar name in
    let term = Term.mk_var tvar sort in
    add_dummy_term tvar sort;
    term
  | _ -> assert false
